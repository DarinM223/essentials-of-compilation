module type R1 = sig
  include Chapter1.R0

  type 'a var
  val var : 'a var -> 'a exp
  val fresh : unit -> 'a var
  val var_of_string : string -> 'a var
  val string_of_var : 'a var -> string
  val lett : 'a var -> 'a exp -> 'b exp -> 'b exp
end

module type R1_Let = sig
  include R1
  val ( let* ) : 'a exp -> ('a var -> 'b exp) -> 'b exp
end

module R1_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R1
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) :
  R1
    with type 'a exp = 'a X_exp.term
     and type 'a program = 'a X_program.term
     and type 'a var = 'a F.var
     and type 'a obs = 'a F.obs = struct
  include Chapter1.R0_T (X_exp) (X_program) (F)
  open X_exp
  type 'a var = 'a F.var
  let string_of_var = F.string_of_var
  let var v = fwd @@ F.var v
  let fresh = F.fresh
  let var_of_string = F.var_of_string
  let lett v e b = fwd @@ F.lett v (bwd e) (bwd b)
end

module R1_R_T (R : Chapter1.Reader) (F : R1) = struct
  include Chapter1.R0_R_T (R) (F)
  type 'a var = 'a F.var

  let var v _ = F.var v
  let string_of_var = F.string_of_var
  let fresh = F.fresh
  let var_of_string = F.var_of_string
  let lett v e b r =
    let e = e r in
    let b = b r in
    F.lett v e b
end

module TransformLetPass (F : R1) = struct
  module R = Chapter1.UnitReader
  module IDelta = struct
    let ( let* ) e f r =
      let e = e r in
      let var = F.fresh () in
      let body = f var r in
      F.lett var e body
  end
end

module TransformLet (F : R1) : R1_Let with type 'a obs = 'a F.obs = struct
  module M = TransformLetPass (F)
  include R1_R_T (M.R) (F)
  include M.IDelta
end

module R1_Partial (F : R1) : R1 with type 'a obs = 'a F.program = struct
  module M = Chapter1.R0_Partial_Pass (F)
  include R1_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module R1_Pretty () = struct
  include Chapter1.R0_Pretty
  type 'a var = string
  let string_of_var v = v
  let var v = "(var " ^ v ^ ")"

  let fresh =
    let c = ref (-1) in
    fun () ->
      incr c;
      "tmp" ^ string_of_int !c
  let var_of_string v = v

  let lett v e b = "(let ([" ^ v ^ " " ^ e ^ "]) " ^ b ^ ")"
end

module type C0 = sig
  type var = string

  type 'a arg

  val int : int -> int arg
  val var : var -> 'a arg

  type 'a exp

  val arg : 'a arg -> 'a exp
  val read : unit -> int exp
  val neg : int arg -> int exp
  val ( + ) : int arg -> int arg -> int exp

  type 'a stmt
  val assign : var -> 'a exp -> unit stmt

  type 'a tail
  val return : 'a exp -> unit tail
  val ( @> ) : unit stmt -> unit tail -> unit tail

  type 'a program
  type label = string

  val program : ?locals:string list -> (label * unit tail) list -> unit program

  type 'a obs
  val observe : 'a program -> 'a obs
end

module C0_R_T (R : Chapter1.Reader) (F : C0) = struct
  type var = F.var
  type 'a arg = R.t -> 'a F.arg
  type 'a exp = R.t -> 'a F.exp
  type 'a stmt = R.t -> 'a F.stmt
  type 'a tail = R.t -> 'a F.tail
  type label = F.label
  type 'a program = unit -> 'a F.program
  type 'a obs = 'a F.obs
  let int i _ = F.int i
  let var v _ = F.var v
  let arg a r = F.arg (a r)
  let read () _ = F.read ()
  let neg a r = F.neg (a r)
  let ( + ) a b r = F.(a r + b r)
  let assign v e r = F.assign v (e r)
  let return e r = F.return (e r)
  let ( @> ) s t r = F.(s r @> t r)
  let program ?locals body () =
    let init = R.init () in
    let body = List.map (fun (l, t) -> (l, t init)) body in
    F.program ?locals body
  let observe p = F.observe (p ())
end

module C0_T
    (X_arg : Chapter1.TRANS)
    (X_exp : Chapter1.TRANS)
    (X_stmt : Chapter1.TRANS)
    (X_tail : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      C0
        with type 'a arg = 'a X_arg.from
         and type 'a exp = 'a X_exp.from
         and type 'a stmt = 'a X_stmt.from
         and type 'a tail = 'a X_tail.from
         and type 'a program = 'a X_program.from) =
struct
  type var = string
  type 'a arg = 'a X_arg.term
  type 'a exp = 'a X_exp.term
  type 'a stmt = 'a X_stmt.term
  type 'a tail = 'a X_tail.term
  type 'a program = 'a X_program.term
  type label = F.label

  let int i = X_arg.fwd @@ F.int i
  let var v = X_arg.fwd @@ F.var v
  let arg a = X_exp.fwd @@ F.arg @@ X_arg.bwd a
  let read () = X_exp.fwd @@ F.read ()
  let neg a = X_exp.fwd @@ F.neg @@ X_arg.bwd a
  let ( + ) a b = X_exp.fwd F.(X_arg.bwd a + X_arg.bwd b)
  let assign v e = X_stmt.fwd @@ F.assign v @@ X_exp.bwd e
  let return e = X_tail.fwd @@ F.return @@ X_exp.bwd e
  let ( @> ) s t = X_tail.fwd @@ F.( @> ) (X_stmt.bwd s) (X_tail.bwd t)
  let program ?locals body =
    X_program.fwd @@ F.program ?locals
    @@ List.map (fun (s, t) -> (s, X_tail.bwd t)) body

  type 'a obs = 'a F.obs
  let observe = F.observe
end

module C0_Pretty = struct
  type var = string
  type 'a arg = string
  let int = string_of_int
  let var = Fun.id

  type 'a exp = string
  let arg = Fun.id
  let read () = "(read)"
  let neg e = "(neg " ^ e ^ ")"
  let ( + ) a b = "(+ " ^ a ^ " " ^ b ^ ")"

  type 'a stmt = string
  let assign v e = "(assign " ^ v ^ " " ^ e ^ ")"

  type 'a tail = string
  let return e = "(return " ^ e ^ ")"
  let ( @> ) stmt rest = "(seq " ^ stmt ^ " " ^ rest ^ ")"

  type 'a program = string
  type label = string
  let info i = "(" ^ String.concat " " i ^ ")"
  let program ?(locals = []) body =
    let pair (label, tail) = "(" ^ label ^ " . " ^ tail ^ ")" in
    let body = String.concat "\n" (List.map pair body) in
    "(program ((locals . " ^ info locals ^ ")) (" ^ body ^ ")"

  type 'a obs = string
  let observe p = p
end

module StringSet = struct
  include Set.Make (String)
  let pp fmt set =
    let open Format in
    let pp_sep fmt _ = fprintf fmt ";@ " in
    fprintf fmt "{@[%a@]}" (pp_print_list ~pp_sep pp_print_string) (to_list set)
end

module StringMap = Map.Make (String)

module Arg = struct
  open Ppx_hash_lib.Std.Hash.Builtin

  type t =
    | Var of string
    | Reg of string
  [@@deriving ord, eq, hash]

  let pp fmt = function
    | Reg reg -> Format.fprintf fmt "Reg %s" reg
    | Var var -> Format.fprintf fmt "Var %s" var

  let show = Format.asprintf "%a" pp
end

module ArgSet = struct
  include Set.Make (Arg)
  let pp fmt set =
    let open Format in
    let pp_sep fmt _ = fprintf fmt ";@ " in
    fprintf fmt "{@[%a@]}" (pp_print_list ~pp_sep Arg.pp) (to_list set)
end

module ArgMap = struct
  include Map.Make (Arg)
  let pp pp_value fmt map =
    let open Format in
    let pp_sep fmt _ = fprintf fmt ";@ " in
    let pp_tuple fmt (a, b) = fprintf fmt "%a -> %a" Arg.pp a pp_value b in
    fprintf fmt "{@[%a@]}" (pp_print_list ~pp_sep pp_tuple) (to_list map)

  let find_var v map =
    match find_opt (Arg.Var v) map with
    | Some r -> r
    | None -> failwith @@ "Invalid variable: " ^ v ^ " not in map"

  let keys map = List.map fst (bindings map)
end

module type X86_0 = sig
  type 'a reg
  val rsp : int reg
  val rbp : int reg
  val rax : int reg
  val rbx : int reg
  val rcx : int reg
  val rdx : int reg
  val rsi : int reg
  val rdi : int reg
  val r8 : int reg
  val r9 : int reg
  val r10 : int reg
  val r11 : int reg
  val r12 : int reg
  val r13 : int reg
  val r14 : int reg
  val r15 : int reg

  type 'a arg
  val reg : 'b reg -> 'a arg
  val deref : 'b reg -> int -> 'a arg
  val int : int -> 'a arg
  val var : string -> 'a arg

  type label = string

  type 'a instr
  val addq : 'a arg -> 'b arg -> unit instr
  val subq : 'a arg -> 'b arg -> unit instr
  val movq : 'a arg -> 'b arg -> unit instr
  val retq : unit instr
  val negq : 'a arg -> unit instr
  val callq : label -> unit instr
  val pushq : 'a arg -> unit instr
  val popq : 'a arg -> unit instr

  type 'a block
  val block : ?live_after:ArgSet.t array -> unit instr list -> unit block

  type 'a program
  val program :
    ?stack_size:int ->
    ?conflicts:ArgSet.t ArgMap.t ->
    ?moves:ArgSet.t ArgMap.t ->
    (label * unit block) list ->
    unit program

  type 'a obs
  val observe : 'a program -> 'a obs
end

module X86_Reg_String (X86 : X86_0) = struct
  let string_of_reg : 'a. 'a X86.reg -> string =
   fun reg ->
    let reg = Hashtbl.hash reg in
    match reg with
    | reg when reg = Hashtbl.hash X86.rsp -> "rsp"
    | reg when reg = Hashtbl.hash X86.rbp -> "rbp"
    | reg when reg = Hashtbl.hash X86.rax -> "rax"
    | reg when reg = Hashtbl.hash X86.rbx -> "rbx"
    | reg when reg = Hashtbl.hash X86.rcx -> "rcx"
    | reg when reg = Hashtbl.hash X86.rdx -> "rdx"
    | reg when reg = Hashtbl.hash X86.rsi -> "rsi"
    | reg when reg = Hashtbl.hash X86.rdi -> "rdi"
    | reg when reg = Hashtbl.hash X86.r8 -> "r8"
    | reg when reg = Hashtbl.hash X86.r9 -> "r9"
    | reg when reg = Hashtbl.hash X86.r10 -> "r10"
    | reg when reg = Hashtbl.hash X86.r11 -> "r11"
    | reg when reg = Hashtbl.hash X86.r12 -> "r12"
    | reg when reg = Hashtbl.hash X86.r13 -> "r13"
    | reg when reg = Hashtbl.hash X86.r14 -> "r14"
    | reg when reg = Hashtbl.hash X86.r15 -> "r15"
    | _ -> failwith "Unknown register"
  let arg_of_reg reg = Arg.Reg (string_of_reg reg)
end

module X86_0_Reg_T
    (X_reg : Chapter1.TRANS)
    (F : X86_0 with type 'a reg = 'a X_reg.from) =
struct
  let rsp = X_reg.fwd F.rsp
  let rbp = X_reg.fwd F.rbp
  let rax = X_reg.fwd F.rax
  let rbx = X_reg.fwd F.rbx
  let rcx = X_reg.fwd F.rcx
  let rdx = X_reg.fwd F.rdx
  let rsi = X_reg.fwd F.rsi
  let rdi = X_reg.fwd F.rdi
  let r8 = X_reg.fwd F.r8
  let r9 = X_reg.fwd F.r9
  let r10 = X_reg.fwd F.r10
  let r11 = X_reg.fwd F.r11
  let r12 = X_reg.fwd F.r12
  let r13 = X_reg.fwd F.r13
  let r14 = X_reg.fwd F.r14
  let r15 = X_reg.fwd F.r15
end

module X86_0_R_T (R : Chapter1.Reader) (F : X86_0) :
  X86_0
    with type 'a reg = R.t -> 'a F.reg
     and type 'a arg = R.t -> 'a F.arg
     and type 'a instr = R.t -> 'a F.instr
     and type 'a block = R.t -> 'a F.block
     and type 'a program = unit -> 'a F.program
     and type label = F.label
     and type 'a obs = 'a F.obs = struct
  type 'a reg = R.t -> 'a F.reg
  type 'a arg = R.t -> 'a F.arg
  type 'a instr = R.t -> 'a F.instr
  type 'a block = R.t -> 'a F.block
  type 'a program = unit -> 'a F.program
  type label = F.label
  include
    X86_0_Reg_T
      (struct
        type 'a from = 'a F.reg
        type 'a term = 'a reg
        let fwd r = fun _ -> r
        let bwd _ = failwith ""
      end)
      (F)
  let reg r ctx = F.reg (r ctx)
  let deref r i ctx = F.deref (r ctx) i
  let int i _ = F.int i
  let var v _ = F.var v
  let addq a b ctx = F.addq (a ctx) (b ctx)
  let subq a b ctx = F.subq (a ctx) (b ctx)
  let movq a b ctx = F.movq (a ctx) (b ctx)
  let retq _ = F.retq
  let negq a ctx = F.negq (a ctx)
  let callq l _ = F.callq l
  let pushq a ctx = F.pushq (a ctx)
  let popq a ctx = F.popq (a ctx)
  let block ?live_after instrs ctx =
    F.block ?live_after (List.map (fun f -> f ctx) instrs)
  let program ?stack_size ?conflicts ?moves blocks () =
    let init = R.init () in
    F.program ?stack_size ?conflicts ?moves
      (List.map (fun (l, b) -> (l, b init)) blocks)

  type 'a obs = 'a F.obs
  let observe p = F.observe (p ())
end

module X86_0_T
    (X_reg : Chapter1.TRANS)
    (X_arg : Chapter1.TRANS)
    (X_instr : Chapter1.TRANS)
    (X_block : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      X86_0
        with type 'a reg = 'a X_reg.from
         and type 'a arg = 'a X_arg.from
         and type 'a instr = 'a X_instr.from
         and type 'a block = 'a X_block.from
         and type 'a program = 'a X_program.from) =
struct
  type 'a reg = 'a X_reg.term
  type 'a arg = 'a X_arg.term
  type 'a instr = 'a X_instr.term
  type 'a block = 'a X_block.term
  type 'a program = 'a X_program.term
  type label = string

  include X86_0_Reg_T (X_reg) (F)

  let reg r = X_arg.fwd @@ F.reg @@ X_reg.bwd r
  let deref r i = X_arg.fwd @@ F.deref (X_reg.bwd r) i

  let int i = X_arg.fwd @@ F.int i
  let var v = X_arg.fwd @@ F.var v

  let addq a b = X_instr.fwd @@ F.addq (X_arg.bwd a) (X_arg.bwd b)
  let subq a b = X_instr.fwd @@ F.subq (X_arg.bwd a) (X_arg.bwd b)
  let movq a b = X_instr.fwd @@ F.movq (X_arg.bwd a) (X_arg.bwd b)
  let retq = X_instr.fwd F.retq
  let negq a = X_instr.fwd @@ F.negq @@ X_arg.bwd a
  let callq l = X_instr.fwd @@ F.callq l
  let pushq a = X_instr.fwd @@ F.pushq @@ X_arg.bwd a
  let popq a = X_instr.fwd @@ F.popq @@ X_arg.bwd a

  let block ?live_after instrs =
    X_block.fwd @@ F.block ?live_after @@ List.map X_instr.bwd instrs

  let program ?stack_size ?conflicts ?moves blocks =
    X_program.fwd
    @@ F.program ?stack_size ?conflicts ?moves
    @@ List.map (fun (l, b) -> (l, X_block.bwd b)) blocks

  type 'a obs = 'a F.obs
  let observe = F.observe
end

module RemoveComplexPass (F : R1) = struct
  module X = struct
    type 'a from = 'a F.exp
    type ann =
      | Simple
      | Complex
    type 'a term = ann * 'a from

    let fwd a = (Complex, a)
    let bwd (_, a) = a
  end
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)
  open X
  module IDelta = struct
    let lett v e b = fwd @@ F.lett v (bwd e) (bwd b)

    let var v = (Simple, F.var v)
    let int i = (Simple, F.int i)
    let read () = (Complex, F.read ())
    let neg (ann, e) =
      match ann with
      | Simple -> (Complex, F.neg e)
      | Complex ->
        let tmp = F.fresh () in
        lett tmp (ann, e) (Complex, F.neg (F.var tmp))
    type _ eff += Normalize : ann * 'a from -> 'a from eff
    let ( + ) (ann1, e1) (ann2, e2) =
      try
        let e1 =
          match ann1 with
          | Simple -> e1
          | Complex -> Effect.perform (Normalize (ann1, e1))
        in
        let e2 =
          match ann2 with
          | Simple -> e2
          | Complex -> Effect.perform (Normalize (ann2, e2))
        in
        (Complex, F.(e1 + e2))
      with effect Normalize (ann, e), k ->
        let tmp = F.fresh () in
        lett tmp (ann, e) (Effect.Deep.continue k (F.var tmp))
  end
end

module RemoveComplex (F : R1) : R1 with type 'a obs = 'a F.obs = struct
  module M = RemoveComplexPass (F)
  include R1_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module ExplicateControl (F : R1) (C0 : C0) () = struct
  type ctx =
    | Tail
    | Assign of string * (unit -> unit C0.tail)
    | Pred of (unit -> unit C0.tail) * (unit -> unit C0.tail)
  type ann_exp = { f : 'a. 'a C0.exp -> 'a C0.exp }
  let ann_id = { f = Fun.id }

  type 'a exp = ann_exp -> ctx -> unit C0.tail
  type 'a program = unit -> unit C0.program
  type 'a var = 'a F.var

  let table : (string, string) Hashtbl.t = Hashtbl.create 100
  let rec lookup v = try lookup (Hashtbl.find table v) with Not_found -> v

  let ( let& ) e f =
    let tmp = F.(string_of_var (fresh ())) in
    e ann_id (Assign (tmp, fun () -> f tmp))

  let string_of_var = F.string_of_var
  let fresh = F.fresh
  let var_of_string = F.var_of_string

  let convert_exp e m = function
    | Tail -> C0.return (m.f e)
    | Assign (v, body) -> C0.(assign v (m.f e) @> body ())
    | Pred _ ->
      failwith "Cannot have a non-boolean expression inside of a predicate"
  let int i = convert_exp C0.(arg (int i))

  let read () = convert_exp C0.(read ())
  let neg e m r =
    let& tmp = e in
    convert_exp C0.(neg (var (lookup tmp))) m r

  let ( + ) e1 e2 m r =
    let& tmp1 = e1 in
    let& tmp2 = e2 in
    convert_exp C0.(var (lookup tmp1) + var (lookup tmp2)) m r

  let var v m r =
    let v = lookup (F.string_of_var v) in
    match r with
    | Tail -> C0.(return (m.f (arg (var v))))
    | Assign (v', body) ->
      Hashtbl.add table v' v;
      body ()
    | Pred _ -> failwith "Predicate for var not handled yet"

  let lett v e b m r = e m (Assign (F.string_of_var v, fun () -> b ann_id r))

  let program e () = C0.(program [ ("start", e ann_id Tail) ])

  type 'a obs = unit C0.obs
  let observe p = C0.observe (p ())
end

module StringHashtbl = Hashtbl.Make (String)

module UncoverLocalsPass (F : C0) = struct
  module R = struct
    type t = unit StringHashtbl.t
    let init () = StringHashtbl.create 100
  end

  module IDelta = struct
    let assign v e tbl =
      StringHashtbl.add tbl v ();
      F.assign v (e tbl)

    let program ?locals:_ body () =
      let init = R.init () in
      let body = List.map (fun (l, t) -> (l, t init)) body in
      let locals =
        StringHashtbl.to_seq_keys init |> List.of_seq |> List.sort compare
      in
      F.(program ~locals body)
  end
end

module UncoverLocals (F : C0) : C0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLocalsPass (F)
  include C0_R_T (M.R) (F)
  include M.IDelta
end

module SelectInstructions (F : C0) (X86 : X86_0) = struct
  type 'a arg = string option * 'a X86.arg
  type ctx =
    | Assign of string
    | Return
    | If of F.label * F.label
  type info = string (* block exit label *)
  type 'a exp = ctx -> unit X86.instr list
  type 'a stmt = info -> unit X86.instr list
  type 'a tail = info -> unit X86.instr list
  type 'a program = unit X86.program
  type var = string
  type label = F.label

  let int i = (None, X86.int i)
  let var v = (Some v, X86.var v)
  let arg (_, arg) = function
    | Assign v -> X86.[ movq arg (var v) ]
    | Return -> X86.[ movq arg (reg rax) ]
    | If _ -> failwith "If not handled for arg for C0"
  let read () = function
    | Assign v -> X86.[ movq (reg rax) (var v); callq "read_int" ]
    | Return -> X86.[ callq "read_int" ]
    | If _ -> failwith "(read) cannot be a condition of if"
  let neg (v', arg) = function
    | Assign v ->
      if Some v = v' then
        X86.[ negq (var v) ]
      else
        X86.[ negq (var v); movq arg (var v) ]
    | Return -> X86.[ negq (reg rax); movq arg (reg rax) ]
    | If _ -> failwith "neg() cannot be a condition of if"
  let ( + ) (v1, arg1) (v2, arg2) = function
    | Assign v ->
      if Some v = v1 then
        X86.[ addq arg2 (var v) ]
      else if Some v = v2 then
        X86.[ addq arg1 (var v) ]
      else
        X86.[ addq arg2 (var v); movq arg1 (var v) ]
    | Return -> X86.[ addq arg2 (reg rax); movq arg1 (reg rax) ]
    | If _ -> failwith "(+) cannot be a condition of if"

  let assign v e _ = e (Assign v)

  let return e _ = X86.retq :: e Return

  let ( @> ) stmts1 stmts2 r = stmts2 r @ stmts1 r

  let program ?locals:_ body =
    X86.(program (List.map (fun (l, t) -> (l, block (List.rev (t "")))) body))

  type 'a obs = unit X86.obs
  let observe = X86.observe
end

module AssignHomesPass (X86 : X86_0) = struct
  module X_reader = struct
    type t = {
      stack_size : unit -> int;
      get_stack_slot : string -> int;
    }

    let init () =
      let stack_size = ref 0 in
      let var_table : (string, int) Hashtbl.t = Hashtbl.create 100 in
      let get_stack_slot (v : string) : int =
        match Hashtbl.find_opt var_table v with
        | Some slot -> slot
        | None ->
          stack_size := !stack_size + 8;
          let slot = - !stack_size in
          Hashtbl.add var_table v slot;
          slot
      in
      { stack_size = (fun () -> !stack_size); get_stack_slot }
  end
  module IDelta = struct
    open X_reader
    let var v ctx = X86.(deref rbp (ctx.get_stack_slot v))
    let program ?stack_size:_ ?conflicts ?moves blocks () =
      let init = init () in
      X86.program ~stack_size:(init.stack_size ()) ?conflicts ?moves
        (List.map (fun (l, b) -> (l, b init)) blocks)
  end
end

module AssignHomes (X86 : X86_0) : X86_0 with type 'a obs = 'a X86.obs = struct
  module M = AssignHomesPass (X86)
  include X86_0_R_T (M.X_reader) (X86)
  include M.IDelta
end

module PatchInstructionsPass (X86 : X86_0) = struct
  module ArgInfo = struct
    type t =
      | MemoryReference of int
      | HashedRegister of int
      | Unk
    let equal a b =
      match (a, b) with
      | MemoryReference a, MemoryReference b -> a = b
      | HashedRegister a, HashedRegister b -> a = b
      | _, _ -> false
  end

  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)

  module X_arg = struct
    type 'a from = 'a X86.arg
    type 'a term = ArgInfo.t * 'a from
    let fwd a = (ArgInfo.Unk, a)
    let bwd (_, a) = a
  end

  module X_instr = struct
    type 'a from = 'a X86.instr
    type 'a term = 'a from list
    let fwd a = [ a ]
    let bwd = List.hd
  end

  module X_block = Chapter1.MkId (struct
    type 'a t = 'a X86.block
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)

  module IDelta = struct
    open ArgInfo
    let reg v = (HashedRegister (Hashtbl.hash v), X86.reg v)
    let deref r i = (MemoryReference (Hashtbl.hash (r, i)), X86.deref r i)
    let addq (info1, a) (info2, b) =
      match (info1, info2) with
      | MemoryReference _, MemoryReference _ ->
        [ X86.(movq a (reg rax)); X86.(addq (reg rax) b) ]
      | _ -> X_instr.fwd @@ X86.addq a b
    let subq (info1, a) (info2, b) =
      match (info1, info2) with
      | MemoryReference _, MemoryReference _ ->
        [ X86.(movq a (reg rax)); X86.(subq (reg rax) b) ]
      | _ -> X_instr.fwd @@ X86.subq a b
    let movq (info1, a) (info2, b) =
      if ArgInfo.equal info1 info2 then
        []
      else
        match (info1, info2) with
        | MemoryReference _, MemoryReference _ ->
          [ X86.(movq a (reg rax)); X86.(movq (reg rax) b) ]
        | _ -> X_instr.fwd @@ X86.movq a b
    let block ?live_after instrs = X86.block ?live_after @@ List.concat instrs
  end
end

module PatchInstructions (F : X86_0) = struct
  module M = PatchInstructionsPass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module ListUtils = struct
  let[@tail_mod_cons] rec add_before_end a = function
    | [ last ] -> a @ [ last ]
    | x :: xs -> x :: add_before_end a xs
    | [] -> a
end

module X86_0_Pretty = struct
  type 'a reg = string
  type 'a arg = string
  type 'a instr = string
  type 'a block = string
  type 'a program = string
  type label = string
  type 'a obs = string
  let rsp = "rsp"
  let rbp = "rbp"
  let rax = "rax"
  let rbx = "rbx"
  let rcx = "rcx"
  let rdx = "rdx"
  let rsi = "rsi"
  let rdi = "rdi"
  let r8 = "r8"
  let r9 = "r9"
  let r10 = "r10"
  let r11 = "r11"
  let r12 = "r12"
  let r13 = "r13"
  let r14 = "r14"
  let r15 = "r15"

  let reg r = "(reg " ^ r ^ ")"
  let deref r i = "(deref " ^ r ^ " " ^ string_of_int i ^ ")"
  let int i = "(int " ^ string_of_int i ^ ")"
  let var v = "(var " ^ v ^ ")"

  let addq a b = "(addq " ^ a ^ " " ^ b ^ ")"
  let subq a b = "(subq " ^ a ^ " " ^ b ^ ")"
  let movq a b = "(movq " ^ a ^ " " ^ b ^ ")"
  let retq = "(retq)"
  let negq a = "(negq " ^ a ^ ")"
  let callq l = "(callq " ^ l ^ ")"
  let pushq a = "(pushq " ^ a ^ ")"
  let popq a = "(pushq " ^ a ^ ")"

  let pp_live_after fmt =
    let open Format in
    let pp_sep fmt _ = fprintf fmt ";@ " in
    fprintf fmt "[@[%a]@]" @@ pp_print_array ~pp_sep ArgSet.pp

  let block_info live_after =
    match live_after with
    | Some live_after -> Format.asprintf "(%a)" pp_live_after live_after
    | None -> "()"
  let enclose s = "(" ^ s ^ ")"
  let program_info stack_size conflicts moves =
    let stack_info =
      match stack_size with
      | Some stack_size -> "(stack_size . " ^ string_of_int stack_size ^ ")"
      | None -> ""
    in
    let conflict_info =
      match conflicts with
      | Some conflicts ->
        Format.asprintf "(conflicts . %a)" (ArgMap.pp ArgSet.pp) conflicts
      | None -> ""
    in
    let move_info =
      match moves with
      | Some moves -> Format.asprintf "(moves . %a)" (ArgMap.pp ArgSet.pp) moves
      | None -> ""
    in
    stack_info ^ conflict_info ^ move_info

  let block ?live_after instrs =
    "(block " ^ block_info live_after ^ "\n" ^ String.concat "\n" instrs ^ ")"

  let program_helper info body =
    "(program " ^ info ^ " "
    ^ String.concat "\n"
        (List.map (fun (l, t) -> "(" ^ l ^ " . " ^ t ^ ")") body)
    ^ ")"
  let program ?stack_size ?conflicts ?moves body =
    program_helper (enclose (program_info stack_size conflicts moves)) body
  let observe s = s
end

module X86_Info = struct
  type t = {
    stack_size : int option;
    root_stack_size : int option;
    header_footer : ((t -> string) list * (t -> string) list) option;
  }

  let init () =
    { stack_size = None; root_stack_size = None; header_footer = None }
end

module X86_0_Printer_Helper (R : Chapter1.Reader) = struct
  type 'a reg = string
  type 'a arg = string
  type 'a instr = R.t -> string
  type 'a block = R.t -> string list
  type 'a program = string
  type label = string
  type 'a obs = string

  let indent s = "  " ^ s

  let rsp = "%rsp"
  let rbp = "%rbp"
  let rax = "%rax"
  let rbx = "%rbx"
  let rcx = "%rcx"
  let rdx = "%rdx"
  let rsi = "%rsi"
  let rdi = "%rdi"
  let r8 = "%r8"
  let r9 = "%r9"
  let r10 = "%r10"
  let r11 = "%r11"
  let r12 = "%r12"
  let r13 = "%r13"
  let r14 = "%r14"
  let r15 = "%r15"

  let reg r = r
  let deref r = function
    | 0 -> "(" ^ r ^ ")"
    | i -> string_of_int i ^ "(" ^ r ^ ")"
  let int i = "$" ^ string_of_int i
  let var v = failwith @@ "Invalid var in X86Printer: " ^ v

  let addq a b _ = "addq " ^ a ^ ", " ^ b
  let subq a b _ = "subq " ^ a ^ ", " ^ b
  let movq a b _ = "movq " ^ a ^ ", " ^ b

  let pop_stack_with_instr instr info =
    match info.X86_Info.header_footer with
    | Some (_, footer) ->
      let footer = List.map (fun f -> f info) footer in
      (match footer @ [ instr ] with
      | head :: rest -> String.concat "\n" (head :: List.map indent rest)
      | [] -> failwith "Empty instruction list with footer, this can't happen")
    | None -> instr

  let retq = pop_stack_with_instr "retq"
  let negq a _ = "negq " ^ a
  let callq l _ = "callq " ^ l
  let pushq a _ = "pushq " ^ a
  let popq a _ = "popq " ^ a

  let function_prologue_epilogue stack_size =
    Option.map
      (fun stack_size ->
        let stack_size =
          if stack_size mod 16 = 0 then stack_size else stack_size + 8
        in
        ( [
            pushq rbp;
            movq rsp rbp;
            pushq r12;
            pushq rbx;
            pushq r13;
            pushq r14;
            subq (int stack_size) rsp;
          ],
          [ popq r14; popq r13; popq rbx; popq r12; movq rbp rsp; popq rbp ] ))
      stack_size

  let block ?live_after:_ instrs r =
    instrs |> List.map (fun f -> f r) |> List.map indent

  let apply_header info instrs =
    match info.X86_Info.header_footer with
    | Some (header, _) ->
      let header = List.map (fun f -> f info) header in
      List.map indent header @ instrs
    | None -> instrs

  let program_helper stack_size blocks =
    let header_footer = function_prologue_epilogue stack_size in
    let init = X86_Info.{ stack_size; root_stack_size = None; header_footer } in
    blocks
    |> List.concat_map (fun (label, block) -> (label ^ ":\n") :: block init)
    |> apply_header init

  let program ?stack_size ?conflicts:_ ?moves:_ blocks =
    String.concat "\n"
    @@ [ ".global main"; ".text"; "main:" ]
    @ program_helper stack_size blocks

  let observe s = s
end

module X86_0_Printer = X86_0_Printer_Helper (X86_Info)

module Compiler
    (T : sig
      type t
    end)
    (F : functor
      (F : R1_Let)
      -> sig
      val res : T.t F.obs
    end)
    () =
  F
    (TransformLet
       (ExplicateControl
          (R1_Pretty ())
          (SelectInstructions
             (UncoverLocals
                (C0_Pretty))
                (AssignHomes (PatchInstructions (X86_0_Printer))))
          ()))

module Ex1 (F : R1_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* x = int 12 + int 20 in
    int 10 + var x
end

module Ex2 (F : R1_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* x = int 32 in
    (let* x = int 10 in
     var x)
    + var x

  let check =
    observe @@ program
    @@
    let* x1 = int 32 in
    (let* x2 = int 10 in
     var x2)
    + var x1
end

module Ex3 (F : R1_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let* x = read () in
    let* y = read () in
    var x + neg (var y)
end

module Ex4 (F : R1) = struct
  open F
  let res = observe @@ program (int 52 + neg (int 10))
end

module Ex5 (F : R1_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 42 in
    let* b = var a in
    var b
end

module Ex6 (F : R1_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* y =
      let* x = int 20 in
      var x
      + let* x = int 22 in
        var x
    in
    var y
end

module C0_Ex1 (F : C0) = struct
  open F

  let res =
    observe
    @@ program
         [
           ( "start",
             assign "x_1" (arg (int 20))
             @> assign "x_2" (arg (int 22))
             @> assign "y" (var "x_1" + var "x_2")
             @> return (arg (var "y")) );
         ]
end

let%expect_test "Example 3 with partial evaluation" =
  let module M = Ex3 (TransformLet (R1_Pretty ())) in
  Format.printf "Ex3 pretty: %s\n" M.res;
  [%expect
    {| Ex3 pretty: (program (let ([tmp0 (read)]) (let ([tmp1 (read)]) (+ (var tmp0) (- (var tmp1)))))) |}]

let%expect_test "Example 4 remove complex" =
  let module M = Ex4 (RemoveComplex (R1_Pretty ())) in
  Format.printf "Ex4: %s\n" M.res;
  [%expect {| Ex4: (program (let ([tmp0 (- 10)]) (+ 52 (var tmp0)))) |}]

let%expect_test "Example 5 remove complex" =
  let module M = Ex5 (TransformLet (RemoveComplex (R1_Pretty ()))) in
  Format.printf "Ex5: %s\n" M.res;
  [%expect
    {| Ex5: (program (let ([tmp0 42]) (let ([tmp1 (var tmp0)]) (var tmp1)))) |}]

let%expect_test "C0 example 1 pretty printing" =
  let module M = C0_Ex1 (C0_Pretty) in
  Format.printf "C0 Ex1: %s\n" M.res;
  [%expect
    {| C0 Ex1: (program ((locals . ())) ((start . (seq (assign x_1 20) (seq (assign x_2 22) (seq (assign y (+ x_1 x_2)) (return y)))))) |}]

let%expect_test "Example 6 explicate control" =
  let module M =
    Ex6 (TransformLet (ExplicateControl (R1_Pretty ()) (C0_Pretty) ())) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {| Ex6: (program ((locals . ())) ((start . (seq (assign tmp0 20) (seq (assign tmp1 22) (seq (assign tmp2 (+ tmp0 tmp1)) (return tmp2)))))) |}]

let%expect_test "Example 6 uncover locals" =
  let module M =
    Ex6
      (TransformLet
         (ExplicateControl (R1_Pretty ()) (UncoverLocals (C0_Pretty)) ())) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {| Ex6: (program ((locals . (tmp0 tmp1 tmp2))) ((start . (seq (assign tmp0 20) (seq (assign tmp1 22) (seq (assign tmp2 (+ tmp0 tmp1)) (return tmp2)))))) |}]

let%expect_test "Example 6 select instructions" =
  let module M =
    Ex6
      (TransformLet
         (ExplicateControl
            (R1_Pretty ())
            (SelectInstructions (UncoverLocals (C0_Pretty)) (X86_0_Pretty))
            ())) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program () (start . (block ()
    (movq (int 20) (var tmp0))
    (movq (int 22) (var tmp1))
    (movq (var tmp0) (var tmp2))
    (addq (var tmp1) (var tmp2))
    (movq (var tmp2) (reg rax))
    (retq))))
    |}]

let%expect_test "Example 6 assign homes" =
  let module M =
    Ex6
      (TransformLet
         (ExplicateControl
            (R1_Pretty ())
            (SelectInstructions
               (UncoverLocals (C0_Pretty)) (AssignHomes (X86_0_Pretty)))
            ())) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program ((stack_size . 24)) (start . (block ()
    (movq (int 20) (deref rbp -8))
    (movq (int 22) (deref rbp -16))
    (movq (deref rbp -8) (deref rbp -24))
    (addq (deref rbp -16) (deref rbp -24))
    (movq (deref rbp -24) (reg rax))
    (retq))))
    |}]

let%expect_test "Example 6 patch instructions" =
  let module M =
    Ex6
      (TransformLet
         (ExplicateControl
            (R1_Pretty ())
            (SelectInstructions
               (UncoverLocals
                  (C0_Pretty))
                  (AssignHomes (PatchInstructions (X86_0_Pretty))))
            ())) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program ((stack_size . 24)) (start . (block ()
    (movq (int 20) (deref rbp -8))
    (movq (int 22) (deref rbp -16))
    (movq (deref rbp -8) (reg rax))
    (movq (reg rax) (deref rbp -24))
    (movq (deref rbp -16) (reg rax))
    (addq (reg rax) (deref rbp -24))
    (movq (deref rbp -24) (reg rax))
    (retq))))
    |}]

let%expect_test "Example 6 final printed X86" =
  let module M = Compiler (Int) (Ex6) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    main:
      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $32, %rsp
    start:

      movq $20, -8(%rbp)
      movq $22, -16(%rbp)
      movq -8(%rbp), %rax
      movq %rax, -24(%rbp)
      movq -16(%rbp), %rax
      addq %rax, -24(%rbp)
      movq -24(%rbp), %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      retq
    |}]

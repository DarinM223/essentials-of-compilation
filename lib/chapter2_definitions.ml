module type R1 = sig
  include Chapter1.R0

  type 'a var
  val var : 'a var -> 'a exp
  val fresh : unit -> 'a var
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
  let lett v e b = fwd @@ F.lett v (bwd e) (bwd b)
end

module TransformLet (F : R1) :
  R1_Let
    with type 'a exp = 'a F.exp
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  module X_exp = Chapter1.MkId (struct
    type 'a t = 'a F.exp
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)
  include R1_T (X_exp) (X_program) (F)
  let ( let* ) e f =
    let var = fresh () in
    let body = f var in
    F.lett var e body
end

module R1_R_T (R : Chapter1.Reader) (F : R1) :
  R1
    with type 'a exp = R.t -> 'a F.exp
     and type 'a program = unit -> 'a F.program
     and type 'a var = 'a F.var
     and type 'a obs = 'a F.obs = struct
  include Chapter1.R0_R_T (R) (F)
  type 'a var = 'a F.var

  let var v _ = F.var v
  let string_of_var = F.string_of_var
  let fresh = F.fresh
  let lett v e b r = F.lett v (e r) (b r)
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
  type info
  val info : string list -> info

  type label = string

  val program : info -> (label * unit tail) list -> unit program

  type 'a obs
  val observe : 'a program -> 'a obs
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
  type info = F.info

  let int i = X_arg.fwd @@ F.int i
  let var v = X_arg.fwd @@ F.var v
  let arg a = X_exp.fwd @@ F.arg @@ X_arg.bwd a
  let read () = X_exp.fwd @@ F.read ()
  let neg a = X_exp.fwd @@ F.neg @@ X_arg.bwd a
  let ( + ) a b = X_exp.fwd F.(X_arg.bwd a + X_arg.bwd b)
  let assign v e = X_stmt.fwd @@ F.assign v @@ X_exp.bwd e
  let return e = X_tail.fwd @@ F.return @@ X_exp.bwd e
  let ( @> ) s t = X_tail.fwd @@ F.( @> ) (X_stmt.bwd s) (X_tail.bwd t)
  let info = F.info
  let program info body =
    X_program.fwd @@ F.program info
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
  type info = string
  type label = string
  let info i = "(" ^ String.concat " " i ^ ")"
  let program info body =
    let pair (label, tail) = "(" ^ label ^ " . " ^ tail ^ ")" in
    let body = String.concat "\n" (List.map pair body) in
    "(program ((locals . " ^ info ^ ")) (" ^ body ^ ")"

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
    | Reg of int
    | Var of string
  [@@deriving show, ord, eq, hash]
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
  val block : ?live_after:StringSet.t array -> unit instr list -> unit block

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

module X86_0_Pretty = struct
  type 'a reg = string
  type 'a arg = string
  type 'a instr = string
  type 'a block = string
  type 'a program = string
  type label = string
  type block_info = string
  type program_info = string
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
    fprintf fmt "[@[%a]@]" @@ pp_print_array ~pp_sep StringSet.pp

  let block_info live_after =
    match live_after with
    | Some live_after -> Format.asprintf "(%a)" pp_live_after live_after
    | None -> "()"
  let program_info stack_size conflicts moves =
    let enclose s = "(" ^ s ^ ")" in
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
    enclose (stack_info ^ conflict_info ^ move_info)

  let block ?live_after instrs =
    "(block " ^ block_info live_after ^ "\n" ^ String.concat "\n" instrs ^ ")"
  let program ?stack_size ?conflicts ?moves body =
    "(program "
    ^ program_info stack_size conflicts moves
    ^ " "
    ^ String.concat "\n"
        (List.map (fun (l, t) -> "(" ^ l ^ " . " ^ t ^ ")") body)
    ^ ")"

  let observe s = s
end

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

module C0_Ex1 (F : C0) = struct
  open F

  let res =
    observe
    @@ program (info [])
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

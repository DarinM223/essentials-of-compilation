open Chapter2_definitions

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
  let module M =
    Ex6
      (TransformLet
         (ExplicateControl
            (R1_Pretty ())
            (SelectInstructions
               (UncoverLocals
                  (C0_Pretty))
                  (AssignHomes (PatchInstructions (X86_0_Printer))))
            ())) in
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

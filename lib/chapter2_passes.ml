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
    let ( let* ) e f = fwd @@ F.( let* ) (bwd e) (fun v -> bwd (f v))

    let int i = (Simple, F.int i)
    let read () = (Complex, F.read ())
    let neg (ann, e) =
      match ann with
      | Simple -> (Complex, F.neg e)
      | Complex ->
        let* tmp = (ann, e) in
        (Complex, F.neg (F.var tmp))
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
        let* tmp = (ann, e) in
        Effect.Deep.continue k (F.var tmp)
  end
end

module RemoveComplex (F : R1) : R1 with type 'a obs = 'a F.obs = struct
  module M = RemoveComplexPass (F)
  include R1_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module ExplicateControlPass (F : R1) (C0 : C0) = struct
  module X = struct
    type 'a from = 'a F.exp

    type 'a res =
      | Arg of 'a C0.arg
      | Exp of 'a C0.exp
      | Unk
    type 'a ann = {
      bindings : unit C0.stmt list;
      result : 'a res;
    }
    type 'a term = 'a ann * 'a from

    let fwd e = ({ bindings = []; result = Unk }, e)
    let bwd (_, e) = e
  end
  module X_program = struct
    type 'a from = 'a F.program
    type 'a term = unit C0.program option * 'a F.program
    let fwd p = (None, p)
    let bwd (_, p) = p
  end
  open X
  module IDelta = struct
    let int i = ({ bindings = []; result = Arg C0.(int i) }, F.int i)
    let read () = ({ bindings = []; result = Exp (C0.read ()) }, F.read ())
    let neg (ann, e) =
      match ann with
      | { bindings; result = Arg a } ->
        ({ bindings; result = Exp (C0.neg a) }, F.neg e)
      | { bindings; _ } -> ({ bindings; result = Unk }, F.neg e)
    let ( + ) (ann1, e1) (ann2, e2) =
      match (ann1, ann2) with
      | { bindings = bs1; result = Arg a1 }, { bindings = bs2; result = Arg a2 }
        ->
        ({ bindings = bs1 @ bs2; result = Exp C0.(a1 + a2) }, F.(e1 + e2))
      | { bindings = bs1; _ }, { bindings = bs2; _ } ->
        ({ bindings = bs1 @ bs2; result = Unk }, F.(e1 + e2))

    let var v =
      ({ bindings = []; result = Arg (C0.var (F.string_of_var v)) }, F.var v)

    let ( let* ) e f =
      let vRef = ref (fun () -> failwith "empty cell") in
      let exp =
        F.( let* ) (bwd e) (fun v ->
            (vRef := fun () -> v);
            bwd (f v))
      in
      let v = !vRef () in
      let binding_stmt =
        C0.assign (F.string_of_var v)
          (match (fst e).result with
          | Arg a -> C0.arg a
          | Exp e -> e
          | Unk -> failwith "Expected expression in let*")
      in
      let { bindings; result }, _ = f v in
      ( { bindings = (fst e).bindings @ bindings @ [ binding_stmt ]; result },
        exp )

    let construct_c0 : 'a ann -> unit C0.program =
     fun ann ->
      let to_stmt = function
        | Arg a -> C0.(return (arg a))
        | Exp e -> C0.return e
        | Unk -> failwith "Unknown type"
      in
      let start =
        match ann.bindings with
        | [] -> to_stmt ann.result
        | _ -> List.fold_right C0.( @> ) ann.bindings (to_stmt ann.result)
      in
      C0.(program (info []) [ ("start", start) ])

    let program (ann, e) = (Some (construct_c0 ann), F.program e)

    type 'a obs = unit C0.obs
    let observe (p, _) =
      match p with
      | Some p -> C0.observe p
      | None -> failwith "Cannot decode program"
  end
end

module ExplicateControl (F : R1) (C0 : C0) : R1 with type 'a obs = unit C0.obs =
struct
  module M = ExplicateControlPass (F) (C0)
  include R1_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module UncoverLocalsPass (F : C0) = struct
  module S = Set.Make (String)
  module MkX (M : sig
    type 'a t
  end) =
  struct
    type 'a from = 'a M.t
    type 'a term = S.t * 'a from
    let fwd a = (S.empty, a)
    let bwd (_, a) = a
  end
  module X_arg = MkX (struct
    type 'a t = 'a F.arg
  end)
  module X_exp = MkX (struct
    type 'a t = 'a F.exp
  end)
  module X_stmt = MkX (struct
    type 'a t = 'a F.stmt
  end)
  module X_tail = MkX (struct
    type 'a t = 'a F.tail
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)

  module IDelta = struct
    let var v = (S.singleton v, F.var v)
    let arg (locals, a) = (locals, F.arg a)
    let neg (locals, a) = (locals, F.neg a)
    let ( + ) (l1, a) (l2, b) = (S.union l1 l2, F.(a + b))
    let assign v (locals, e) = (S.add v locals, F.assign v e)
    let return (locals, e) = (locals, F.return e)
    let ( @> ) (l1, s) (l2, t) = (S.union l1 l2, F.( @> ) s t)
    let program _ body =
      let locals =
        body
        |> List.fold_left
             (fun acc (_, (locals, _)) -> S.union locals acc)
             S.empty
        |> S.to_list
      in
      let body = List.map (fun (s, t) -> (s, X_tail.bwd t)) body in
      F.(program (info locals) body)
  end
end

module UncoverLocals (F : C0) : C0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLocalsPass (F)
  include C0_T (M.X_arg) (M.X_exp) (M.X_stmt) (M.X_tail) (M.X_program) (F)
  include M.IDelta
end

module SelectInstructions (F : C0) (X86 : X86_0) :
  C0 with type 'a obs = unit X86.obs = struct
  type 'a tagged_arg = string option * 'a X86.arg
  type 'a tagged_exp =
    | Arg of 'a tagged_arg
    | Exp of string * 'a tagged_arg list
  type 'a arg = 'a tagged_arg
  type 'a exp = unit X86.instr list * 'a tagged_exp
  type 'a stmt = unit X86.instr list
  type 'a tail = unit X86.instr list
  type 'a program = unit X86.program
  type var = string
  type info = F.info

  let fresh =
    let c = ref (-1) in
    fun s ->
      incr c;
      s ^ string_of_int !c

  let int i = (None, X86.int i)
  let var v = (Some v, X86.var v)
  let arg a = ([], Arg a)
  let read () =
    let lhs = fresh "lhs" in
    ( X86.[ movq (reg rax) (var lhs); callq "read_int" ],
      Arg (Some lhs, X86.var lhs) )
  let neg a = ([], Exp ("neg", [ a ]))
  let ( + ) a b = ([], Exp ("+", [ a; b ]))

  let assign v (stmts, tag) =
    match tag with
    | Exp ("neg", [ (Some v', _) ]) when v = v' -> X86.(negq (var v)) :: stmts
    | Exp ("neg", [ (_, arg) ]) ->
      X86.(negq (var v)) :: X86.(movq arg (var v)) :: stmts
    | Exp ("+", [ (Some v', _); (_, arg) ])
    | Exp ("+", [ (_, arg); (Some v', _) ])
      when v = v' ->
      X86.(addq arg (var v)) :: stmts
    | Exp ("+", [ (_, arg1); (_, arg2) ]) ->
      X86.(addq arg2 (var v)) :: X86.(movq arg1 (var v)) :: stmts
    | Arg (_, a) -> X86.(movq a (var v)) :: stmts
    | _ -> stmts

  let return (stmts, tag) =
    match tag with
    | Arg (_, a) -> X86.retq :: X86.(movq a (reg rax)) :: stmts
    | Exp _ ->
      let v = fresh "v" in
      let stmts = assign v (stmts, tag) in
      (* TODO: jump to exit block and mark exit block so that stack can unwind before retq *)
      X86.retq :: X86.(movq (var v) (reg rax)) :: stmts

  let ( @> ) stmts1 stmts2 = stmts2 @ stmts1
  let info = F.info

  let program _ body =
    X86.(program (List.map (fun (l, t) -> (l, block (List.rev t))) body))

  type 'a obs = unit X86.obs
  let observe = X86.observe
end

module AssignHomes (X86 : X86_0) : X86_0 with type 'a obs = 'a X86.obs = struct
  type 'a reg = 'a X86.reg
  type 'a arg = (string -> int) -> 'a X86.arg
  type 'a instr = (string -> int) -> 'a X86.instr
  type 'a block = (string -> int) -> 'a X86.block
  type 'a program = 'a X86.program
  type label = X86.label

  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a reg
  end)

  include X86_0_Reg_T (X_reg) (X86)

  let reg v _ = X86.reg v
  let var v f = X86.(deref rbp (f v))
  let int v _ = X86.int v
  let deref r i _ = X86.deref r i

  let addq a b f = X86.addq (a f) (b f)
  let subq a b f = X86.subq (a f) (b f)
  let movq a b f = X86.movq (a f) (b f)
  let negq a f = X86.negq (a f)
  let pushq a f = X86.pushq (a f)
  let popq a f = X86.popq (a f)
  let retq _ = X86.retq
  let callq l _ = X86.callq l

  let block ?live_after instrs f =
    X86.block ?live_after @@ List.map (fun i -> i f) instrs

  let program ?stack_size:_ ?conflicts ?moves blocks =
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
    let blocks = List.map (fun (l, b) -> (l, b get_stack_slot)) blocks in
    X86.program ~stack_size:!stack_size ?conflicts ?moves blocks

  type 'a obs = 'a X86.obs
  let observe = X86.observe
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
    type 'a term = ArgInfo.t * 'a from (* true if arg is a memory reference *)
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
    | [ last ] -> [ a; last ]
    | x :: xs -> x :: add_before_end a xs
    | [] -> [ a ]
end

module X86_0_Printer = struct
  type 'a reg = string
  type 'a arg = string
  type 'a instr = string
  type 'a block = string list
  type 'a program = string
  type label = string
  type block_info = string
  type program_info = (string list * string) option
  type 'a obs = string
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
  let deref r i = string_of_int i ^ "(" ^ r ^ ")"
  let int i = "$" ^ string_of_int i
  let var v = failwith @@ "Invalid var in X86Printer: " ^ v

  let addq a b = "addq " ^ a ^ ", " ^ b
  let subq a b = "subq " ^ a ^ ", " ^ b
  let movq a b = "movq " ^ a ^ ", " ^ b
  let retq = "retq"
  let negq a = "negq " ^ a
  let callq l = "callq " ^ l
  let pushq a = "pushq " ^ a
  let popq a = "popq " ^ a

  let program_info stack_size =
    Option.map
      (fun stack_size ->
        let stack_size =
          if (stack_size + 8) mod 16 = 0 then stack_size else stack_size + 8
        in
        ( [ "movq " ^ rsp ^ ", " ^ rbp; "subq " ^ int stack_size ^ ", " ^ rsp ],
          "addq " ^ int stack_size ^ ", " ^ rsp ))
      stack_size

  let indent s = "  " ^ s

  let block ?live_after:_ = List.map indent

  let program ?stack_size ?conflicts:_ ?moves:_ blocks =
    let instrs =
      List.concat_map (fun (label, block) -> (label ^ ":\n") :: block) blocks
    in
    let instrs =
      match program_info stack_size with
      | Some (header, footer) ->
        ListUtils.add_before_end ("  " ^ footer)
          (List.map indent header @ instrs)
      | None -> instrs
    in
    String.concat "\n" @@ [ ".global _start"; ".text"; "_start:" ] @ instrs

  let observe s = s
end

module Ex4 (F : R1) = struct
  open F
  let res = observe @@ program (int 52 + neg (int 10))
end

module Ex5 (F : R1) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 42 in
    let* b = var a in
    var b
end

module Ex6 (F : R1) = struct
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

let run () =
  let module M = Ex4 (RemoveComplex (R1_Pretty)) in
  Format.printf "Ex4: %s\n" M.res;
  let module M = Ex5 (RemoveComplex (R1_Pretty)) in
  Format.printf "Ex5: %s\n" M.res;
  let module M = C0_Ex1 (C0_Pretty) in
  Format.printf "C0 Ex1: %s\n" M.res;
  let module M = Ex6 (ExplicateControl (R1_Pretty) (C0_Pretty)) in
  Format.printf "Ex6: %s\n" M.res;
  let module M = Ex6 (ExplicateControl (R1_Pretty) (UncoverLocals (C0_Pretty))) in
  Format.printf "Ex6 with locals: %s\n" M.res;
  let module M =
    Ex6
      (ExplicateControl
         (R1_Pretty)
         (SelectInstructions (UncoverLocals (C0_Pretty)) (X86_0_Pretty))) in
  Format.printf "Ex6 with locals: %s\n" M.res;
  let module M =
    Ex6
      (ExplicateControl
         (R1_Pretty)
         (SelectInstructions
            (UncoverLocals (C0_Pretty)) (AssignHomes (X86_0_Pretty)))) in
  Format.printf "Ex6 with assigned homes: %s\n" M.res;
  let module M =
    Ex6
      (ExplicateControl
         (R1_Pretty)
         (SelectInstructions
            (UncoverLocals
               (C0_Pretty))
               (AssignHomes (PatchInstructions (X86_0_Pretty))))) in
  Format.printf "Ex6 with patched instructions: %s\n" M.res;
  let module M =
    Ex6
      (ExplicateControl
         (R1_Pretty)
         (SelectInstructions
            (UncoverLocals
               (C0_Pretty))
               (AssignHomes (PatchInstructions (X86_0_Printer))))) in
  Format.printf "Ex6 with printed X86: \n%s\n" M.res

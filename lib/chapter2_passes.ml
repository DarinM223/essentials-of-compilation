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
      let go () =
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
      in
      match go () with
      | result -> result
      | effect Normalize (ann, e), k ->
        let* tmp = (ann, e) in
        Effect.Deep.continue k (F.var tmp)
  end
end

module RemoveComplex (F : R1) = struct
  module M = RemoveComplexPass (F)
  include R1_T (M.X) (F)
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
      C0.program { locals = [] } [ ("start", start) ]

    (* Overrides program to return the transformed program in the C0 language *)
    type 'a program = 'a C0.program
    let program (ann, _) = construct_c0 ann
  end
end

module ExplicateControl (F : R1) (C0 : C0) = struct
  module M = ExplicateControlPass (F) (C0)
  include R1_T (M.X) (F)
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
  module X_program = struct
    type 'a from = 'a F.program
    type 'a term = 'a from
    let fwd a = a
    let bwd a = a
  end

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
      F.program { locals } body
  end
end

module UncoverLocals (F : C0) = struct
  module M = UncoverLocalsPass (F)
  include C0_T (M.X_arg) (M.X_exp) (M.X_stmt) (M.X_tail) (M.X_program) (F)
  include M.IDelta
end

module SelectInstructionsPass (F : C0) (X86 : X86_0) = struct
  type 'a tagged_arg = string option * 'a X86.arg
  type 'a tagged_exp =
    | Arg of 'a tagged_arg
    | Exp of string * 'a tagged_arg list
  module X_arg = struct
    type 'a from = 'a F.arg
    type 'a term = 'a tagged_arg option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end
  module X_exp = struct
    type 'a from = 'a F.exp
    type 'a term = unit X86.instr list * 'a tagged_exp option * 'a from
    let fwd a = ([], None, a)
    let bwd (_, _, a) = a
  end
  module X_stmt = struct
    type 'a from = 'a F.stmt
    type 'a term = unit X86.instr list * 'a from
    let fwd a = ([], a)
    let bwd (_, a) = a
  end
  module X_tail = struct
    type 'a from = 'a F.tail
    type 'a term = unit X86.instr list * 'a from
    let fwd a = ([], a)
    let bwd (_, a) = a
  end
  module X_program = struct
    type 'a from = 'a F.program
    type 'a term = unit X86.program option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end

  module IDelta = struct
    let int i = (Some (None, X86.int i), F.int i)
    let var v = (Some (Some v, X86.var v), F.var v)

    let arg (ann, arg) =
      match ann with
      | Some a -> ([], Some (Arg a), F.arg arg)
      | None -> ([], None, F.arg arg)

    let fresh =
      let c = ref (-1) in
      fun s ->
        incr c;
        s ^ string_of_int !c

    let read () =
      let lhs = fresh "lhs" in
      ( X86.[ movq (reg rax) (var lhs); callq "read_int" ],
        Some (Arg (Some lhs, X86.var lhs)),
        F.read () )

    let neg (tag, e) =
      match tag with
      | Some tag -> ([], Some (Exp ("neg", [ tag ])), F.neg e)
      | None -> ([], None, F.neg e)
    let ( + ) (tag1, e1) (tag2, e2) =
      match (tag1, tag2) with
      | Some tag1, Some tag2 ->
        ([], Some (Exp ("+", [ tag1; tag2 ])), F.(e1 + e2))
      | _ -> ([], None, F.(e1 + e2))

    let assign v (stmts, tag, e) =
      match tag with
      | Some (Exp ("neg", [ (Some v', _) ])) when v = v' ->
        (X86.(negq (var v)) :: stmts, F.assign v e)
      | Some (Exp ("neg", [ (_, arg) ])) ->
        (X86.(negq (var v)) :: X86.(movq arg (var v)) :: stmts, F.assign v e)
      | Some (Exp ("+", [ (Some v', _); (_, arg) ]))
      | Some (Exp ("+", [ (_, arg); (Some v', _) ]))
        when v = v' ->
        (X86.(addq arg (var v)) :: stmts, F.assign v e)
      | Some (Exp ("+", [ (_, arg1); (_, arg2) ])) ->
        ( X86.(addq arg2 (var v)) :: X86.(movq arg1 (var v)) :: stmts,
          F.assign v e )
      | _ -> (stmts, F.assign v e)

    let return (stmts, tag, e) =
      let v = fresh "v" in
      let stmts, _ = assign v (stmts, tag, e) in
      (X86.retq :: X86.(movq (var v) (reg rax)) :: stmts, F.return e)
    let ( @> ) (stmts1, s1) (stmts2, s2) = (stmts2 @ stmts1, F.( @> ) s1 s2)

    let program info body =
      let info' : X86.info = failwith "info" in
      let program =
        X86.program info'
          (List.map (fun (l, (t, _)) -> (l, X86.block info' t)) body)
      in
      let body = List.map (fun (l, t) -> (l, X_tail.bwd t)) body in
      (Some program, F.program info body)

    type 'a obs = unit X86.program
    let observe = function
      | Some program, _ -> program
      | _ -> failwith "Error: can't build X86 program"
  end
end

module SelectInstructions (F : C0) (X86 : X86_0) = struct
  module M = SelectInstructionsPass (F) (X86)
  include C0_T (M.X_arg) (M.X_exp) (M.X_stmt) (M.X_tail) (M.X_program) (F)
  include M.IDelta
end

module Ex4 (F : R1) = struct
  open F
  let res = program (int 52 + neg (int 10))
end

module Ex5 (F : R1) = struct
  open F
  let res =
    program
    @@
    let* a = int 42 in
    let* b = var a in
    var b
end

module Ex6 (F : R1) = struct
  open F

  let res =
    program
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
  Format.printf "Ex6 with locals: %s\n" M.res
(* let module M =
    Ex6
      (ExplicateControl
         (R1_Pretty)
         (SelectInstructions (UncoverLocals (C0_Pretty)) (X86_0_Pretty))) in
  Format.printf "Ex6 with locals: %s\n" M.res *)

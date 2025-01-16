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
    let (+) (ann1, e1) (ann2, e2) =
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
      | effect (Normalize (ann, e)), k ->
        let* tmp = (ann, e) in
        Effect.Deep.continue k (F.var tmp)
  end
end

module RemoveComplex (F : R1) = struct
  module M = RemoveComplexPass (F)
  include R1_T (M.X) (F)
  include M.IDelta
end

module ExplicateControlPass (F : R1) (C0: C0) = struct
  module X = struct
    type 'a from = 'a F.exp

    type 'a ann = {
      bindings: C0.stmt list;
      exp: 'a C0.exp;
    }
    type 'a term = 'a ann * 'a from

    let fwd e = ({ bindings = []; exp = C0.(arg (var "unknown")) }, e)
    let bwd (_, e) = e
  end
  open X
  module IDelta = struct
    (* TODO: override R1 functions to annotate with the ann type *)

    let construct_c0 : 'a ann -> C0.program = fun ann ->
      let start =
        match ann.bindings with
        | [] -> C0.return ann.exp
        | _ -> List.fold_right C0.(@>) ann.bindings (C0.return ann.exp)
      in
      C0.program { locals = [] } [("start", start)]

    (* Overrides program to return the transformed program in the C0 language *)
    type 'a program = C0.program
    let program (ann, _) = construct_c0 ann
  end
end

module ExplicateControl (F: R1) (C0 : C0) = struct
  module M = ExplicateControlPass (F) (C0)
  include R1_T (M.X) (F)
  include M.IDelta
end

module Ex4 (F : R1) = struct
  open F
  let res = program @@
    int 52 + neg (int 10)
end

module Ex5 (F : R1) = struct
  open F
  let res = program @@
    let* a = int 42 in
    let* b = var a in
    var b
end

let run () =
  let module M = Ex4 (RemoveComplex (R1_Pretty)) in
  Format.printf "Ex4: %s\n" M.res;
  let module M = Ex5 (RemoveComplex (R1_Pretty)) in
  Format.printf "Ex5: %s\n" M.res;
  let module M = C0_Ex1 (C0_Pretty) in
  Format.printf "C0 Ex1: %s\n" M.res
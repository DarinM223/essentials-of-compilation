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
  Format.printf "Ex5: %s\n" M.res
module type R0 = sig
  type 'a exp

  val int : int -> int exp
  val read : unit -> int exp
  val neg : int exp -> int exp
  val (+) : int exp -> int exp -> int exp

  type 'a program

  val program : 'a exp -> 'a program
end

module type TRANS = sig
  type 'a from
  type 'a term

  val fwd : 'a from -> 'a term
  val bwd : 'a term -> 'a from
end

module R0_T(X: TRANS) (F : R0 with type 'a exp = 'a X.from) = struct
  open X

  type 'a exp = 'a term
  type 'a program = 'a F.program

  let int i = fwd @@ F.int i
  let read () = fwd @@ F.read ()
  let neg e = fwd @@ F.neg (bwd e)
  let (+) a b = fwd @@ F.(+) (bwd a) (bwd b)

  let program e = F.program (bwd e)
end

module R0_Interp = struct
  type 'a exp = 'a

  let int i = i
  let read () =
    print_endline "Enter integer: ";
    read_int ()
  let neg i = -i
  let (+) = (+)

  type 'a program = 'a
  let program i = i
end

module R0_Pretty = struct
  type 'a exp = string
  let int = string_of_int
  let read () = "(read)"
  let neg i = "(- " ^ i ^ ")"
  let (+) a b = "(+ " ^ a ^ " " ^ b ^ ")"

  type 'a program = string
  let program i = "(program " ^ i ^ ")"
end

module R0_Partial_Pass (F : R0) = struct
  module X = struct
    type 'a from = 'a F.exp
    type ann = Unk | Int of int
    type 'a term = ann * 'a from

    let fwd a = (Unk, a)
    let bwd (_, a) = a
  end

  open X
  module IDelta = struct
    let int i = (Int i, F.int i)
    let neg (ann, i) =
      match ann with
      | Int n -> (Int (-n), F.int (-n))
      | _ -> (ann, i)

    let (+) (ann1, i1) (ann2, i2) =
      match (ann1, ann2) with
      | Int n1, Int n2 -> (Int (n1 + n2), F.int (n1 + n2))
      | _, Int n2 -> (Unk, F.(+) i1 (F.int n2))
      | Int n1, _ -> (Unk, F.(+) (F.int n1) i2)
      | _ -> (Unk, F.(+) i1 i2)
  end
end

module R0_Partial (F : R0) = struct
  module M = R0_Partial_Pass (F)
  include R0_T (M.X) (F)
  include M.IDelta
end

module Ex1(F : R0) = struct
  open F

  let res = program @@ read () + neg (int 5 + int 3)
end

let run () =
  let module M = Ex1 (R0_Interp) in
  Format.printf "Ex1: %d\n" M.res;
  let module M = Ex1 (R0_Pretty) in
  Format.printf "Ex1: %s\n" M.res;
  let module M = Ex1 (R0_Partial (R0_Pretty)) in
  Format.printf "Ex1: %s\n" M.res
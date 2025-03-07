module type R0 = sig
  type 'a exp

  val int : int -> int exp
  val read : unit -> int exp
  val neg : int exp -> int exp
  val ( + ) : int exp -> int exp -> int exp

  type 'a program
  val program : 'a exp -> 'a program

  type 'a obs
  val observe : 'a program -> 'a obs
end

module type TRANS = sig
  type 'a from
  type 'a term

  val fwd : 'a from -> 'a term
  val bwd : 'a term -> 'a from
end

module MkId (F : sig
  type 'a t
end) : TRANS with type 'a from = 'a F.t and type 'a term = 'a F.t = struct
  type 'a from = 'a F.t
  type 'a term = 'a from
  let fwd a = a
  let bwd a = a
end

module R0_T
    (X_exp : TRANS)
    (X_program : TRANS)
    (F :
      R0
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  open X_exp

  type 'a exp = 'a term
  type 'a program = 'a X_program.term

  let int i = fwd @@ F.int i
  let read () = fwd @@ F.read ()
  let neg e = fwd @@ F.neg (bwd e)
  let ( + ) a b = fwd @@ F.( + ) (bwd a) (bwd b)

  let program e = X_program.fwd @@ F.program (bwd e)

  type 'a obs = 'a F.obs
  let observe a = F.observe a
end

module type Reader = sig
  type t
  val init : t (* Initial state *)
end

module R0_R_T (R : Reader) (F : R0) = struct
  type 'a exp = R.t -> 'a F.exp
  type 'a program = unit -> 'a F.program

  let int i _ = F.int i
  let read () _ = F.read ()
  let neg e r = F.neg (e r)
  let ( + ) a b r = F.(a r + b r)
  let program e () = F.program (e R.init)

  type 'a obs = 'a F.obs
  let observe a = F.observe (a ())
end

module R0_Interp (ReadInt : sig
  val read_int : unit -> int
end) =
struct
  type 'a exp = 'a

  let int i = i
  let read () =
    print_endline "Enter integer: ";
    ReadInt.read_int ()
  let neg i = -i
  let ( + ) = ( + )

  type 'a program = 'a
  let program i = i

  type 'a obs = 'a
  let observe i = i
end

module R0_Pretty = struct
  type 'a exp = string
  let int = string_of_int
  let read () = "(read)"
  let neg i = "(- " ^ i ^ ")"
  let ( + ) a b = "(+ " ^ a ^ " " ^ b ^ ")"

  type 'a program = string
  let program i = "(program " ^ i ^ ")"

  type 'a obs = string
  let observe s = s
end

module R0_Partial_Pass (F : R0) = struct
  module X = struct
    type 'a from = 'a F.exp
    type ann =
      | Ann of {
          dynamic : int from option;
          static : int;
        }
      | Unk
    type 'a term = ann * 'a from

    let fwd (a : 'a from) = (Unk, a)
    let bwd ((_, a) : 'a term) = a
  end

  module X_program = struct
    type 'a from = 'a F.program
    type 'a term = 'a from
    let fwd a = a
    let bwd a = a
  end

  open X
  module IDelta = struct
    let int i = (Ann { dynamic = None; static = i }, F.int i)
    let read () =
      let exp = F.read () in
      (Ann { dynamic = Some exp; static = 0 }, exp)

    let add_options a b =
      match (a, b) with
      | Some a, Some b -> Some F.(a + b)
      | Some a, None -> Some a
      | None, Some b -> Some b
      | None, None -> None

    let ann_to_exp = function
      | Ann { dynamic = Some dynamic; static } -> F.(dynamic + int static)
      | Ann { dynamic = None; static } -> F.int static
      | Unk -> failwith "ann_to_exp: expected Ann constructor"

    let neg (ann, e) =
      match ann with
      | Ann { dynamic; static } ->
        let ann =
          Ann { dynamic = Option.map F.neg dynamic; static = -static }
        in
        (ann, ann_to_exp ann)
      | Unk -> (Unk, e)

    let ( + ) (ann1, e1) (ann2, e2) =
      match (ann1, ann2) with
      | Ann n1, Ann n2 ->
        let ann =
          Ann
            {
              dynamic = add_options n1.dynamic n2.dynamic;
              static = n1.static + n2.static;
            }
        in
        (ann, ann_to_exp ann)
      | Unk, Ann n2 ->
        let ann =
          Ann { dynamic = add_options (Some e1) n2.dynamic; static = n2.static }
        in
        (ann, ann_to_exp ann)
      | Ann n1, Unk ->
        let ann =
          Ann { dynamic = add_options n1.dynamic (Some e2); static = n1.static }
        in
        (ann, ann_to_exp ann)
      | Unk, Unk -> (Unk, F.(e1 + e2))

    type 'a obs = 'a F.program
    let observe a = a
  end
end

module R0_Partial (F : R0) : R0 with type 'a obs = 'a F.program = struct
  module M = R0_Partial_Pass (F)
  include R0_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module Ex1 (F : R0) = struct
  open F

  let res = observe @@ program (read () + neg (int 5 + int 3))
end

module Ex2 (F : R0) = struct
  open F
  let res = observe @@ program (int 1 + (read () + int 1))
end

module Ex3 (F : R0) = struct
  open F
  let res = observe @@ program (int 4 + neg (read () + int 2) + neg (int 3))
end

let%expect_test "Example 1 evaluation" =
  let module M = Ex1 (R0_Interp (struct
    let read_int () =
      let input = 9 in
      Format.printf "%d\n" input;
      input
  end)) in
  Format.printf "Ex1: %d\n" M.res;
  [%expect {|
    Enter integer:
    9
    Ex1: 1
    |}]

let%expect_test "Example 1 pretty printing" =
  let module M = Ex1 (R0_Pretty) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect {| Ex1: (program (+ (read) (- (+ 5 3)))) |}]

let%expect_test "Example 1 after partial evaluation" =
  let module M = Ex1 (R0_Partial (R0_Pretty)) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect {| Ex1: (program (+ (read) -8)) |}]

let%expect_test "Example 2 after partial evaluation" =
  let module M = Ex2 (R0_Partial (R0_Pretty)) in
  Format.printf "Ex2: %s\n" M.res;
  [%expect {| Ex2: (program (+ (read) 2)) |}]

let%expect_test "Example 3 after partial evaluation" =
  let module M = Ex3 (R0_Partial (R0_Pretty)) in
  Format.printf "Ex3: %s\n" M.res;
  [%expect {| Ex3: (program (+ (- (read)) -1)) |}]

let run () =
  let module M = Ex1 (R0_Interp (Stdlib)) in
  Format.printf "Ex1: %d\n" M.res

module type R2_Shrink = sig
  include Chapter2_definitions.R1
  val t : bool exp
  val f : bool exp

  val not : bool exp -> bool exp
  val ( = ) : 'a exp -> 'a exp -> bool exp
  val ( < ) : int exp -> int exp -> bool exp
  val if_ : bool exp -> 'a exp -> 'a exp -> 'a exp
end

module type R2 = sig
  include R2_Shrink

  val ( - ) : int exp -> int exp -> int exp

  val andd : bool exp -> bool exp -> bool exp
  val orr : bool exp -> bool exp -> bool exp
  val ( <> ) : 'a exp -> 'a exp -> bool exp
  val ( <= ) : int exp -> int exp -> bool exp
  val ( > ) : int exp -> int exp -> bool exp
  val ( >= ) : int exp -> int exp -> bool exp
end

module R2_Shrink_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R2_Shrink
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter2_definitions.R1_T (X_exp) (X_program) (F)
  open X_exp
  let t = fwd F.t
  let f = fwd F.f
  let not a = fwd (F.not (bwd a))
  let ( = ) a b = fwd F.(bwd a = bwd b)
  let ( < ) a b = fwd F.(bwd a < bwd b)
  let if_ a b c = fwd @@ F.if_ (bwd a) (bwd b) (bwd c)
end

module Shrink (F : R2_Shrink) : R2 with type 'a obs = 'a F.obs = struct
  module X_exp = Chapter1.MkId (struct
    type 'a t = 'a F.exp
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)
  include R2_Shrink_T (X_exp) (X_program) (F)
  let ( - ) a b = F.(a + neg b)
  let andd a b = F.(if_ a b f)
  let orr a b = F.(if_ a t b)
  let ( <> ) a b = F.(not (a = b))
  let ( <= ) a b = F.(not (b < a))
  let ( > ) a b = F.(b < a)
  let ( >= ) a b = F.(not (a < b))
end

module R2_Shrink_Pretty = struct
  include Chapter2_definitions.R1_Pretty
  let t = "t"
  let f = "f"
  let not a = "(not " ^ a ^ ")"
  let ( = ) a b = "(= " ^ a ^ " " ^ b ^ ")"
  let ( < ) a b = "(< " ^ a ^ " " ^ b ^ ")"
  let if_ a b c = "(if " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
end

module Ex1 (F : R2) = struct
  open F

  let res =
    observe @@ program
    @@
    let* a = int 2 in
    let* b = read () in
    if_ (andd (var a <= int 5) (var b > var a)) (var b - var a) (var b + var a)
end

let%expect_test "Example 1 shrink" =
  let module M = Ex1 (Shrink (R2_Shrink_Pretty)) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {| Ex1: (program (let ([tmp0 2]) (let ([tmp1 (read)]) (if (if (not (< 5 (var tmp0))) (< (var tmp0) (var tmp1)) f) (+ (var tmp1) (- (var tmp0))) (+ (var tmp1) (var tmp0)))))) |}]

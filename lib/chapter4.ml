module type R2_Shrink = sig
  include Chapter2_definitions.R1
  val t : bool exp
  val f : bool exp

  val not : bool exp -> bool exp
  val ( = ) : int exp -> int exp -> bool exp
  val ( < ) : int exp -> int exp -> bool exp
  val if_ : bool exp -> 'a exp -> 'a exp -> 'a exp
end

module type R2 = sig
  include R2_Shrink

  val ( - ) : int exp -> int exp -> int exp

  val andd : bool exp -> bool exp -> bool exp
  val orr : bool exp -> bool exp -> bool exp
  val ( <> ) : int exp -> int exp -> bool exp
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

module R2_Shrink_Pretty = struct
  include Chapter2_definitions.R1_Pretty
  let t = "t"
  let f = "f"
  let not a = "(not " ^ a ^ ")"
  let ( = ) a b = "(= " ^ a ^ " " ^ b ^ ")"
  let ( < ) a b = "(< " ^ a ^ " " ^ b ^ ")"
  let if_ a b c = "(if " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
end

module type C1 = sig
  include Chapter2_definitions.C0
  val t : bool arg
  val f : bool arg

  type cmp =
    | Eq
    | Lt
  val not : bool arg -> bool exp
  val ( = ) : int arg -> int arg -> bool exp
  val ( < ) : int arg -> int arg -> bool exp

  val goto : label -> unit tail
  val if_ : bool exp -> label -> label -> unit tail
end

module type X86_1 = sig
  include Chapter2_definitions.X86_0
  val byte_reg : 'b reg -> 'a arg

  type cc =
    | E
    | L
    | Le
    | G
    | Ge

  val xorq : 'a arg -> 'b arg -> unit instr
  val cmpq : 'a arg -> 'b arg -> unit instr
  val set : cc -> 'a arg -> unit instr
  val movzbq : 'a arg -> 'b arg -> unit instr
  val jmp : label -> unit instr
  val jmp_if : cc -> label -> unit instr
  val label : label -> unit instr
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

module RemoveComplex (F : R2_Shrink) : R2_Shrink with type 'a obs = 'a F.obs =
struct
  module M = Chapter2_passes.RemoveComplexPass (F)
  include R2_Shrink_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module ExplicateControl (F : R2_Shrink) (C1 : C1) :
  R2_Shrink with type 'a obs = unit C1.obs = struct
  module M = Chapter2_passes.ExplicateControlPass (F) (C1)
  include R2_Shrink_T (M.X) (M.X_program) (F)
  include M.IDelta
  open M.X
  let t =
    let ann, e = fwd F.t in
    ({ ann with result = Arg C1.t }, e)
  let f =
    let ann, e = fwd F.f in
    ({ ann with result = Arg C1.f }, e)
  let not (ann, e) =
    match ann with
    | { result = If (update, cond, t, f); _ } ->
      (* TODO: swap the false and true block bodies *)
      ({ ann with result = If ((fun t f -> update f t), cond, t, f) }, F.not e)
    | { result = Arg a; _ } -> ({ ann with result = Exp (C1.not a) }, F.not e)
    | _ -> ({ ann with result = Unk }, F.not e)

  let fresh =
    let c = ref (-1) in
    fun () ->
      incr c;
      !c

  let handle_cond c1_cond r2_cond (ann1, e1) (ann2, e2) =
    let merged = merge ann1 ann2 in
    match (ann1, ann2) with
    | { result = Arg a1; _ }, { result = Arg a2; _ } ->
      let t_label = "block" ^ string_of_int (fresh ()) in
      let f_label = "block" ^ string_of_int (fresh ()) in
      let module StringMap = Chapter2_definitions.StringMap in
      let blocks =
        merged.blocks
        |> StringMap.add t_label C1.(return (arg t))
        |> StringMap.add f_label C1.(return (arg f))
      in
      let update t f blocks =
        blocks
        |> StringMap.update t_label (fun _ -> Some (C1.goto t))
        |> StringMap.update f_label (fun _ -> Some (C1.goto f))
      in
      ( {
          merged with
          blocks;
          result = If (update, c1_cond a1 a2, t_label, f_label);
        },
        r2_cond e1 e2 )
    | _ -> (merged, r2_cond e1 e2)

  let ( = ) = handle_cond C1.( = ) F.( = )
  let ( < ) = handle_cond C1.( < ) F.( < )

  let if_ a b c = fwd @@ F.if_ (bwd a) (bwd b) (bwd c)
  (* TODO add overloads to generate control flow stuff *)
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

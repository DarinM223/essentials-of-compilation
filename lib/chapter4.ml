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

module R2_Shrink_R_T (R : Chapter1.Reader) (F : R2_Shrink) = struct
  include Chapter2_definitions.R1_R_T (R) (F)
  let t _ = F.t
  let f _ = F.f
  let not a r = F.not (a r)
  let ( = ) a b r = F.(a r = b r)
  let ( < ) a b r = F.(a r < b r)
  let if_ a b c r = F.if_ (a r) (b r) (c r)
end

module R2_Shrink_Pretty () = struct
  include Chapter2_definitions.R1_Pretty ()
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

  val not : bool arg -> bool exp
  val ( = ) : int arg -> int arg -> bool exp
  val ( < ) : int arg -> int arg -> bool exp

  val goto : label -> unit tail
  val if_ : bool exp -> label -> label -> unit tail
end

module C1_Pretty = struct
  include Chapter2_definitions.C0_Pretty
  let t = "t"
  let f = "f"
  let not a = "(not " ^ a ^ ")"
  let ( = ) a b = "(= " ^ a ^ " " ^ b ^ ")"
  let ( < ) a b = "(< " ^ a ^ " " ^ b ^ ")"

  let goto l = "(goto " ^ l ^ ")"
  let if_ a b c = "(if " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
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
  let not (ann, e) =
    let open M.X in
    match ann with
    | Simple -> (Complex, F.not e)
    | Complex ->
      let* tmp = (ann, e) in
      (Complex, F.not (F.var tmp))
end

module ExplicateControl (F : R2_Shrink) (C1 : C1) () :
  R2_Shrink with type 'a obs = unit C1.obs = struct
  include Chapter2_passes.ExplicateControl (F) (C1) ()

  let block_map : (string, unit C1.tail) Hashtbl.t = Hashtbl.create 100
  let fresh_block =
    let c = ref (-1) in
    fun block_name ->
      incr c;
      block_name ^ string_of_int !c
  let insert_block block_name body =
    let label = fresh_block block_name in
    Hashtbl.add block_map label body;
    label
  let convert_cond e = function
    | Tail -> C1.return e
    | Assign (v, body) -> C1.(assign v e @> body ())
    | Pred (t, f) ->
      let t_label = insert_block "t" (t ()) in
      let f_label = insert_block "f" (f ()) in
      C1.if_ e t_label f_label

  let t = function
    | Tail -> C1.(return (arg t))
    | Assign (v, body) -> C1.(assign v (arg t) @> body ())
    | Pred (t, _) -> t ()
  let f = function
    | Tail -> C1.(return (arg f))
    | Assign (v, body) -> C1.(assign v (arg f) @> body ())
    | Pred (_, f) -> f ()
  let not e = function
    | Tail ->
      let tmp = F.(string_of_var (fresh ())) in
      e (Assign (tmp, fun () -> C1.(return (not (var (lookup tmp))))))
    | Assign (v, body) ->
      let tmp = F.(string_of_var (fresh ())) in
      e
        (Assign
           (tmp, fun () -> C1.(assign v (not (var (lookup tmp))) @> body ())))
    | Pred (t, f) -> e (Pred (f, t))
  let ( = ) a b r =
    let tmp1 = F.(string_of_var (fresh ())) in
    let tmp2 = F.(string_of_var (fresh ())) in
    a
      (Assign
         ( tmp1,
           fun () ->
             b
               (Assign (tmp2, fun () -> convert_cond C1.(var tmp1 = var tmp2) r))
         ))
  let ( < ) a b r =
    let tmp1 = F.(string_of_var (fresh ())) in
    let tmp2 = F.(string_of_var (fresh ())) in
    a
      (Assign
         ( tmp1,
           fun () ->
             b
               (Assign (tmp2, fun () -> convert_cond C1.(var tmp1 < var tmp2) r))
         ))

  let if_ cond t_branch f_branch = function
    | Tail ->
      let t_label = insert_block "t" @@ t_branch Tail in
      let f_label = insert_block "f" @@ f_branch Tail in
      cond (Pred ((fun () -> C1.goto t_label), fun () -> C1.goto f_label))
    | Assign (v, body) ->
      let body_label = insert_block "body" @@ body () in
      let t_label =
        insert_block "t" @@ t_branch @@ Assign (v, fun () -> C1.goto body_label)
      in
      let f_label =
        insert_block "f" @@ f_branch @@ Assign (v, fun () -> C1.goto body_label)
      in
      cond (Pred ((fun () -> C1.goto t_label), fun () -> C1.goto f_label))
    | Pred (t, f) ->
      cond
        (Pred
           ((fun () -> t_branch (Pred (t, f))), fun () -> f_branch (Pred (t, f))))

  let program e () =
    let start_body = e Tail in
    let blocks = List.of_seq @@ Hashtbl.to_seq block_map in
    C1.(program (info [])) (("start", start_body) :: blocks)
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

module Ex2 (F : R2) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 2 in
    if_ (var a < int 5) (var a + int 1) (int 6 + int 7)
end

module Ex3 (F : R2) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 2 in
       var a < int 5
end

module Ex4 (F : R2) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 1 in
       let* b = not (var a < int 5) in
       var b
end

let%expect_test "Example 1 shrink" =
  let module M = Ex1 (Shrink (R2_Shrink_Pretty ())) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {| Ex1: (program (let ([tmp0 2]) (let ([tmp1 (read)]) (if (if (not (< 5 (var tmp0))) (< (var tmp0) (var tmp1)) f) (+ (var tmp1) (- (var tmp0))) (+ (var tmp1) (var tmp0)))))) |}]

let%expect_test "Remove complex with simple conditional" =
  let module M = Ex2 (Shrink (RemoveComplex (R2_Shrink_Pretty ()))) in
  Format.printf "Ex2: %s\n" M.res;
  [%expect
    {| Ex2: (program (let ([tmp0 2]) (if (< (var tmp0) 5) (+ (var tmp0) 1) (+ 6 7)))) |}]

(* let%expect_test "Explicate control with simple conditional" =
  let module M =
    Ex3 (Shrink (RemoveComplex (ExplicateControl (R2_Shrink_Pretty) (C1_Pretty)))) in
  Format.printf "Ex3: %s\n" M.res;
  [%expect
    {|
    Ex3: (program ((locals . ())) ((block2 . (return t))
    (block3 . (return f))
    (start . (seq (assign tmp3 2) (if (< tmp3 5) block2 block3))))
    |}] *)

(* let%expect_test "Explicate control with assignment to conditional" =
  let module M =
    Ex4 (Shrink (RemoveComplex (ExplicateControl (R2_Shrink_Pretty) (C1_Pretty)))) in
  Format.printf "Ex4: %s\n" M.res;
  (* TODO: bindings generated in wrong order. assign tmp4 1 should be the first binding *)
  [%expect
    {|
    Ex4: (program ((locals . ())) ((block2 . (return t))
    (block3 . (return f))
    (start . (seq (assign tmp7 (< tmp4 5)) (seq (assign tmp8 (not tmp7)) (seq (assign tmp4 1) (return tmp8))))))
    |}] *)

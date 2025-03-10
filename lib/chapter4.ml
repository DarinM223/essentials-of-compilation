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

(* module ExplicateControl (F : R2_Shrink) (C1 : C1) :
  R2_Shrink with type 'a obs = unit C1.obs = struct
  module M = Chapter2_passes.ExplicateControlPass (F) (C1)
  include R2_Shrink_R_T (M.X_reader) (R2_Shrink_T (M.X) (M.X_program) (F))
  include M.IDelta
  open M.X
  open Chapter2_definitions
  let t _ = ({ empty_ann with result = Arg C1.t }, F.t)
  let f _ = ({ empty_ann with result = Arg C1.f }, F.f)
  let not e r =
    let ann, e = e r in
    match ann with
    | { result = If (update, cond, t, f); _ } ->
      (* Swap the false and true block bodies *)
      let blocks =
        ann.blocks
        |> StringMap.update t (fun _ -> StringMap.find_opt f ann.blocks)
        |> StringMap.update f (fun _ -> StringMap.find_opt t ann.blocks)
      in
      ( { ann with blocks; result = If ((fun t f -> update f t), cond, t, f) },
        F.not e )
    | { result = Arg a; _ } -> ({ ann with result = Exp (C1.not a) }, F.not e)
    | _ -> ({ ann with result = Unk }, F.not e)

  let fresh =
    let c = ref (-1) in
    fun () ->
      incr c;
      !c

  let add_ann_block ?label ann blocks =
    let to_stmt = function
      | Arg a -> C1.(return (arg a))
      | Exp e -> C1.return e
      | If (_update, cond, t, f) -> C1.if_ cond t f
      | Unk -> failwith "Unknown type"
    in
    let tail =
      match ann.bindings with
      | [] -> to_stmt ann.result
      | _ -> List.fold_right C1.( @> ) ann.bindings (to_stmt ann.result)
    in
    let new_block_label =
      match label with
      | Some label -> label
      | None -> "block" ^ string_of_int (fresh ())
    in
    (new_block_label, StringMap.add new_block_label tail blocks)

  let handle_cond c1_cond r2_cond e1 e2 r =
    let ann1, e1 = e1 r in
    let ann2, e2 = e2 r in
    let merged = merge ann1 ann2 in
    match (ann1, ann2) with
    | { result = Arg a1; _ }, { result = Arg a2; _ } ->
      let t_label = "block" ^ string_of_int (fresh ()) in
      let f_label = "block" ^ string_of_int (fresh ()) in
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
      let cond = c1_cond a1 a2 in
      ( { merged with blocks; result = If (update, cond, t_label, f_label) },
        r2_cond e1 e2 )
    | _ -> (merged, r2_cond e1 e2)

  let ( = ) = handle_cond C1.( = ) F.( = )
  let ( < ) = handle_cond C1.( < ) F.( < )

  let if_ cond th els r =
    let ann1, cond = cond r in
    let ann2, th = th r in
    let ann3, els = els r in
    let blocks = ann1.blocks in
    let then_label, blocks = add_ann_block ann2 blocks in
    let else_label, blocks = add_ann_block ann3 blocks in
    (* if ann2 or ann3 are not IF, then call conditional's update function *)
    let cond_exp =
      match ann1.result with
      | If (_, cond_exp, _, _) -> cond_exp
      | _ -> failwith "Expected conditional to have conditional result"
    in
    let update = failwith "" in
    ( {
        ann1 with
        blocks;
        result = If (update, cond_exp, then_label, else_label);
      },
      F.if_ cond th els )

  let construct_c1 ann =
    let _, blocks = add_ann_block ~label:"start" ann ann.blocks in
    C1.(program (info []) (StringMap.to_list blocks))

  let program e () =
    let ann, e = e M.X_reader.init in
    (Some (construct_c1 ann), F.program e)
end *)

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

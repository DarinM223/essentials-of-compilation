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

module CC = struct
  type t =
    | E
    | L
    | Le
    | G
    | Ge
  [@@deriving show]
end

module type X86_1 = sig
  include Chapter2_definitions.X86_0
  val byte_reg : 'b reg -> 'a arg

  val xorq : 'a arg -> 'b arg -> unit instr
  val cmpq : 'a arg -> 'b arg -> unit instr
  val set : CC.t -> 'a arg -> unit instr
  val movzbq : 'a arg -> 'b arg -> unit instr
  val jmp : label -> unit instr
  val jmp_if : CC.t -> label -> unit instr
  val label : label -> unit instr
end

module X86_1_T
    (X_reg : Chapter1.TRANS)
    (X_arg : Chapter1.TRANS)
    (X_instr : Chapter1.TRANS)
    (X_block : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      X86_1
        with type 'a reg = 'a X_reg.from
         and type 'a arg = 'a X_arg.from
         and type 'a instr = 'a X_instr.from
         and type 'a block = 'a X_block.from
         and type 'a program = 'a X_program.from) =
struct
  include
    Chapter2_definitions.X86_0_T (X_reg) (X_arg) (X_instr) (X_block) (X_program)
      (F)
  let byte_reg reg = X_arg.fwd @@ F.byte_reg @@ X_reg.bwd reg
  let xorq a b = X_instr.fwd @@ F.xorq (X_arg.bwd a) (X_arg.bwd b)
  let cmpq a b = X_instr.fwd @@ F.cmpq (X_arg.bwd a) (X_arg.bwd b)
  let set cc a = X_instr.fwd @@ F.set cc @@ X_arg.bwd a
  let movzbq a b = X_instr.fwd @@ F.movzbq (X_arg.bwd a) (X_arg.bwd b)
  let jmp l = X_instr.fwd @@ F.jmp l
  let jmp_if cc l = X_instr.fwd @@ F.jmp_if cc l
  let label l = X_instr.fwd @@ F.label l
end

module X86_1_Pretty = struct
  include Chapter2_definitions.X86_0_Pretty
  let byte_reg reg = "(byte-reg" ^ reg ^ ")"
  let xorq a b = "(xorq" ^ a ^ " " ^ b ^ ")"
  let cmpq a b = "(cmpq " ^ a ^ " " ^ b ^ ")"
  let set cc a = "(set " ^ CC.show cc ^ " " ^ a ^ ")"
  let movzbq a b = "(movzbq " ^ a ^ " " ^ b ^ ")"
  let jmp l = "(jmp " ^ l ^ ")"
  let jmp_if cc l = "(jmp-if " ^ CC.show cc ^ " " ^ l ^ ")"
  let label l = "(label " ^ l ^ ")"
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
      let t_label = insert_block "block_t" (t ()) in
      let f_label = insert_block "block_f" (f ()) in
      C1.if_ e t_label f_label

  let var v = function
    | Pred (t, f) ->
      convert_cond C1.(arg (var (F.string_of_var v))) (Pred (t, f))
    | r -> var v r

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
               (Assign
                  ( tmp2,
                    fun () ->
                      convert_cond C1.(var (lookup tmp1) = var (lookup tmp2)) r
                  )) ))
  let ( < ) a b r =
    let tmp1 = F.(string_of_var (fresh ())) in
    let tmp2 = F.(string_of_var (fresh ())) in
    a
      (Assign
         ( tmp1,
           fun () ->
             b
               (Assign
                  ( tmp2,
                    fun () ->
                      convert_cond C1.(var (lookup tmp1) < var (lookup tmp2)) r
                  )) ))

  let if_ cond t_branch f_branch = function
    | Tail ->
      let t_label = insert_block "block_t" @@ t_branch Tail in
      let f_label = insert_block "block_f" @@ f_branch Tail in
      cond (Pred ((fun () -> C1.goto t_label), fun () -> C1.goto f_label))
    | Assign (v, body) ->
      let body_label = insert_block "block_body" @@ body () in
      let t_label =
        insert_block "block_t" @@ t_branch
        @@ Assign (v, fun () -> C1.goto body_label)
      in
      let f_label =
        insert_block "block_f" @@ f_branch
        @@ Assign (v, fun () -> C1.goto body_label)
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

module SelectInstructions (F : C1) (X86 : X86_1) :
  C1 with type 'a obs = unit X86.obs = struct
  include Chapter2_passes.SelectInstructions (F) (X86)

  let t = (None, X86.int 1)
  let f = (None, X86.int 0)

  let arg (v', a) = function
    | If (t, f) -> X86.[ jmp t; jmp_if E f; cmpq (int 0) a ]
    | r -> arg (v', a) r

  let not (v', arg) = function
    | Assign v ->
      if Some v = v' then
        X86.[ xorq (int 1) (var v) ]
      else
        X86.[ xorq (int 1) (var v); movq arg (var v) ]
    | Return -> X86.[ xorq (int 1) (reg rax); movq arg (reg rax) ]
    | If (t, f) -> X86.[ jmp f; jmp_if E t; cmpq (int 0) arg ]
  let ( = ) (_, arg1) (_, arg2) = function
    | Assign v ->
      (* The register al is the byte register of rax *)
      X86.
        [ movzbq (byte_reg rax) (var v); set E (byte_reg rax); cmpq arg2 arg1 ]
    | Return ->
      (* TODO: is the movzbq from al to rax necessary? *)
      X86.
        [
          movzbq (byte_reg rax) (reg rax); set E (byte_reg rax); cmpq arg2 arg1;
        ]
    | If (t, f) -> X86.[ jmp f; jmp_if E t; cmpq arg2 arg1 ]
  let ( < ) (_, arg1) (_, arg2) = function
    | Assign v ->
      X86.
        [ movzbq (byte_reg rax) (var v); set L (byte_reg rax); cmpq arg2 arg1 ]
    | Return ->
      X86.
        [
          movzbq (byte_reg rax) (reg rax); set L (byte_reg rax); cmpq arg2 arg1;
        ]
    | If (t, f) -> X86.[ jmp f; jmp_if L t; cmpq arg2 arg1 ]
  let goto label = [ X86.jmp label ]
  let if_ cond t_label f_label = cond (If (t_label, f_label))
end

module G = Graph.Imperative.Digraph.Concrete (String)
module Topsort = Graph.Topological.Make (G)
module StringHashtbl = Hashtbl.Make (String)

module UncoverLivePass (X86 : X86_1) = struct
  open Chapter2_definitions
  module M = Chapter3.UncoverLivePass (X86)
  include M

  module X_block = struct
    type 'a from = 'a X86.block
    type 'a term = {
      (* Every block requires a list of the live_before sets of its successor blocks.
         Returns the live before set of the current block along with the rest of the block. *)
      build_fn : StringSet.t list -> StringSet.t * 'a from;
      (* List of successor labels for the block. *)
      successors : X86.label list;
    }
    let fwd b = { build_fn = (fun _ -> (StringSet.empty, b)); successors = [] }
    let bwd { build_fn; _ } = snd (build_fn [])
  end

  module IDelta = struct
    include M.IDelta
    let xorq a b = IDelta.two_arg_instr X86.xorq a b
    let cmpq a b = IDelta.two_arg_instr X86.cmpq a b
    let set cc = IDelta.one_arg_instr (X86.set cc)
    let movzbq a b =
      X86.movzbq (X_arg.bwd a) (X_arg.bwd b)
      |> X_instr.fwd |> IDelta.add_read a |> IDelta.add_write b
    let jmp l =
      let ann, e = X_instr.fwd (X86.jmp l) in
      (X_instr.{ ann with jmp_label = Some l }, e)
    let jmp_if cc l =
      let ann, e = X_instr.fwd (X86.jmp_if cc l) in
      (X_instr.{ ann with jmp_label = Some l }, e)

    let block ?live_after:_ instrs =
      let anns, instrs = List.split instrs in
      let anns = Array.of_list anns in
      let successors = ref [] in
      let add_successor ann =
        match ann.X_instr.jmp_label with
        | Some succ -> successors := succ :: !successors
        | None -> ()
      in
      Array.iter add_successor anns;
      let build_fn succ_live_before =
        (* First element is the live set before the first instruction (live_before). *)
        let live_after = Array.make (Array.length anns + 1) StringSet.empty in
        (* Live after set of the block is the union of the live before sets of the
           successor blocks. *)
        live_after.(Array.length anns) <-
          List.fold_left StringSet.union StringSet.empty succ_live_before;
        for i = Array.length anns - 1 downto 0 do
          live_after.(i) <-
            StringSet.(
              union
                (diff live_after.(i + 1) anns.(i).X_instr.vars_write)
                anns.(i).vars_read)
        done;
        (live_after.(0), X86.block ~live_after instrs)
      in
      { X_block.build_fn; successors = !successors }

    let rev_topsort_block_labels blocks =
      let graph = G.create () in
      List.iter (Fun.compose (G.add_vertex graph) fst) blocks;
      let add_edges (block_label, { X_block.successors; _ }) =
        List.iter (G.add_edge graph block_label) successors
      in
      List.iter add_edges blocks;
      let rev_topo_labels = ref [] in
      Topsort.iter (fun v -> rev_topo_labels := v :: !rev_topo_labels) graph;
      (G.succ graph, !rev_topo_labels)

    let program ?stack_size ?conflicts ?moves blocks =
      let build_fn_map =
        blocks
        |> List.map (fun (label, { X_block.build_fn; _ }) -> (label, build_fn))
        |> List.to_seq |> StringHashtbl.of_seq
      in
      (* From the blocks construct a graph using the successors and do a reverse topsort.
         Then for each block in the ordering, pass in the live_before sets of the
         previously calculated blocks that are successors to the block. *)
      let block_succ, rev_topsort_labels = rev_topsort_block_labels blocks in
      let cached_live_before = StringHashtbl.create (List.length blocks) in
      let result_blocks = StringHashtbl.create (List.length blocks) in
      let go label =
        let succ_live_before =
          List.map (StringHashtbl.find cached_live_before) (block_succ label)
        in
        let build_fn = StringHashtbl.find build_fn_map label in
        let live_before, block = build_fn succ_live_before in
        StringHashtbl.add cached_live_before label live_before;
        StringHashtbl.add result_blocks label block
      in
      List.iter go rev_topsort_labels;
      let blocks =
        rev_topsort_labels |> List.rev
        |> List.map (fun label ->
               (label, StringHashtbl.find result_blocks label))
      in
      X86.program ?stack_size ?conflicts ?moves blocks
  end
end

module UncoverLive (F : X86_1) = struct
  module M = UncoverLivePass (F)
  include X86_1_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
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

module Ex5 (F : R2) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 1 in
    if_
      (var a < int 5)
      (let* b = int 5 in
       let* c = int 6 in
       var b + var c)
      (var a + neg (int 1))
end

module Ex6 (F : R2) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 5 in
    let* b = int 6 in
    if_
      (if_
         (not (var a < int 5))
         (if_
            (var b = int 7)
            (let* c = t in
             not (var c))
            (var b = int 6))
         f)
      (let* d = int 10 in
       let* e = var d + neg (int 1) in
       var e + var d)
      (if_ (var a < var b) (var a + var b) (var a + neg (var b)))
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

let%expect_test "Explicate control with simple conditional" =
  let module M =
    Ex3
      (Shrink
         (RemoveComplex (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ()))) in
  Format.printf "Ex3: %s\n" M.res;
  [%expect
    {| Ex3: (program ((locals . ())) ((start . (seq (assign tmp0 2) (seq (assign tmp2 5) (return (< tmp0 tmp2)))))) |}]

let%expect_test "Explicate control with assignment to conditional" =
  let module M =
    Ex4
      (Shrink
         (RemoveComplex (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ()))) in
  Format.printf "Ex4: %s\n" M.res;
  [%expect
    {| Ex4: (program ((locals . ())) ((start . (seq (assign tmp0 1) (seq (assign tmp4 5) (seq (assign tmp2 (< tmp0 tmp4)) (seq (assign tmp1 (not tmp2)) (return tmp1))))))) |}]

let%expect_test "Explicate control with conditional that creates blocks" =
  let module M =
    Ex5
      (Shrink
         (RemoveComplex (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ()))) in
  Format.printf "Ex5: %s\n" M.res;
  [%expect
    {|
    Ex5: (program ((locals . ())) ((start . (seq (assign tmp0 1) (seq (assign tmp10 5) (if (< tmp0 tmp10) block_t2 block_f3))))
    (block_t0 . (seq (assign tmp1 5) (seq (assign tmp2 6) (return (+ tmp1 tmp2)))))
    (block_f1 . (seq (assign tmp6 1) (seq (assign tmp5 (neg tmp6)) (return (+ tmp0 tmp5)))))
    (block_t2 . (goto block_t0))
    (block_f3 . (goto block_f1)))
    |}]

let%expect_test "Explicate control with nots, nested ifs, booleans in ifs" =
  let module M =
    Ex6
      (Shrink
         (RemoveComplex (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ()))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program ((locals . ())) ((start . (seq (assign tmp0 5) (seq (assign tmp1 6) (seq (assign tmp19 5) (if (< tmp0 tmp19) block_t6 block_f13)))))
    (block_t3 . (goto block_t1))
    (block_t0 . (seq (assign tmp2 10) (seq (assign tmp5 1) (seq (assign tmp4 (neg tmp5)) (seq (assign tmp3 (+ tmp2 tmp4)) (return (+ tmp3 tmp2)))))))
    (block_f5 . (if (< tmp0 tmp1) block_t3 block_f4))
    (block_t10 . (goto block_t0))
    (block_f2 . (seq (assign tmp12 (neg tmp1)) (return (+ tmp0 tmp12))))
    (block_t7 . (goto block_f5))
    (block_t6 . (goto block_f5))
    (block_t9 . (seq (assign tmp22 t) (if tmp22 block_t7 block_f8)))
    (block_f13 . (seq (assign tmp21 7) (if (= tmp1 tmp21) block_t9 block_f12)))
    (block_f11 . (goto block_f5))
    (block_t1 . (return (+ tmp0 tmp1)))
    (block_f12 . (seq (assign tmp24 6) (if (= tmp1 tmp24) block_t10 block_f11)))
    (block_f4 . (goto block_f2))
    (block_f8 . (goto block_t0)))
    |}]

let%expect_test "Select instructions" =
  let module M =
    Ex6
      (Shrink
         (RemoveComplex
            (ExplicateControl
               (R2_Shrink_Pretty ())
               (SelectInstructions (C1_Pretty) (X86_1_Pretty))
               ()))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program () (start . (block ()
    (movq (int 5) (var tmp0))
    (movq (int 6) (var tmp1))
    (movq (int 5) (var tmp19))
    (cmpq (var tmp19) (var tmp0))
    (jmp-if Chapter4.CC.L block_t6)
    (jmp block_f13)))
    (block_t3 . (block ()
    (jmp block_t1)))
    (block_t0 . (block ()
    (movq (int 10) (var tmp2))
    (movq (int 1) (var tmp5))
    (movq (var tmp5) (var tmp4))
    (negq (var tmp4))
    (movq (var tmp2) (var tmp3))
    (addq (var tmp4) (var tmp3))
    (movq (var tmp3) (reg rax))
    (addq (var tmp2) (reg rax))
    (retq)))
    (block_f5 . (block ()
    (cmpq (var tmp1) (var tmp0))
    (jmp-if Chapter4.CC.L block_t3)
    (jmp block_f4)))
    (block_t10 . (block ()
    (jmp block_t0)))
    (block_f2 . (block ()
    (movq (var tmp1) (var tmp12))
    (negq (var tmp12))
    (movq (var tmp0) (reg rax))
    (addq (var tmp12) (reg rax))
    (retq)))
    (block_t7 . (block ()
    (jmp block_f5)))
    (block_t6 . (block ()
    (jmp block_f5)))
    (block_t9 . (block ()
    (movq (int 1) (var tmp22))
    (cmpq (int 0) (var tmp22))
    (jmp-if Chapter4.CC.E block_f8)
    (jmp block_t7)))
    (block_f13 . (block ()
    (movq (int 7) (var tmp21))
    (cmpq (var tmp21) (var tmp1))
    (jmp-if Chapter4.CC.E block_t9)
    (jmp block_f12)))
    (block_f11 . (block ()
    (jmp block_f5)))
    (block_t1 . (block ()
    (movq (var tmp0) (reg rax))
    (addq (var tmp1) (reg rax))
    (retq)))
    (block_f12 . (block ()
    (movq (int 6) (var tmp24))
    (cmpq (var tmp24) (var tmp1))
    (jmp-if Chapter4.CC.E block_t10)
    (jmp block_f11)))
    (block_f4 . (block ()
    (jmp block_f2)))
    (block_f8 . (block ()
    (jmp block_t0))))
    |}]

let%expect_test "Uncover live" =
  let module M =
    Ex6
      (Shrink
         (RemoveComplex
            (ExplicateControl
               (R2_Shrink_Pretty ())
               (SelectInstructions (C1_Pretty) (UncoverLive (X86_1_Pretty)))
               ()))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program () (start . (block ([{}; {tmp0}; {tmp0; tmp1}; {tmp0; tmp1; tmp19}; {tmp0; tmp1}; {tmp0; tmp1};
      {tmp0; tmp1}])
    (movq (int 5) (var tmp0))
    (movq (int 6) (var tmp1))
    (movq (int 5) (var tmp19))
    (cmpq (var tmp19) (var tmp0))
    (jmp-if Chapter4.CC.L block_t6)
    (jmp block_f13)))
    (block_t6 . (block ([{tmp0; tmp1}; {tmp0; tmp1}])
    (jmp block_f5)))
    (block_f13 . (block ([{tmp0; tmp1}; {tmp0; tmp1; tmp21}; {tmp0; tmp1}; {tmp0; tmp1};
      {tmp0; tmp1}])
    (movq (int 7) (var tmp21))
    (cmpq (var tmp21) (var tmp1))
    (jmp-if Chapter4.CC.E block_t9)
    (jmp block_f12)))
    (block_t9 . (block ([{tmp0; tmp1}; {tmp0; tmp1; tmp22}; {tmp0; tmp1}; {tmp0; tmp1};
      {tmp0; tmp1}])
    (movq (int 1) (var tmp22))
    (cmpq (int 0) (var tmp22))
    (jmp-if Chapter4.CC.E block_f8)
    (jmp block_t7)))
    (block_f12 . (block ([{tmp0; tmp1}; {tmp0; tmp1; tmp24}; {tmp0; tmp1}; {tmp0; tmp1};
      {tmp0; tmp1}])
    (movq (int 6) (var tmp24))
    (cmpq (var tmp24) (var tmp1))
    (jmp-if Chapter4.CC.E block_t10)
    (jmp block_f11)))
    (block_t7 . (block ([{tmp0; tmp1}; {tmp0; tmp1}])
    (jmp block_f5)))
    (block_f8 . (block ([{}; {}])
    (jmp block_t0)))
    (block_t10 . (block ([{}; {}])
    (jmp block_t0)))
    (block_f11 . (block ([{tmp0; tmp1}; {tmp0; tmp1}])
    (jmp block_f5)))
    (block_t0 . (block ([{}; {tmp2}; {tmp2; tmp5}; {tmp2; tmp4}; {tmp2; tmp4}; {tmp2; tmp3; tmp4};
      {tmp2; tmp3}; {tmp2}; {}; {}])
    (movq (int 10) (var tmp2))
    (movq (int 1) (var tmp5))
    (movq (var tmp5) (var tmp4))
    (negq (var tmp4))
    (movq (var tmp2) (var tmp3))
    (addq (var tmp4) (var tmp3))
    (movq (var tmp3) (reg rax))
    (addq (var tmp2) (reg rax))
    (retq)))
    (block_f5 . (block ([{tmp0; tmp1}; {tmp0; tmp1}; {tmp0; tmp1}; {tmp0; tmp1}])
    (cmpq (var tmp1) (var tmp0))
    (jmp-if Chapter4.CC.L block_t3)
    (jmp block_f4)))
    (block_t3 . (block ([{tmp0; tmp1}; {tmp0; tmp1}])
    (jmp block_t1)))
    (block_f4 . (block ([{tmp0; tmp1}; {tmp0; tmp1}])
    (jmp block_f2)))
    (block_t1 . (block ([{tmp0; tmp1}; {tmp1}; {}; {}])
    (movq (var tmp0) (reg rax))
    (addq (var tmp1) (reg rax))
    (retq)))
    (block_f2 . (block ([{tmp0; tmp1}; {tmp0; tmp12}; {tmp0; tmp12}; {tmp12}; {}; {}])
    (movq (var tmp1) (var tmp12))
    (negq (var tmp12))
    (movq (var tmp0) (reg rax))
    (addq (var tmp12) (reg rax))
    (retq))))
    |}]

module type R2_Shrink = sig
  include Chapter2.R1
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

module type R2_Let = sig
  include R2
  include Chapter2.R1_Let with type 'a exp := 'a exp
end

module R2_Shrink_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R2_Shrink
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter2.R1_T (X_exp) (X_program) (F)
  open X_exp
  let t = fwd F.t
  let f = fwd F.f
  let not a = fwd (F.not (bwd a))
  let ( = ) a b = fwd F.(bwd a = bwd b)
  let ( < ) a b = fwd F.(bwd a < bwd b)
  let if_ a b c = fwd @@ F.if_ (bwd a) (bwd b) (bwd c)
end

module R2_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R2
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include R2_Shrink_T (X_exp) (X_program) (F)
  open X_exp
  let ( - ) a b = fwd F.(bwd a - bwd b)
  let andd a b = fwd @@ F.andd (bwd a) (bwd b)
  let orr a b = fwd @@ F.orr (bwd a) (bwd b)
  let ( <> ) a b = fwd F.(bwd a <> bwd b)
  let ( <= ) a b = fwd F.(bwd a <= bwd b)
  let ( > ) a b = fwd F.(bwd a > bwd b)
  let ( >= ) a b = fwd F.(bwd a >= bwd b)
end

module R2_Shrink_R_T (R : Chapter1.Reader) (F : R2_Shrink) = struct
  include Chapter2.R1_R_T (R) (F)
  let t _ = F.t
  let f _ = F.f
  let not a r = F.not (a r)
  let ( = ) a b r =
    let a = a r in
    let b = b r in
    F.(a = b)
  let ( < ) a b r =
    let a = a r in
    let b = b r in
    F.(a < b)
  let if_ a b c r =
    let a = a r in
    let b = b r in
    let c = c r in
    F.if_ a b c
end

module R2_R_T (R : Chapter1.Reader) (F : R2) = struct
  include R2_Shrink_R_T (R) (F)
  let ( - ) a b r =
    let a = a r in
    let b = b r in
    F.(a - b)
  let andd a b r =
    let a = a r in
    let b = b r in
    F.andd a b
  let orr a b r =
    let a = a r in
    let b = b r in
    F.orr a b
  let ( <> ) a b r =
    let a = a r in
    let b = b r in
    F.(a <> b)
  let ( <= ) a b r =
    let a = a r in
    let b = b r in
    F.(a <= b)
  let ( > ) a b r =
    let a = a r in
    let b = b r in
    F.(a > b)
  let ( >= ) a b r =
    let a = a r in
    let b = b r in
    F.(a >= b)
end

module R2_Shrink_Pretty () = struct
  include Chapter2.R1_Pretty ()
  let t = "t"
  let f = "f"
  let not a = "(not " ^ a ^ ")"
  let ( = ) a b = "(= " ^ a ^ " " ^ b ^ ")"
  let ( < ) a b = "(< " ^ a ^ " " ^ b ^ ")"
  let if_ a b c = "(if " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
end

module R2_Pretty () = struct
  include R2_Shrink_Pretty ()
  let ( - ) a b = "(- " ^ a ^ " " ^ b ^ ")"

  let andd a b = "(and " ^ a ^ " " ^ b ^ ")"
  let orr a b = "(or " ^ a ^ " " ^ b ^ ")"
  let ( <> ) a b = "(<> " ^ a ^ " " ^ b ^ ")"
  let ( <= ) a b = "(<= " ^ a ^ " " ^ b ^ ")"
  let ( > ) a b = "(> " ^ a ^ " " ^ b ^ ")"
  let ( >= ) a b = "(>= " ^ a ^ " " ^ b ^ ")"
end

module type C1 = sig
  include Chapter2.C0
  val t : bool arg
  val f : bool arg

  val not : bool arg -> bool exp
  val ( = ) : int arg -> int arg -> bool exp
  val ( < ) : int arg -> int arg -> bool exp

  val goto : label -> unit tail
  val if_ : bool exp -> label -> label -> unit tail
end

module C1_R_T (R : Chapter1.Reader) (F : C1) = struct
  include Chapter2.C0_R_T (R) (F)
  let t _ = F.t
  let f _ = F.f
  let not a r = F.not (a r)
  let ( = ) a b r = F.(a r = b r)
  let ( < ) a b r = F.(a r < b r)
  let goto l _ = F.goto l
  let if_ e thn els r = F.if_ (e r) thn els
end

module C1_Pretty = struct
  include Chapter2.C0_Pretty
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
  [@@deriving show { with_path = false }]
end

module type X86_1 = sig
  include Chapter2.X86_0
  val byte_reg : 'b reg -> 'a arg

  val xorq : 'a arg -> 'b arg -> unit instr
  val cmpq : 'a arg -> 'b arg -> unit instr
  val set : CC.t -> 'a arg -> unit instr
  val movzbq : 'a arg -> 'b arg -> unit instr
  val jmp : label -> unit instr
  val jmp_if : CC.t -> label -> unit instr
  val label : label -> unit instr
end

module X86_1_R_T (R : Chapter1.Reader) (F : X86_1) :
  X86_1
    with type 'a reg = R.t -> 'a F.reg
     and type 'a arg = R.t -> 'a F.arg
     and type 'a instr = R.t -> 'a F.instr
     and type 'a block = R.t -> 'a F.block
     and type 'a program = unit -> 'a F.program
     and type label = F.label
     and type 'a obs = 'a F.obs = struct
  include Chapter2.X86_0_R_T (R) (F)
  let byte_reg r ctx = F.byte_reg (r ctx)
  let xorq a b ctx = F.xorq (a ctx) (b ctx)
  let cmpq a b ctx = F.cmpq (a ctx) (b ctx)
  let set cc a ctx = F.set cc (a ctx)
  let movzbq a b ctx = F.movzbq (a ctx) (b ctx)
  let jmp l _ = F.jmp l
  let jmp_if cc l _ = F.jmp_if cc l
  let label l _ = F.label l
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
  include Chapter2.X86_0_T (X_reg) (X_arg) (X_instr) (X_block) (X_program) (F)
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
  include Chapter2.X86_0_Pretty
  let byte_reg reg = "(byte-reg" ^ reg ^ ")"
  let xorq a b = "(xorq" ^ a ^ " " ^ b ^ ")"
  let cmpq a b = "(cmpq " ^ a ^ " " ^ b ^ ")"
  let set cc a = "(set " ^ CC.show cc ^ " " ^ a ^ ")"
  let movzbq a b = "(movzbq " ^ a ^ " " ^ b ^ ")"
  let jmp l = "(jmp " ^ l ^ ")"
  let jmp_if cc l = "(jmp-if " ^ CC.show cc ^ " " ^ l ^ ")"
  let label l = "(label " ^ l ^ ")"
end

module X86_1_Printer_Helper (R : Chapter1.Reader) = struct
  include Chapter2.X86_0_Printer_Helper (R)

  let byte_reg = function
    | "%rsp" -> "%spl"
    | "%rbp" -> "%bpl"
    | "%rax" -> "%al"
    | "%rbx" -> "%bl"
    | "%rcx" -> "%cl"
    | "%rdx" -> "%dl"
    | "%rsi" -> "%sil"
    | "%rdi" -> "%dil"
    | "%r8" -> "%r8b"
    | "%r9" -> "%r9b"
    | "%r10" -> "%r10b"
    | "%r11" -> "%r11b"
    | "%r12" -> "%r12b"
    | "%r13" -> "%r13b"
    | "%r14" -> "%r14b"
    | "%r15" -> "%r15b"
    | _ -> failwith "Unknown register"

  let xorq a b _ = "xorq " ^ a ^ ", " ^ b
  let cmpq a b _ = "cmpq " ^ a ^ ", " ^ b

  let set cc a _ =
    let set_instr =
      match cc with
      | CC.E -> "sete"
      | CC.G -> "setg"
      | CC.Ge -> "setge"
      | CC.L -> "setl"
      | CC.Le -> "setle"
    in
    set_instr ^ " " ^ a
  let movzbq a b _ = "movzbq " ^ a ^ ", " ^ b
  let jmp l _ = "jmp " ^ l
  let jmp_if cc l _ =
    let jmp_instr =
      match cc with
      | CC.E -> "je"
      | CC.G -> "jg"
      | CC.Ge -> "jge"
      | CC.L -> "jl"
      | CC.Le -> "jle"
    in
    jmp_instr ^ " " ^ l
  let label l _ = l ^ ":"
end

module X86_1_Printer = X86_1_Printer_Helper (Chapter2.X86_Info)

module TransformLet (F : R2) : R2_Let with type 'a obs = 'a F.obs = struct
  module M = Chapter2.TransformLetPass (F)
  include R2_R_T (M.R) (F)
  include M.IDelta
end

module ShrinkPass (F : R2_Shrink) = struct
  module X_exp = Chapter1.MkId (struct
    type 'a t = 'a F.exp
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)
  module IDelta = struct
    let ( - ) a b = F.(a + neg b)
    let andd a b = F.(if_ a b f)
    let orr a b = F.(if_ a t b)
    let ( <> ) a b = F.(not (a = b))
    let ( <= ) a b = F.(not (b < a))
    let ( > ) a b = F.(b < a)
    let ( >= ) a b = F.(not (a < b))
  end
end

module Shrink (F : R2_Shrink) : R2 with type 'a obs = 'a F.obs = struct
  module M = ShrinkPass (F)
  include R2_Shrink_T (M.X_exp) (M.X_program) (F)
  include M.IDelta
end

module RemoveComplex (F : R2_Shrink) : R2_Shrink with type 'a obs = 'a F.obs =
struct
  module M = Chapter2.RemoveComplexPass (F)
  include R2_Shrink_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module ExplicateControl (F : R2_Shrink) (C1 : C1) () = struct
  include Chapter2.ExplicateControl (F) (C1) ()

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
  let convert_cond e m = function
    | Tail -> C1.return (m.f e)
    | Assign (v, body) -> C1.(assign v (m.f e) @> body ())
    | Pred (t, f) ->
      let t_label = insert_block "block_t" (t ()) in
      let f_label = insert_block "block_f" (f ()) in
      C1.if_ (m.f e) t_label f_label

  let var v m = function
    | Pred (t, f) ->
      convert_cond C1.(arg (var (F.string_of_var v))) m (Pred (t, f))
    | r -> var v m r

  let t m = function
    | Pred (t, _) -> t ()
    | ctx -> convert_cond C1.(arg t) m ctx
  let f m = function
    | Pred (_, f) -> f ()
    | ctx -> convert_cond C1.(arg f) m ctx
  let not e m = function
    | Pred (t, f) -> e ann_id (Pred (f, t))
    | ctx ->
      let& tmp = e in
      convert_cond C1.(not (var (lookup tmp))) m ctx
  let ( = ) a b m r =
    let& tmp1 = a in
    let& tmp2 = b in
    convert_cond C1.(var (lookup tmp1) = var (lookup tmp2)) m r
  let ( < ) a b m r =
    let& tmp1 = a in
    let& tmp2 = b in
    convert_cond C1.(var (lookup tmp1) < var (lookup tmp2)) m r

  let if_ cond t_branch f_branch m = function
    | Tail ->
      let t_label = insert_block "block_t" @@ t_branch m Tail in
      let f_label = insert_block "block_f" @@ f_branch m Tail in
      cond ann_id
        (Pred ((fun () -> C1.goto t_label), fun () -> C1.goto f_label))
    | Assign (v, body) ->
      let body_label = insert_block "block_body" @@ body () in
      let t_label =
        insert_block "block_t" @@ t_branch m
        @@ Assign (v, fun () -> C1.goto body_label)
      in
      let f_label =
        insert_block "block_f" @@ f_branch m
        @@ Assign (v, fun () -> C1.goto body_label)
      in
      cond ann_id
        (Pred ((fun () -> C1.goto t_label), fun () -> C1.goto f_label))
    | Pred (t, f) ->
      cond ann_id
        (Pred
           ( (fun () -> t_branch m (Pred (t, f))),
             fun () -> f_branch m (Pred (t, f)) ))

  let program e () =
    let start_body = e ann_id Tail in
    let blocks = List.of_seq @@ Hashtbl.to_seq block_map in
    C1.program (("start", start_body) :: blocks)
end

module SelectInstructions (F : C1) (X86 : X86_1) = struct
  include Chapter2.SelectInstructions (F) (X86)

  let return e exit_label = X86.jmp exit_label :: e Return
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
  let goto label _ = [ X86.jmp label ]
  let if_ cond t_label f_label _ = cond (If (t_label, f_label))

  let fresh_exit_label =
    let c = ref (-1) in
    fun () ->
      incr c;
      if Int.equal !c 0 then
        "block_exit"
      else
        "block_exit" ^ string_of_int !c
  let program ?locals:_ body =
    let exit_label = fresh_exit_label () in
    let body =
      List.map (fun (l, t) -> (l, X86.block (List.rev (t exit_label)))) body
    in
    let exit_block = (exit_label, X86.(block [ retq ])) in
    X86.program (exit_block :: body)
end

module G = Graph.Imperative.Digraph.Concrete (String)
module Topsort = Graph.Topological.Make (G)
module StringHashtbl = Chapter2.StringHashtbl

module UncoverLivePass (X86 : X86_1) = struct
  open Chapter2
  include Chapter3.UncoverLivePass (X86)

  module X_block = struct
    type 'a from = 'a X86.block
    type 'a term = {
      (* Every block requires a list of the live_before sets of its successor blocks.
         Returns the live before set of the current block along with the rest of the block. *)
      build_fn : ArgSet.t list -> ArgSet.t * 'a from;
      (* List of successor labels for the block. *)
      successors : X86.label list;
    }
    let fwd b = { build_fn = (fun _ -> (ArgSet.empty, b)); successors = [] }
    let bwd { build_fn; _ } = snd (build_fn [])
  end

  module IDelta = struct
    include IDelta
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
        let live_after = Array.make (Array.length anns + 1) ArgSet.empty in
        (* Live after set of the block is the union of the live before sets of the
           successor blocks. *)
        live_after.(Array.length anns) <-
          List.fold_left ArgSet.union ArgSet.empty succ_live_before;
        for i = Array.length anns - 1 downto 0 do
          live_after.(i) <-
            ArgSet.(
              union
                (diff live_after.(i + 1) anns.(i).X_instr.args_write)
                anns.(i).args_read)
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
      (graph, !rev_topo_labels)

    let program_helper blocks =
      let build_fn_map =
        blocks
        |> List.map (fun (label, { X_block.build_fn; _ }) -> (label, build_fn))
        |> List.to_seq |> StringHashtbl.of_seq
      in
      (* From the blocks construct a graph using the successors and do a reverse topsort.
         Then for each block in the ordering, pass in the live_before sets of the
         previously calculated blocks that are successors to the block. *)
      let graph, rev_topsort_labels = rev_topsort_block_labels blocks in
      let cached_live_before = StringHashtbl.create (List.length blocks) in
      let result_blocks = StringHashtbl.create (List.length blocks) in
      let go label =
        (* Don't handle unreachable blocks, they will be removed in filter_map *)
        if
          String.starts_with ~prefix:"start" label
          || not (List.is_empty (G.pred graph label))
        then (
          let succ_live_before =
            List.map
              (StringHashtbl.find cached_live_before)
              (G.succ graph label)
          in
          let build_fn = StringHashtbl.find build_fn_map label in
          let live_before, block = build_fn succ_live_before in
          StringHashtbl.add cached_live_before label live_before;
          StringHashtbl.add result_blocks label block)
      in
      List.iter go rev_topsort_labels;
      rev_topsort_labels |> List.rev
      |> List.filter_map (fun label ->
             Option.map
               (fun block -> (label, block))
               (StringHashtbl.find_opt result_blocks label))

    let program ?stack_size ?conflicts ?moves blocks =
      let blocks = program_helper blocks in
      X86.program ?stack_size ?conflicts ?moves blocks
  end
end

module UncoverLive (F : X86_1) : X86_1 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include X86_1_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module BuildInterferencePass (X86 : X86_1) = struct
  include Chapter3.BuildInterferencePass (X86)
  module IDelta = struct
    include IDelta

    let byte_reg r = (Some (arg_of_reg r), X86.byte_reg r)

    let xorq (_, a) (dest, b) =
      match dest with
      | Some dest -> (arith dest, X86.xorq a b)
      | None -> X_instr.fwd @@ X86.xorq a b

    let set cc (dest, a) =
      match dest with
      | Some dest -> (arith dest, X86.set cc a)
      | None -> X_instr.fwd @@ X86.set cc a

    let movzbq (src, a) (dest, b) =
      let open Chapter2 in
      match dest with
      | Some dest ->
        let acc_graph live_after graph =
          ArgSet.fold
            (fun v graph ->
              if Some v = src || v = dest then
                graph
              else
                Chapter3.GraphUtils.add_interference dest v graph)
            live_after graph
        in
        (acc_graph, X86.movzbq a b)
      | None -> X_instr.fwd @@ X86.movzbq a b
  end
end

module BuildInterference (F : X86_1) : X86_1 with type 'a obs = 'a F.obs =
struct
  module M = BuildInterferencePass (F)
  include X86_1_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module BuildMovesPass (X86 : X86_1) = struct
  include Chapter3.BuildMovesPass (X86)
  module IDelta = struct
    include IDelta

    let byte_reg r = (Some (arg_of_reg r), X86.byte_reg r)
    let movzbq (arg1, a) (arg2, b) =
      match (arg1, arg2) with
      | Some arg1, Some arg2 ->
        (Chapter3.GraphUtils.add_interference arg1 arg2, X86.movzbq a b)
      | _ -> X_instr.fwd @@ X86.movzbq a b
  end
end

module BuildMoves (F : X86_1) : X86_1 with type 'a obs = 'a F.obs = struct
  module M = BuildMovesPass (F)
  include X86_1_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module AllocateRegisters (X86 : X86_1) : X86_1 with type 'a obs = 'a X86.obs =
struct
  module M = Chapter3.AllocateRegistersPass (X86)
  include X86_1_R_T (M.X_reader) (X86)
  include M.IDelta
end

module Ex1 (F : R2_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* a = int 2 in
    let* b = read () in
    if_ (andd (var a <= int 5) (var b > var a)) (var b - var a) (var b + var a)
end

module PatchInstructionsPass (X86 : X86_1) = struct
  include Chapter2.PatchInstructionsPass (X86)
  module IDelta = struct
    include IDelta
    open ArgInfo
    let byte_reg r = (ArgInfo.HashedRegister (Hashtbl.hash r), X86.byte_reg r)

    let xorq (info1, a) (info2, b) =
      match (info1, info2) with
      | MemoryReference _, MemoryReference _ ->
        X86.[ movq a (reg rax); xorq (reg rax) b ]
      | _ -> X_instr.fwd @@ X86.xorq a b
    let cmpq (info1, a) (info2, b) =
      match (info1, info2) with
      | MemoryReference _, MemoryReference _ ->
        X86.[ movq a (reg rax); cmpq (reg rax) b ]
      | _, (MemoryReference _ | HashedRegister _) -> X_instr.fwd @@ X86.cmpq a b
      (* Destination with immediate *)
      | _ -> X86.[ movq b (reg rax); cmpq a (reg rax) ]
    let movzbq (info1, a) (info2, b) =
      if ArgInfo.equal info1 info2 then
        []
      else
        match (info1, info2) with
        | MemoryReference _, MemoryReference _ ->
          X86.[ movq a (reg rax); movzbq (reg rax) b ]
        | _ -> X_instr.fwd @@ X86.movzbq a b
  end
end

module PatchInstructions (F : X86_1) = struct
  module M = PatchInstructionsPass (F)
  include X86_1_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module Ex2 (F : R2_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let* a = int 2 in
    if_ (var a < int 5) (var a + int 1) (int 6 + int 7)
end

module Ex3 (F : R2_Let) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 2 in
       var a < int 5
end

module Ex4 (F : R2_Let) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 1 in
       let* b = not (var a < int 5) in
       var b
end

module Ex5 (F : R2_Let) = struct
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

module Ex6 (F : R2_Let) = struct
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
  let module M = Ex1 (TransformLet (Shrink (R2_Shrink_Pretty ()))) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {| Ex1: (program (let ([tmp0 2]) (let ([tmp1 (read)]) (if (if (not (< 5 (var tmp0))) (< (var tmp0) (var tmp1)) f) (+ (var tmp1) (- (var tmp0))) (+ (var tmp1) (var tmp0)))))) |}]

let%expect_test "Remove complex with simple conditional" =
  let module M = Ex2 (TransformLet (Shrink (RemoveComplex (R2_Shrink_Pretty ())))) in
  Format.printf "Ex2: %s\n" M.res;
  [%expect
    {| Ex2: (program (let ([tmp0 2]) (if (< (var tmp0) 5) (+ (var tmp0) 1) (+ 6 7)))) |}]

let%expect_test "Explicate control with simple conditional" =
  let module M =
    Ex3
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ())))) in
  Format.printf "Ex3: %s\n" M.res;
  [%expect
    {| Ex3: (program ((locals . ())) ((start . (seq (assign tmp0 2) (seq (assign tmp2 5) (return (< tmp0 tmp2)))))) |}]

let%expect_test "Explicate control with assignment to conditional" =
  let module M =
    Ex4
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ())))) in
  Format.printf "Ex4: %s\n" M.res;
  [%expect
    {| Ex4: (program ((locals . ())) ((start . (seq (assign tmp0 1) (seq (assign tmp4 5) (seq (assign tmp2 (< tmp0 tmp4)) (seq (assign tmp1 (not tmp2)) (return tmp1))))))) |}]

let%expect_test "Explicate control with conditional that creates blocks" =
  let module M =
    Ex5
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ())))) in
  Format.printf "Ex5: %s\n" M.res;
  [%expect
    {|
    Ex5: (program ((locals . ())) ((start . (seq (assign tmp0 1) (seq (assign tmp10 5) (if (< tmp0 tmp10) block_t2 block_f3))))
    (block_t0 . (seq (assign tmp1 5) (seq (assign tmp2 6) (return (+ tmp1 tmp2)))))
    (block_f1 . (seq (assign tmp6 1) (seq (assign tmp3 (neg tmp6)) (return (+ tmp0 tmp3)))))
    (block_t2 . (goto block_t0))
    (block_f3 . (goto block_f1)))
    |}]

let%expect_test "Explicate control with nots, nested ifs, booleans in ifs" =
  let module M =
    Ex6
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl (R2_Shrink_Pretty ()) (C1_Pretty) ())))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program ((locals . ())) ((start . (seq (assign tmp0 5) (seq (assign tmp1 6) (seq (assign tmp20 5) (if (< tmp0 tmp20) block_t6 block_f13)))))
    (block_t3 . (goto block_t1))
    (block_t0 . (seq (assign tmp3 10) (seq (assign tmp7 1) (seq (assign tmp4 (neg tmp7)) (seq (assign tmp5 (+ tmp3 tmp4)) (return (+ tmp5 tmp3)))))))
    (block_f5 . (if (< tmp0 tmp1) block_t3 block_f4))
    (block_t10 . (goto block_t0))
    (block_f2 . (seq (assign tmp6 (neg tmp1)) (return (+ tmp0 tmp6))))
    (block_t7 . (goto block_f5))
    (block_t6 . (goto block_f5))
    (block_t9 . (seq (assign tmp2 t) (if tmp2 block_t7 block_f8)))
    (block_f13 . (seq (assign tmp22 7) (if (= tmp1 tmp22) block_t9 block_f12)))
    (block_f11 . (goto block_f5))
    (block_t1 . (return (+ tmp0 tmp1)))
    (block_f12 . (seq (assign tmp24 6) (if (= tmp1 tmp24) block_t10 block_f11)))
    (block_f4 . (goto block_f2))
    (block_f8 . (goto block_t0)))
    |}]

let%expect_test "Select instructions" =
  let module M =
    Ex6
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl
                  (R2_Shrink_Pretty ())
                  (SelectInstructions (C1_Pretty) (X86_1_Pretty))
                  ())))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program () (block_exit . (block ()
    (retq)))
    (start . (block ()
    (movq (int 5) (var tmp0))
    (movq (int 6) (var tmp1))
    (movq (int 5) (var tmp20))
    (cmpq (var tmp20) (var tmp0))
    (jmp-if L block_t6)
    (jmp block_f13)))
    (block_t3 . (block ()
    (jmp block_t1)))
    (block_t0 . (block ()
    (movq (int 10) (var tmp3))
    (movq (int 1) (var tmp7))
    (movq (var tmp7) (var tmp4))
    (negq (var tmp4))
    (movq (var tmp3) (var tmp5))
    (addq (var tmp4) (var tmp5))
    (movq (var tmp5) (reg rax))
    (addq (var tmp3) (reg rax))
    (jmp block_exit)))
    (block_f5 . (block ()
    (cmpq (var tmp1) (var tmp0))
    (jmp-if L block_t3)
    (jmp block_f4)))
    (block_t10 . (block ()
    (jmp block_t0)))
    (block_f2 . (block ()
    (movq (var tmp1) (var tmp6))
    (negq (var tmp6))
    (movq (var tmp0) (reg rax))
    (addq (var tmp6) (reg rax))
    (jmp block_exit)))
    (block_t7 . (block ()
    (jmp block_f5)))
    (block_t6 . (block ()
    (jmp block_f5)))
    (block_t9 . (block ()
    (movq (int 1) (var tmp2))
    (cmpq (int 0) (var tmp2))
    (jmp-if E block_f8)
    (jmp block_t7)))
    (block_f13 . (block ()
    (movq (int 7) (var tmp22))
    (cmpq (var tmp22) (var tmp1))
    (jmp-if E block_t9)
    (jmp block_f12)))
    (block_f11 . (block ()
    (jmp block_f5)))
    (block_t1 . (block ()
    (movq (var tmp0) (reg rax))
    (addq (var tmp1) (reg rax))
    (jmp block_exit)))
    (block_f12 . (block ()
    (movq (int 6) (var tmp24))
    (cmpq (var tmp24) (var tmp1))
    (jmp-if E block_t10)
    (jmp block_f11)))
    (block_f4 . (block ()
    (jmp block_f2)))
    (block_f8 . (block ()
    (jmp block_t0))))
    |}]

let%expect_test "Uncover live" =
  let module M =
    Ex6
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl
                  (R2_Shrink_Pretty ())
                  (SelectInstructions (C1_Pretty) (UncoverLive (X86_1_Pretty)))
                  ())))) in
  Format.printf "Ex6: %s\n" M.res;
  [%expect
    {|
    Ex6: (program () (start . (block ([{}; {Var tmp0}; {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1; Var tmp20};
      {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (movq (int 5) (var tmp0))
    (movq (int 6) (var tmp1))
    (movq (int 5) (var tmp20))
    (cmpq (var tmp20) (var tmp0))
    (jmp-if L block_t6)
    (jmp block_f13)))
    (block_t6 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (jmp block_f5)))
    (block_f13 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1; Var tmp22};
      {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (movq (int 7) (var tmp22))
    (cmpq (var tmp22) (var tmp1))
    (jmp-if E block_t9)
    (jmp block_f12)))
    (block_t9 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1; Var tmp2}; {Var tmp0; Var tmp1};
      {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (movq (int 1) (var tmp2))
    (cmpq (int 0) (var tmp2))
    (jmp-if E block_f8)
    (jmp block_t7)))
    (block_f12 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1; Var tmp24};
      {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (movq (int 6) (var tmp24))
    (cmpq (var tmp24) (var tmp1))
    (jmp-if E block_t10)
    (jmp block_f11)))
    (block_t7 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (jmp block_f5)))
    (block_f8 . (block ([{}; {}])
    (jmp block_t0)))
    (block_t10 . (block ([{}; {}])
    (jmp block_t0)))
    (block_f11 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (jmp block_f5)))
    (block_t0 . (block ([{}; {Var tmp3}; {Var tmp3; Var tmp7}; {Var tmp3; Var tmp4};
      {Var tmp3; Var tmp4}; {Var tmp3; Var tmp4; Var tmp5}; {Var tmp3; Var tmp5};
      {Var tmp3; Reg rax}; {}; {}])
    (movq (int 10) (var tmp3))
    (movq (int 1) (var tmp7))
    (movq (var tmp7) (var tmp4))
    (negq (var tmp4))
    (movq (var tmp3) (var tmp5))
    (addq (var tmp4) (var tmp5))
    (movq (var tmp5) (reg rax))
    (addq (var tmp3) (reg rax))
    (jmp block_exit)))
    (block_f5 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}; {Var tmp0; Var tmp1};
      {Var tmp0; Var tmp1}])
    (cmpq (var tmp1) (var tmp0))
    (jmp-if L block_t3)
    (jmp block_f4)))
    (block_t3 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (jmp block_t1)))
    (block_f4 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp1}])
    (jmp block_f2)))
    (block_t1 . (block ([{Var tmp0; Var tmp1}; {Var tmp1; Reg rax}; {}; {}])
    (movq (var tmp0) (reg rax))
    (addq (var tmp1) (reg rax))
    (jmp block_exit)))
    (block_f2 . (block ([{Var tmp0; Var tmp1}; {Var tmp0; Var tmp6}; {Var tmp0; Var tmp6};
      {Var tmp6; Reg rax}; {}; {}])
    (movq (var tmp1) (var tmp6))
    (negq (var tmp6))
    (movq (var tmp0) (reg rax))
    (addq (var tmp6) (reg rax))
    (jmp block_exit)))
    (block_exit . (block ([{}; {}])
    (retq))))
    |}]

let%expect_test "Allocate Registers" =
  let module M =
    Ex6
      (TransformLet
         (Shrink
            (RemoveComplex
               (ExplicateControl
                  (R2_Shrink_Pretty ())
                  (SelectInstructions
                     (C1_Pretty)
                     (UncoverLive
                        (BuildInterference
                           (BuildMoves
                              (AllocateRegisters
                                 (PatchInstructions (X86_1_Printer)))))))
                  ())))) in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    main:
      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
    start:

      movq $5, %rdx
      movq $6, %rdi
      movq $5, %rsi
      cmpq %rsi, %rdx
      jl block_t6
      jmp block_f13
    block_t6:

      jmp block_f5
    block_f13:

      movq $7, %rsi
      cmpq %rsi, %rdi
      je block_t9
      jmp block_f12
    block_t9:

      movq $1, %rsi
      cmpq $0, %rsi
      je block_f8
      jmp block_t7
    block_f12:

      movq $6, %rsi
      cmpq %rsi, %rdi
      je block_t10
      jmp block_f11
    block_t7:

      jmp block_f5
    block_f8:

      jmp block_t0
    block_t10:

      jmp block_t0
    block_f11:

      jmp block_f5
    block_t0:

      movq $10, %rdx
      movq $1, %rsi
      movq %rsi, %rdi
      negq %rdi
      movq %rdx, %rsi
      addq %rdi, %rsi
      movq %rsi, %rax
      addq %rdx, %rax
      jmp block_exit
    block_f5:

      cmpq %rdi, %rdx
      jl block_t3
      jmp block_f4
    block_t3:

      jmp block_t1
    block_f4:

      jmp block_f2
    block_t1:

      movq %rdx, %rax
      addq %rdi, %rax
      jmp block_exit
    block_f2:

      movq %rdi, %rsi
      negq %rsi
      movq %rdx, %rax
      addq %rsi, %rax
      jmp block_exit
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      retq
    |}]

open Chapter2_definitions

module UncoverLivePass (X86 : X86_0) = struct
  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)
  module X_arg = struct
    type 'a from = 'a X86.arg
    type 'a term = Arg.t option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end

  module X_instr = struct
    type 'a from = 'a X86.instr
    type ann = {
      args_write : ArgSet.t;
      args_read : ArgSet.t;
      jmp_label : X86.label option;
    }
    type 'a term = ann * 'a from
    let fwd a =
      ( { args_write = ArgSet.empty; args_read = ArgSet.empty; jmp_label = None },
        a )
    let bwd (_, a) = a
  end

  module X_block = Chapter1.MkId (struct
    type 'a t = 'a X86.block
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)

  module X86_String = X86_Reg_String (X86)

  module IDelta = struct
    let var v = (Some (Arg.Var v), X86.var v)
    let reg r = (Some (X86_String.arg_of_reg r), X86.reg r)

    let add_read (v, _) (ann, r) =
      let ann =
        match v with
        | Some v -> X_instr.{ ann with args_read = ArgSet.add v ann.args_read }
        | None -> ann
      in
      (ann, r)
    let add_write (v, _) (ann, r) =
      let ann =
        match v with
        | Some v ->
          X_instr.{ ann with args_write = ArgSet.add v ann.args_write }
        | None -> ann
      in
      (ann, r)

    let caller_saves = X86.[ rax; rcx; rdx; rsi; rdi; r8; r9; r10; r11 ]

    let one_arg_instr f a = f (X_arg.bwd a) |> X_instr.fwd |> add_read a
    let two_arg_instr f a b =
      f (X_arg.bwd a) (X_arg.bwd b) |> X_instr.fwd |> add_read a |> add_read b

    let addq a b = two_arg_instr X86.addq a b
    let subq a b = two_arg_instr X86.subq a b
    let movq a b =
      X86.movq (X_arg.bwd a) (X_arg.bwd b)
      |> X_instr.fwd |> add_read a |> add_write b
    let retq = X_instr.fwd X86.retq
    let negq a = one_arg_instr X86.negq a
    let callq l =
      X_instr.fwd (X86.callq l)
      |> List.fold_right (fun r -> add_write (reg r)) caller_saves
    let pushq a = one_arg_instr X86.pushq a
    let popq a = one_arg_instr X86.pushq a

    let block ?live_after:_ instrs =
      let anns, instrs = List.split instrs in
      let anns = Array.of_list anns in
      (* First element is the live set before the first instruction (live_before). *)
      let live_after = Array.make (Array.length anns + 1) ArgSet.empty in
      for i = Array.length anns - 1 downto 0 do
        live_after.(i) <-
          ArgSet.(
            union
              (diff live_after.(i + 1) anns.(i).X_instr.args_write)
              anns.(i).args_read)
      done;
      X86.block ~live_after instrs
  end
end

module UncoverLive (F : X86_0) : X86_0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module GraphUtils = struct
  module IntSet = Set.Make (Int)
  module ArgTable = Hashtbl.Make (Arg)
  let add_interference k v graph =
    if k = v then
      graph
    else
      let update k v graph =
        let go = function
          | Some set -> Some (ArgSet.add v set)
          | None -> Some (ArgSet.singleton v)
        in
        ArgMap.update k go graph
      in
      graph |> update k v |> update v k

  let neighbors graph v =
    Option.value ~default:ArgSet.empty (ArgMap.find_opt v graph)
  let saturation color graph v =
    let go w acc =
      try IntSet.add (ArgTable.find color w) acc with Not_found -> acc
    in
    ArgSet.fold go (neighbors graph v) IntSet.empty

  let rec remove_list a = function
    | [] -> []
    | e :: es -> if a = e then es else e :: remove_list a es

  let color_graph moves graph vars =
    let color_table = ArgTable.create (List.length vars) in
    let module Elem = struct
      type t = Arg.t
      let compare_by_saturation a b =
        let a_saturation = IntSet.cardinal (saturation color_table graph a) in
        let b_saturation = IntSet.cardinal (saturation color_table graph b) in
        if a_saturation = b_saturation then
          Arg.compare a b
        else
          Int.compare a_saturation b_saturation

      let compare a b =
        match (a, b) with
        | Arg.Reg _, Arg.Reg _ -> compare_by_saturation a b
        | Arg.Var _, Arg.Var _ -> compare_by_saturation a b
        | Arg.Reg _, Arg.Var _ -> Arg.compare a b
        | Arg.Var _, Arg.Reg _ -> Arg.compare a b
    end in
    let module Worklist = Set.Make (Elem) in
    let rec go worklist =
      if not (List.is_empty worklist) then begin
        let u = Worklist.(max_elt (of_list worklist)) in
        let adjacent_colors = saturation color_table graph u in
        let rec find_color color =
          if IntSet.mem color adjacent_colors then
            find_color (color + 1)
          else
            color
        in
        let biased_colors =
          IntSet.filter
            (fun color -> not (IntSet.mem color adjacent_colors))
            (saturation color_table moves u)
        in
        let c =
          if IntSet.is_empty biased_colors then
            find_color 0
          else
            IntSet.min_elt biased_colors
        in
        ArgTable.add color_table u c;
        go (remove_list u worklist)
      end
    in
    go vars;
    ArgMap.of_seq @@ ArgTable.to_seq color_table
end

module BuildInterferencePass (X86 : X86_0) = struct
  type acc_graph = ArgSet.t ArgMap.t -> ArgSet.t ArgMap.t
  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)
  module X_arg = struct
    type 'a from = 'a X86.arg
    type 'a term = Arg.t option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end
  module X_instr = struct
    type 'a from = 'a X86.instr
    type 'a term = (ArgSet.t -> acc_graph) * 'a from
    let fwd a = ((fun _ graph -> graph), a)
    let bwd (_, a) = a
  end
  module X_block = struct
    type 'a from = 'a X86.block
    type 'a term = acc_graph * 'a from
    let fwd a = (Fun.id, a)
    let bwd (_, a) = a
  end
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)
  module IDelta = struct
    include Chapter2_definitions.X86_Reg_String (X86)
    let reg r = (Some (arg_of_reg r), X86.reg r)
    let var v = (Some (Arg.Var v), X86.var v)

    let arith dest live_after graph =
      ArgSet.fold
        (fun v graph -> GraphUtils.add_interference dest v graph)
        live_after graph
    let caller_saves = X86.[ rax; rcx; rdx; rsi; rdi; r8; r9; r10; r11 ]

    let addq (_, a) (dest, b) =
      match dest with
      | Some dest -> (arith dest, X86.addq a b)
      | None -> X_instr.fwd @@ X86.addq a b
    let subq (_, a) (dest, b) =
      match dest with
      | Some dest -> (arith dest, X86.subq a b)
      | None -> X_instr.fwd @@ X86.subq a b
    let negq (dest, a) =
      match dest with
      | Some dest -> (arith dest, X86.negq a)
      | None -> X_instr.fwd @@ X86.negq a
    let pushq (dest, a) =
      match dest with
      | Some dest -> (arith dest, X86.pushq a)
      | None -> X_instr.fwd @@ X86.pushq a
    let popq (dest, a) =
      match dest with
      | Some dest -> (arith dest, X86.popq a)
      | None -> X_instr.fwd @@ X86.popq a

    let movq (src, a) (dest, b) =
      match dest with
      | Some dest ->
        let acc_graph live_after graph =
          ArgSet.fold
            (fun v graph ->
              if Some v = src || v = dest then
                graph
              else
                GraphUtils.add_interference dest v graph)
            live_after graph
        in
        (acc_graph, X86.movq a b)
      | None -> X_instr.fwd @@ X86.movq a b

    let callq label =
      let acc_graph live_after graph =
        let edges =
          let ( let* ) a f = List.concat_map f a in
          let* r = caller_saves in
          let* v = ArgSet.to_list live_after in
          if v <> arg_of_reg r then
            [ (arg_of_reg r, v) ]
          else
            []
        in
        List.fold_left
          (fun graph (k, v) -> GraphUtils.add_interference k v graph)
          graph edges
      in
      (acc_graph, X86.callq label)

    let block ?live_after instrs =
      let live_after' = Option.value ~default:[||] live_after in
      (* The live_before set is the first element in the live_after array.
         To get the live_after list for each instruction, ignore the first element.
      *)
      let live_after' =
        match Array.to_list live_after' with
        | _ :: tl -> tl
        | _ ->
          failwith
            "Could not get the live_before set, did you run UncoverLive before \
             BuildInterference?"
      in
      let acc_block graph =
        List.fold_left
          (fun graph (live_after, (f, _)) -> f live_after graph)
          graph
          (List.combine live_after' instrs)
      in
      let instrs = List.map (fun (_, instr) -> instr) instrs in
      (acc_block, X86.block ?live_after instrs)

    (* TODO: merge with regs from AllocateRegistersPass *)
    let regs =
      X86.[ rbx; rcx; rdx; rsi; rdi; r8; r9; r10; r11; r12; r13; r14; r15 ]
    let init_interference_graph =
      let ( let* ) a f = List.concat_map f a in
      let conflicts =
        let* a = regs in
        let* b = regs in
        if arg_of_reg a = arg_of_reg b then
          []
        else
          [ (arg_of_reg a, arg_of_reg b) ]
      in
      List.fold_left
        (fun acc (a, b) -> GraphUtils.add_interference a b acc)
        ArgMap.empty conflicts

    let program ?stack_size ?conflicts:_ ?moves blocks =
      let interference_graph =
        List.fold_left
          (fun graph (_, (f, _)) -> f graph)
          init_interference_graph blocks
      in
      let blocks = List.map (fun (l, (_, block)) -> (l, block)) blocks in
      X86.program ?stack_size ~conflicts:interference_graph ?moves blocks
  end
end

module BuildInterference (F : X86_0) : X86_0 with type 'a obs = 'a F.obs =
struct
  module M = BuildInterferencePass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module BuildMovesPass (X86 : X86_0) = struct
  type acc_graph = ArgSet.t ArgMap.t -> ArgSet.t ArgMap.t
  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)
  module X_arg = struct
    type 'a from = 'a X86.arg
    type 'a term = Arg.t option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end
  module X_instr = struct
    type 'a from = 'a X86.instr
    type 'a term = acc_graph * 'a from
    let fwd a = (Fun.id, a)
    let bwd (_, a) = a
  end
  module X_block = struct
    type 'a from = 'a X86.block
    type 'a term = acc_graph * 'a from
    let fwd a = (Fun.id, a)
    let bwd (_, a) = a
  end
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)
  module IDelta = struct
    include Chapter2_definitions.X86_Reg_String (X86)
    let arg_of_reg reg = Arg.Reg (string_of_reg reg)
    let reg r = (Some (arg_of_reg r), X86.reg r)
    let var v = (Some (Arg.Var v), X86.var v)
    let movq (arg1, a) (arg2, b) =
      match (arg1, arg2) with
      | Some arg1, Some arg2 ->
        (GraphUtils.add_interference arg1 arg2, X86.movq a b)
      | _ -> X_instr.fwd @@ X86.movq a b

    let block ?live_after instrs =
      let accs, instrs = List.split instrs in
      let acc = List.fold_right Fun.compose accs (fun a -> a) in
      (acc, X86.block ?live_after instrs)

    let program_helper blocks =
      let moves =
        List.fold_left (fun graph (_, (f, _)) -> f graph) ArgMap.empty blocks
      in
      let blocks = List.map (fun (l, (_, block)) -> (l, block)) blocks in
      (moves, blocks)

    let program ?stack_size ?conflicts ?moves:_ blocks =
      let moves, blocks = program_helper blocks in
      X86.program ?stack_size ?conflicts ~moves blocks
  end
end

module BuildMoves (F : X86_0) : X86_0 with type 'a obs = 'a F.obs = struct
  module M = BuildMovesPass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module AllocateRegistersPass (X86 : X86_0) = struct
  module X_reader = Chapter1.UnitReader

  module IDelta = struct
    type _ eff += Rename : string -> 'a X86.arg eff
    let var v _ = Effect.perform (Rename v)

    let spill stack_size slot_table reg color =
      let slot =
        try Hashtbl.find slot_table color
        with Not_found ->
          stack_size := !stack_size + 8;
          let slot = - !stack_size in
          Hashtbl.add slot_table color slot;
          slot
      in
      X86.deref reg slot

    let regs =
      X86.[| rbx; rcx; rdx; rsi; rdi; r8; r9; r10; r11; r12; r13; r14; r15 |]

    let reg_of_color stack_size color_slot_table regs color =
      if color < Array.length regs then
        X86.reg regs.(color)
      else
        spill stack_size color_slot_table X86.rbp color

    include Chapter2_definitions.X86_Reg_String (X86)

    let program ?stack_size:_ ?(conflicts = ArgMap.empty)
        ?(moves = ArgMap.empty) blocks () =
      let stack_size = ref 0 in
      let color_slot_table : (int, int) Hashtbl.t = Hashtbl.create 100 in
      (* Remove rax from the interference graph *)
      let rax = Arg.Reg (string_of_reg X86.rax) in
      let conflicts =
        conflicts |> ArgMap.remove rax |> ArgMap.map (ArgSet.remove rax)
      in
      let vars = ArgMap.keys conflicts in
      let colors = GraphUtils.color_graph moves conflicts vars in
      (* TODO: add this once the expectation test changes are verified *)
      (* Array.sort
        (fun a b ->
          Int.compare
            (ArgMap.find (arg_of_reg a) colors)
            (ArgMap.find (arg_of_reg b) colors))
        regs; *)
      let get_arg v =
        reg_of_color stack_size color_slot_table regs (ArgMap.find_var v colors)
      in
      let blocks =
        try List.map (fun (l, b) -> (l, b ())) blocks
        with effect Rename v, k -> Effect.Deep.continue k (get_arg v)
      in
      X86.program ~stack_size:!stack_size ~conflicts ~moves blocks
  end
end

module AllocateRegisters (X86 : X86_0) : X86_0 with type 'a obs = 'a X86.obs =
struct
  module M = AllocateRegistersPass (X86)
  include Chapter2_definitions.X86_0_R_T (M.X_reader) (X86)
  include M.IDelta
end

module Ex1 (F : X86_0) = struct
  open F

  let res =
    observe
    @@ program
         [
           ( "start",
             block
               [
                 movq (int 1) (var "v");
                 movq (int 46) (var "w");
                 movq (var "v") (var "x");
                 addq (int 7) (var "x");
                 movq (var "x") (var "y");
                 addq (int 4) (var "y");
                 movq (var "x") (var "z");
                 addq (var "w") (var "z");
                 movq (var "y") (var "t.1");
                 negq (var "t.1");
                 movq (var "z") (reg rax);
                 addq (var "t.1") (reg rax);
                 retq;
               ] );
         ]
end

let%expect_test "Example 1 after uncover live" =
  let module M = Ex1 (UncoverLive (X86_0_Pretty)) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {|
    Ex1: (program () (start . (block ([{}; {Var v}; {Var v; Var w}; {Var w; Var x}; {Var w; Var x};
      {Var w; Var x; Var y}; {Var w; Var x; Var y}; {Var w; Var y; Var z};
      {Var y; Var z}; {Var t.1; Var z}; {Var t.1; Var z}; {Var t.1; Reg rax}; {
      }; {}])
    (movq (int 1) (var v))
    (movq (int 46) (var w))
    (movq (var v) (var x))
    (addq (int 7) (var x))
    (movq (var x) (var y))
    (addq (int 4) (var y))
    (movq (var x) (var z))
    (addq (var w) (var z))
    (movq (var y) (var t.1))
    (negq (var t.1))
    (movq (var z) (reg rax))
    (addq (var t.1) (reg rax))
    (retq))))
    |}]

let%expect_test "Example 1 after build interference" =
  let module M = Ex1 (UncoverLive (BuildInterference (X86_0_Pretty))) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {|
    Ex1: (program ((conflicts . {Var t.1 -> {Var z; Reg rax}; Var v -> {Var w};
                  Var w -> {Var v; Var x; Var y; Var z}; Var x -> {Var w; Var y};
                  Var y -> {Var w; Var x; Var z};
                  Var z -> {Var t.1; Var w; Var y};
                  Reg r10 -> {Reg r11; Reg r12; Reg r13; Reg r14; Reg r15;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r11 -> {Reg r10; Reg r12; Reg r13; Reg r14; Reg r15;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r12 -> {Reg r10; Reg r11; Reg r13; Reg r14; Reg r15;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r13 -> {Reg r10; Reg r11; Reg r12; Reg r14; Reg r15;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r14 -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r15;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r15 -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg r8 -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                             Reg r15; Reg r9; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                             Reg rsi};
                  Reg r9 -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                             Reg r15; Reg r8; Reg rbx; Reg rcx; Reg rdi; Reg rdx;
                             Reg rsi};
                  Reg rax -> {Var t.1};
                  Reg rbx -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r15; Reg r8; Reg r9; Reg rcx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg rcx -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r15; Reg r8; Reg r9; Reg rbx; Reg rdi; Reg rdx;
                              Reg rsi};
                  Reg rdi -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r15; Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdx;
                              Reg rsi};
                  Reg rdx -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r15; Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi;
                              Reg rsi};
                  Reg rsi -> {Reg r10; Reg r11; Reg r12; Reg r13; Reg r14;
                              Reg r15; Reg r8; Reg r9; Reg rbx; Reg rcx; Reg rdi;
                              Reg rdx}})) (start . (block ([{}; {Var v}; {Var v; Var w}; {Var w; Var x}; {Var w; Var x};
      {Var w; Var x; Var y}; {Var w; Var x; Var y}; {Var w; Var y; Var z};
      {Var y; Var z}; {Var t.1; Var z}; {Var t.1; Var z}; {Var t.1; Reg rax}; {
      }; {}])
    (movq (int 1) (var v))
    (movq (int 46) (var w))
    (movq (var v) (var x))
    (addq (int 7) (var x))
    (movq (var x) (var y))
    (addq (int 4) (var y))
    (movq (var x) (var z))
    (addq (var w) (var z))
    (movq (var y) (var t.1))
    (negq (var t.1))
    (movq (var z) (reg rax))
    (addq (var t.1) (reg rax))
    (retq))))
    |}]

let%expect_test "Example 1 after allocate registers" =
  let open Chapter2_passes in
  let module M =
    Ex1 (UncoverLive (BuildInterference (AllocateRegisters (X86_0_Printer)))) in
  Format.printf "%s\n" M.res;
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

      movq $1, %rbx
      movq $46, %rdx
      movq %rbx, %rbx
      addq $7, %rbx
      movq %rbx, %rcx
      addq $4, %rcx
      movq %rbx, %rbx
      addq %rdx, %rbx
      movq %rcx, %rcx
      negq %rcx
      movq %rbx, %rax
      addq %rcx, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      retq
    |}]

let%expect_test "Example 1 after allocate registers with move biasing" =
  let open Chapter2_passes in
  let module M =
    Ex1
      (UncoverLive
         (BuildInterference (BuildMoves (AllocateRegisters (X86_0_Printer))))) in
  Format.printf "%s\n" M.res;
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

      movq $1, %rbx
      movq $46, %rdx
      movq %rbx, %rbx
      addq $7, %rbx
      movq %rbx, %rcx
      addq $4, %rcx
      movq %rbx, %rbx
      addq %rdx, %rbx
      movq %rcx, %rcx
      negq %rcx
      movq %rbx, %rax
      addq %rcx, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      retq
    |}]

let%expect_test
    "Example 1 after allocate registers with move biasing and patching \
     instructions" =
  let open Chapter2_passes in
  let module M =
    Ex1
      (UncoverLive
         (BuildInterference
            (BuildMoves (AllocateRegisters (PatchInstructions (X86_0_Printer)))))) in
  Format.printf "%s\n" M.res;
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

      movq $1, %rbx
      movq $46, %rdx
      addq $7, %rbx
      movq %rbx, %rcx
      addq $4, %rcx
      addq %rdx, %rbx
      negq %rcx
      movq %rbx, %rax
      addq %rcx, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      retq
    |}]

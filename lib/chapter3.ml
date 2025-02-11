open Chapter2_definitions

module UncoverLivePass (X86 : X86_0) = struct
  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)
  module X_arg = struct
    type 'a from = 'a X86.arg
    type 'a term = string option * 'a from
    let fwd a = (None, a)
    let bwd (_, a) = a
  end

  module X_instr = struct
    type 'a from = 'a X86.instr
    type ann = {
      vars_write : StringSet.t;
      vars_read : StringSet.t;
    }
    type 'a term = ann * 'a from
    let fwd a =
      ({ vars_write = StringSet.empty; vars_read = StringSet.empty }, a)
    let bwd (_, a) = a
  end

  module X_block = Chapter1.MkId (struct
    type 'a t = 'a X86.block
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)

  module IDelta = struct
    let var v = (Some v, X86.var v)

    let add_read (v, _) (ann, r) =
      let ann =
        match v with
        | Some v ->
          X_instr.{ ann with vars_read = StringSet.add v ann.vars_read }
        | None -> ann
      in
      (ann, r)
    let add_write (v, _) (ann, r) =
      let ann =
        match v with
        | Some v ->
          X_instr.{ ann with vars_write = StringSet.add v ann.vars_write }
        | None -> ann
      in
      (ann, r)

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
    let callq l = X_instr.fwd @@ X86.callq l
    let pushq a = one_arg_instr X86.pushq a
    let popq a = one_arg_instr X86.pushq a

    let block ?live_after:_ instrs =
      let anns, instrs = List.split instrs in
      let anns = Array.of_list anns in
      let live_after = Array.make (Array.length anns) StringSet.empty in
      for i = Array.length anns - 2 downto 0 do
        live_after.(i) <-
          StringSet.(
            union
              (diff live_after.(i + 1) anns.(i + 1).X_instr.vars_write)
              anns.(i + 1).vars_read)
      done;
      X86.block ~live_after instrs
  end
end

module UncoverLive (F : X86_0) : X86_0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
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
    type 'a term = (StringSet.t -> acc_graph) * 'a from
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
    let arg_of_reg reg = Arg.Reg (Hashtbl.hash reg)
    let reg r = (Some (arg_of_reg r), X86.reg r)
    let var v = (Some (Arg.Var v), X86.var v)

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

    let arith dest live_after graph =
      StringSet.fold
        (fun v graph -> add_interference dest (Arg.Var v) graph)
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
          StringSet.fold
            (fun v graph ->
              let v = Arg.Var v in
              if Some v = src || v = dest then
                graph
              else
                add_interference dest v graph)
            live_after graph
        in
        (acc_graph, X86.movq a b)
      | None -> X_instr.fwd @@ X86.movq a b

    let callq label =
      let acc_graph live_after graph =
        let edges =
          let ( let* ) a f = List.concat_map f a in
          let* r = caller_saves in
          let* v = StringSet.to_list live_after in
          [ (arg_of_reg r, Arg.Var v) ]
        in
        List.fold_left
          (fun graph (k, v) -> add_interference k v graph)
          graph edges
      in
      (acc_graph, X86.callq label)

    let block ?live_after instrs =
      let live_after' = Option.value ~default:[||] live_after in
      let acc_block graph =
        List.fold_left
          (fun graph (live_after, (f, _)) -> f live_after graph)
          graph
          (List.combine (Array.to_list live_after') instrs)
      in
      let instrs = List.map (fun (_, instr) -> instr) instrs in
      (acc_block, X86.block ?live_after instrs)

    let program ?stack_size ?conflicts:_ ?moves blocks =
      let interference_graph =
        List.fold_left (fun graph (_, (f, _)) -> f graph) ArgMap.empty blocks
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

module GraphUtils = struct
  module IntSet = Set.Make (Int)
  module ArgTable = Hashtbl.Make (Arg)
  let neighbors graph v =
    Option.value ~default:ArgSet.empty (ArgMap.find_opt v graph)
  let saturation color graph v =
    let go w acc =
      try IntSet.add (ArgTable.find color w) acc with Not_found -> acc
    in
    ArgSet.fold go (neighbors graph v) IntSet.empty

  let color_graph graph vars =
    let color_table = ArgTable.create (List.length vars) in
    let module Elem = struct
      type t = Arg.t
      let compare a b =
        let a_saturation = IntSet.cardinal (saturation color_table graph a) in
        let b_saturation = IntSet.cardinal (saturation color_table graph b) in
        if a_saturation = b_saturation then
          Arg.compare a b
        else
          Int.compare a_saturation b_saturation
    end in
    let module Worklist = Set.Make (Elem) in
    let rec go worklist =
      if not (Worklist.is_empty worklist) then begin
        let u = Worklist.max_elt worklist in
        let adjacent_colors = saturation color_table graph u in
        let rec find_color color =
          if IntSet.mem color adjacent_colors then
            find_color (color + 1)
          else
            color
        in
        let c = find_color 0 in
        ArgTable.add color_table u c;
        go (Worklist.remove u worklist)
      end
    in
    go (Worklist.of_list vars);
    ArgMap.of_seq @@ ArgTable.to_seq color_table
end

module AllocateRegisters (X86 : X86_0) : X86_0 with type 'a obs = 'a X86.obs =
struct
  type 'a reg = 'a X86.reg

  type color_result =
    | Stack_slot of int
    | Int_register of int reg

  let arg_of_color_result = function
    | Stack_slot slot -> X86.(deref rbp slot)
    | Int_register reg -> X86.reg reg

  type 'a arg = (string -> color_result) -> 'a X86.arg
  type 'a instr = (string -> color_result) -> 'a X86.instr
  type 'a block = (string -> color_result) -> 'a X86.block
  type 'a program = 'a X86.program
  type label = X86.label

  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a reg
  end)

  include X86_0_Reg_T (X_reg) (X86)

  let reg v _ = X86.reg v
  let var v f = arg_of_color_result (f v)
  let int v _ = X86.int v
  let deref r i _ = X86.deref r i

  let addq a b f = X86.addq (a f) (b f)
  let subq a b f = X86.subq (a f) (b f)
  let movq a b f = X86.movq (a f) (b f)
  let negq a f = X86.negq (a f)
  let pushq a f = X86.pushq (a f)
  let popq a f = X86.popq (a f)
  let retq _ = X86.retq
  let callq l _ = X86.callq l

  let block ?live_after instrs f =
    X86.block ?live_after @@ List.map (fun i -> i f) instrs

  let program ?stack_size:_ ?(conflicts = ArgMap.empty) ?moves:_ blocks =
    let stack_size = ref 0 in
    let color_slot_table : (int, int) Hashtbl.t = Hashtbl.create 100 in
    (* Remove rax from the interference graph *)
    let rax = Arg.Reg (Hashtbl.hash X86.rax) in
    let conflicts =
      conflicts |> ArgMap.remove rax |> ArgMap.map (ArgSet.remove rax)
    in
    let vars = conflicts |> ArgMap.bindings |> List.map (fun (key, _) -> key) in
    let colors = GraphUtils.color_graph conflicts vars in
    let get_arg (v : string) : color_result =
      let color =
        match ArgMap.find_opt (Arg.Var v) colors with
        | Some color -> color
        | None -> failwith @@ "Invalid variable: " ^ v ^ " not in colors map"
      in
      match color with
      | 0 -> Int_register X86.rbx
      | 1 -> Int_register X86.rcx
      | 2 -> Int_register X86.rdx
      | 3 -> Int_register X86.rsi
      | 4 -> Int_register X86.rdi
      | 5 -> Int_register X86.r8
      | 6 -> Int_register X86.r9
      | 7 -> Int_register X86.r10
      | 8 -> Int_register X86.r11
      | 9 -> Int_register X86.r12
      | 10 -> Int_register X86.r13
      | 11 -> Int_register X86.r14
      | 12 -> Int_register X86.r15
      | c ->
        let slot =
          try Hashtbl.find color_slot_table c
          with Not_found ->
            stack_size := !stack_size + 8;
            let slot = - !stack_size in
            Hashtbl.add color_slot_table c slot;
            slot
        in
        Stack_slot slot
    in
    let blocks = List.map (fun (l, b) -> (l, b get_arg)) blocks in
    X86.program ~stack_size:!stack_size ~conflicts blocks

  type 'a obs = 'a X86.obs
  let observe = X86.observe
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

let run () =
  let module M = Ex1 (UncoverLive (X86_0_Pretty)) in
  Format.printf "Ex1 after uncover live: %s\n" M.res;
  let module M = Ex1 (UncoverLive (BuildInterference (X86_0_Pretty))) in
  Format.printf "Ex1 after build interference: %s\n" M.res;
  let module M =
    Ex1 (UncoverLive (BuildInterference (AllocateRegisters (X86_0_Pretty)))) in
  Format.printf "Ex1 after allocate registers: %s\n" M.res

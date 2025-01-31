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

    let block _ instrs =
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
      let info = X86.block_info ~live_after () in
      X86.block info instrs
  end
end

module UncoverLive (F : X86_0) : X86_0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module Ex1 (F : X86_0) = struct
  open F

  let res =
    observe
    @@ program (program_info ())
         [
           ( "start",
             block (block_info ())
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
  Format.printf "Ex1: %s\n" M.res

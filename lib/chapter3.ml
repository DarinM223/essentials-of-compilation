open Chapter2_definitions

module UncoverLivePass (X86 : X86_0) = struct
  module X_reg = Chapter1.MkId (struct
    type 'a t = 'a X86.reg
  end)
  module X_arg = Chapter1.MkId (struct
    type 'a t = 'a X86.arg
  end)

  module X_instr = struct
    type 'a from = 'a X86.instr
    type ann = {
      vars_written : StringSet.t;
      vars_read : StringSet.t;
    }
    type 'a term = ann * 'a from
    let fwd a =
      ({ vars_written = StringSet.empty; vars_read = StringSet.empty }, a)
    let bwd (_, a) = a
  end

  module X_block = Chapter1.MkId (struct
    type 'a t = 'a X86.block
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a X86.program
  end)

  module IDelta = struct end
end

module UncoverLive (F : X86_0) : X86_0 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include X86_0_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

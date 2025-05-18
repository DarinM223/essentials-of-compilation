module R4_Types = struct
  include Chapter5.R3_Types

  type typ =
    [ Chapter5.R3_Types.typ
    | `Fn of typ list * typ
    ]
  [@@deriving show]
end

module type R4_Shrink = sig
  include Chapter5.R3_Shrink
  val ( $ ) : ('tup -> 'a) exp -> 'tup ExpHList.hlist -> 'a exp
  module VarHList : Chapter5.HLIST with type 'a el = 'a var
  type 'a def

  val define :
    ('tup -> 'a) var -> 'tup VarHList.hlist -> 'a exp -> 'b def -> 'b def
  val body : 'a exp -> 'a def
  val endd : unit -> 'a def

  val program : 'a def -> 'a program
end

module type R4 = sig
  include Chapter5.R3
  include R4_Shrink with type 'a exp := 'a exp
end

module type R4_Collect = sig
  include Chapter5.R3_Collect
  include R4 with type 'a exp := 'a exp
end

module type R4_Let = sig
  include Chapter2_definitions.R1_Let
  include R4 with type 'a exp := 'a exp and type 'a var := 'a var
  module UnitHList : Chapter5.HLIST with type 'a el = unit

  type ('r, 'a) wrapped = {
    realized : 'r UnitHList.hlist;
    fn : 'r VarHList.hlist -> 'a exp;
  }

  val ( @> ) :
    'r UnitHList.hlist -> ('r VarHList.hlist -> 'a exp) -> ('r, 'a) wrapped
  val ( let@ ) : ('tup, 'a) wrapped -> (('tup -> 'a) var -> 'b def) -> 'b def
end

module R3_of_R4_Shrink (F : R4_Shrink) = struct
  include F
  let program e = F.program (body e)
end

module R3_of_R4 (F : R4) = struct
  include F
  let program e = F.program (body e)
end

module R3_of_R4_Collect (F : R4_Collect) = struct
  include F
  let program e = F.program (body e)
end

module R4_Shrink_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R4_Shrink
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter5.R3_Shrink_T (X_exp) (X_program) (R3_of_R4_Shrink (F))
  type 'a def = 'a X_def.term
  module VarHList = F.VarHList
  open X_exp

  let ( $ ) f es =
    let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
      | ExpHList.(x :: xs) -> F.ExpHList.(bwd x :: go xs)
      | ExpHList.[] -> F.ExpHList.[]
    in
    fwd @@ F.( $ ) (bwd f) (go es)
  let define v vs body rest =
    X_def.fwd @@ F.define v vs (bwd body) (X_def.bwd rest)
  let body e = X_def.fwd @@ F.body (bwd e)
  let endd () = X_def.fwd (F.endd ())
  let program def = X_program.fwd (F.program (X_def.bwd def))
end

module R4_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R4
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include R4_Shrink_T (X_exp) (X_def) (X_program) (F)
  include Chapter4.R2_T (X_exp) (X_program) (R3_of_R4 (F))
end

module R4_Collect_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R4_Collect
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include R4_Shrink_T (X_exp) (X_def) (X_program) (F)
  include Chapter5.R3_Collect_T (X_exp) (X_program) (R3_of_R4_Collect (F))
end

module BuildFn
    (M : sig
      type r
    end)
    (F : R4) : sig
  val result : M.r F.VarHList.hlist
end = struct
  let result = failwith ""
end

module TransformLetPass (F : R4) = struct
  include Chapter2_definitions.TransformLetPass (R3_of_R4 (F))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a F.def
  end)
  module IDelta = struct
    include IDelta
    module UnitHList = Chapter5.HList (struct
      type 'a t = unit
    end)
    type ('r, 'a) wrapped = {
      realized : 'r UnitHList.hlist;
      fn : 'r F.VarHList.hlist -> 'a F.exp;
    }
    let ( @> ) realized fn = { realized; fn }

    let ( let@ ) : type tup.
        (tup, 'a) wrapped -> ((tup -> 'a) F.var -> 'b F.def) -> 'b F.def =
     fun f g ->
      let var = F.fresh () in
      let rec go : type r. r UnitHList.hlist -> r F.VarHList.hlist = function
        | UnitHList.(_ :: xs) -> F.VarHList.(F.fresh () :: go xs)
        | UnitHList.[] -> F.VarHList.[]
      in
      let params = go f.realized in
      let body = f.fn params in
      let rest = g var in
      F.define var params body rest

    let program def = X_program.fwd (F.program (X_def.bwd def))
  end
end

module TransformLet (F : R4) :
  R4_Let
    with type 'a exp = 'a F.exp
     and type 'a program = 'a F.program
     and type 'a def = 'a F.def
     and type 'a obs = 'a F.obs = struct
  module M = TransformLetPass (F)
  include R4_T (M.X_exp) (M.X_def) (M.X_program) (F)
  include M.IDelta
end

module Ex1 (F : R4_Let) = struct
  open F

  let res =
    program
    @@
    let@ map_vec =
      [ (); () ] @> fun [ f; v ] ->
      vector
        [
          var f $ [ vector_ref (var v) Here ];
          var f $ [ vector_ref (var v) (Next Here) ];
        ]
    in
    let@ add1 = [ () ] @> fun [ x ] -> var x + int 1 in
    body
    @@ vector_ref
         (var map_vec $ [ var add1; vector [ int 0; int 41 ] ])
         (Next Here)
end

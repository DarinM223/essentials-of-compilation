module StringMap = Map.Make (String)
module StringHashtbl = Hashtbl.Make (String)
module ArgSet = Chapter2_definitions.ArgSet
module ArgMap = Chapter2_definitions.ArgMap

module type LIMIT = sig
  module HList : Chapter5.HLIST
  open HList

  type _ limit =
    | LX :
        ('a * ('b * ('c * ('d * ('e * (('f * 'g) * unit)))))) hlist
        * ('f * 'g) hlist
        -> ('a * ('b * ('c * ('d * ('e * ('f * 'g)))))) limit
    | L : 'r hlist -> 'r limit

  type convert = { f : 'a. 'a hlist -> 'a el }
  val fwd : convert -> 't hlist -> 't limit
  val bwd : 't limit -> 't hlist
end

module LimitFn (HList : Chapter5.HLIST) = struct
  module HList = HList
  open HList

  type _ limit =
    | LX :
        ('a * ('b * ('c * ('d * ('e * (('f * 'g) * unit)))))) hlist
        * ('f * 'g) hlist
        -> ('a * ('b * ('c * ('d * ('e * ('f * 'g)))))) limit
    | L : 'r hlist -> 'r limit

  type convert = { f : 'a. 'a hlist -> 'a el }

  let fwd (type t) conv (xs : t hlist) : t limit =
    match xs with
    | [ _; _; _; _; _; _ ] -> L xs
    | a :: b :: c :: d :: e :: f :: g ->
      LX ([ a; b; c; d; e; conv.f (f :: g) ], f :: g)
    | _ -> L xs

  let bwd : type t. t limit -> t hlist = function
    | LX ([ a; b; c; d; e; _ ], f :: g) -> a :: b :: c :: d :: e :: f :: g
    | L l -> l
end

module R3_Types = Chapter5.R3_Types

module rec TyHList : (Chapter5.HLIST with type 'a el = 'a Ty.ty) =
Chapter5.HListFn (struct
  type 'a t = 'a Ty.ty
end)

and Ty : sig
  module TyLimitList : LIMIT with type 'a HList.el = 'a TyHList.el
  type 'a ty =
    | Int : int ty
    | Bool : bool ty
    | Void : unit ty
    | Vector : 'tup TyHList.hlist -> 'tup ty
    | Fn : 'tup TyLimitList.limit * 'a ty -> ('tup -> 'a) ty
  val to_hlist : 'r TyLimitList.HList.hlist -> 'r TyHList.hlist
  val ( --> ) : 'a TyHList.hlist -> 'b ty -> ('a -> 'b) ty
  val reflect : 'a ty -> R3_Types.typ
end = struct
  module TyLimitList = LimitFn (TyHList)

  let rec to_hlist : type r. r TyLimitList.HList.hlist -> r TyHList.hlist =
    function
    | v :: vs -> v :: to_hlist vs
    | [] -> []

  type _ ty =
    | Int : int ty
    | Bool : bool ty
    | Void : unit ty
    | Vector : 'tup TyHList.hlist -> 'tup ty
    | Fn : 'tup TyLimitList.limit * 'a ty -> ('tup -> 'a) ty

  let ( --> ) a b = Fn (TyLimitList.fwd { f = (fun ts -> Vector ts) } a, b)

  let[@tail_mod_cons] rec list_of_types : type r.
      r TyHList.hlist -> R3_Types.typ list = function
    | x :: xs -> reflect x :: list_of_types xs
    | [] -> []

  and reflect : type a. a ty -> R3_Types.typ = function
    | Int -> Int
    | Bool -> Bool
    | Void -> Void
    | Vector tys -> Vector (list_of_types tys)
    | Fn (params, ret) ->
      let params =
        match params with
        | LX (l, _) -> list_of_types l
        | L l -> list_of_types l
      in
      Fn (params, reflect ret)
end

module type R4_Shrink = sig
  include Chapter5.R3_Shrink
  module ExpLimitList : LIMIT with module HList = ExpHList
  module VarHList : Chapter5.HLIST with type 'a el = 'a var
  module VarLimitList : LIMIT with module HList = VarHList
  type 'a def

  val app : ('tup -> 'a) exp -> 'tup ExpLimitList.limit -> 'a exp
  val define :
    ('tup -> 'a) Ty.ty ->
    ('tup -> 'a) var ->
    'tup VarLimitList.limit ->
    'a exp ->
    'b def ->
    'b def
  val body : 'a Ty.ty -> 'a exp -> 'a def
  val endd : unit -> 'a def

  val program : 'a def -> 'a program
end

module type R4 = sig
  include Chapter5.R3
  include R4_Shrink with type 'a exp := 'a exp
end

module type F1 = sig
  include R4_Shrink
  val fun_ref : string -> 'a exp
end

module type F1_Collect = sig
  include Chapter5.R3_Collect
  include F1 with type 'a exp := 'a exp
end

module type FN_HLIST = sig
  type ('a, 'b) el
  type _ hlist =
    | [] : unit hlist
    | ( :: ) : ('a, 'b) el * 'c hlist -> (('a -> 'b) * 'c) hlist
end
module FnHListFn (E : sig
  type ('a, 'b) t
end) : FN_HLIST with type ('a, 'b) el = ('a, 'b) E.t = struct
  type ('a, 'b) el = ('a, 'b) E.t
  type _ hlist =
    | [] : unit hlist
    | ( :: ) : ('a, 'b) el * 'c hlist -> (('a -> 'b) * 'c) hlist
end

module type R4_Let = sig
  include Chapter2_definitions.R1_Let
  include R4 with type 'a exp := 'a exp and type 'a var := 'a var
  module UnitHList : Chapter5.HLIST with type 'a el = unit

  module Wrapped : sig
    type ('r, 'a) t = {
      ty : ('r -> 'a) Ty.ty;
      fn : 'r VarHList.hlist -> 'a exp;
    }
  end
  module FnHList : FN_HLIST with type ('a, 'b) el = ('a, 'b) Wrapped.t
  module Wrapped2 : sig
    type ('r, 'a) t = {
      realized : 'r UnitHList.hlist;
      fn : 'r VarHList.hlist -> 'r FnHList.hlist;
    }
  end

  val ( $ ) : ('tup -> 'a) exp -> 'tup ExpHList.hlist -> 'a exp
  val ( @> ) :
    ('r -> 'a) Ty.ty -> ('r VarHList.hlist -> 'a exp) -> ('r, 'a) Wrapped.t
  val ( let@ ) : ('tup, 'a) Wrapped.t -> (('tup -> 'a) var -> 'b def) -> 'b def
  val ( @@> ) :
    'r UnitHList.hlist ->
    ('r VarHList.hlist -> 'r FnHList.hlist) ->
    ('r, 'a) Wrapped2.t
  val ( let@@ ) :
    ('tup, 'a) Wrapped2.t -> ('tup VarHList.hlist -> 'b def) -> 'b def
end

module R3_of_R4_Shrink (F : R4_Shrink) = struct
  include F
  let program _ = failwith "Please handle program"
end

module R3_of_R4 (F : R4) = struct
  include F
  let program _ = failwith "Please handle program"
end

module R3_of_F1_Collect (F : F1_Collect) = struct
  include F
  let program _ = failwith "Please handle program"
end

module R4_Shrink_R_T (R : Chapter1.Reader) (F : R4_Shrink) = struct
  include Chapter5.R3_Shrink_R_T (R) (R3_of_R4_Shrink (F))
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = F.VarHList
  module VarLimitList = F.VarLimitList
  type 'a def = R.t -> 'a F.def
  let rec convert_hlist : type t. R.t -> t ExpHList.hlist -> t F.ExpHList.hlist
      =
   fun r -> function
    | x :: xs ->
      let x = x r in
      x :: convert_hlist r xs
    | [] -> []
  let convert_hlist_limit : type t.
      R.t -> t ExpLimitList.limit -> t F.ExpLimitList.limit =
   fun r -> function
    | LX (l, l') -> LX (convert_hlist r l, convert_hlist r l')
    | L l -> L (convert_hlist r l)

  let app e es r =
    let e = e r in
    let es = convert_hlist_limit r es in
    F.app e es

  let define ty v vs e rest r =
    let e = e r in
    let rest = rest r in
    F.define ty v vs e rest

  let body ty e r = F.body ty (e r)
  let endd () _ = F.endd ()

  let program def () =
    let init = R.init () in
    F.program (def init)
end

module R4_R_T (R : Chapter1.Reader) (F : R4) = struct
  include Chapter4.R2_R_T (R) (R3_of_R4 (F))
  include R4_Shrink_R_T (R) (F)
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
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = F.VarHList
  module VarLimitList = F.VarLimitList
  open X_exp
  let rec convert_hlist : type t. t ExpHList.hlist -> t F.ExpHList.hlist =
    function
    | x :: xs ->
      let x = bwd x in
      x :: convert_hlist xs
    | [] -> []
  let convert_hlist_limit : type r.
      r ExpLimitList.limit -> r F.ExpLimitList.limit = function
    | LX (l, l') -> LX (convert_hlist l, convert_hlist l')
    | L l -> L (convert_hlist l)

  let app f es = fwd @@ F.app (bwd f) (convert_hlist_limit es)
  let define ty v vs body rest =
    X_def.fwd @@ F.define ty v vs (bwd body) (X_def.bwd rest)
  let body ty e = X_def.fwd @@ F.body ty (bwd e)
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

module F1_R_T (R : Chapter1.Reader) (F : F1) = struct
  include R4_Shrink_R_T (R) (F)
  let fun_ref label _ = F.fun_ref label
end

module F1_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      F1
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include R4_Shrink_T (X_exp) (X_def) (X_program) (F)
  let fun_ref label = X_exp.fwd @@ F.fun_ref label
end

module F1_Collect_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      F1_Collect
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter5.R3_Collect_T (X_exp) (X_program) (R3_of_F1_Collect (F))
  include F1_T (X_exp) (X_def) (X_program) (F)
end

module type C3 = sig
  include Chapter5.C2
  module ArgHList : Chapter5.HLIST with type 'a el = 'a arg
  module ArgLimitList : LIMIT with module HList = ArgHList
  val fun_ref : string -> 'a exp
  val call : ('tup -> 'a) arg -> 'tup ArgLimitList.limit -> 'a exp
  val tailcall : ('tup -> 'a) arg -> 'tup ArgLimitList.limit -> 'a tail
  type 'a def
  val define :
    ?locals:(var * R3_Types.typ) list ->
    label ->
    var list ->
    (label * unit tail) list ->
    unit def
  val program : unit def list -> unit program
end

module C2_of_C3 (F : C3) = struct
  include F
  let program ?locals blocks = F.program [ F.define ?locals "main" [] blocks ]
end

module C3_R_T (R : Chapter1.Reader) (F : C3) = struct
  include Chapter5.C2_R_T (R) (C2_of_C3 (F))
  type 'a def = unit -> 'a F.def
  module ArgHList = Chapter5.HListFn (struct
    type 'a t = 'a arg
  end)
  module ArgLimitList = LimitFn (ArgHList)
  let rec pass_args : type r. 'a -> r ArgHList.hlist -> r F.ArgHList.hlist =
   fun r -> function
    | x :: xs ->
      let x = x r in
      x :: pass_args r xs
    | [] -> []
  let pass_args_limit : type r.
      'a -> r ArgLimitList.limit -> r F.ArgLimitList.limit =
   fun r -> function
    | LX (l, l') -> LX (pass_args r l, pass_args r l')
    | L l -> L (pass_args r l)
  let fun_ref label _ = F.fun_ref label
  let call f ps r =
    let f = f r in
    let ps = pass_args_limit r ps in
    F.call f ps
  let tailcall f ps r =
    let f = f r in
    let ps = pass_args_limit r ps in
    F.tailcall f ps
  let define ?locals v vs body () =
    let init = R.init () in
    let body = List.map (fun (l, t) -> (l, t init)) body in
    F.define ?locals v vs body
  let program defs () =
    let defs = List.map (fun def -> def ()) defs in
    F.program defs
end

module type X86_3 = sig
  include Chapter5.X86_2
  val fun_ref : string -> 'a arg
  val indirect_callq : 'a arg -> unit instr
  val tail_jmp : 'a arg -> unit instr
  val leaq : 'a arg -> 'b arg -> unit instr
  type 'a def
  val define :
    ?locals:R3_Types.typ StringMap.t ->
    ?stack_size:int ->
    ?root_stack_size:int ->
    ?conflicts:ArgSet.t ArgMap.t ->
    ?moves:ArgSet.t ArgMap.t ->
    label ->
    (label * unit block) list ->
    unit def
  val program : unit def list -> unit program
end

module X86_2_of_X86_3 (F : X86_3) = struct
  include F
  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves blocks =
    F.program
      [
        F.define ?locals ?stack_size ?root_stack_size ?conflicts ?moves "main"
          blocks;
      ]
end

module X86_3_R_T (R : Chapter1.Reader) (F : X86_3) :
  X86_3
    with type 'a reg = R.t -> 'a F.reg
     and type 'a arg = R.t -> 'a F.arg
     and type 'a instr = R.t -> 'a F.instr
     and type 'a block = R.t -> 'a F.block
     and type 'a def = unit -> 'a F.def
     and type 'a program = unit -> 'a F.program
     and type label = F.label
     and type 'a obs = 'a F.obs = struct
  include Chapter5.X86_2_R_T (R) (X86_2_of_X86_3 (F))
  type 'a def = unit -> 'a F.def
  let fun_ref label _ = F.fun_ref label
  let indirect_callq arg r = F.indirect_callq (arg r)
  let tail_jmp arg r = F.tail_jmp (arg r)
  let leaq a1 a2 r =
    let a1 = a1 r in
    let a2 = a2 r in
    F.leaq a1 a2
  let define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v body () =
    let init = R.init () in
    F.define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v
      (List.map (fun (l, b) -> (l, b init)) body)
  let program defs () = F.program @@ List.map (fun def -> def ()) defs
end

module X86_3_T
    (X_reg : Chapter1.TRANS)
    (X_arg : Chapter1.TRANS)
    (X_instr : Chapter1.TRANS)
    (X_block : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      X86_3
        with type 'a reg = 'a X_reg.from
         and type 'a arg = 'a X_arg.from
         and type 'a instr = 'a X_instr.from
         and type 'a block = 'a X_block.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include
    Chapter5.X86_2_T (X_reg) (X_arg) (X_instr) (X_block) (X_program)
      (X86_2_of_X86_3 (F))
  type 'a def = 'a X_def.term
  let fun_ref label = X_arg.fwd (F.fun_ref label)
  let indirect_callq arg = X_instr.fwd (F.indirect_callq (X_arg.bwd arg))
  let tail_jmp arg = X_instr.fwd (F.tail_jmp (X_arg.bwd arg))
  let leaq a1 a2 = X_instr.fwd (F.leaq (X_arg.bwd a1) (X_arg.bwd a2))
  let define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v blocks =
    X_def.fwd
    @@ F.define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v
    @@ List.map (fun (l, b) -> (l, X_block.bwd b)) blocks
  let program defs = X_program.fwd @@ F.program @@ List.map X_def.bwd defs
end

module StringSet = Chapter2_definitions.StringSet
module TransformLetPass (F : R4) = struct
  include Chapter2_definitions.TransformLetPass (R3_of_R4 (F))
  module R = struct
    type t = {
      mutable to_exp : 'a. string -> 'a F.exp;
      mutable free_vars : StringSet.t;
      mutable lifted_defs : 'a. 'a F.def -> 'a F.def;
    }
    let init () =
      {
        to_exp = (fun v -> F.var (F.var_of_string v));
        free_vars = StringSet.empty;
        lifted_defs = (fun def -> def);
      }
    let clone { to_exp; free_vars; lifted_defs } =
      { to_exp; free_vars; lifted_defs }
  end
  module IDelta (F' : R4 with type 'a exp = R.t -> 'a F.exp) = struct
    include IDelta
    open F'
    module UnitHList = Chapter5.HListFn (struct
      type 'a t = unit
    end)
    module Wrapped = struct
      type ('r, 'a) t = {
        ty : ('r -> 'a) Ty.ty;
        fn : 'r F.VarHList.hlist -> 'a F'.exp;
      }
    end
    module FnHList = FnHListFn (struct
      type ('a, 'b) t = ('a, 'b) Wrapped.t
    end)
    module Wrapped2 = struct
      type ('r, 'a) t = {
        realized : 'r UnitHList.hlist;
        fn : 'r F.VarHList.hlist -> 'r FnHList.hlist;
      }
    end
    let ( @> ) ty fn = Wrapped.{ ty; fn }
    let ( @@> ) realized fn = Wrapped2.{ realized; fn }

    let rec convert_exps : type r. R.t -> r ExpHList.hlist -> r F.ExpHList.hlist
        =
     fun r -> function
      | x :: xs ->
        let x = x r in
        x :: convert_exps r xs
      | [] -> []

    let rec vars_of_tys : type r.
        r Ty.TyLimitList.HList.hlist -> r F.VarHList.hlist = function
      | _ :: xs ->
        let v = F.fresh () in
        v :: vars_of_tys xs
      | [] -> []

    let rec vars_of_units : type r. r UnitHList.hlist -> r F.VarHList.hlist =
      function
      | _ :: xs ->
        let v = F.fresh () in
        v :: vars_of_units xs
      | [] -> []

    let ( $ ) f es r =
      let f = f r in
      let es =
        F.ExpLimitList.fwd { f = (fun l -> F.vector l) } (convert_exps r es)
      in
      F.app f es

    let var v r = r.R.to_exp (F.string_of_var v)

    let tuple_handler (r : R.t) : F.VarLimitList.convert =
      let handler l =
        let tuple_var = F.fresh () in
        let rec go : type a tup t.
            t F.VarHList.hlist * (a, tup) Chapter5.ptr -> unit = function
          | x :: xs, ptr ->
            let x = F.string_of_var x in
            let old_handler = r.to_exp in
            r.to_exp <-
              (fun v ->
                if Stdlib.( = ) x v then
                  F.vector_ref (F.var tuple_var) (Obj.magic ptr)
                else
                  old_handler v);
            go (xs, Chapter5.Next ptr)
          | [], _ -> ()
        in
        go (l, Here);
        tuple_var
      in
      { f = handler }

    let let_helper var f g r =
      let (Ty.Fn (params, _) as ty) = f.Wrapped.ty in
      let params = vars_of_tys (Ty.TyLimitList.bwd params) in
      let r' = R.clone r in
      let params' = F.VarLimitList.fwd (tuple_handler r') params in
      let body = f.fn params r' in
      let rest = g var r in
      F.define ty var params' body rest

    let ( let@ ) f g r = let_helper (F.fresh ()) f g r

    let ( let@@ ) f g r =
      let vars = vars_of_units f.Wrapped2.realized in
      let fns = f.fn vars in
      let rest = g vars r in
      let rec go : type r. r FnHList.hlist * r F.VarHList.hlist -> 'a F.def =
        function
        | wrapped :: xs, v :: vs ->
          let_helper v wrapped (fun _ -> fun _ -> go (xs, vs)) r
        | [], [] -> rest
      in
      go (fns, vars)

    let program def () =
      let init = R.init () in
      F.program (def init)
  end
end

module TransformLet (F : R4) : R4_Let with type 'a obs = 'a F.obs = struct
  module M = TransformLetPass (F)
  module R = R4_R_T (M.R) (F)
  include R
  include M.IDelta (R)
end

module ShrinkPass (F : R4_Shrink) = struct
  include Chapter4.ShrinkPass (R3_of_R4_Shrink (F))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a F.def
  end)

  module IDelta = struct
    include IDelta
    let body ty e =
      F.(define Ty.([] --> ty) (var_of_string "main") (L []) e (endd ()))
  end
end
module Shrink (F : R4_Shrink) : R4 with type 'a obs = 'a F.obs = struct
  module M = ShrinkPass (F)
  include R4_Shrink_T (M.X_exp) (M.X_def) (M.X_program) (F)
  include M.IDelta
end

module RevealFunctionsPass (F : F1) = struct
  module R = struct
    type t = unit StringHashtbl.t
    let init () = StringHashtbl.create 100
  end

  module IDelta = struct
    let var v is_function =
      if StringHashtbl.mem is_function (F.string_of_var v) then
        F.fun_ref (F.string_of_var v)
      else
        F.var v
    let define ty v params body rest is_function =
      StringHashtbl.add is_function (F.string_of_var v) ();
      let rest = rest is_function in
      let body = body is_function in
      F.define ty v params body rest
  end
end
module RevealFunctions (F : F1) : R4_Shrink with type 'a obs = 'a F.obs = struct
  module M = RevealFunctionsPass (F)
  include R4_Shrink_R_T (M.R) (F)
  include M.IDelta
end

module R4_Annotate_Types (F : R4_Shrink) = struct
  include Chapter5.R3_Annotate_Types (R3_of_R4_Shrink (F))
  type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = F.VarHList
  module VarLimitList = F.VarLimitList

  let rec convert_exps : type r.
      R3_Types.typ StringHashtbl.t -> r ExpHList.hlist -> r F.ExpHList.hlist =
   fun m -> function
    | x :: xs ->
      let x = snd (x m) in
      x :: convert_exps m xs
    | [] -> []
  let convert_exps_limit : type r.
      R3_Types.typ StringHashtbl.t ->
      r ExpLimitList.limit ->
      r F.ExpLimitList.limit =
   fun m -> function
    | LX (l, l') -> LX (convert_exps m l, convert_exps m l')
    | L l -> L (convert_exps m l)

  let app e es m =
    let ety, e = e m in
    let rty =
      match ety with
      | R3_Types.Fn (_, ret) -> ret
      | _ -> failwith "Applying expression that isn't a function type"
    in
    let es = convert_exps_limit m es in
    (rty, F.has_type (F.app e es) rty)

  let rec add_param_types : type r.
      'a -> r VarHList.hlist -> r Ty.TyLimitList.HList.hlist -> unit =
   fun table vars tys ->
    match (vars, tys) with
    | v :: vs, t :: ts ->
      StringHashtbl.add table (F.string_of_var v) (Ty.reflect t);
      add_param_types table vs ts
    | [], [] -> ()
  let add_param_types_limit (type r) table (vars : r VarLimitList.limit)
      (tys : r Ty.TyLimitList.limit) =
    match (vars, tys) with
    | LX (vs, _), LX (ts, _) -> add_param_types table vs ts
    | L vs, L ts -> add_param_types table vs ts
    | _, _ -> failwith "This can never happen"

  let rec remove_param_types : type r.
      'a StringHashtbl.t -> r VarHList.hlist -> unit =
   fun table -> function
    | v :: vs ->
      StringHashtbl.remove table (F.string_of_var v);
      remove_param_types table vs
    | [] -> ()
  let remove_param_types_limit : type r.
      'a StringHashtbl.t -> r VarLimitList.limit -> unit =
   fun table -> function
    | LX (l, _) -> remove_param_types table l
    | L l -> remove_param_types table l

  let define (Ty.Fn (params, _) as ty) v vs body rest m =
    StringHashtbl.add m (F.string_of_var v) (Ty.reflect ty);
    let rest = rest m in
    add_param_types_limit m vs params;
    let _, body = body m in
    remove_param_types_limit m vs;
    F.define ty v vs body rest

  let body ty e m =
    let _, e = e m in
    F.body ty e
  let endd () _ = F.endd ()
  let program def =
    let def = def (StringHashtbl.create 100) in
    F.program def
end
module F1_Annotate_Types (F : F1) :
  F1
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp
     and type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include R4_Annotate_Types (F)
  let fun_ref label m =
    let ty = StringHashtbl.find m label in
    (ty, F.has_type (F.fun_ref label) ty)
end
module F1_Collect_Annotate_Types (F : F1_Collect) :
  F1_Collect
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp
     and type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include Chapter5.R3_Collect_Annotate_Types (R3_of_F1_Collect (F))
  include F1_Annotate_Types (F)
end

module ExposeAllocation (F : F1_Collect) : F1 with type 'a obs = 'a F.obs =
struct
  module M = Chapter5.ExposeAllocationPass (R3_of_F1_Collect (F))
  module F' = F1_Collect_Annotate_Types (F)
  include F'
  include M.IDelta (R3_of_F1_Collect (F'))
end

module RemoveComplexPass (F : F1_Collect) = struct
  include Chapter2_passes.RemoveComplexPass (R3_of_F1_Collect (F))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a F.def
  end)
  open X
  module IDelta (F' : F1_Collect with type 'a exp = 'a X.term) = struct
    let rec convert_exps : type r. r F'.ExpHList.hlist -> r F.ExpHList.hlist =
      function
      | x :: xs -> bwd x :: convert_exps xs
      | [] -> []
    let convert_exps_limit : type r.
        r F'.ExpLimitList.limit -> r F.ExpLimitList.limit = function
      | LX (l, l') -> LX (convert_exps l, convert_exps l')
      | L l -> L (convert_exps l)

    let app e es = (Complex, F.app (bwd e) (convert_exps_limit es))
    let fun_ref label = (Complex, F.fun_ref label)
  end
end
module RemoveComplex (F : F1_Collect) : F1_Collect with type 'a obs = 'a F.obs =
struct
  module M = RemoveComplexPass (F)
  module F' = F1_Collect_T (M.X) (M.X_def) (M.X_program) (F)
  include F'
  include M.IDelta (F')
end

module ExplicateControl (F : F1_Collect) (C3 : C3) () = struct
  include Chapter5.ExplicateControl (R3_of_F1_Collect (F)) (C2_of_C3 (C3)) ()
  module VarHList = F.VarHList
  module VarLimitList = LimitFn (VarHList)
  module ExpLimitList = LimitFn (ExpHList)
  type 'a def = unit -> unit C3.def list

  let rec vars_of_exps : type r. r ExpHList.hlist -> r VarHList.hlist = function
    | _ :: xs ->
      let var = F.fresh () in
      var :: vars_of_exps xs
    | [] -> []
  let vars_of_exps_limit : type r. r ExpLimitList.limit -> r VarLimitList.limit
      = function
    | LX (l, l') -> LX (vars_of_exps l, vars_of_exps l')
    | L l -> L (vars_of_exps l)

  let rec args_of_vars : type r. r VarHList.hlist -> r C3.ArgHList.hlist =
    function
    | x :: xs -> C3.var (lookup (F.string_of_var x)) :: args_of_vars xs
    | [] -> []
  let args_of_vars_limit : type r.
      r VarLimitList.limit -> r C3.ArgLimitList.limit = function
    | LX (l, l') -> LX (args_of_vars l, args_of_vars l')
    | L l -> L (args_of_vars l)

  let app e es m r =
    let& e = e in
    let vs = vars_of_exps_limit es in
    let rec go : type r. r ExpHList.hlist * r VarHList.hlist -> unit C3.tail =
      function
      | e :: es, v :: vs ->
        e ann_id (Assign (F.string_of_var v, fun () -> go (es, vs)))
      | [], [] ->
        let args = args_of_vars_limit vs in
        (match r with
        | Tail -> C3.(tailcall (var (lookup e)) args)
        | Assign (v, body) ->
          C3.(assign v (m.f (call (var (lookup e)) args)) @> body ())
        | Pred _ -> failwith "Call should not be in an if expression")
    in
    let go : type r. r ExpLimitList.limit * r VarLimitList.limit -> unit C3.tail
        = function
      | LX (es, _), LX (vs, _) -> go (es, vs)
      | L es, L vs -> go (es, vs)
      | _ -> failwith "app: ExpLimitList and VarLimitList are different sizes"
    in
    go (es, vs)
  let define ty v vs body rest () =
    Hashtbl.clear block_map;
    let start_body = body ann_id Tail in
    let blocks = List.of_seq @@ Hashtbl.to_seq block_map in
    let start_block = fresh_block "start" in
    let blocks = (start_block, start_body) :: blocks in
    let (Ty.Fn (tys, _)) = ty in
    let rec param_locals : type r.
        r Ty.TyLimitList.HList.hlist * r VarHList.hlist ->
        (string * R3_Types.typ) list = function
      | t :: ts, v :: vs ->
        (F.string_of_var v, Ty.reflect t) :: param_locals (ts, vs)
      | [], [] -> []
    in
    let param_locals : type r.
        r Ty.TyLimitList.limit * r VarLimitList.limit ->
        (string * R3_Types.typ) list = function
      | LX (ts, _), LX (vs, _) -> param_locals (ts, vs)
      | L ts, L vs -> param_locals (ts, vs)
      | _ -> failwith "This cannot happen"
    in
    let locals = param_locals (tys, vs) in
    C3.define ~locals (F.string_of_var v) (List.map fst locals) blocks
    :: rest ()
  let body _ _ () =
    failwith "ExplicateControl: body should have been eliminated"
  let endd () () = []
  let program def () = C3.program (def ())
  let fun_ref label = convert_exp (C3.fun_ref label)
end

module UncoverLocalsPass (F : C3) = struct
  include Chapter5.UncoverLocalsPass (C2_of_C3 (F))
  module IDelta = struct
    include IDelta
    let define ?(locals = []) v vs body () =
      let ((_, table) as init) = R.init () in
      let body = List.map (fun (l, t) -> (l, t init)) body in
      let locals' =
        StringHashtbl.to_seq table |> List.of_seq |> List.sort R.compare
      in
      F.define ~locals:(locals @ locals') v vs body

    let program defs () =
      let defs = List.map (fun def -> def ()) defs in
      F.program defs
  end
end
module UncoverLocals (F : C3) : C3 with type 'a obs = 'a F.obs = struct
  module M = UncoverLocalsPass (F)
  include C3_R_T (M.R) (F)
  include M.IDelta
end

module SelectInstructions (F : C3) (X86 : X86_3) :
  C3 with type 'a obs = unit X86.obs = struct
  include Chapter5.SelectInstructions (C2_of_C3 (F)) (X86_2_of_X86_3 (X86))
  module ArgHList = Chapter5.HListFn (struct
    type 'a t = 'a arg
  end)
  module ArgLimitList = LimitFn (ArgHList)
  type 'a def = unit X86.def

  let call_conv = X86.[| rdi; rsi; rdx; rcx; r8; r9 |]

  let pass_params : type r. r ArgLimitList.limit -> unit X86.instr list =
    function
    | LX ([ a; b; c; d; e; f ], _) ->
      X86.
        [
          movq (snd f) (reg r9);
          movq (snd e) (reg r8);
          movq (snd d) (reg rcx);
          movq (snd c) (reg rdx);
          movq (snd b) (reg rsi);
          movq (snd a) (reg rdi);
        ]
    | L l ->
      let rec go : type r. int -> r ArgHList.hlist -> unit X86.instr list =
       fun i -> function
         | x :: xs ->
           X86.(movq (snd x) (reg call_conv.(i))) :: go (Stdlib.( + ) i 1) xs
         | [] -> []
      in
      go 0 l
  let extract_params vs =
    let rec go i acc = function
      | x :: xs ->
        go (Stdlib.( + ) i 1) (X86.(movq (reg call_conv.(i)) (var x)) :: acc) xs
      | [] -> acc
    in
    go 0 [] vs

  let fun_ref l = function
    | Assign v -> X86.[ leaq (fun_ref l) (var v) ]
    | Return -> X86.[ leaq (fun_ref l) (reg rax) ]
    | If _ -> failwith "(fun-ref) cannot be a condition of if"

  let call (_, fn) ps = function
    | Assign v ->
      X86.[ movq (reg rax) (var v); indirect_callq fn ] @ pass_params ps
    | Return -> X86.indirect_callq fn :: pass_params ps
    | If (t, f) ->
      X86.[ jmp t; jmp_if E f; cmpq (int 0) (reg rax); indirect_callq fn ]
      @ pass_params ps

  let tailcall (_, f) ps _ = X86.tail_jmp f :: pass_params ps

  let define ?(locals = []) v vs body =
    let locals = StringMap.of_list locals in
    let exit_label = fresh_exit_label () in
    let header l =
      if String.starts_with ~prefix:"start" l then extract_params vs else []
    in
    let body =
      List.map
        (fun (l, t) -> (l, X86.block (List.rev (t exit_label @ header l))))
        body
    in
    let exit_block = (exit_label, X86.(block [ retq ])) in
    X86.define ~locals v (exit_block :: body)

  let program = X86.program
end

module UncoverLivePass (X86 : X86_3) = struct
  include Chapter4.UncoverLivePass (Chapter5.X86_1_of_X86_2 (X86_2_of_X86_3 (X86)))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a X86.def
  end)
  module IDelta = struct
    include IDelta

    let indirect_callq arg =
      X_instr.fwd (X86.indirect_callq (X_arg.bwd arg))
      |> add_read arg
      |> List.fold_right (fun r -> add_write (reg r)) caller_saves
    let tail_jmp arg =
      X_instr.fwd @@ X86.tail_jmp @@ X_arg.bwd arg |> add_read arg
    let leaq src dest =
      X_instr.fwd (X86.leaq (X_arg.bwd src) (X_arg.bwd dest))
      |> add_read src |> add_write dest
    let define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v blocks =
      let blocks = program_helper blocks in
      X86.define ?locals ?stack_size ?root_stack_size ?conflicts ?moves v blocks
    let program = X86.program
  end
end
module UncoverLive (F : X86_3) : X86_3 with type 'a obs = 'a F.obs = struct
  module M = UncoverLivePass (F)
  include
    X86_3_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_def) (M.X_program)
      (F)
  include M.IDelta
end

module BuildInterferencePass (X86 : X86_3) = struct
  include Chapter5.BuildInterferencePass (X86_2_of_X86_3 (X86))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a X86.def
  end)
  module IDelta = struct
    include IDelta
    let leaq (_, a) (dest, b) =
      match dest with
      | Some dest -> (arith dest, X86.leaq a b)
      | None -> X_instr.fwd @@ X86.leaq a b
    let indirect_callq (_, arg) =
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
          (fun graph (k, v) -> Chapter3.GraphUtils.add_interference k v graph)
          graph edges
      in
      (acc_graph, X86.indirect_callq arg)
    let define ?(locals = StringMap.empty) ?stack_size ?root_stack_size
        ?conflicts:_ ?moves v blocks =
      let interference_graph = build_interference_graph locals blocks in
      let blocks = List.map (fun (l, (_, block)) -> (l, block)) blocks in
      X86.define ~locals ?stack_size ?root_stack_size
        ~conflicts:interference_graph ?moves v blocks
    let program = X86.program
  end
end
module BuildInterference (F : X86_3) : X86_3 with type 'a obs = 'a F.obs =
struct
  module M = BuildInterferencePass (F)
  include
    X86_3_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_def) (M.X_program)
      (F)
  include M.IDelta
end

module BuildMovesPass (X86 : X86_3) = struct
  include Chapter5.BuildMovesPass (X86_2_of_X86_3 (X86))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a X86.def
  end)
  module IDelta = struct
    include IDelta
    let define ?locals ?stack_size ?root_stack_size ?conflicts ?moves:_ v blocks
        =
      let moves, blocks = program_helper blocks in
      X86.define ?locals ?stack_size ?root_stack_size ?conflicts ~moves v blocks
    let program = X86.program
  end
end
module BuildMoves (F : X86_3) : X86_3 with type 'a obs = 'a F.obs = struct
  module M = BuildMovesPass (F)
  include
    X86_3_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_def) (M.X_program)
      (F)
  include M.IDelta
end

module AllocateRegistersPass (X86 : X86_3) = struct
  include Chapter5.AllocateRegistersPass (X86_2_of_X86_3 (X86))
  module IDelta = struct
    include IDelta
    let define ?(locals = StringMap.empty) ?stack_size:_ ?root_stack_size:_
        ?(conflicts = ArgMap.empty) ?(moves = ArgMap.empty) v blocks () =
      let stack_size, root_stack_size, conflicts, moves, blocks =
        program_helper locals conflicts moves blocks
      in
      X86.define ~locals ~stack_size ~root_stack_size ~conflicts ~moves v blocks
    let program defs () = X86.program @@ List.map (fun def -> def ()) defs
  end
end
module AllocateRegisters (F : X86_3) : X86_3 with type 'a obs = 'a F.obs =
struct
  module M = AllocateRegistersPass (F)
  include X86_3_R_T (M.X_reader) (F)
  include M.IDelta
end

module PatchInstructionsPass (X86 : X86_3) = struct
  include Chapter5.PatchInstructionsPass (X86_2_of_X86_3 (X86))
  module X_def = Chapter1.MkId (struct
    type 'a t = 'a X86.def
  end)
  module IDelta = struct
    include IDelta
    let leaq (_, src) (info2, dest) =
      match info2 with
      | ArgInfo.MemoryReference _ ->
        X86.[ leaq src (reg rax); movq (reg rax) dest ]
      | _ -> X_instr.fwd @@ X86.leaq src dest

    let tail_jmp (info, arg) =
      if info = ArgInfo.HashedRegister (Hashtbl.hash X86.rax) then
        X_instr.fwd @@ X86.tail_jmp arg
      else
        X86.[ movq arg (reg rax); X86.tail_jmp (reg rax) ]
  end
end
module PatchInstructions (F : X86_3) : X86_3 with type 'a obs = 'a F.obs =
struct
  module M = PatchInstructionsPass (F)
  include
    X86_3_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_def) (M.X_program)
      (F)
  include M.IDelta
end

module R4_Shrink_Pretty () = struct
  include Chapter5.R3_Pretty ()
  type 'a def = string
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = Chapter5.HListFn (struct
    type 'a t = 'a var
  end)
  module VarLimitList = LimitFn (VarHList)

  let app fexp es =
    let rec show_hlist : type a. a ExpHList.hlist -> string = function
      | x :: xs -> " " ^ x ^ show_hlist xs
      | [] -> ""
    in
    let go : type a. a ExpLimitList.limit -> string = function
      | LX (l, _) -> show_hlist l
      | L l -> show_hlist l
    in
    "(" ^ fexp ^ go es ^ ")"

  let define _ty v vs e rest =
    let rec show_hlist : type a. a VarHList.hlist -> string = function
      | x :: xs -> " " ^ x ^ show_hlist xs
      | [] -> ""
    in
    let go : type a. a VarLimitList.limit -> string = function
      | LX (l, _) -> show_hlist l
      | L l -> show_hlist l
    in
    "(define (" ^ v ^ go vs ^ ")\n  " ^ e ^ ")\n" ^ rest

  let body _ = failwith "Body should have been eliminated by the Shrink pass"
  let endd () = ""

  let program def = "(program\n" ^ def ^ ")"
end

module F1_Pretty () = struct
  include R4_Shrink_Pretty ()
  let fun_ref label = "(fun-ref " ^ label ^ ")"
end

module F1_Collect_Pretty () = struct
  include Chapter5.R3_Collect_Pretty ()
  include F1_Pretty ()
end

module C3_Pretty = struct
  include Chapter5.C2_Pretty
  type 'a def = string
  module ArgHList = Chapter5.HListFn (struct
    type 'a t = 'a arg
  end)
  module ArgLimitList = LimitFn (ArgHList)
  let rec show_args : type r. r ArgHList.hlist -> string = function
    | x :: xs -> " " ^ x ^ show_args xs
    | [] -> ""
  let show_args_limit : type r. r ArgLimitList.limit -> string = function
    | LX (l, _) -> show_args l
    | L l -> show_args l

  let fun_ref label = "(fun-ref " ^ label ^ ")"
  let call f ps = "(call " ^ f ^ show_args_limit ps ^ ")"
  let tailcall f ps = "(tailcall " ^ f ^ show_args_limit ps ^ ")"
  let define ?(locals = []) v vs body =
    let pair (label, tail) = "(" ^ label ^ " . " ^ tail ^ ")" in
    let body = String.concat "\n" (List.map pair body) in
    "(define ((locals . " ^ info locals ^ ")) " ^ v ^ " " ^ String.concat " " vs
    ^ " " ^ body ^ ")"
  let program defs = "(program \n" ^ String.concat "\n" defs ^ ")"
end

module X86_3_Pretty = struct
  include Chapter5.X86_2_Pretty
  let fun_ref label = "(fun-ref " ^ label ^ ")"
  let indirect_callq arg = "(indirect-callq " ^ arg ^ ")"
  let tail_jmp arg = "(tail-jmp " ^ arg ^ ")"
  let leaq a b = "(leaq " ^ a ^ " " ^ b ^ ")"
  type 'a def = string
  let function_helper info label body =
    "(define " ^ info ^ " " ^ label
    ^ String.concat "\n"
        (List.map (fun (l, t) -> "(" ^ l ^ " . " ^ t ^ ")") body)
    ^ ")"
  let define ?locals ?stack_size ?root_stack_size ?conflicts ?moves label body =
    let info =
      enclose @@ locals_info locals
      ^ root_stack_info root_stack_size
      ^ program_info stack_size conflicts moves
    in
    function_helper info label body
  let program = String.concat "\n"
end

module X86_Info = Chapter2_passes.X86_Info
module X86_3_Printer_Helper (R : Chapter1.Reader with type t = X86_Info.t) :
  X86_3 with type 'a obs = string = struct
  include Chapter5.X86_2_Printer_Helper (R)
  type 'a def = string

  let fun_ref label = label ^ "(%rip)"
  let indirect_callq a _ = "callq *" ^ a
  let tail_jmp a = pop_stack_with_instr ("jmp *" ^ a)
  let leaq a b _ = "leaq " ^ a ^ ", " ^ b

  let function_info stack_size root_stack_size =
    let add_root_stack (header, footer) =
      match root_stack_size with
      | Some stack_size ->
        ( header @ [ addq (int stack_size) r15 ],
          footer @ [ subq (int stack_size) r15 ] )
      | None -> (header, footer)
    in
    Option.map add_root_stack (function_prologue_epilogue stack_size)

  let function_helper stack_size root_stack_size blocks =
    let header_footer = function_info stack_size root_stack_size in
    let init = X86_Info.{ stack_size; root_stack_size; header_footer } in
    blocks
    |> List.concat_map (fun (label, block) -> (label ^ ":\n") :: block init)
    |> apply_header init

  let define ?locals:_ ?stack_size ?root_stack_size ?conflicts:_ ?moves:_ v
      blocks =
    String.concat "\n"
      ((v ^ ":\n")
      ::
      (if v = "main" then
         program_helper stack_size root_stack_size blocks
       else
         function_helper stack_size root_stack_size blocks))
  let program defs = String.concat "\n" @@ [ ".global main"; ".text" ] @ defs
end

module X86_3_Printer = X86_3_Printer_Helper (X86_Info)

module Ex1 (F : R4_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let@ map_vec =
      Ty.([ [ Int ] --> Int; Vector [ Int; Int ] ] --> Vector [ Int; Int ])
      @> fun [ f; v ] ->
      vector
        [
          var f $ [ vector_ref (var v) Here ];
          var f $ [ vector_ref (var v) (Next Here) ];
        ]
    in
    let@ add1 = Ty.([ Int ] --> Int) @> fun [ x ] -> var x + int 1 in
    body Ty.Int
    @@ vector_ref
         (var map_vec $ [ var add1; vector [ int 0; int 41 ] ])
         (Next Here)
end

(* Test mutually recursive functions *)
module Ex2 (F : R4_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let@@ [ is_even; _ ] =
      [ (); () ] @@> fun [ is_even; is_odd ] ->
      [
        begin
          Ty.([ Int ] --> Bool) @> fun [ v ] ->
          if_ (var v = int 0) t (var is_odd $ [ var v - int 1 ])
        end;
        begin
          Ty.([ Int ] --> Bool) @> fun [ v ] ->
          if_ (var v = int 0) f (var is_even $ [ var v - int 1 ])
        end;
      ]
    in
    body Ty.Bool (var is_even $ [ int 24 ])
end

module Ex3 (F : R4_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let@ add =
      Ty.([ Int; Int; Int; Int; Int; Int; Int ] --> Int)
      @> fun [ a; b; c; d; e; f; g ] ->
      var a + var b + var c + var d + var e + var f + var g
    in
    body Ty.Int (var add $ [ int 1; int 2; int 3; int 4; int 5; int 6; int 7 ])
end

module Ex4 (F : R4_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let@ bar = Ty.([ Int; Int ] --> Int) @> fun [ a; b ] -> var a + var b in
    let@ foo =
      Ty.([ Int; Int ] --> Int) @> fun [ a; b ] -> var bar $ [ var b; var a ]
    in
    body Ty.Int (var foo $ [ int 3; int 4 ])
end

let%expect_test "Example 1 RemoveLet, Shrink, and RevealFunctions" =
  let module M = Ex1 (TransformLet (Shrink (RevealFunctions (F1_Pretty ())))) in
  Format.printf "Ex1: %s" M.res;
  [%expect
    {|
    Ex1: (program
    (define (tmp0 tmp1 tmp2)
      (vector ((var tmp1) (vector-ref (var tmp2) 0)) ((var tmp1) (vector-ref (var tmp2) 1))))
    (define (tmp3 tmp4)
      (+ (var tmp4) 1))
    (define (main)
      (vector-ref ((fun-ref tmp0) (fun-ref tmp3) (vector 0 41)) 1))
    )
    |}]

let%expect_test "Example 2 RemoveLet, Shrink, and RevealFunctions" =
  let module M = Ex2 (TransformLet (Shrink (RevealFunctions (F1_Pretty ())))) in
  Format.printf "Ex2: %s" M.res;
  [%expect
    {|
    Ex2: (program
    (define (tmp0 tmp2)
      (if (= (var tmp2) 0) t ((fun-ref tmp1) (+ (var tmp2) (- 1)))))
    (define (tmp1 tmp3)
      (if (= (var tmp3) 0) f ((fun-ref tmp0) (+ (var tmp3) (- 1)))))
    (define (main)
      ((fun-ref tmp0) 24))
    )
    |}]

let%expect_test "Example 3 RemoveLet, Shrink, and RevealFunctions" =
  let module M = Ex3 (TransformLet (Shrink (RevealFunctions (F1_Pretty ())))) in
  Format.printf "Ex3: %s" M.res;
  [%expect
    {|
    Ex3: (program
    (define (tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp8)
      (+ (+ (+ (+ (+ (+ (var tmp1) (var tmp2)) (var tmp3)) (var tmp4)) (var tmp5)) (vector-ref (var tmp8) 0)) (vector-ref (var tmp8) 1)))
    (define (main)
      ((fun-ref tmp0) 1 2 3 4 5 (vector 6 7)))
    )
    |}]

let%expect_test "Example 2 Annotate Types" =
  let module M =
    Ex2 (TransformLet (Shrink (RevealFunctions (F1_Annotate_Types (F1_Pretty ()))))) in
  Format.printf "Ex2: %s" M.res;
  [%expect
    {|
    Ex2: (program
    (define (tmp0 tmp2)
      (has-type (if (has-type (= (has-type (var tmp2) Int) (has-type 0 Int)) Bool) (has-type t Bool) (has-type ((has-type (fun-ref tmp1) (Fn ([Int], Bool))) (has-type (+ (has-type (var tmp2) Int) (has-type (- (has-type 1 Int)) Int)) Int)) Bool)) Bool))
    (define (tmp1 tmp3)
      (has-type (if (has-type (= (has-type (var tmp3) Int) (has-type 0 Int)) Bool) (has-type f Bool) (has-type ((has-type (fun-ref tmp0) (Fn ([Int], Bool))) (has-type (+ (has-type (var tmp3) Int) (has-type (- (has-type 1 Int)) Int)) Int)) Bool)) Bool))
    (define (main)
      (has-type ((has-type (fun-ref tmp0) (Fn ([Int], Bool))) (has-type 24 Int)) Bool))
    )
    |}]

let%expect_test "Example 3 Annotate Types" =
  let module M =
    Ex3 (TransformLet (Shrink (RevealFunctions (F1_Annotate_Types (F1_Pretty ()))))) in
  Format.printf "Ex3: %s" M.res;
  [%expect
    {|
    Ex3: (program
    (define (tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp8)
      (has-type (+ (has-type (+ (has-type (+ (has-type (+ (has-type (+ (has-type (+ (has-type (var tmp1) Int) (has-type (var tmp2) Int)) Int) (has-type (var tmp3) Int)) Int) (has-type (var tmp4) Int)) Int) (has-type (var tmp5) Int)) Int) (has-type (vector-ref (has-type (var tmp8) (Vector [Int; Int])) 0) Int)) Int) (has-type (vector-ref (has-type (var tmp8) (Vector [Int; Int])) 1) Int)) Int))
    (define (main)
      (has-type ((has-type (fun-ref tmp0) (Fn ([Int; Int; Int; Int; Int; (Vector [Int; Int])], Int))) (has-type 1 Int) (has-type 2 Int) (has-type 3 Int) (has-type 4 Int) (has-type 5 Int) (has-type (vector (has-type 6 Int) (has-type 7 Int)) (Vector [Int; Int]))) Int))
    )
    |}]

let%expect_test "Example 1 ExposeAllocation & RemoveComplex" =
  let module M =
    Ex1
      (TransformLet
         (Shrink
            (RevealFunctions
               (ExposeAllocation
                  (RemoveComplex
                     (F1_Collect_Annotate_Types (F1_Collect_Pretty ()))))))) in
  Format.printf "Ex1: %s" M.res;
  [%expect
    {|
    Ex1: (program
    (define (tmp0 tmp1 tmp2)
      (has-type (let ([tmp12 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 24 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 24) Int)) Void)]) (has-type (let ([tmp9 (has-type (allocate 1 (Vector [Int; Int])) (Vector [Int; Int]))]) (has-type (let ([tmp11 (has-type (vector-set! (has-type (var tmp9) (Vector [Int; Int])) 0 (has-type ((has-type (var tmp1) (Fn ([Int], Int))) (has-type (vector-ref (has-type (var tmp2) (Vector [Int; Int])) 0) Int)) Int)) Void)]) (has-type (let ([tmp10 (has-type (vector-set! (has-type (var tmp9) (Vector [Int; Int])) 1 (has-type ((has-type (var tmp1) (Fn ([Int], Int))) (has-type (vector-ref (has-type (var tmp2) (Vector [Int; Int])) 1) Int)) Int)) Void)]) (has-type (var tmp9) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int])))
    (define (tmp3 tmp4)
      (has-type (+ (has-type (var tmp4) Int) (has-type 1 Int)) Int))
    (define (main)
      (has-type (vector-ref (has-type ((has-type (fun-ref tmp0) (Fn ([(Fn ([Int], Int)); (Vector [Int; Int])], (Vector [Int; Int])))) (has-type (fun-ref tmp3) (Fn ([Int], Int))) (has-type (let ([tmp8 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 24 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 24) Int)) Void)]) (has-type (let ([tmp5 (has-type (allocate 1 (Vector [Int; Int])) (Vector [Int; Int]))]) (has-type (let ([tmp7 (has-type (vector-set! (has-type (var tmp5) (Vector [Int; Int])) 0 (has-type 0 Int)) Void)]) (has-type (let ([tmp6 (has-type (vector-set! (has-type (var tmp5) (Vector [Int; Int])) 1 (has-type 41 Int)) Void)]) (has-type (var tmp5) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int]))) (Vector [Int; Int])) 1) Int))
    )
    |}]

let%expect_test "Example 1 ExplicateControl & UncoverLocals" =
  let module M =
    Ex1
      (TransformLet
         (Shrink
            (RevealFunctions
               (ExposeAllocation
                  (RemoveComplex
                     (F1_Collect_Annotate_Types
                        (ExplicateControl
                           (F1_Collect_Pretty ())
                           (UncoverLocals (C3_Pretty))
                           ()))))))) in
  Format.printf "Ex1: %s" M.res;
  [%expect
    {|
    Ex1: (program
    (define ((locals . ((tmp1 . (Fn ([Int], Int))) (tmp2 . (Vector [Int; Int])) (tmp9 . (Vector [Int; Int])) (tmp10 . Void) (tmp11 . Void) (tmp12 . Void) (tmp14 . Int) (tmp16 . Int) (tmp19 . Int) (tmp21 . Int) (tmp23 . Int) (tmp24 . Int) (tmp25 . Int) (tmp26 . Int)))) tmp0 tmp1 tmp2 (start5 . (seq (assign tmp24 (global-value free_ptr)) (seq (assign tmp25 24) (seq (assign tmp23 (+ tmp24 tmp25)) (seq (assign tmp26 (global-value fromspace_end)) (if (< tmp23 tmp26) block_t3 block_f4))))))
    (block_t3 . (goto block_t1))
    (block_f2 . (seq (collect 24) (goto block_body0)))
    (block_body0 . (seq (assign tmp9 (allocate 1 (Vector [Int; Int]))) (seq (assign tmp16 (vector-ref tmp2 0)) (seq (assign tmp14 (call tmp1 tmp16)) (seq (assign tmp11 (vector-set! tmp9 0 tmp14)) (seq (assign tmp21 (vector-ref tmp2 1)) (seq (assign tmp19 (call tmp1 tmp21)) (seq (assign tmp10 (vector-set! tmp9 1 tmp19)) (return tmp9)))))))))
    (block_t1 . (seq (assign tmp12 (void)) (goto block_body0)))
    (block_f4 . (goto block_f2)))
    (define ((locals . ((tmp4 . Int) (tmp28 . Int)))) tmp3 tmp4 (start6 . (seq (assign tmp28 1) (return (+ tmp4 tmp28)))))
    (define ((locals . ((tmp5 . (Vector [Int; Int])) (tmp6 . Void) (tmp7 . Void) (tmp8 . Void) (tmp29 . (Vector [Int; Int])) (tmp30 . (Fn ([(Fn ([Int], Int)); (Vector [Int; Int])], (Vector [Int; Int])))) (tmp31 . (Fn ([Int], Int))) (tmp34 . Int) (tmp36 . Int) (tmp37 . Int) (tmp38 . Int) (tmp39 . Int) (tmp40 . Int)))) main  (start12 . (seq (assign tmp30 (fun-ref tmp0)) (seq (assign tmp31 (fun-ref tmp3)) (seq (assign tmp38 (global-value free_ptr)) (seq (assign tmp39 24) (seq (assign tmp37 (+ tmp38 tmp39)) (seq (assign tmp40 (global-value fromspace_end)) (if (< tmp37 tmp40) block_t10 block_f11))))))))
    (block_t10 . (goto block_t8))
    (block_f9 . (seq (collect 24) (goto block_body7)))
    (block_body7 . (seq (assign tmp5 (allocate 1 (Vector [Int; Int]))) (seq (assign tmp34 0) (seq (assign tmp7 (vector-set! tmp5 0 tmp34)) (seq (assign tmp36 41) (seq (assign tmp6 (vector-set! tmp5 1 tmp36)) (seq (assign tmp29 (call tmp30 tmp31 tmp5)) (return (vector-ref tmp29 1)))))))))
    (block_t8 . (seq (assign tmp8 (void)) (goto block_body7)))
    (block_f11 . (goto block_f9))))
    |}]

module Compiler
    (T : sig
      type t
    end)
    (F : functor
      (F : R4_Let)
      -> sig
      val res : T.t F.obs
    end)
    () =
  F
    (TransformLet
       (Shrink
          (RevealFunctions
             (ExposeAllocation
                (RemoveComplex
                   (F1_Collect_Annotate_Types
                      (ExplicateControl
                         (F1_Collect_Pretty ())
                         (UncoverLocals
                            (SelectInstructions
                               (C3_Pretty)
                               (UncoverLive
                                  (BuildInterference
                                     (BuildMoves
                                        (AllocateRegisters
                                           (PatchInstructions (X86_3_Printer))))))))
                         ())))))))

let%expect_test
    "Example 1 SelectInstructions & Uncover Live & Allocate Registers" =
  let module M = Compiler (Int) (Ex1) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    tmp0:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $16, %r15
    start5:

      movq %rdi, %rbx
      movq %rsi, -8(%r15)
      movq free_ptr(%rip), %rdx
      movq $24, %rsi
      addq %rsi, %rdx
      movq fromspace_end(%rip), %rsi
      cmpq %rsi, %rdx
      jl block_t3
      jmp block_f4
    block_t3:

      jmp block_t1
    block_f4:

      jmp block_f2
    block_t1:

      movq $0, %rsi
      jmp block_body0
    block_f2:

      movq %r15, %rdi
      movq $24, %rsi
      callq collect
      jmp block_body0
    block_body0:

      movq free_ptr(%rip), %rax
      movq %rax, -16(%r15)
      addq $16, free_ptr(%rip)
      movq -16(%r15), %r11
      movq $5, (%r11)
      movq -8(%r15), %r11
      movq 8(%r11), %rdi
      callq *%rbx
      movq %rax, %rsi
      movq -16(%r15), %r11
      movq %rsi, 8(%r11)
      movq $0, %rsi
      movq -8(%r15), %r11
      movq 16(%r11), %rdi
      callq *%rbx
      movq %rax, %rsi
      movq -16(%r15), %r11
      movq %rsi, 16(%r11)
      movq $0, %rsi
      movq -16(%r15), %rax
      jmp block_exit
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $16, %r15
      retq
    tmp3:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start6:

      movq $1, %rsi
      movq %rdi, %rax
      addq %rsi, %rax
      jmp block_exit1
    block_exit1:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    main:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      movq $16384, %rdi
      movq $16, %rsi
      callq initialize
      movq rootstack_begin(%rip), %r15
      movq $0, (%r15)
      addq $0, %r15
    start12:

      leaq tmp0(%rip), %r14
      leaq tmp3(%rip), %rbx
      movq free_ptr(%rip), %rdi
      movq $24, %rdx
      addq %rdx, %rdi
      movq fromspace_end(%rip), %rdx
      cmpq %rdx, %rdi
      jl block_t10
      jmp block_f11
    block_t10:

      jmp block_t8
    block_f11:

      jmp block_f9
    block_t8:

      movq $0, %rsi
      jmp block_body7
    block_f9:

      movq %r15, %rdi
      movq $24, %rsi
      callq collect
      jmp block_body7
    block_body7:

      movq free_ptr(%rip), %rsi
      addq $16, free_ptr(%rip)
      movq %rsi, %r11
      movq $5, (%r11)
      movq $0, %rdx
      movq %rsi, %r11
      movq %rdx, 8(%r11)
      movq $0, %rdx
      movq $41, %rdx
      movq %rsi, %r11
      movq %rdx, 16(%r11)
      movq $0, %rdx
      movq %rbx, %rdi
      callq *%r14
      movq %rax, %rsi
      movq %rsi, %r11
      movq 16(%r11), %rax
      jmp block_exit2
    block_exit2:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    |}]

let%expect_test "Example 2 Allocate Registers" =
  let module M = Compiler (Bool) (Ex2) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    tmp0:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start4:

      movq $0, %rsi
      cmpq %rsi, %rdi
      je block_t2
      jmp block_f3
    block_t2:

      jmp block_t0
    block_f3:

      jmp block_f1
    block_t0:

      movq $1, %rax
      jmp block_exit
    block_f1:

      leaq tmp1(%rip), %rsi
      movq $1, %rdx
      negq %rdx
      addq %rdx, %rdi
      movq %rsi, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    tmp1:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start9:

      movq $0, %rsi
      cmpq %rsi, %rdi
      je block_t7
      jmp block_f8
    block_t7:

      jmp block_t5
    block_f8:

      jmp block_f6
    block_t5:

      movq $0, %rax
      jmp block_exit1
    block_f6:

      leaq tmp0(%rip), %rsi
      movq $1, %rdx
      negq %rdx
      addq %rdx, %rdi
      movq %rsi, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    block_exit1:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    main:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      movq $16384, %rdi
      movq $16, %rsi
      callq initialize
      movq rootstack_begin(%rip), %r15
      movq $0, (%r15)
      addq $0, %r15
    start10:

      leaq tmp0(%rip), %rsi
      movq $24, %rdi
      movq %rsi, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    |}]

let%expect_test "Example 3 Allocate Registers" =
  let module M = Compiler (Int) (Ex3) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    tmp0:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start0:

      addq %rsi, %rdi
      addq %rdx, %rdi
      addq %rcx, %rdi
      addq %r8, %rdi
      movq %r9, %r11
      movq 8(%r11), %rsi
      addq %rsi, %rdi
      movq %r9, %r11
      movq 16(%r11), %rsi
      movq %rdi, %rax
      addq %rsi, %rax
      jmp block_exit
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    main:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $16, %rsp
      movq $16384, %rdi
      movq $16, %rsi
      callq initialize
      movq rootstack_begin(%rip), %r15
      movq $0, (%r15)
      addq $0, %r15
    start6:

      leaq tmp0(%rip), %rax
      movq %rax, -8(%rbp)
      movq $1, -16(%rbp)
      movq $2, %r12
      movq $3, %r13
      movq $4, %r14
      movq $5, %rbx
      movq free_ptr(%rip), %rdx
      movq $24, %rsi
      addq %rsi, %rdx
      movq fromspace_end(%rip), %rsi
      cmpq %rsi, %rdx
      jl block_t4
      jmp block_f5
    block_t4:

      jmp block_t2
    block_f5:

      jmp block_f3
    block_t2:

      movq $0, %rsi
      jmp block_body1
    block_f3:

      movq %r15, %rdi
      movq $24, %rsi
      callq collect
      jmp block_body1
    block_body1:

      movq free_ptr(%rip), %r9
      addq $16, free_ptr(%rip)
      movq %r9, %r11
      movq $5, (%r11)
      movq $6, %rsi
      movq %r9, %r11
      movq %rsi, 8(%r11)
      movq $0, %rsi
      movq $7, %rsi
      movq %r9, %r11
      movq %rsi, 16(%r11)
      movq $0, %rsi
      movq -16(%rbp), %rdi
      movq %r12, %rsi
      movq %r13, %rdx
      movq %r14, %rcx
      movq %rbx, %r8
      movq -8(%rbp), %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    |}]

let%expect_test "Example 4 Allocate Registers" =
  let module M = Compiler (Int) (Ex4) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    tmp0:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start0:

      movq %rdi, %rax
      addq %rsi, %rax
      jmp block_exit
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      retq
    tmp3:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start1:

      movq %rdi, %rcx
      movq %rsi, %rdi
      leaq tmp0(%rip), %rdx
      movq %rcx, %rsi
      movq %rdx, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    main:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      movq $16384, %rdi
      movq $16, %rsi
      callq initialize
      movq rootstack_begin(%rip), %r15
      movq $0, (%r15)
      addq $0, %r15
    start2:

      leaq tmp3(%rip), %rdx
      movq $3, %rdi
      movq $4, %rsi
      movq %rdx, %rax
      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $0, %r15
      jmp *%rax
    |}]

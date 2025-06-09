module Ty = Chapter6.Ty

module type CLOSURE = sig
  module Limit : Chapter6.LIMIT
  open Limit

  type 'r closure = (unit * 'r) limit

  val fwd : convert -> unit HList.el -> 't Limit.HList.hlist -> 't closure
end

module ClosureFn (Limit : Chapter6.LIMIT) = struct
  module Limit = Limit
  open Limit
  type 'r closure = (unit * 'r) limit
  let fwd (type t) conv (h : unit HList.el) (xs : t HList.hlist) : t closure =
    fwd conv (h :: xs)
end

module type R5_Shrink = sig
  include Chapter6.R4_Shrink
  module ExpClosure : CLOSURE with module Limit = ExpLimitList
  module VarClosure : CLOSURE with module Limit = VarLimitList

  val app : (unit * 'tup -> 'a) exp -> 'tup ExpClosure.closure -> 'a exp
  val define :
    ('tup -> 'a) Ty.ty ->
    (unit * 'tup -> 'a) var ->
    'tup VarClosure.closure ->
    'a exp ->
    'b def ->
    'b def

  val lam :
    ('tup -> 'a) Ty.ty ->
    'tup VarClosure.closure ->
    'a exp ->
    (unit * 'tup -> 'a) exp

  val unsafe_vector : string list -> 'a exp
  val unsafe_vector_ref : 'a exp -> int -> 'b exp
end

module type R5 = sig
  include Chapter6.R4
  include R5_Shrink with type 'a exp := 'a exp
end

module type R5_Let = sig
  include Chapter2_definitions.R1_Let
  include Chapter6.R4_Let
  include
    R5
      with type 'a exp := 'a exp
       and type 'a var := 'a var
       and type 'a def := 'a def
       and module VarHList := VarHList
       and module ExpHList := ExpHList
  val lambda : ('tup, 'a) Wrapped.t -> ('tup -> 'a) exp
end

module type F2 = sig
  include R5_Shrink
  val fun_ref : string -> 'a exp
end

module R4_of_R5_Shrink (F : R5_Shrink) = struct
  include F
  let app _ _ = failwith "Please handle app"
  let define _ _ _ _ _ = failwith "Please handle define"
end

module R4_of_R5 (F : R5) = struct
  include F
  let app _ _ = failwith "Please handle app"
  let define _ _ _ _ _ = failwith "Please handle define"
end

module R5_Shrink_R_T (R : Chapter1.Reader) (F : R5_Shrink) = struct
  include Chapter6.R4_Shrink_R_T (R) (R4_of_R5_Shrink (F))
  module VarClosure = ClosureFn (VarLimitList)
  module ExpClosure = ClosureFn (ExpLimitList)

  let app e es r =
    let e = e r in
    let es = convert_hlist_limit r es in
    F.app e es

  let define ty v vs e rest r =
    let e = e r in
    let rest = rest r in
    F.define ty v vs e rest

  let lam ty vs e r = F.lam ty vs (e r)
  let unsafe_vector vs _ = F.unsafe_vector vs
  let unsafe_vector_ref e i r = F.unsafe_vector_ref (e r) i
end

module R5_R_T (R : Chapter1.Reader) (F : R5) = struct
  include Chapter6.R4_R_T (R) (R4_of_R5 (F))
  include R5_Shrink_R_T (R) (F)
end

module F2_R_T (R : Chapter1.Reader) (F : F2) = struct
  include R5_Shrink_R_T (R) (F)
  let fun_ref label _ = F.fun_ref label
end

module R5_Shrink_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R5_Shrink
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter6.R4_Shrink_T (X_exp) (X_def) (X_program) (R4_of_R5_Shrink (F))
  module VarClosure = ClosureFn (VarLimitList)
  module ExpClosure = ClosureFn (ExpLimitList)
  let app f es = X_exp.fwd @@ F.app (X_exp.bwd f) (convert_hlist_limit es)
  let define ty v vs body rest =
    X_def.fwd @@ F.define ty v vs (X_exp.bwd body) (X_def.bwd rest)
  let lam ty vs e = X_exp.fwd @@ F.lam ty vs (X_exp.bwd e)
  let unsafe_vector vs = X_exp.fwd @@ F.unsafe_vector vs
  let unsafe_vector_ref e i = X_exp.fwd @@ F.unsafe_vector_ref (X_exp.bwd e) i
end

module R5_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R5
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include R5_Shrink_T (X_exp) (X_def) (X_program) (F)
  include Chapter4.R2_T (X_exp) (X_program) (Chapter6.R3_of_R4 (R4_of_R5 (F)))
  let program _ = failwith "Please handle program"
end

module F2_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      F2
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include R5_Shrink_T (X_exp) (X_def) (X_program) (F)
  let fun_ref label = X_exp.fwd @@ F.fun_ref label
end

module StringSet = Chapter2_definitions.StringSet
module TransformLetPass (F : R5) = struct
  include Chapter6.TransformLetPass (R4_of_R5 (F))

  module IDelta (F' : R5 with type 'a exp = R.t -> 'a F.exp) = struct
    include IDelta (R4_of_R5 (F'))

    let ( let* ) e f r =
      let e = e r in
      let var = F.fresh () in
      let body = f var r in
      r.R.free_vars <- StringSet.remove (F.string_of_var var) r.R.free_vars;
      F.lett var e body

    let ( $ ) fn es r =
      let fn = fn r in
      let tmp = F.fresh () in
      let es =
        F.ExpLimitList.fwd
          { f = (fun l -> F.vector l) }
          (F.(var (var_of_string (string_of_var tmp))) :: convert_exps r es)
      in
      F.(lett tmp fn (app (unsafe_vector_ref (var tmp) 0) es))

    let var v r =
      let v = F.string_of_var v in
      r.R.free_vars <- StringSet.add v r.R.free_vars;
      r.to_exp v

    let let_helper var f g r =
      let (Ty.Fn (params, _) as ty) = f.Wrapped.ty in
      let params = vars_of_tys (Ty.TyLimitList.bwd params) in
      let params' = F.VarHList.(F.fresh () :: params) in
      let r' = R.clone r in
      let params' = F.VarLimitList.fwd (tuple_handler r') params' in
      let body = f.fn params r' in
      let rest = g var r in
      (* Define lifted up definitions before this one *)
      r'.lifted_defs
      @@ F.define ty (F.var_of_string (F.string_of_var var)) params' body rest

    let ( let@ ) f g r = let_helper (F.fresh ()) f g r

    let ( let@@ ) f g r =
      let vars = vars_of_units f.Wrapped2.realized in
      let fns = f.fn vars in
      let rest = g vars r in
      let rec go : type r. r FnHList.hlist * r F.VarHList.hlist -> 'a F.def =
        function
        | wrapped :: xs, v :: vs ->
          let_helper
            F.(var_of_string (string_of_var v))
            wrapped
            (fun _ -> fun _ -> go (xs, vs))
            r
        | [], [] -> rest
      in
      go (fns, vars)

    let rec set_of_hlist : type r. r F.VarHList.hlist -> StringSet.t = function
      | v :: vs -> StringSet.add (F.string_of_var v) (set_of_hlist vs)
      | [] -> StringSet.empty
    let set_of_hlist_limit : type r. r F.VarLimitList.limit -> StringSet.t =
      function
      | LX (vs, _) -> set_of_hlist vs
      | L vs -> set_of_hlist vs

    let lambda f r =
      let r' = { (R.clone r) with free_vars = StringSet.empty } in
      let (Ty.Fn (params, _) as ty) = f.Wrapped.ty in
      let params = vars_of_tys (Ty.TyLimitList.bwd params) in
      let params' = F.VarHList.(F.fresh () :: params) in
      let body = f.fn params r' in
      let params' = F.VarLimitList.fwd (tuple_handler r') params' in
      let lambda_def_var = F.fresh () in
      (* TODO: unpack free vars in body *)
      let lifted_lambda_def rest =
        F.define ty
          (F.var_of_string (F.string_of_var lambda_def_var))
          params' body rest
      in
      r.free_vars <-
        StringSet.diff
          (StringSet.union r.free_vars r'.free_vars)
          (set_of_hlist_limit params');
      let lifted_defs = r.lifted_defs in
      r.lifted_defs <-
        (fun def -> r'.lifted_defs (lifted_lambda_def (lifted_defs def)));
      let closure_params =
        F.string_of_var lambda_def_var :: StringSet.to_list r'.free_vars
      in
      F.unsafe_vector closure_params
  end
end

module TransformLet (F : R5) : R5_Let with type 'a obs = 'a F.obs = struct
  module M = TransformLetPass (F)
  module R = R5_R_T (M.R) (F)
  include R
  include M.IDelta (R)
end

module Ex (F : R5_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let@ f =
      Ty.([ Int ] --> ([ Int ] --> Int)) @> fun [ x ] ->
      let* y = int 4 in
      lambda @@ Ty.([ Int ] --> Int) @> fun [ z ] -> var x + var y + var z
    in
    body Ty.Int
      (let* g = var f $ [ int 5 ] in
       let* h = var f $ [ int 3 ] in
       (var g $ [ int 11 ]) + (var h $ [ int 15 ]))
end

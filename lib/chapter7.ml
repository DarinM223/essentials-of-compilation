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

module TransformLetPass (F : R5) = struct
  include Chapter6.TransformLetPass (R4_of_R5 (F))

  module X_exp = struct
    type 'a from = 'a F.exp
    type 'a term = 'a F.var list * 'a F.def list * 'a from
    let fwd t = ([], [], t)
    let bwd (_, _, t) = t
  end

  module X_def = Chapter1.MkId (struct
    type 'a t = 'a F.def
  end)
  module X_program = Chapter1.MkId (struct
    type 'a t = 'a F.program
  end)

  module IDelta (F' : R5 with type 'a exp = R.t -> 'a X_exp.term) = struct
    (* include IDelta (R4_of_R5 (F')) *)
    include F'
    module UnitHList = Chapter5.HListFn (struct
      type 'a t = unit
    end)
    module Wrapped = struct
      type ('r, 'a) t = {
        ty : ('r -> 'a) Ty.ty;
        fn : 'r F.VarHList.hlist -> 'a F'.exp;
      }
    end
    module FnHList = Chapter6.FnHListFn (struct
      type ('a, 'b) t = ('a, 'b) Wrapped.t
    end)
    module Wrapped2 = struct
      type ('r, 'a) t = {
        realized : 'r UnitHList.hlist;
        fn : 'r F.VarHList.hlist -> 'r FnHList.hlist;
      }
    end

    let rec convert_exps : type r. R.t -> r ExpHList.hlist -> r F.ExpHList.hlist
        =
     fun r -> function
      | x :: xs ->
        let _, _, x = x r in
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

    let ( @> ) ty fn = Wrapped.{ ty; fn }
    let ( @@> ) realized fn = Wrapped2.{ realized; fn }

    let ( let* ) = failwith ""

    let ( $ ) fn es r =
      let _, _, fn = fn r in
      let tmp = F.fresh () in
      let es =
        F.ExpLimitList.fwd
          { f = (fun l -> F.vector l) }
          (F.(var (var_of_string (string_of_var tmp))) :: convert_exps r es)
      in
      ([], [], F.(lett tmp fn (app (unsafe_vector_ref (var tmp) 0) es)))

    (* TODO: expressions pass up list of free variables and list of definitions *)

    let var v r = ([], [], r.R.to_exp (F.string_of_var v))

    let let_helper var f g r =
      let (Ty.Fn (params, _) as ty) = f.Wrapped.ty in
      let params = vars_of_tys (Ty.TyLimitList.bwd params) in
      let params' = F.VarHList.(F.fresh () :: params) in
      let r' = R.{ to_exp = r.to_exp } in
      let tuple_handler (type r) (l : r F.VarHList.hlist) : r F.var =
        let tuple_var = F.fresh () in
        let rec go : type a tup t.
            t F.VarHList.hlist * (a, tup) Chapter5.ptr -> unit = function
          | x :: xs, ptr ->
            let x : string = F.string_of_var x in
            let old_handler = r'.to_exp in
            r'.to_exp <-
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
      let params' = F.VarLimitList.fwd { f = tuple_handler } params' in
      let _, _, body = f.fn params r' in
      let rest = g var r in
      (* TODO: define lifted up definitions before this one *)
      F.define ty (F.var_of_string (F.string_of_var var)) params' body rest

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

    (* let program def () =
      let init = R.init () in
      F.program (def init) *)
    let program _ = failwith ""

    let lambda _ = failwith ""
  end
end

module TransformLet (F : R5) : R5_Let with type 'a obs = 'a F.obs = struct
  module M = TransformLetPass (F)
  module R = R5_R_T (M.R) (R5_T (M.X_exp) (M.X_def) (M.X_program) (F))
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

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
  val ( --> ) : 'a TyHList.hlist -> 'b ty -> ('a -> 'b) ty
  val reflect : 'a ty -> R3_Types.typ
end = struct
  module TyLimitList = LimitFn (TyHList)
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

  let app e es r =
    let rec convert_hlist : type t. t ExpHList.hlist -> t F.ExpHList.hlist =
      function
      | x :: xs ->
        let x = x r in
        x :: convert_hlist xs
      | [] -> []
    in
    let go : type t. t ExpLimitList.limit -> t F.ExpLimitList.limit = function
      | LX (l, l') -> LX (convert_hlist l, convert_hlist l')
      | L l -> L (convert_hlist l)
    in
    let e = e r in
    let es = go es in
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

  let app f es =
    let rec convert_hlist : type t. t ExpHList.hlist -> t F.ExpHList.hlist =
      function
      | x :: xs ->
        let x = bwd x in
        x :: convert_hlist xs
      | [] -> []
    in
    let go : type r. r ExpLimitList.limit -> r F.ExpLimitList.limit = function
      | LX (l, l') -> LX (convert_hlist l, convert_hlist l')
      | L l -> L (convert_hlist l)
    in
    fwd @@ F.app (bwd f) (go es)
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
  val define : label -> var list -> (label * unit tail) list -> unit def
  val program : ?locals:string list -> unit def list -> unit program
end

module StringHashtbl = Hashtbl.Make (String)
module TransformLetPass (F : R4) = struct
  include Chapter2_definitions.TransformLetPass (R3_of_R4 (F))
  module R = struct
    type t = { mutable to_exp : 'a. string -> 'a F.exp }
    let init () = { to_exp = (fun v -> F.var (F.var_of_string v)) }
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

    let ( $ ) f es r =
      let f = f r in
      let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
        | x :: xs ->
          let x = x r in
          x :: go xs
        | [] -> []
      in
      let es = F.ExpLimitList.fwd { f = (fun l -> F.vector l) } (go es) in
      F.app f es

    let var v r = r.R.to_exp (F.string_of_var v)

    let let_helper var f g r =
      let rec go : type r. r Ty.TyLimitList.HList.hlist -> r F.VarHList.hlist =
        function
        | _ :: xs ->
          let v = F.fresh () in
          v :: go xs
        | [] -> []
      in
      let (Ty.Fn (params, _) as ty) = f.Wrapped.ty in
      let params = go (Ty.TyLimitList.bwd params) in
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
      let params' = F.VarLimitList.fwd { f = tuple_handler } params in
      let body = f.fn params r' in
      let rest = g var r in
      F.define ty var params' body rest

    let ( let@ ) f g r = let_helper (F.fresh ()) f g r

    let ( let@@ ) f g r =
      let rec go : type r. r UnitHList.hlist -> r F.VarHList.hlist = function
        | _ :: xs ->
          let v = F.fresh () in
          v :: go xs
        | [] -> []
      in
      let vars = go f.Wrapped2.realized in
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

module StringMap = Map.Make (String)
module R4_Annotate_Types (F : R4_Shrink) :
  R4_Shrink
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a def =
      R3_Types.typ StringMap.t -> R3_Types.typ StringMap.t * 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include Chapter5.R3_Annotate_Types (R3_of_R4_Shrink (F))
  type 'a def = R3_Types.typ StringMap.t -> R3_Types.typ StringMap.t * 'a F.def
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = F.VarHList
  module VarLimitList = F.VarLimitList

  let app e es m =
    let ety, e = e m in
    let rty =
      match ety with
      | R3_Types.Fn (_, ret) -> ret
      | _ -> failwith "Applying expression that isn't a function type"
    in
    let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
      | x :: xs ->
        let x = snd (x m) in
        x :: go xs
      | [] -> []
    in
    let go : type r. r ExpLimitList.limit -> r F.ExpLimitList.limit = function
      | LX (l, l') -> LX (go l, go l')
      | L l -> L (go l)
    in
    let es = go es in
    (rty, F.has_type (F.app e es) rty)
  let define (Ty.Fn (params, _) as ty) v vs body rest m =
    let m = StringMap.add (F.string_of_var v) (Ty.reflect ty) m in
    let m, rest = rest m in
    let rec add_param_types : type r.
        r VarHList.hlist -> r Ty.TyLimitList.HList.hlist -> 'a -> 'a =
     fun vars tys map ->
      match (vars, tys) with
      | v :: vs, t :: ts ->
        add_param_types vs ts
          (StringMap.add (F.string_of_var v) (Ty.reflect t) map)
      | [], [] -> map
    in
    let add_param_types (type r) (vars : r VarLimitList.limit)
        (tys : r Ty.TyLimitList.limit) map =
      match (vars, tys) with
      | LX (vs, _), LX (ts, _) -> add_param_types vs ts map
      | L vs, L ts -> add_param_types vs ts map
      | _, _ -> failwith "This can never happen"
    in
    let m' = add_param_types vs params m in
    let _, body = body m' in
    (m, F.define ty v vs body rest)

  let body ty e m =
    let _, e = e m in
    (m, F.body ty e)
  let endd () m = (m, F.endd ())
  let program def =
    let _, def = def StringMap.empty in
    F.program def
end
module F1_Annotate_Types (F : F1) :
  F1
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a def =
      R3_Types.typ StringMap.t -> R3_Types.typ StringMap.t * 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include R4_Annotate_Types (F)
  let fun_ref label m =
    let ty = StringMap.find label m in
    (ty, F.has_type (F.fun_ref label) ty)
end
module F1_Collect_Annotate_Types (F : F1_Collect) :
  F1_Collect
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a def =
      R3_Types.typ StringMap.t -> R3_Types.typ StringMap.t * 'a F.def
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
    let app e es =
      let rec go : type r. r F'.ExpHList.hlist -> r F.ExpHList.hlist = function
        | x :: xs -> bwd x :: go xs
        | [] -> []
      in
      let go : type r. r F'.ExpLimitList.limit -> r F.ExpLimitList.limit =
        function
        | LX (l, l') -> LX (go l, go l')
        | L l -> L (go l)
      in
      (Complex, F.app (bwd e) (go es))
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

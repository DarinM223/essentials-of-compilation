module Ty = Chapter6.Ty
module StringHashtbl = Chapter6.StringHashtbl
module R3_Types = struct
  include Chapter5.R3_Types

  (* Adds closure parameter (handling argument limiting at runtime) and returns wrapped closure *)
  let convert_to_closure params ret =
    match params with
    | [ a; b; c; d; e; f ] ->
      let rec ty = Vector [ Fn (ty :: [ a; b; c; d; Vector [ e; f ] ], ret) ] in
      ty
    | _ ->
      let rec ty = Vector [ Fn (ty :: params, ret) ] in
      ty
end
module StringSet = Chapter2_definitions.StringSet
module StringMap = Chapter6.StringMap

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
    R3_Types.typ ->
    (unit * 'tup -> 'a) var ->
    'tup VarClosure.closure ->
    'a exp ->
    'b def ->
    'b def

  val unsafe_vector : string list -> 'a exp
  val unsafe_vector_ref : 'a exp -> int -> 'b exp
  val unsafe_vector_set : 'a exp -> int -> 'b exp -> unit exp
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

module type F2_Collect = sig
  include Chapter5.R3_Collect
  include F2 with type 'a exp := 'a exp
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

module F1_of_F2 (F : F2) = struct
  include F
  let app _ _ = failwith "Please handle app"
  let define _ _ _ _ _ = failwith "Please handle define"
end

module F1_of_F2_Collect (F : F2_Collect) = struct
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

  let unsafe_vector vs _ = F.unsafe_vector vs
  let unsafe_vector_ref e i r = F.unsafe_vector_ref (e r) i
  let unsafe_vector_set e i e' r =
    let e = e r in
    let e' = e' r in
    F.unsafe_vector_set e i e'
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
  let unsafe_vector vs = X_exp.fwd @@ F.unsafe_vector vs
  let unsafe_vector_ref e i = X_exp.fwd @@ F.unsafe_vector_ref (X_exp.bwd e) i
  let unsafe_vector_set e i e' =
    X_exp.fwd @@ F.unsafe_vector_set (X_exp.bwd e) i (X_exp.bwd e')
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

module F2_Collect_T
    (X_exp : Chapter1.TRANS)
    (X_def : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      F2_Collect
        with type 'a exp = 'a X_exp.from
         and type 'a def = 'a X_def.from
         and type 'a program = 'a X_program.from) =
struct
  include
    Chapter5.R3_Collect_T (X_exp) (X_program)
      (Chapter6.R3_of_F1_Collect (F1_of_F2_Collect (F)))
  include F2_T (X_exp) (X_def) (X_program) (F)
end

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

    let mk_closure_type ty =
      match Ty.reflect ty with
      | Fn (Void :: params, ret) ->
        let rec ty'' = R3_Types.(Fn (Vector [ ty'' ] :: params, ret)) in
        ty''
      | _ -> failwith "Can't make closure type for non function type"

    let let_helper var f g r =
      let (Ty.Fn (params, ret)) = f.Wrapped.ty in
      let params = Ty.TyLimitList.bwd params in
      let ty = Ty.(to_hlist TyLimitList.HList.(Void :: params) --> ret) in
      let params = vars_of_tys params in
      let r' = R.clone r in
      let params' =
        F.VarLimitList.fwd (tuple_handler r') (F.fresh () :: params)
      in
      let body = f.fn params r' in
      let rest = g var r in
      (* Define lifted up definitions before this one *)
      r'.lifted_defs
      @@ F.define (mk_closure_type ty)
           (F.var_of_string (F.string_of_var var))
           params' body rest

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
      let (Ty.Fn (params, ret)) = f.Wrapped.ty in
      let params = Ty.TyLimitList.bwd params in
      let ty = Ty.(to_hlist TyLimitList.HList.(Void :: params) --> ret) in
      let params = vars_of_tys params in
      let closure_var = F.fresh () in
      let params' =
        F.VarLimitList.fwd (tuple_handler r') (closure_var :: params)
      in
      let body = f.fn params r' in
      let lambda_def_var = F.fresh () in
      let free_vars =
        StringSet.diff r'.free_vars (set_of_hlist_limit params')
      in
      (* Unpack free vars in body *)
      let body =
        let rec unpack_free_vars i = function
          | v :: vs ->
            F.(
              lett (var_of_string v)
                (unsafe_vector_ref (var closure_var) i)
                (unpack_free_vars (Stdlib.( + ) i 1) vs))
          | [] -> body
        in
        unpack_free_vars 1 @@ StringSet.to_list free_vars
      in
      let lifted_lambda_def rest =
        F.define (mk_closure_type ty)
          (F.var_of_string (F.string_of_var lambda_def_var))
          params' body rest
      in
      r.free_vars <- StringSet.union r.free_vars free_vars;
      let lifted_defs = r.lifted_defs in
      r.lifted_defs <-
        (fun def -> r'.lifted_defs (lifted_lambda_def (lifted_defs def)));
      let closure_params =
        F.string_of_var lambda_def_var :: StringSet.to_list free_vars
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

module Shrink (F : R5_Shrink) : R5 with type 'a obs = 'a F.obs = struct
  module M = Chapter6.ShrinkPass (R4_of_R5_Shrink (F))
  include R5_Shrink_T (M.X_exp) (M.X_def) (M.X_program) (F)
  include M.IDelta
  let body ty e =
    F.(
      define
        (R3_Types.Fn ([ Void ], Ty.reflect ty))
        (var_of_string "main")
        (L [ fresh () ])
        e (endd ()))
end

module RevealFunctions (F : F2) : R5_Shrink with type 'a obs = 'a F.obs = struct
  module M = Chapter6.RevealFunctionsPass (F1_of_F2 (F))
  include R5_Shrink_R_T (M.R) (F)
  include M.IDelta
  let var v is_function =
    if StringHashtbl.mem is_function (F.string_of_var v) then
      F.unsafe_vector [ F.string_of_var v ]
    else
      F.var v
  let define ty v params body rest is_function =
    StringHashtbl.add is_function (F.string_of_var v) ();
    let rest = rest is_function in
    let body = body is_function in
    F.define ty v params body rest
end

let expand_closure_params m = function
  | head :: rest ->
    let rest_types = List.map (StringHashtbl.find m) rest in
    (match StringHashtbl.find_opt m head with
    | Some R3_Types.(Fn (Vector _ :: params, ret)) ->
      (* Expand existing function type to include closure params *)
      let rec fn_ty =
        R3_Types.(Fn (Vector (fn_ty :: rest_types) :: params, ret))
      in
      StringHashtbl.replace m head fn_ty;
      (* Return closure type from function type *)
      let closure_ty =
        match fn_ty with
        | Fn (closure :: _, _) -> closure
        | _ -> failwith "Just created closure type cannot be found"
      in
      closure_ty
    | Some ty -> R3_Types.Vector (ty :: rest_types)
    | None -> failwith "Can't find type for first parameter of unsafe_vector")
  | [] -> R3_Types.Vector []

module R5_Annotate_Types (F : R5_Shrink) :
  R5_Shrink
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp
     and type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include Chapter6.R4_Annotate_Types (R4_of_R5_Shrink (F))
  module ExpClosure = ClosureFn (ExpLimitList)
  module VarClosure = ClosureFn (VarLimitList)
  let app e es m =
    let ety, e = e m in
    let rty =
      match ety with
      (* If return type is function, convert it to return closure *)
      | R3_Types.Fn (_, Fn (params, ret)) ->
        R3_Types.convert_to_closure params ret
      | R3_Types.Fn (_, ret) -> ret
      | _ -> failwith "Applying expression that isn't a function type"
    in
    let es = convert_exps_limit m es in
    (rty, F.has_type (F.app e es) rty)

  let rec vars_to_list : type r. r VarHList.hlist -> string list = function
    | v :: vs -> F.string_of_var v :: vars_to_list vs
    | [] -> []
  let vars_to_list_limit : type r. r VarLimitList.limit -> string list =
    function
    | LX (l, _) -> vars_to_list l
    | L l -> vars_to_list l

  let define ty v vs body rest m =
    StringHashtbl.add m (F.string_of_var v) ty;
    let rest = rest m in
    (* Lookup the function type again in case the other functions modified it *)
    let params, ty =
      match StringHashtbl.find_opt m (F.string_of_var v) with
      | Some (R3_Types.Fn (params, _) as ty) -> (params, ty)
      | _ -> failwith "Function variable is missing after being added"
    in
    List.iter2 (StringHashtbl.add m) (vars_to_list_limit vs) params;
    let _, body = body m in
    remove_param_types_limit m vs;
    F.define ty v vs body rest

  let unsafe_vector vs m =
    let closure_ty = expand_closure_params m vs in
    (closure_ty, F.has_type (F.unsafe_vector vs) closure_ty)

  let unsafe_vector_ref e i m =
    let (t : R3_Types.typ), e = e m in
    let indexed_ty =
      match t with
      | Vector typs ->
        (try List.nth typs i
         with Failure _e ->
           failwith @@ "Error getting index " ^ string_of_int i ^ " for types "
           ^ [%show: R3_Types.typ list] typs)
      | _ -> failwith "Expected vector type as argument to unsafe_vector_ref"
    in
    (indexed_ty, F.has_type (F.unsafe_vector_ref e i) indexed_ty)

  let unsafe_vector_set e i e' m =
    let _, e = e m in
    let _, e' = e' m in
    R3_Types.(Void, F.has_type (F.unsafe_vector_set e i e') Void)
end

module F2_Annotate_Types (F : F2) :
  F2
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp
     and type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include R5_Annotate_Types (F)
  let fun_ref label m =
    let ty = StringHashtbl.find m label in
    (ty, F.has_type (F.fun_ref label) ty)
end

module F2_Collect_Annotate_Types (F : F2_Collect) :
  F2_Collect
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp
     and type 'a def = R3_Types.typ StringHashtbl.t -> 'a F.def
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include Chapter6.F1_Collect_Annotate_Types (F1_of_F2_Collect (F))
  include F2_Annotate_Types (F)
end

module ExposeAllocationPass (F : F2_Collect) = struct
  include
    Chapter5.ExposeAllocationPass
      (Chapter6.R3_of_F1_Collect (F1_of_F2_Collect (F)))
  module IDelta
      (F' :
        F2_Collect
          with type 'a exp =
            R3_Types.typ StringHashtbl.t -> R3_Types.typ * 'a F.exp) =
  struct
    include IDelta (Chapter6.R3_of_F1_Collect (F1_of_F2_Collect (F')))
    open F'
    let unsafe_vector vs m =
      let ty = expand_closure_params m vs in
      let ty_size = R3_Types.allocation_size ty in
      let exp =
        allocate_vector ty ty_size @@ fun alloc ->
        (* For every field set to the corresponding expression with unsafe_vector_set *)
        let rec go i = function
          | v :: vs ->
            (* First argument in closure is a function reference, so need to use fun_ref for it
               We only expand out fun_ref here because annotate types extends the function type
               to include the closure parameters.
             *)
            let e =
              if Int.equal i 0 then fun_ref v else var (var_of_string v)
            in
            lett (fresh ()) (unsafe_vector_set (var alloc) i e)
            @@ go (Stdlib.( + ) i 1) vs
          | [] -> var alloc
        in
        go 0 vs
      in
      exp m
  end
end
module ExposeAllocation (F : F2_Collect) : F2 with type 'a obs = 'a F.obs =
struct
  module M = ExposeAllocationPass (F)
  module F' = F2_Collect_Annotate_Types (F)
  include F'
  include M.IDelta (F')
end

module RemoveComplexPass (F : F2_Collect) = struct
  include Chapter6.RemoveComplexPass (F1_of_F2_Collect (F))
  open X
  module IDelta (F' : F2_Collect with type 'a exp = 'a X.term) = struct
    include IDelta (F1_of_F2_Collect (F'))
    let app e es = (Complex, F.app (bwd e) (convert_exps_limit es))
    let fun_ref label = (Complex, F.fun_ref label)
  end
end
module RemoveComplex (F : F2_Collect) : F2_Collect with type 'a obs = 'a F.obs =
struct
  module M = RemoveComplexPass (F)
  module F' = F2_Collect_T (M.X) (M.X_def) (M.X_program) (F)
  include F'
  include M.IDelta (F')
end

module ExplicateControl (F : F2_Collect) (C3 : Chapter6.C3) () = struct
  include Chapter6.ExplicateControl (F1_of_F2_Collect (F)) (C3) ()
  module ExpClosure = ClosureFn (ExpLimitList)
  module VarClosure = ClosureFn (VarLimitList)
  let unsafe_vector_ref e i m r =
    let& tmp = e in
    convert_exp C3.(vector_ref (var (lookup tmp)) i) m r
  let unsafe_vector_set e i v m r =
    let& tmp1 = e in
    let& tmp2 = v in
    convert_exp C3.(vector_set (var (lookup tmp1)) i (var (lookup tmp2))) m r
  let unsafe_vector _ _ _ = failwith "unsafe_vector should've been eliminated"
end

module R5_Shrink_Pretty () = struct
  include Chapter6.R4_Shrink_Pretty ()
  module ExpClosure = ClosureFn (ExpLimitList)
  module VarClosure = ClosureFn (VarLimitList)
  let unsafe_vector vars = "(vector " ^ String.concat " " vars ^ ")"
  let unsafe_vector_ref e i = "(vector-ref " ^ e ^ " " ^ string_of_int i ^ ")"
  let unsafe_vector_set e i e' =
    "(vector-set! " ^ e ^ " " ^ string_of_int i ^ " " ^ e' ^ ")"
end

module F2_Pretty () = struct
  include R5_Shrink_Pretty ()
  let fun_ref label = "(fun-ref " ^ label ^ ")"
end

module F2_Collect_Pretty () = struct
  include Chapter5.R3_Collect_Pretty ()
  include F2_Pretty ()
end

module Ex (F : R5_Let) = struct
  open F

  (* res should be 42 *)
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

let%expect_test "Example RemoveLet & Shrink" =
  let module M = Ex (TransformLet (Shrink (RevealFunctions (F2_Pretty ())))) in
  Format.printf "Ex: %s" M.res;
  [%expect
    {|
    Ex: (program
    (define (tmp6 tmp5 tmp4)
      (let ([tmp1 (vector-ref (var tmp5) 1)]) (let ([tmp3 (vector-ref (var tmp5) 2)]) (+ (+ (var tmp1) (var tmp3)) (var tmp4)))))
    (define (tmp0 tmp2 tmp1)
      (let ([tmp3 4]) (vector tmp6 tmp1 tmp3)))
    (define (main tmp13)
      (let ([tmp8 (let ([tmp7 (vector tmp0)]) ((vector-ref (var tmp7) 0) (var tmp7) 5))]) (let ([tmp10 (let ([tmp9 (vector tmp0)]) ((vector-ref (var tmp9) 0) (var tmp9) 3))]) (+ (let ([tmp12 (var tmp8)]) ((vector-ref (var tmp12) 0) (var tmp12) 11)) (let ([tmp11 (var tmp10)]) ((vector-ref (var tmp11) 0) (var tmp11) 15))))))
    )
    |}]

let%expect_test "Example Annotate Types" =
  let module M =
    Ex (TransformLet (Shrink (RevealFunctions (F2_Annotate_Types (F2_Pretty ()))))) in
  Format.printf "Ex: %s" M.res;
  [%expect
    {|
    Ex: (program
    (define (tmp6 tmp5 tmp4)
      (has-type (let ([tmp1 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 1) Int)]) (has-type (let ([tmp3 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 2) Int)]) (has-type (+ (has-type (+ (has-type (var tmp1) Int) (has-type (var tmp3) Int)) Int) (has-type (var tmp4) Int)) Int)) Int)) Int))
    (define (tmp0 tmp2 tmp1)
      (has-type (let ([tmp3 (has-type 4 Int)]) (has-type (vector tmp6 tmp1 tmp3) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])))
    (define (main tmp13)
      (has-type (let ([tmp8 (has-type (let ([tmp7 (has-type (vector tmp0) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 5 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (let ([tmp10 (has-type (let ([tmp9 (has-type (vector tmp0) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 3 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (+ (has-type (let ([tmp12 (has-type (var tmp8) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 11 Int)) Int)) Int) (has-type (let ([tmp11 (has-type (var tmp10) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 15 Int)) Int)) Int)) Int)) Int)) Int))
    )
    |}]

let%expect_test "Example Expose Allocation & Remove Complex" =
  let module M =
    Ex
      (TransformLet
         (Shrink
            (RevealFunctions
               (ExposeAllocation (RemoveComplex (F2_Collect_Pretty ())))))) in
  Format.printf "Ex: %s" M.res;
  [%expect
    {|
    Ex: (program
    (define (tmp6 tmp5 tmp4)
      (has-type (let ([tmp1 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 1) Int)]) (has-type (let ([tmp3 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 2) Int)]) (has-type (+ (has-type (+ (has-type (var tmp1) Int) (has-type (var tmp3) Int)) Int) (has-type (var tmp4) Int)) Int)) Int)) Int))
    (define (tmp0 tmp2 tmp1)
      (has-type (let ([tmp3 (has-type 4 Int)]) (has-type (let ([tmp24 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 32 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 32) Int)) Void)]) (has-type (let ([tmp20 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))]) (has-type (let ([tmp23 (has-type (vector-set! (has-type (var tmp20) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 0 (has-type (fun-ref tmp6) (Fn ([(Vector [<cycle>; Int; Int]); Int], Int)))) Void)]) (has-type (let ([tmp22 (has-type (vector-set! (has-type (var tmp20) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 1 (has-type (var tmp1) Int)) Void)]) (has-type (let ([tmp21 (has-type (vector-set! (has-type (var tmp20) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 2 (has-type (var tmp3) Int)) Void)]) (has-type (var tmp20) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])))
    (define (main tmp13)
      (has-type (let ([tmp8 (has-type (let ([tmp7 (has-type (let ([tmp16 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 16 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 16) Int)) Void)]) (has-type (let ([tmp14 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type (let ([tmp15 (has-type (vector-set! (has-type (var tmp14) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) Void)]) (has-type (var tmp14) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 5 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (let ([tmp10 (has-type (let ([tmp9 (has-type (let ([tmp19 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 16 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 16) Int)) Void)]) (has-type (let ([tmp17 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type (let ([tmp18 (has-type (vector-set! (has-type (var tmp17) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) Void)]) (has-type (var tmp17) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 3 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (+ (has-type (let ([tmp12 (has-type (var tmp8) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 11 Int)) Int)) Int) (has-type (let ([tmp11 (has-type (var tmp10) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 15 Int)) Int)) Int)) Int)) Int)) Int))
    )
    |}]

let%expect_test "Example Explicate Control" =
  let module M =
    Ex
      (TransformLet
         (Shrink
            (RevealFunctions
               (ExposeAllocation
                  (RemoveComplex
                     (ExplicateControl
                        (F2_Collect_Pretty ())
                        (Chapter6.C3_Pretty)
                        ())))))) in
  Format.printf "Ex: %s" M.res;
  [%expect
    {|
    Ex: (program
    (define ((locals . ((tmp5 . (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) (tmp4 . Int)))) tmp6 tmp5 tmp4 (start0 . (seq (assign tmp1 (has-type (vector-ref tmp5 1) Int)) (seq (assign tmp3 (has-type (vector-ref tmp5 2) Int)) (seq (assign tmp27 (has-type (+ tmp1 tmp3) Int)) (return (has-type (+ tmp27 tmp4) Int)))))))
    (define ((locals . ((tmp2 . (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (tmp1 . Int)))) tmp0 tmp2 tmp1 (start6 . (seq (assign tmp3 (has-type 4 Int)) (seq (assign tmp38 (has-type (global-value free_ptr) Int)) (seq (assign tmp39 (has-type 32 Int)) (seq (assign tmp37 (has-type (+ tmp38 tmp39) Int)) (seq (assign tmp40 (has-type (global-value fromspace_end) Int)) (if (has-type (< tmp37 tmp40) Bool) block_t4 block_f5)))))))
    (block_f5 . (goto block_f3))
    (block_body1 . (seq (assign tmp20 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (seq (assign tmp32 (has-type (fun-ref tmp6) (Fn ([(Vector [<cycle>; Int; Int]); Int], Int)))) (seq (assign tmp23 (has-type (vector-set! tmp20 0 tmp32) Void)) (seq (assign tmp22 (has-type (vector-set! tmp20 1 tmp1) Void)) (seq (assign tmp21 (has-type (vector-set! tmp20 2 tmp3) Void)) (return (has-type tmp20 (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])))))))))
    (block_t4 . (goto block_t2))
    (block_t2 . (seq (assign tmp24 (has-type (void) Void)) (goto block_body1)))
    (block_f3 . (seq (collect 32) (goto block_body1))))
    (define ((locals . ((tmp13 . Void)))) main tmp13 (start17 . (seq (assign tmp68 (has-type (global-value free_ptr) Int)) (seq (assign tmp69 (has-type 16 Int)) (seq (assign tmp67 (has-type (+ tmp68 tmp69) Int)) (seq (assign tmp70 (has-type (global-value fromspace_end) Int)) (if (has-type (< tmp67 tmp70) Bool) block_t15 block_f16))))))
    (block_t13 . (seq (assign tmp16 (has-type (void) Void)) (goto block_body12)))
    (block_t10 . (goto block_t8))
    (block_t15 . (goto block_t13))
    (block_f16 . (goto block_f14))
    (block_f9 . (seq (collect 16) (goto block_body7)))
    (block_body7 . (seq (assign tmp17 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (seq (assign tmp48 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) (seq (assign tmp18 (has-type (vector-set! tmp17 0 tmp48) Void)) (seq (assign tmp49 (has-type (vector-ref tmp17 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) (seq (assign tmp52 (has-type 3 Int)) (seq (assign tmp10 (has-type (call tmp49 tmp17 tmp52) (Vector [(Fn ([<cycle>; Int], Int))]))) (seq (assign tmp54 (has-type (vector-ref tmp8 0) (Fn ([(Vector [<cycle>]); Int], Int)))) (seq (assign tmp57 (has-type 11 Int)) (seq (assign tmp53 (has-type (call tmp54 tmp8 tmp57) Int)) (seq (assign tmp59 (has-type (vector-ref tmp10 0) (Fn ([(Vector [<cycle>]); Int], Int)))) (seq (assign tmp62 (has-type 15 Int)) (seq (assign tmp58 (has-type (call tmp59 tmp10 tmp62) Int)) (return (has-type (+ tmp53 tmp58) Int)))))))))))))))
    (block_body12 . (seq (assign tmp14 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (seq (assign tmp42 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) (seq (assign tmp15 (has-type (vector-set! tmp14 0 tmp42) Void)) (seq (assign tmp43 (has-type (vector-ref tmp14 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) (seq (assign tmp46 (has-type 5 Int)) (seq (assign tmp8 (has-type (call tmp43 tmp14 tmp46) (Vector [(Fn ([<cycle>; Int], Int))]))) (seq (assign tmp64 (has-type (global-value free_ptr) Int)) (seq (assign tmp65 (has-type 16 Int)) (seq (assign tmp63 (has-type (+ tmp64 tmp65) Int)) (seq (assign tmp66 (has-type (global-value fromspace_end) Int)) (if (has-type (< tmp63 tmp66) Bool) block_t10 block_f11))))))))))))
    (block_t8 . (seq (assign tmp19 (has-type (void) Void)) (goto block_body7)))
    (block_f14 . (seq (collect 16) (goto block_body12)))
    (block_f11 . (goto block_f9))))
    |}]

module Compiler
    (T : sig
      type t
    end)
    (F : functor
      (F : R5_Let)
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
                   (F2_Collect_Annotate_Types
                      (ExplicateControl
                         (F2_Collect_Pretty ())
                         (Chapter6.UncoverLocals
                            (Chapter6.SelectInstructions
                               (Chapter6.C3_Pretty)
                               (Chapter6.UncoverLive
                                  (Chapter6.BuildInterference
                                     (Chapter6.BuildMoves
                                        (Chapter6.AllocateRegisters
                                           (Chapter6.PatchInstructions
                                              (Chapter6.X86_3_Printer))))))))
                         ())))))))

let%expect_test "Example to X86" =
  let module M = Compiler (Int) (Ex) () in
  print_endline M.res;
  [%expect
    {|
    .global main
    .text
    tmp6:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start0:

      movq %rdi, %r11
      movq 16(%r11), %rcx
      movq %rdi, %r11
      movq 24(%r11), %rdx
      addq %rdx, %rcx
      movq %rcx, %rax
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
    tmp0:

      pushq %rbp
      movq %rsp, %rbp
      pushq %r12
      pushq %rbx
      pushq %r13
      pushq %r14
      subq $0, %rsp
      addq $0, %r15
    start6:

      movq %rsi, %r14
      movq $4, %rbx
      movq free_ptr(%rip), %rdx
      movq $32, %rsi
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
      movq $32, %rsi
      callq collect
      jmp block_body1
    block_body1:

      movq free_ptr(%rip), %rsi
      addq $16, free_ptr(%rip)
      movq %rsi, %r11
      movq $7, (%r11)
      leaq tmp6(%rip), %rdx
      movq %rsi, %r11
      movq %rdx, 8(%r11)
      movq $0, %rdx
      movq %rsi, %r11
      movq %r14, 16(%r11)
      movq $0, %rdx
      movq %rsi, %r11
      movq %rbx, 24(%r11)
      movq $0, %rdx
      movq %rsi, %rax
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
      addq $16, %r15
    start17:

      movq %rdi, %rsi
      movq free_ptr(%rip), %rdx
      movq $16, %rsi
      addq %rsi, %rdx
      movq fromspace_end(%rip), %rsi
      cmpq %rsi, %rdx
      jl block_t15
      jmp block_f16
    block_t15:

      jmp block_t13
    block_f16:

      jmp block_f14
    block_t13:

      movq $0, %rsi
      jmp block_body12
    block_f14:

      movq %r15, %rdi
      movq $16, %rsi
      callq collect
      jmp block_body12
    block_body12:

      movq free_ptr(%rip), %rdi
      addq $16, free_ptr(%rip)
      movq %rdi, %r11
      movq $3, (%r11)
      leaq tmp0(%rip), %rsi
      movq %rdi, %r11
      movq %rsi, 8(%r11)
      movq $0, %rsi
      movq %rdi, %r11
      movq 8(%r11), %rdx
      movq $5, %rsi
      callq *%rdx
      movq %rax, -8(%r15)
      movq free_ptr(%rip), %rdx
      movq $16, %rsi
      addq %rsi, %rdx
      movq fromspace_end(%rip), %rsi
      cmpq %rsi, %rdx
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
      movq $16, %rsi
      callq collect
      jmp block_body7
    block_body7:

      movq free_ptr(%rip), %rdi
      addq $16, free_ptr(%rip)
      movq %rdi, %r11
      movq $3, (%r11)
      leaq tmp0(%rip), %rsi
      movq %rdi, %r11
      movq %rsi, 8(%r11)
      movq $0, %rsi
      movq %rdi, %r11
      movq 8(%r11), %rdx
      movq $3, %rsi
      callq *%rdx
      movq %rax, -16(%r15)
      movq -8(%r15), %r11
      movq 8(%r11), %rdx
      movq $11, %rsi
      movq -8(%r15), %rdi
      callq *%rdx
      movq %rax, %rbx
      movq -16(%r15), %r11
      movq 8(%r11), %rdx
      movq $15, %rsi
      movq -16(%r15), %rdi
      callq *%rdx
      movq %rax, %rsi
      movq %rbx, %rax
      addq %rsi, %rax
      jmp block_exit2
    block_exit2:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $16, %r15
      retq
    |}]

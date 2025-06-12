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
    ('tup -> 'a) Ty.ty ->
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
      let closure_var = F.fresh () in
      let params' = F.VarHList.(closure_var :: params) in
      let body = f.fn params r' in
      let params' = F.VarLimitList.fwd (tuple_handler r') params' in
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
        F.define ty
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
      define Ty.([] --> ty) (var_of_string "main") (L [ fresh () ]) e (endd ()))
end

module RevealFunctions (F : F2) : R5_Shrink with type 'a obs = 'a F.obs = struct
  module M = Chapter6.RevealFunctionsPass (F1_of_F2 (F))
  include R5_Shrink_R_T (M.R) (F)
  include M.IDelta
  let var v is_function =
    if StringHashtbl.mem is_function (F.string_of_var v) then
      let tmp = F.fresh () in
      F.lett tmp
        (F.fun_ref (F.string_of_var v))
        (F.unsafe_vector [ F.string_of_var tmp ])
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

  let define (Ty.Fn (params, ret) as ty) v vs body rest m =
    let params = Ty.TyLimitList.bwd params in
    let ty' = Ty.(to_hlist TyLimitList.HList.(Void :: params) --> ret) in
    let ty' =
      match Ty.reflect ty' with
      | Fn (Void :: params, ret) ->
        let rec ty'' = R3_Types.(Fn (Vector [ ty'' ] :: params, ret)) in
        ty''
      | _ -> failwith "Invalid type in define"
    in
    StringHashtbl.add m (F.string_of_var v) ty';
    let rest = rest m in
    (* Lookup the function type again in case the other functions modified it *)
    let params =
      match StringHashtbl.find_opt m (F.string_of_var v) with
      | Some (R3_Types.Fn (params, _)) -> params
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
            lett (fresh ())
              (unsafe_vector_set (var alloc) i (var (var_of_string v)))
            @@ go (Stdlib.( + ) i 1) vs
          | _ -> var alloc
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
      (let ([tmp8 (let ([tmp7 (let ([tmp14 (fun-ref tmp0)]) (vector tmp14))]) ((vector-ref (var tmp7) 0) (var tmp7) 5))]) (let ([tmp10 (let ([tmp9 (let ([tmp15 (fun-ref tmp0)]) (vector tmp15))]) ((vector-ref (var tmp9) 0) (var tmp9) 3))]) (+ (let ([tmp12 (var tmp8)]) ((vector-ref (var tmp12) 0) (var tmp12) 11)) (let ([tmp11 (var tmp10)]) ((vector-ref (var tmp11) 0) (var tmp11) 15))))))
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
      (has-type (let ([tmp8 (has-type (let ([tmp7 (has-type (let ([tmp14 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))]) (has-type (vector tmp14) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 5 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (let ([tmp10 (has-type (let ([tmp9 (has-type (let ([tmp15 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))]) (has-type (vector tmp15) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 3 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (+ (has-type (let ([tmp12 (has-type (var tmp8) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 11 Int)) Int)) Int) (has-type (let ([tmp11 (has-type (var tmp10) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 15 Int)) Int)) Int)) Int)) Int)) Int))
    )
    |}]

let%expect_test "Example Expose Allocation" =
  let module M =
    Ex
      (TransformLet
         (Shrink (RevealFunctions (ExposeAllocation (F2_Collect_Pretty ()))))) in
  Format.printf "Ex: %s" M.res;
  [%expect
    {|
    Ex: (program
    (define (tmp6 tmp5 tmp4)
      (has-type (let ([tmp1 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 1) Int)]) (has-type (let ([tmp3 (has-type (vector-ref (has-type (var tmp5) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 2) Int)]) (has-type (+ (has-type (+ (has-type (var tmp1) Int) (has-type (var tmp3) Int)) Int) (has-type (var tmp4) Int)) Int)) Int)) Int))
    (define (tmp0 tmp2 tmp1)
      (has-type (let ([tmp3 (has-type 4 Int)]) (has-type (let ([tmp26 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 32 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 32) Int)) Void)]) (has-type (let ([tmp22 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))]) (has-type (let ([tmp25 (has-type (vector-set! (has-type (var tmp22) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 0 (has-type (var tmp6) (Fn ([(Vector [<cycle>; Int; Int]); Int], Int)))) Void)]) (has-type (let ([tmp24 (has-type (vector-set! (has-type (var tmp22) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 1 (has-type (var tmp1) Int)) Void)]) (has-type (let ([tmp23 (has-type (vector-set! (has-type (var tmp22) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])) 2 (has-type (var tmp3) Int)) Void)]) (has-type (var tmp22) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int]))) (Vector [(Fn ([<cycle>; Int], Int)); Int; Int])))
    (define (main tmp13)
      (has-type (let ([tmp8 (has-type (let ([tmp7 (has-type (let ([tmp14 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))]) (has-type (let ([tmp18 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 16 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 16) Int)) Void)]) (has-type (let ([tmp16 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type (let ([tmp17 (has-type (vector-set! (has-type (var tmp16) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0 (has-type (var tmp14) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) Void)]) (has-type (var tmp16) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp7) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 5 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (let ([tmp10 (has-type (let ([tmp9 (has-type (let ([tmp15 (has-type (fun-ref tmp0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))]) (has-type (let ([tmp21 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 16 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 16) Int)) Void)]) (has-type (let ([tmp19 (has-type (allocate 1 (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type (let ([tmp20 (has-type (vector-set! (has-type (var tmp19) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0 (has-type (var tmp15) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int)))))) Void)]) (has-type (var tmp19) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))]))]) (has-type ((has-type (vector-ref (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) 0) (Fn ([(Vector [<cycle>]); Int], (Fn ([Int], Int))))) (has-type (var tmp9) (Vector [(Fn ([<cycle>; Int], (Fn ([Int], Int))))])) (has-type 3 Int)) (Vector [(Fn ([<cycle>; Int], Int))]))) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type (+ (has-type (let ([tmp12 (has-type (var tmp8) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp12) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 11 Int)) Int)) Int) (has-type (let ([tmp11 (has-type (var tmp10) (Vector [(Fn ([<cycle>; Int], Int))]))]) (has-type ((has-type (vector-ref (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) 0) (Fn ([(Vector [<cycle>]); Int], Int))) (has-type (var tmp11) (Vector [(Fn ([<cycle>; Int], Int))])) (has-type 15 Int)) Int)) Int)) Int)) Int)) Int))
    )
    |}]

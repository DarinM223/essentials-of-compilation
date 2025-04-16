type (_, _) ptr =
  | Here : ('a, 'a * _) ptr
  | Next : ('a, 'r) ptr -> ('a, _ * 'r) ptr

let ptr_num ptr =
  let rec go : type a r. int -> (a, r) ptr -> int =
   fun i -> function
     | Here -> i
     | Next n -> go (i + 1) n
  in
  go 0 ptr

module type HLIST = sig
  type 'a el
  type _ hlist =
    | [] : unit hlist
    | ( :: ) : 'a el * 'b hlist -> ('a * 'b) hlist
  val proj : 'r hlist -> ('a, 'r) ptr -> 'a el
  val replace : 'r hlist -> ('a, 'r) ptr -> 'a el -> 'r hlist
end

module HList (E : sig
  type 'a t
end) : HLIST with type 'a el = 'a E.t = struct
  type 'a el = 'a E.t
  type _ hlist =
    | [] : unit hlist
    | ( :: ) : 'a el * 'b hlist -> ('a * 'b) hlist

  let rec proj : type a r. r hlist -> (a, r) ptr -> a el =
   fun l n ->
    match (l, n) with
    | x :: _, Here -> x
    | _ :: xs, Next n -> proj xs n
    | [], _ -> . (* Refutation case *)

  let rec replace : type a r. r hlist -> (a, r) ptr -> a el -> r hlist =
   fun l n e ->
    match (l, n) with
    | _ :: xs, Here -> e :: xs
    | x :: xs, Next n -> x :: replace xs n e
    | [], _ -> .
end

module OptionHList = HList (struct
  type 'a t = 'a option
end)
let example : (int * (string * (float * unit))) OptionHList.hlist =
  OptionHList.[ Some 1; Some "hello"; Some 3.0 ]

module R3_Types = struct
  (* Runtime representation of types for garbage collection.
     Uses polymorphic variants so it can be extended
     with more types in the future.
   *)
  type typ =
    [ `Int
    | `Bool
    | `Void
    | `Vector of typ list
    ]
  [@@deriving show]

  (* TODO: check if these sizes are correct *)
  let rec allocation_size : typ -> int = function
    | `Int -> 8
    | `Bool -> 1
    | `Void -> 0
    | `Vector ts ->
      8 + List.fold_left (fun acc t -> acc + allocation_size t) 0 ts
end

module type R3_Shrink = sig
  include Chapter4.R2_Shrink

  module ExpHList : HLIST with type 'a el = 'a exp

  val has_type : 'a exp -> R3_Types.typ -> 'a exp
  val void : unit exp
  val vector : 'tup ExpHList.hlist -> 'tup exp
  val vector_ref : 'tup exp -> ('a, 'tup) ptr -> 'a exp
  val vector_set : 'tup exp -> ('a, 'tup) ptr -> 'a exp -> unit exp
end

module type R3 = sig
  include Chapter4.R2
  include R3_Shrink with type 'a exp := 'a exp
end

module type R3_Let = sig
  include R3
  include Chapter2_definitions.R1_Let with type 'a exp := 'a exp
end

module StringMap = Chapter2_definitions.StringMap

module R2_Shrink_AnnotateTypes (F : Chapter4.R2_Shrink) :
  Chapter4.R2_Shrink
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  open R3_Types
  type 'a var = 'a F.var
  type 'a exp = typ StringMap.t -> typ * 'a F.exp
  type 'a program = 'a F.program
  type 'a obs = 'a F.obs

  let bin_op f e1 e2 m =
    let t, e1 = e1 m in
    let _, e2 = e2 m in
    (t, f e1 e2)
  let bool_op f e1 e2 m =
    let _, e1 = e1 m in
    let _, e2 = e2 m in
    (`Bool, f e1 e2)

  let int i _ = (`Int, F.int i)
  let read () _ = (`Int, F.read ())
  let neg e m =
    let t, e = e m in
    (t, F.neg e)
  let ( + ) e1 e2 m = bin_op F.( + ) e1 e2 m
  let var v m = (StringMap.find (F.string_of_var v) m, F.var v)
  let fresh = F.fresh
  let string_of_var = F.string_of_var
  let lett v e b m =
    let typ, e = e m in
    let result_typ, b = b (StringMap.add (F.string_of_var v) typ m) in
    (result_typ, F.lett v e b)

  let t _ = (`Bool, F.t)
  let f _ = (`Bool, F.f)
  let not e m =
    let t, e = e m in
    (t, F.not e)
  let ( = ) e1 e2 m = bool_op F.( = ) e1 e2 m
  let ( < ) e1 e2 m = bool_op F.( < ) e1 e2 m
  let if_ cond thn els m =
    let _, cond = cond m in
    let t, thn = thn m in
    let _, els = els m in
    (t, F.if_ cond thn els)

  let program e =
    let _, e = e StringMap.empty in
    F.program e
  let observe p = F.observe p
end

module R3_Annotate_Types (F : R3_Shrink) :
  R3_Shrink
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include R2_Shrink_AnnotateTypes (F)
  open R3_Types
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)

  (* Annotate types for R2 lacks the has_type form so we need to redefine all
     the existing functions in R2 to use this form now.
   *)
  let ann_type f m =
    let ty, e = f m in
    (ty, F.has_type e ty)
  let int i = ann_type (int i)
  let read () = ann_type (read ())
  let neg e = ann_type (neg e)
  let ( + ) e1 e2 = ann_type (e1 + e2)
  let var v = ann_type (var v)
  let lett v e b = ann_type (lett v e b)
  let t = ann_type t
  let f = ann_type f
  let not e = ann_type (not e)
  let ( = ) e1 e2 = ann_type (e1 = e2)
  let ( < ) e1 e2 = ann_type (e1 < e2)
  let if_ cond thn els = ann_type (if_ cond thn els)

  let has_type e ty m =
    let _, e = e m in
    (ty, e)
  let void _ = (`Void, F.has_type F.void `Void)
  let vector hl m =
    let rec go : type a. a ExpHList.hlist -> typ list * a F.ExpHList.hlist =
      function
      | ExpHList.(e :: xs) ->
        let typ, e = e m in
        let res_typs, res_es = go xs in
        (typ :: res_typs, F.ExpHList.(e :: res_es))
      | ExpHList.[] -> ([], F.ExpHList.[])
    in
    let res_typs, res_es = go hl in
    (`Vector res_typs, F.has_type (F.vector res_es) (`Vector res_typs))
  let vector_ref e ptr m =
    let (t : typ), e = e m in
    let typs =
      match t with
      | `Vector typs -> typs
      | _ -> failwith "Expected vector type as argument to vector_ref"
    in
    let rec index_typ : type a r. typ list -> (a, r) ptr -> typ =
     fun typs ptr ->
      match (typs, ptr) with
      | typ :: _, Here -> typ
      | _ :: typs, Next ptr -> index_typ typs ptr
      | [], _ -> failwith "Cannot get type from the index"
    in
    let indexed_ty = index_typ typs ptr in
    (indexed_ty, F.has_type (F.vector_ref e ptr) indexed_ty)
  let vector_set e ptr v m =
    let _, e = e m in
    let _, v = v m in
    (`Void, F.has_type (F.vector_set e ptr v) `Void)
end

module type R3_Collect = sig
  include R3_Shrink
  val collect : int -> unit exp
  val allocate : int -> R3_Types.typ -> 'a exp
  val global_value : string -> int exp
end

module R3_Collect_Annotate_Types (F : R3_Collect) :
  R3_Collect
    with type 'a var = 'a F.var
     and type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  include R3_Annotate_Types (F)
  let collect i _ = (`Int, F.has_type (F.collect i) `Int)
  let allocate i ty _ = (ty, F.has_type (F.allocate i ty) ty)
  let global_value name _ = (`Int, F.has_type (F.global_value name) `Int)
end

module R3_Shrink_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R3_Shrink
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include Chapter4.R2_Shrink_T (X_exp) (X_program) (F)
  open X_exp
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)
  let has_type e t = fwd @@ F.has_type (bwd e) t
  let void = fwd F.void
  let vector hl =
    let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
      | ExpHList.(x :: xs) -> F.ExpHList.(bwd x :: go xs)
      | ExpHList.[] -> F.ExpHList.[]
    in
    fwd @@ F.vector @@ go hl
  let vector_ref e ptr = fwd @@ F.vector_ref (bwd e) ptr
  let vector_set e ptr v = fwd @@ F.vector_set (bwd e) ptr (bwd v)
end

module R3_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R3
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include R3_Shrink_T (X_exp) (X_program) (F)
  include Chapter4.R2_T (X_exp) (X_program) (F)
end

module R3_Collect_T
    (X_exp : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      R3_Collect
        with type 'a exp = 'a X_exp.from
         and type 'a program = 'a X_program.from) =
struct
  include R3_Shrink_T (X_exp) (X_program) (F)
  open X_exp
  let collect i = fwd @@ F.collect i
  let allocate i ty = fwd @@ F.allocate i ty
  let global_value name = fwd @@ F.global_value name
end

module TransformLet (F : R3) :
  R3_Let
    with type 'a exp = 'a F.exp
     and type 'a program = 'a F.program
     and type 'a obs = 'a F.obs = struct
  module M = Chapter2_definitions.TransformLetPass (F)
  include R3_T (M.X_exp) (M.X_program) (F)
  include M.IDelta
end

module Shrink (F : R3_Shrink) : R3 with type 'a obs = 'a F.obs = struct
  module M = Chapter4.ShrinkPass (F)
  include R3_Shrink_T (M.X_exp) (M.X_program) (F)
  include M.IDelta
end

module RemoveComplex (F : R3_Collect) : R3_Collect with type 'a obs = 'a F.obs =
struct
  module M = Chapter2_passes.RemoveComplexPass (F)
  include R3_Collect_T (M.X) (M.X_program) (F)
  include M.IDelta
end

module ExposeAllocation (F : R3_Collect) :
  R3_Shrink with type 'a obs = 'a F.obs = struct
  include R3_Collect_Annotate_Types (F)

  let vector_helper hl m =
    let rec go : type a.
        a ExpHList.hlist -> R3_Types.typ list * a F.ExpHList.hlist = function
      | ExpHList.(e :: xs) ->
        let typ, e = e m in
        let res_typs, res_es = go xs in
        (typ :: res_typs, F.ExpHList.(e :: res_es))
      | ExpHList.[] -> ([], F.ExpHList.[])
    in
    go hl

  let vector : type tup. tup ExpHList.hlist -> tup exp =
   fun hl m ->
    let vtys, ves = vector_helper hl m in
    let ty = `Vector vtys in
    let ty_size = R3_Types.allocation_size ty in
    let exp =
      let alloc = fresh () in
      lett (fresh ())
        (if_
           (global_value "free_ptr" + int ty_size < global_value "fromspace_end")
           void (collect ty_size))
      @@ lett alloc (allocate 1 ty)
      @@
      (* For every field set to the corresponding expression with vector_set *)
      let rec go : type r a.
          R3_Types.typ list -> r F.ExpHList.hlist -> (a, tup) ptr -> tup exp =
       fun tys hl ptr ->
        match (tys, hl) with
        | ty :: tys, F.ExpHList.(e :: es) ->
          let ptr = Obj.magic @@ Next ptr in
          lett (fresh ()) (vector_set (var alloc) ptr (fun _ -> (ty, e)))
          @@ go tys es ptr
        | _ -> var alloc
      in
      match (vtys, ves) with
      | ty :: tys, F.ExpHList.(e :: es) ->
        let ptr = Here in
        lett (fresh ()) (vector_set (var alloc) ptr (fun _ -> (ty, e)))
        @@ go tys es ptr
      | _ -> var alloc
    in
    exp m
end

module type C2 = sig
  include Chapter4.C1
  val has_type : 'a exp -> R3_Types.typ -> 'a exp
  val allocate : int -> R3_Types.typ -> 'a exp
  val vector_ref : 'tup arg -> ('a, 'tup) ptr -> 'a exp
  val vector_set : 'tup arg -> ('a, 'tup) ptr -> 'a arg -> unit exp
  val global_value : string -> int exp
  val void : unit exp

  val collect : int -> unit stmt
  val program :
    ?locals:(string * R3_Types.typ) list ->
    (label * unit tail) list ->
    unit program
end

module ExplicateControl (F : R3_Collect) (C2 : C2) () = struct
  module C1 = struct
    include C2
    let program ?locals body =
      let locals = Option.map (List.map (fun l -> (l, `Void))) locals in
      program ?locals body
  end
  include Chapter4.ExplicateControl (F) (C1) ()
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)

  let has_type e ty _ r =
    let ann_fn = { f = (fun exp -> C2.has_type exp ty) } in
    e ann_fn r
  let void = convert_exp C2.void
  let vector _ _ _ =
    failwith "vector should have been eliminated before explicate control"
  let vector_ref e ptr m r =
    let tmp = F.(string_of_var (fresh ())) in
    e ann_id
      (Assign
         (tmp, fun () -> convert_exp C2.(vector_ref (var (lookup tmp)) ptr) m r))
  let vector_set e ptr v m r =
    let tmp1 = F.(string_of_var (fresh ())) in
    let tmp2 = F.(string_of_var (fresh ())) in
    e ann_id
      (Assign
         ( tmp1,
           fun () ->
             v ann_id
               (Assign
                  ( tmp2,
                    fun () ->
                      convert_exp
                        C2.(
                          vector_set (var (lookup tmp1)) ptr (var (lookup tmp2)))
                        m r )) ))
  let collect i _ _ = C2.collect i
  let allocate i ty = convert_exp (C2.allocate i ty)
  let global_value name = convert_exp (C2.global_value name)
end

module R3_Pretty () = struct
  include Chapter4.R2_Shrink_Pretty ()
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)

  let has_type e ty = "(has-type " ^ e ^ " " ^ R3_Types.show_typ ty ^ ")"
  let void = "(void)"
  let vector hl =
    let rec go : type r. r ExpHList.hlist -> string = function
      | ExpHList.(x :: xs) -> " " ^ x ^ go xs
      | ExpHList.[] -> ""
    in
    "(vector" ^ go hl ^ ")"
  let vector_ref v ptr =
    "(vector-ref " ^ v ^ " " ^ string_of_int (ptr_num ptr) ^ ")"
  let vector_set v ptr r =
    "(vector-set! " ^ v ^ " " ^ string_of_int (ptr_num ptr) ^ " " ^ r ^ ")"
end

module R3_Collect_Pretty () = struct
  include R3_Pretty ()
  let collect i = "(collect " ^ string_of_int i ^ ")"
  let allocate i typ =
    "(allocate " ^ string_of_int i ^ " " ^ R3_Types.show_typ typ ^ ")"
  let global_value name = "(global-value " ^ name ^ ")"
end

module C2_Pretty = struct
  include Chapter4.C1_Pretty
  let has_type e typ = "(has-type " ^ e ^ " " ^ R3_Types.show_typ typ ^ ")"
  let allocate i typ =
    "(allocate " ^ string_of_int i ^ " " ^ R3_Types.show_typ typ ^ ")"
  let vector_ref v ptr =
    "(vector-ref " ^ v ^ " " ^ string_of_int (ptr_num ptr) ^ ")"
  let vector_set v ptr r =
    "(vector-set! " ^ v ^ " " ^ string_of_int (ptr_num ptr) ^ " " ^ r ^ ")"
  let global_value name = "(global-value " ^ name ^ ")"
  let void = "(void)"
  let collect i = "(collect " ^ string_of_int i ^ ")"
  let info i =
    "("
    ^ String.concat " "
        (List.map
           (fun (v, typ) -> Format.asprintf "(%s . %a)" v R3_Types.pp_typ typ)
           i)
    ^ ")"
  let program ?(locals = []) body =
    let pair (label, tail) = "(" ^ label ^ " . " ^ tail ^ ")" in
    let body = String.concat "\n" (List.map pair body) in
    "(program ((locals . " ^ info locals ^ ")) (" ^ body ^ ")"
end

module Ex0 (F : R3_Let) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 1 in
       var a + int 2
end

module Ex1 (F : R3_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* t1 = vector ExpHList.[ int 1; t ] in
    let* t2 = var t1 in
    let* _ = vector_set (var t2) Here (int 42) in
    let* _ = vector_set (var t2) (Next Here) f in
    vector_ref (var t1) Here
end

module Ex2 (F : R3) = struct
  open F
  let res =
    observe @@ program
    @@ vector_ref
         (vector_ref (vector ExpHList.[ vector ExpHList.[ int 42 ] ]) Here)
         Here
end

module Ex3 (F : R3_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* v =
      vector
        ExpHList.
          [
            (let* a = int 1 in
             var a + int 2);
          ]
    in
    let* _ =
      vector_set (var v) Here
        (let* b = int 2 in
         var b + int 1)
    in
    vector_ref (var v) Here
end

let%expect_test "Ex1 test expose allocation" =
  let module M =
    Ex1 (TransformLet (Shrink (ExposeAllocation (R3_Collect_Pretty ())))) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {| Ex1: (program (has-type (let ([tmp0 (has-type (let ([tmp7 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) `Int) (has-type 17 `Int)) `Int) (has-type (global-value fromspace_end) `Int)) `Bool) (has-type (void) `Void) (has-type (collect 17) `Int)) `Void)]) (has-type (let ([tmp4 (has-type (allocate 1 `Vector ([`Int; `Bool])) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp6 (has-type (vector-set! (has-type (var tmp4) `Vector ([`Int; `Bool])) 0 (has-type 1 `Int)) `Void)]) (has-type (let ([tmp5 (has-type (vector-set! (has-type (var tmp4) `Vector ([`Int; `Bool])) 1 (has-type t `Bool)) `Void)]) (has-type (var tmp4) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp1 (has-type (var tmp0) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp2 (has-type (vector-set! (has-type (var tmp1) `Vector ([`Int; `Bool])) 0 (has-type 42 `Int)) `Void)]) (has-type (let ([tmp3 (has-type (vector-set! (has-type (var tmp1) `Vector ([`Int; `Bool])) 1 (has-type f `Bool)) `Void)]) (has-type (vector-ref (has-type (var tmp0) `Vector ([`Int; `Bool])) 0) `Int)) `Int)) `Int)) `Int)) `Int)) |}]

let%expect_test "Ex0 annotate types twice" =
  let module M =
    Ex0
      (TransformLet
         (Shrink
            (R3_Collect_Annotate_Types
               (R3_Collect_Annotate_Types (R3_Collect_Pretty ()))))) in
  Format.printf "Ex0: %s\n" M.res;
  [%expect
    {| Ex0: (program (has-type (let ([tmp0 (has-type 1 `Int)]) (has-type (+ (has-type (var tmp0) `Int) (has-type 2 `Int)) `Int)) `Int)) |}]

let%expect_test "Ex3 annotate types twice" =
  let module M =
    Ex3
      (TransformLet
         (Shrink
            (R3_Annotate_Types
               (ExposeAllocation
                  (R3_Collect_Annotate_Types (R3_Collect_Pretty ())))))) in
  Format.printf "Ex3: %s\n" M.res;
  [%expect
    {| Ex3: (program (has-type (let ([tmp1 (has-type (let ([tmp6 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) `Int) (has-type 16 `Int)) `Int) (has-type (global-value fromspace_end) `Int)) `Bool) (has-type (void) `Void) (has-type (collect 16) `Int)) `Void)]) (has-type (let ([tmp4 (has-type (allocate 1 `Vector ([`Int])) `Vector ([`Int]))]) (has-type (let ([tmp5 (has-type (vector-set! (has-type (var tmp4) `Vector ([`Int])) 0 (has-type (let ([tmp0 (has-type 1 `Int)]) (has-type (+ (has-type (var tmp0) `Int) (has-type 2 `Int)) `Int)) `Int)) `Void)]) (has-type (var tmp4) `Vector ([`Int]))) `Vector ([`Int]))) `Vector ([`Int]))) `Vector ([`Int]))]) (has-type (let ([tmp3 (has-type (vector-set! (has-type (var tmp1) `Vector ([`Int])) 0 (has-type (let ([tmp2 (has-type 2 `Int)]) (has-type (+ (has-type (var tmp2) `Int) (has-type 1 `Int)) `Int)) `Int)) `Void)]) (has-type (vector-ref (has-type (var tmp1) `Vector ([`Int])) 0) `Int)) `Int)) `Int)) |}]

let%expect_test "Ex1 explicate control" =
  let module M =
    Ex1
      (TransformLet
         (Shrink
            (ExposeAllocation
               (RemoveComplex
                  (ExplicateControl (R3_Collect_Pretty ()) (C2_Pretty) ()))))) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {|
    Ex1: (program ((locals . ())) ((start . (seq (assign tmp8 (has-type (global-value free_ptr) `Int)) (seq (assign tmp9 (has-type 17 `Int)) (seq (assign tmp19 (+ tmp8 tmp9)) (seq (assign tmp20 (has-type (global-value fromspace_end) `Int)) (if (has-type (< tmp19 tmp20) `Bool) block_t3 block_f4))))))
    (block_t3 . (goto block_t1))
    (block_f2 . (collect 17))
    (block_body0 . (seq (assign tmp4 (has-type (allocate 1 `Vector ([`Int; `Bool])) `Vector ([`Int; `Bool]))) (seq (assign tmp11 (has-type 1 `Int)) (seq (assign tmp6 (has-type (vector-set! tmp4 0 tmp11) `Void)) (seq (assign tmp13 (has-type t `Bool)) (seq (assign tmp5 (has-type (vector-set! tmp4 1 tmp13) `Void)) (seq (assign tmp15 (has-type 42 `Int)) (seq (assign tmp2 (has-type (vector-set! tmp4 0 tmp15) `Void)) (seq (assign tmp17 (has-type f `Bool)) (seq (assign tmp3 (has-type (vector-set! tmp4 1 tmp17) `Void)) (return (has-type (vector-ref tmp4 0) `Int))))))))))))
    (block_t1 . (seq (assign tmp7 (has-type (void) `Void)) (goto block_body0)))
    (block_f4 . (goto block_f2)))
    |}]

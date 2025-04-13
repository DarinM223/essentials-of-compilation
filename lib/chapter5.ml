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

module type R3 = sig
  include Chapter4.R2_Shrink

  module ExpHList : HLIST with type 'a el = 'a exp

  val has_type : 'a exp -> R3_Types.typ -> 'a exp
  val void : unit exp
  val vector : 'tup ExpHList.hlist -> 'tup exp
  val vector_ref : 'tup exp -> ('a, 'tup) ptr -> 'a exp
  val vector_set : 'tup exp -> ('a, 'tup) ptr -> 'a exp -> unit exp
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
  let ( let* ) e f m =
    let typ, e = e m in
    let result_typ : (unit -> typ) ref =
      ref (fun () -> failwith "Cannot get type from let expression")
    in
    let result =
      F.( let* ) e (fun v ->
          let typ, e = f v (StringMap.add (F.string_of_var v) typ m) in
          (result_typ := fun () -> typ);
          e)
    in
    (!result_typ (), result)

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

module R3_Annotate_Types (F : R3) :
  R3
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
  let ( let* ) e f = ann_type (( let* ) e f)
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
  include R3
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

module ExposeAllocation (F : R3_Collect) : R3 with type 'a obs = 'a F.obs =
struct
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
      let* _ =
        if_
          (global_value "free_ptr" + int ty_size < global_value "fromspace_end")
          void (collect ty_size)
      in
      let* alloc : tup var = allocate 1 ty in
      (* For every field set to the corresponding expression with vector_set *)
      let rec go : type r a.
          R3_Types.typ list -> r F.ExpHList.hlist -> (a, tup) ptr -> tup exp =
       fun tys hl ptr ->
        match (tys, hl) with
        | ty :: tys, F.ExpHList.(e :: es) ->
          let ptr = Obj.magic @@ Next ptr in
          let* _ = vector_set (var alloc) ptr (fun _ -> (ty, e)) in
          go tys es ptr
        | _ -> var alloc
      in
      match (vtys, ves) with
      | ty :: tys, F.ExpHList.(e :: es) ->
        let ptr = Here in
        let* _ = vector_set (var alloc) ptr (fun _ -> (ty, e)) in
        go tys es ptr
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
end

module ExplicateControl (F : R3_Collect) (C2 : C2) () = struct
  include Chapter4.ExplicateControl (F) (C2) ()
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)

  let has_type e ty _ r =
    let ann_fn = { f = (fun exp -> C2.has_type exp ty) } in
    e ann_fn r
  let void = failwith ""
  let vector = failwith ""
  let vector_ref = failwith ""
  let vector_set = failwith ""
  let collect = failwith ""
  let allocate = failwith ""
  let global_value = failwith ""
  (* val void : unit exp
  val vector : 'tup ExpHList.hlist -> 'tup exp
  val vector_ref : 'tup exp -> ('a, 'tup) ptr -> 'a exp
  val vector_set : 'tup exp -> ('a, 'tup) ptr -> 'a exp -> unit exp *)
  (* val collect : int -> unit exp
  val allocate : int -> R3_Types.typ -> 'a exp
  val global_value : string -> int exp *)
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

module Ex0 (F : R3) = struct
  open F
  let res =
    observe @@ program
    @@ let* a = int 1 in
       var a + int 2
end

module Ex1 (F : R3) = struct
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

let%expect_test "Ex1 test expose allocation" =
  let module M = Ex1 (ExposeAllocation (R3_Collect_Pretty ())) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {| Ex1: (program (has-type (let ([tmp4 (has-type (let ([tmp0 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) `Int) (has-type 17 `Int)) `Int) (has-type (global-value fromspace_end) `Int)) `Bool) (has-type (void) `Void) (has-type (collect 17) `Int)) `Void)]) (has-type (let ([tmp1 (has-type (allocate 1 `Vector ([`Int; `Bool])) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp2 (has-type (vector-set! (has-type (var tmp1) `Vector ([`Int; `Bool])) 0 (has-type 1 `Int)) `Void)]) (has-type (let ([tmp3 (has-type (vector-set! (has-type (var tmp1) `Vector ([`Int; `Bool])) 1 (has-type t `Bool)) `Void)]) (has-type (var tmp1) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp5 (has-type (var tmp4) `Vector ([`Int; `Bool]))]) (has-type (let ([tmp6 (has-type (vector-set! (has-type (var tmp5) `Vector ([`Int; `Bool])) 0 (has-type 42 `Int)) `Void)]) (has-type (let ([tmp7 (has-type (vector-set! (has-type (var tmp5) `Vector ([`Int; `Bool])) 1 (has-type f `Bool)) `Void)]) (has-type (vector-ref (has-type (var tmp4) `Vector ([`Int; `Bool])) 0) `Int)) `Int)) `Int)) `Int)) `Int)) |}]

let%expect_test "Ex0 annotate types twice" =
  let module M =
    Ex0
      (R3_Collect_Annotate_Types
         (R3_Collect_Annotate_Types (R3_Collect_Pretty ()))) in
  Format.printf "Ex1: %s\n" M.res

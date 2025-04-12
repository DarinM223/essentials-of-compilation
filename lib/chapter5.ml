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

module type R3 = sig
  include Chapter4.R2

  module ExpHList : HLIST with type 'a el = 'a exp

  val void : unit exp
  val vector : 'tup ExpHList.hlist -> 'tup exp
  val vector_ref : 'tup exp -> ('a, 'tup) ptr -> 'a exp
  val vector_set : 'tup exp -> ('a, 'tup) ptr -> 'a exp -> unit exp
end

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

module StringMap = Chapter2_definitions.StringMap

module R2_AnnotateTypes (F : Chapter4.R2) :
  Chapter4.R2
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

  let ( - ) e1 e2 m = bin_op F.( - ) e1 e2 m
  let andd e1 e2 m = bin_op F.andd e1 e2 m
  let orr e1 e2 m = bin_op F.orr e1 e2 m
  let ( <> ) e1 e2 m = bool_op F.( <> ) e1 e2 m
  let ( <= ) e1 e2 m = bool_op F.( <= ) e1 e2 m
  let ( > ) e1 e2 m = bool_op F.( > ) e1 e2 m
  let ( >= ) e1 e2 m = bool_op F.( >= ) e1 e2 m

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
  include R2_AnnotateTypes (F)
  open R3_Types
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)
  let void _ = (`Void, F.void)
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
    (`Vector res_typs, F.vector res_es)
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
    (index_typ typs ptr, F.vector_ref e ptr)
  let vector_set e ptr v m =
    let _, e = e m in
    let _, v = v m in
    (`Void, F.vector_set e ptr v)
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
  let collect i _ = (`Int, F.collect i)
  let allocate i ty _ = (ty, F.allocate i ty)
  let global_value name _ = (`Int, F.global_value name)
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

module R3_Pretty () = struct
  include Chapter4.R2_Pretty ()
  module ExpHList = HList (struct
    type 'a t = 'a exp
  end)

  let void = "void"
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
    {| Ex1: (program (let ([tmp4 (let ([tmp0 (if (< (+ (global-value free_ptr) 17) (global-value fromspace_end)) void (collect 17))]) (let ([tmp1 (allocate 1 `Vector ([`Int; `Bool]))]) (let ([tmp2 (vector-set! (var tmp1) 0 1)]) (let ([tmp3 (vector-set! (var tmp1) 1 t)]) (var tmp1)))))]) (let ([tmp5 (var tmp4)]) (let ([tmp6 (vector-set! (var tmp5) 0 42)]) (let ([tmp7 (vector-set! (var tmp5) 1 f)]) (vector-ref (var tmp4) 0)))))) |}]

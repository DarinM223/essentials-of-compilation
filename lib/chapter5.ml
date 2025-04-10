type (_, _) ptr =
  | Here : ('a, 'a * _) ptr
  | Next : ('a, 'r) ptr -> ('a, _ * 'r) ptr

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

module type R3_Collect = sig
  include R3
  val collect : int -> unit exp
  val allocate : int -> R3_Types.typ -> 'a exp
  val global_value : string -> 'a exp
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

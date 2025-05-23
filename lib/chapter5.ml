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
  val length : 'r hlist -> int
end

module HListFn (E : sig
  type 'a t
end) =
struct
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

  let length l =
    let rec go : type r. int -> r hlist -> int =
     fun acc -> function
       | _ :: xs -> go (acc + 1) xs
       | [] -> acc
    in
    go 0 l
end

module R3_Types = struct
  (* Runtime representation of types for garbage collection. *)
  type typ =
    | Int
    | Bool
    | Void
    | Vector of typ list
    | Fn of typ list * typ
  [@@deriving show { with_path = false }]

  let rec allocation_size : typ -> int = function
    | Vector ts ->
      8 + List.fold_left (fun acc t -> acc + allocation_size t) 0 ts
    | _ -> 8

  let mk_tag : typ -> int = function
    | Vector typs when List.length typs > 50 ->
      failwith "Tuple has a max length of 50 elements"
    | Vector typs ->
      (* Fill out 63 bit tag:
         bits 58-62: unused space
         bits 7-57: 50 bits for pointer mask, 1 if pointer, 0 if other kind of data
         bits 1-6: length of the tuple
         bit 0: 1 if tuple hasn't been copied, 0 if forwarding pointer
       *)
      let mask = ref 0 in
      let go i = function
        | Vector _ -> mask := !mask lor (1 lsl i)
        | _ -> ()
      in
      List.iteri go typs;
      let len = List.length typs in
      mask := (!mask lsl 6) lor len;
      mask := (!mask lsl 1) lor 1;
      !mask
    | _ -> failwith "Expected tagged pointer type for mk_tag"
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
    (Bool, f e1 e2)

  let int i _ = (Int, F.int i)
  let read () _ = (Int, F.read ())
  let neg e m =
    let t, e = e m in
    (t, F.neg e)
  let ( + ) e1 e2 m = bin_op F.( + ) e1 e2 m
  let var v m = (StringMap.find (F.string_of_var v) m, F.var v)
  let fresh = F.fresh
  let var_of_string = F.var_of_string
  let string_of_var = F.string_of_var
  let lett v e b m =
    let typ, e = e m in
    let result_typ, b = b (StringMap.add (F.string_of_var v) typ m) in
    (result_typ, F.lett v e b)

  let t _ = (Bool, F.t)
  let f _ = (Bool, F.f)
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
  module ExpHList = HListFn (struct
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
  let void _ = (Void, F.has_type F.void Void)
  let vector hl m =
    let rec go : type a. a ExpHList.hlist -> typ list * a F.ExpHList.hlist =
      function
      | e :: xs ->
        let typ, e = e m in
        let res_typs, res_es = go xs in
        (typ :: res_typs, e :: res_es)
      | [] -> ([], [])
    in
    let res_typs, res_es = go hl in
    (Vector res_typs, F.has_type (F.vector res_es) (Vector res_typs))
  let vector_ref e ptr m =
    let (t : typ), e = e m in
    let typs =
      match t with
      | Vector typs -> typs
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
    (Void, F.has_type (F.vector_set e ptr v) Void)
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
  let collect i _ = (R3_Types.Int, F.has_type (F.collect i) Int)
  let allocate i ty _ = (ty, F.has_type (F.allocate i ty) ty)
  let global_value name _ = (R3_Types.Int, F.has_type (F.global_value name) Int)
end

module R3_Shrink_R_T (R : Chapter1.Reader) (F : R3_Shrink) = struct
  include Chapter4.R2_Shrink_R_T (R) (F)
  module ExpHList = HListFn (struct
    type 'a t = 'a exp
  end)
  let has_type e t r = F.has_type (e r) t
  let void _ = F.void
  let vector es r =
    let rec go : type t. t ExpHList.hlist -> t F.ExpHList.hlist = function
      | x :: xs ->
        let x = x r in
        x :: go xs
      | [] -> []
    in
    F.vector (go es)
  let vector_ref v ptr r = F.vector_ref (v r) ptr
  let vector_set v ptr e r =
    let v = v r in
    let e = e r in
    F.vector_set v ptr e
end

module R3_R_T (R : Chapter1.Reader) (F : R3) = struct
  include Chapter4.R2_R_T (R) (F)
  include R3_Shrink_R_T (R) (F)
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
  module ExpHList = HListFn (struct
    type 'a t = 'a exp
  end)
  let has_type e t = fwd @@ F.has_type (bwd e) t
  let void = fwd F.void
  let vector hl =
    let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
      | x :: xs -> bwd x :: go xs
      | [] -> []
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

module TransformLet (F : R3) : R3_Let with type 'a obs = 'a F.obs = struct
  module M = Chapter2_definitions.TransformLetPass (F)
  include R3_R_T (M.R) (F)
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

module ExposeAllocationPass (F : R3_Collect) = struct
  module IDelta
      (F' :
        R3_Collect
          with type 'a exp = R3_Types.typ StringMap.t -> R3_Types.typ * 'a F.exp) =
  struct
    open F'
    let vector_helper hl m =
      let rec go : type a.
          a ExpHList.hlist -> R3_Types.typ list * a F.ExpHList.hlist = function
        | e :: xs ->
          let typ, e = e m in
          let res_typs, res_es = go xs in
          (typ :: res_typs, e :: res_es)
        | [] -> ([], [])
      in
      go hl

    let vector : type tup. tup ExpHList.hlist -> tup exp =
     fun hl m ->
      let vtys, ves = vector_helper hl m in
      let ty = R3_Types.Vector vtys in
      let ty_size = R3_Types.allocation_size ty in
      let exp =
        let alloc = fresh () in
        lett (fresh ())
          (if_
             (global_value "free_ptr" + int ty_size
             < global_value "fromspace_end")
             void (collect ty_size))
        @@ lett alloc (allocate 1 ty)
        @@
        (* For every field set to the corresponding expression with vector_set *)
        let rec go : type r a.
            R3_Types.typ list -> r F.ExpHList.hlist -> (a, tup) ptr -> tup exp =
         fun tys hl ptr ->
          match (tys, hl) with
          | ty :: tys, e :: es ->
            let ptr = Obj.magic @@ Next ptr in
            lett (fresh ()) (vector_set (var alloc) ptr (fun _ -> (ty, e)))
            @@ go tys es ptr
          | _ -> var alloc
        in
        match (vtys, ves) with
        | ty :: tys, e :: es ->
          let ptr = Here in
          lett (fresh ()) (vector_set (var alloc) ptr (fun _ -> (ty, e)))
          @@ go tys es ptr
        | _ -> var alloc
      in
      exp m
  end
end
module ExposeAllocation (F : R3_Collect) :
  R3_Shrink with type 'a obs = 'a F.obs = struct
  module M = ExposeAllocationPass (F)
  module F' = R3_Collect_Annotate_Types (F)
  include F'
  include M.IDelta (F')
end

module type C2 = sig
  include Chapter4.C1
  val has_type : 'a exp -> R3_Types.typ -> 'a exp
  val allocate : int -> R3_Types.typ -> 'a exp
  val vector_ref : 'tup arg -> int -> 'a exp
  val vector_set : 'tup arg -> int -> 'a arg -> unit exp
  val global_value : string -> int exp
  val void : unit exp

  val collect : int -> unit stmt
  val program :
    ?locals:(string * R3_Types.typ) list ->
    (label * unit tail) list ->
    unit program
end

module C1_of_C2 (C2 : C2) = struct
  include C2
  let program ?locals body =
    let locals = Option.map (List.map (fun l -> (l, R3_Types.Void))) locals in
    program ?locals body
end

module C2_R_T (R : Chapter1.Reader) (F : C2) = struct
  include Chapter4.C1_R_T (R) (C1_of_C2 (F))
  let has_type e ty r = F.has_type (e r) ty
  let allocate i ty _ = F.allocate i ty
  let vector_ref v ptr r = F.vector_ref (v r) ptr
  let vector_set v ptr w r = F.vector_set (v r) ptr (w r)
  let global_value name _ = F.global_value name
  let void _ = F.void
  let collect i _ = F.collect i
  let program ?locals body () =
    let init = R.init () in
    let body = List.map (fun (l, t) -> (l, t init)) body in
    F.program ?locals body
end

module type X86_2 = sig
  include Chapter4.X86_1
  open Chapter2_definitions
  val global_value : string -> 'a arg
  val program :
    ?locals:R3_Types.typ StringMap.t ->
    ?stack_size:int ->
    ?root_stack_size:int ->
    ?conflicts:ArgSet.t ArgMap.t ->
    ?moves:ArgSet.t ArgMap.t ->
    (label * unit block) list ->
    unit program
end

module X86_1_of_X86_2 (X86 : X86_2) = struct
  include X86
  let program ?stack_size ?conflicts ?moves blocks =
    program ~locals:StringMap.empty ~root_stack_size:0 ?stack_size ?conflicts
      ?moves blocks
end

module X86_2_T
    (X_reg : Chapter1.TRANS)
    (X_arg : Chapter1.TRANS)
    (X_instr : Chapter1.TRANS)
    (X_block : Chapter1.TRANS)
    (X_program : Chapter1.TRANS)
    (F :
      X86_2
        with type 'a reg = 'a X_reg.from
         and type 'a arg = 'a X_arg.from
         and type 'a instr = 'a X_instr.from
         and type 'a block = 'a X_block.from
         and type 'a program = 'a X_program.from) =
struct
  include
    Chapter4.X86_1_T (X_reg) (X_arg) (X_instr) (X_block) (X_program)
      (X86_1_of_X86_2 (F))
  let global_value label = X_arg.fwd @@ F.global_value label
  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves blocks =
    X_program.fwd
    @@ F.program ?locals ?stack_size ?root_stack_size ?conflicts ?moves
    @@ List.map (fun (l, b) -> (l, X_block.bwd b)) blocks
end

module X86_2_R_T (R : Chapter1.Reader) (F : X86_2) :
  X86_2
    with type 'a reg = R.t -> 'a F.reg
     and type 'a arg = R.t -> 'a F.arg
     and type 'a instr = R.t -> 'a F.instr
     and type 'a block = R.t -> 'a F.block
     and type 'a program = unit -> 'a F.program
     and type label = F.label
     and type 'a obs = 'a F.obs = struct
  module M = X86_1_of_X86_2 (F)
  include Chapter4.X86_1_R_T (R) (M)
  let global_value label _ = F.global_value label
  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves blocks () =
    let init = R.init () in
    F.program ?locals ?stack_size ?root_stack_size ?conflicts ?moves
      (List.map (fun (l, b) -> (l, b init)) blocks)
end

module ExplicateControl (F : R3_Collect) (C2 : C2) () = struct
  include Chapter4.ExplicateControl (F) (C1_of_C2 (C2)) ()
  module ExpHList = HListFn (struct
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
         ( tmp,
           fun () ->
             convert_exp C2.(vector_ref (var (lookup tmp)) (ptr_num ptr)) m r ))
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
                          vector_set
                            (var (lookup tmp1))
                            (ptr_num ptr)
                            (var (lookup tmp2)))
                        m r )) ))

  let collect i _ = function
    | Tail -> C2.(collect i @> return void)
    | Assign (_, body) -> C2.(collect i @> body ())
    | Pred _ ->
      failwith "Garbage collection isn't a boolean used for short circuiting"
  let allocate i ty = convert_exp (C2.allocate i ty)
  let global_value name = convert_exp (C2.global_value name)
end

module StringHashtbl = Chapter2_passes.StringHashtbl
module UncoverLocalsPass (F : C2) = struct
  module R = struct
    type t = string option * R3_Types.typ StringHashtbl.t
    let init () = (None, StringHashtbl.create 100)
    let compare (a, _) (b, _) =
      match Int.compare (String.length a) (String.length b) with
      | 0 -> String.compare a b
      | c -> c
  end

  module IDelta = struct
    let assign v e (_, tbl) = F.assign v (e (Some v, tbl))
    let has_type e ty = function
      | Some v, tbl ->
        StringHashtbl.add tbl v ty;
        e (None, tbl)
      | None, tbl -> e (None, tbl)

    let program ?locals:_ body () =
      let ((_, table) as init) = R.init () in
      let body = List.map (fun (l, t) -> (l, t init)) body in
      let locals =
        StringHashtbl.to_seq table |> List.of_seq |> List.sort R.compare
      in
      F.(program ~locals body)
  end
end
module UncoverLocals (F : C2) : C2 with type 'a obs = 'a F.obs = struct
  module M = UncoverLocalsPass (F)
  include C2_R_T (M.R) (F)
  include M.IDelta
end

module SelectInstructions (F : C2) (X86 : X86_2) :
  C2 with type 'a obs = unit X86.obs = struct
  module C1 = C1_of_C2 (F)
  include Chapter4.SelectInstructions (C1) (X86_1_of_X86_2 (X86))
  let has_type e _ ctx = e ctx
  let allocate len typ =
    let off = Int.(8 * add len 1) in
    let tag = R3_Types.mk_tag typ in
    let create lhs =
      X86.
        [
          movq (int tag) (deref r11 0);
          movq lhs (reg r11);
          addq (int off) (global_value "free_ptr");
          movq (global_value "free_ptr") lhs;
        ]
    in
    function
    | Assign v -> create (X86.var v)
    | Return -> create X86.(reg rax)
    | If _ -> failwith "allocate cannot be used in an if statement"
  let vector_ref (_, vec) n =
    let off = Int.(8 * add n 1) in
    function
    | Assign v -> X86.[ movq (deref r11 off) (var v); movq vec (reg r11) ]
    | Return -> X86.[ movq (deref r11 off) (reg rax); movq vec (reg r11) ]
    | If (t, f) ->
      X86.
        [ jmp t; jmp_if E f; cmpq (int 0) (deref r11 off); movq vec (reg r11) ]
  let vector_set (_, vec) n (_, arg) =
    let off = Int.(8 * add n 1) in
    function
    | Assign v ->
      X86.[ movq (int 0) (var v); movq arg (deref r11 off); movq vec (reg r11) ]
    | Return ->
      X86.
        [ movq (int 0) (reg rax); movq arg (deref r11 off); movq vec (reg r11) ]
    | If (_t, f) -> X86.[ jmp f; movq arg (deref r11 off); movq vec (reg r11) ]
  let global_value name = function
    | Assign v -> X86.[ movq (global_value name) (var v) ]
    | Return -> X86.[ movq (global_value name) (reg rax) ]
    | If (t, f) -> X86.[ jmp t; jmp_if E f; cmpq (int 0) (global_value name) ]
  let collect i =
    X86.[ callq "collect"; movq (int i) (reg rsi); movq (reg r15) (reg rdi) ]
  let void = arg (int 0)
  let program ?(locals = []) body =
    let locals = StringMap.of_list locals in
    let body = List.map (fun (l, t) -> (l, X86.block (List.rev t))) body in
    let exit_block = (exit_label, X86.(block [ retq ])) in
    X86.program ~locals (exit_block :: body)
end

module UncoverLive (F : X86_2) : X86_2 with type 'a obs = 'a F.obs = struct
  module M = Chapter4.UncoverLivePass (X86_1_of_X86_2 (F))
  include X86_2_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves blocks =
    let blocks = program_helper blocks in
    F.program ?locals ?stack_size ?root_stack_size ?conflicts ?moves blocks
end

module ArgSet = Chapter2_definitions.ArgSet
module ArgMap = Chapter2_definitions.ArgMap
module GraphUtils = Chapter3.GraphUtils
module BuildInterferencePass (X86 : X86_2) = struct
  include Chapter4.BuildInterferencePass (X86_1_of_X86_2 (X86))
  module IDelta = struct
    include IDelta

    let callee_saves = X86.[ rbx; r12; r13; r14; r15 ]

    include Chapter2_definitions.X86_Reg_String (X86_1_of_X86_2 (X86))

    let program ?(locals = StringMap.empty) ?stack_size ?root_stack_size
        ?conflicts:_ ?moves blocks =
      let interference_graph =
        (* If a vector typed variable is live during a call to the collector,
           it must be spilled to ensure it is visible to the collector.
           This is done by adding interferences for vector typed variables
           to all callee save registers so it must be spilled into a stack slot.
           Also, to prevent root stack slots sharing colors with stack slots,
           interferences are added between all vector typed variables and
           non vector typed variables.
         *)
        let non_pointer_locals =
          locals |> StringMap.bindings
          |> List.filter_map (function
               | _, R3_Types.Vector _ -> None
               | v, _ -> Some v)
        in
        let add_pointer_interferences var typ graph =
          match typ with
          | R3_Types.Vector _ ->
            let add_register_interference acc reg =
              GraphUtils.add_interference
                (Reg (string_of_reg reg))
                (Var var) acc
            in
            let add_var_interference acc var' =
              GraphUtils.add_interference (Var var') (Var var) acc
            in
            List.fold_left add_var_interference
              (List.fold_left add_register_interference graph callee_saves)
              non_pointer_locals
          | _ -> ArgMap.add (Var var) ArgSet.empty graph
        in
        StringMap.fold add_pointer_interferences locals init_interference_graph
      in
      let interference_graph =
        List.fold_left
          (fun graph (_, (f, _)) -> f graph)
          interference_graph blocks
      in
      let blocks = List.map (fun (l, (_, block)) -> (l, block)) blocks in
      X86.program ~locals ?stack_size ?root_stack_size
        ~conflicts:interference_graph ?moves blocks
  end
end
module BuildInterference (F : X86_2) = struct
  module M = BuildInterferencePass (F)
  include X86_2_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module BuildMoves (F : X86_2) : X86_2 with type 'a obs = 'a F.obs = struct
  module M = Chapter4.BuildMovesPass (X86_1_of_X86_2 (F))
  include X86_2_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves:_ blocks =
    let moves, blocks = program_helper blocks in
    F.program ?locals ?stack_size ?root_stack_size ?conflicts ~moves blocks
end

module AllocateRegistersPass (X86 : X86_2) = struct
  include Chapter3.AllocateRegistersPass (X86_1_of_X86_2 (X86))
  module IDelta = struct
    include IDelta
    open Chapter2_definitions
    let regs = X86.[| rbx; rcx; rdx; rsi; rdi; r8; r9; r10; r12; r13; r14 |]
    let reg_of_color root_stack_size stack_size color_slot_table regs typ color
        =
      if color < Array.length regs then
        X86.reg regs.(color)
      else
        match typ with
        | R3_Types.Vector _ ->
          spill root_stack_size color_slot_table X86.r15 color
        | _ -> spill stack_size color_slot_table X86.rbp color

    include Chapter2_definitions.X86_Reg_String (X86_1_of_X86_2 (X86))

    let program ?(locals = StringMap.empty) ?stack_size:_ ?root_stack_size:_
        ?(conflicts = ArgMap.empty) ?(moves = ArgMap.empty) blocks () =
      let root_stack_size = ref 0 in
      let stack_size = ref 0 in
      let color_slot_table : (int, int) Hashtbl.t = Hashtbl.create 100 in
      (* Remove rax, r11, and r15 from the interference graph *)
      let rax = Arg.Reg (string_of_reg X86.rax) in
      let r11 = Arg.Reg (string_of_reg X86.r11) in
      let r15 = Arg.Reg (string_of_reg X86.r15) in
      let conflicts =
        conflicts |> ArgMap.remove rax |> ArgMap.remove r11 |> ArgMap.remove r15
        |> ArgMap.map (ArgSet.remove rax)
        |> ArgMap.map (ArgSet.remove r11)
        |> ArgMap.map (ArgSet.remove r15)
      in
      let vars = ArgMap.keys conflicts in
      let colors = GraphUtils.color_graph moves conflicts vars in
      let get_arg v =
        let color = ArgMap.find_var v colors in
        let typ = StringMap.find v locals in
        reg_of_color root_stack_size stack_size color_slot_table regs typ color
      in
      let blocks =
        try List.map (fun (l, b) -> (l, b ())) blocks
        with effect Rename v, k -> Effect.Deep.continue k (get_arg v)
      in
      X86.program ~locals ~stack_size:!stack_size
        ~root_stack_size:!root_stack_size ~conflicts ~moves blocks
  end
end
module AllocateRegisters (X86 : X86_2) : X86_2 with type 'a obs = 'a X86.obs =
struct
  module M = AllocateRegistersPass (X86)
  include X86_2_R_T (M.X_reader) (X86)
  include M.IDelta
end
module PatchInstructionsPass (X86 : X86_2) = struct
  include Chapter4.PatchInstructionsPass (X86_1_of_X86_2 (X86))
  module IDelta = struct
    include IDelta
    let global_value n =
      (ArgInfo.MemoryReference (Hashtbl.hash (X86.rdi, n)), X86.global_value n)
  end
end
module PatchInstructions (F : X86_2) : X86_2 with type 'a obs = 'a F.obs =
struct
  module M = PatchInstructionsPass (F)
  include X86_2_T (M.X_reg) (M.X_arg) (M.X_instr) (M.X_block) (M.X_program) (F)
  include M.IDelta
end

module R3_Pretty () = struct
  include Chapter4.R2_Shrink_Pretty ()
  module ExpHList = HListFn (struct
    type 'a t = 'a exp
  end)

  let has_type e ty = "(has-type " ^ e ^ " " ^ R3_Types.show_typ ty ^ ")"
  let void = "(void)"
  let vector hl =
    let rec go : type r. r ExpHList.hlist -> string = function
      | x :: xs -> " " ^ x ^ go xs
      | [] -> ""
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
  let vector_ref v n = "(vector-ref " ^ v ^ " " ^ string_of_int n ^ ")"
  let vector_set v n r =
    "(vector-set! " ^ v ^ " " ^ string_of_int n ^ " " ^ r ^ ")"
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

module X86_2_Pretty = struct
  include Chapter4.X86_1_Pretty
  let global_value label = "(global-value " ^ label ^ ")"
  let locals_info = function
    | Some locals ->
      let locals = StringMap.bindings locals in
      let pp_pair fmt (lab, typ) =
        Format.fprintf fmt "(%s . %a)" lab R3_Types.pp_typ typ
      in
      Format.asprintf "(locals . %a)" (Format.pp_print_list pp_pair) locals
    | None -> ""
  let root_stack_info = function
    | Some stack_size -> "(root_stack_size . " ^ string_of_int stack_size ^ ")"
    | None -> ""

  let program ?locals ?stack_size ?root_stack_size ?conflicts ?moves body =
    let info =
      enclose @@ locals_info locals
      ^ root_stack_info root_stack_size
      ^ program_info stack_size conflicts moves
    in
    program_helper info body
end

module X86_2_Printer = struct
  include Chapter4.X86_1_Printer

  let global_value label = label ^ "(%rip)"

  let root_stack_total_size = 16384
  let root_stack_heap_size = 16

  let program_info stack_size root_stack_size =
    let add_root_stack (header, footer) =
      match root_stack_size with
      | Some stack_size ->
        ( header
          @ [
              movq (int root_stack_total_size) rdi;
              movq (int root_stack_heap_size) rsi;
              callq "initialize";
              movq (global_value "rootstack_begin") r15;
              movq (int 0) (deref r15 0);
              addq (int stack_size) r15;
            ],
          footer @ [ subq (int stack_size) r15 ] )
      | None -> (header, footer)
    in
    Option.map add_root_stack (function_prologue_epilogue stack_size)

  let program_helper stack_size root_stack_size blocks =
    blocks
    |> List.concat_map (fun (label, block) -> (label ^ ":\n") :: block)
    |> apply_header_footer (program_info stack_size root_stack_size)

  let program ?locals:_ ?stack_size ?root_stack_size ?conflicts:_ ?moves:_
      blocks =
    String.concat "\n"
    @@ [ ".global main"; ".text"; "main:" ]
    @ program_helper stack_size root_stack_size blocks
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
    let* t1 = vector [ int 1; t ] in
    let* t2 = var t1 in
    let* _ = vector_set (var t2) Here (int 42) in
    let* _ = vector_set (var t2) (Next Here) f in
    vector_ref (var t1) Here
end

module Ex2 (F : R3) = struct
  open F
  let res =
    observe @@ program
    @@ vector_ref (vector_ref (vector [ vector [ int 42 ] ]) Here) Here
end

module Ex3 (F : R3_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let* v =
      vector
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
    {| Ex1: (program (has-type (let ([tmp0 (has-type (let ([tmp7 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 24 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 24) Int)) Void)]) (has-type (let ([tmp4 (has-type (allocate 1 (Vector [Int; Bool])) (Vector [Int; Bool]))]) (has-type (let ([tmp6 (has-type (vector-set! (has-type (var tmp4) (Vector [Int; Bool])) 0 (has-type 1 Int)) Void)]) (has-type (let ([tmp5 (has-type (vector-set! (has-type (var tmp4) (Vector [Int; Bool])) 1 (has-type t Bool)) Void)]) (has-type (var tmp4) (Vector [Int; Bool]))) (Vector [Int; Bool]))) (Vector [Int; Bool]))) (Vector [Int; Bool]))) (Vector [Int; Bool]))]) (has-type (let ([tmp1 (has-type (var tmp0) (Vector [Int; Bool]))]) (has-type (let ([tmp2 (has-type (vector-set! (has-type (var tmp1) (Vector [Int; Bool])) 0 (has-type 42 Int)) Void)]) (has-type (let ([tmp3 (has-type (vector-set! (has-type (var tmp1) (Vector [Int; Bool])) 1 (has-type f Bool)) Void)]) (has-type (vector-ref (has-type (var tmp0) (Vector [Int; Bool])) 0) Int)) Int)) Int)) Int)) Int)) |}]

let%expect_test "Ex0 annotate types twice" =
  let module M =
    Ex0
      (TransformLet
         (Shrink
            (R3_Collect_Annotate_Types
               (R3_Collect_Annotate_Types (R3_Collect_Pretty ()))))) in
  Format.printf "Ex0: %s\n" M.res;
  [%expect
    {| Ex0: (program (has-type (let ([tmp0 (has-type 1 Int)]) (has-type (+ (has-type (var tmp0) Int) (has-type 2 Int)) Int)) Int)) |}]

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
    {| Ex3: (program (has-type (let ([tmp1 (has-type (let ([tmp6 (has-type (if (has-type (< (has-type (+ (has-type (global-value free_ptr) Int) (has-type 16 Int)) Int) (has-type (global-value fromspace_end) Int)) Bool) (has-type (void) Void) (has-type (collect 16) Int)) Void)]) (has-type (let ([tmp4 (has-type (allocate 1 (Vector [Int])) (Vector [Int]))]) (has-type (let ([tmp5 (has-type (vector-set! (has-type (var tmp4) (Vector [Int])) 0 (has-type (let ([tmp0 (has-type 1 Int)]) (has-type (+ (has-type (var tmp0) Int) (has-type 2 Int)) Int)) Int)) Void)]) (has-type (var tmp4) (Vector [Int]))) (Vector [Int]))) (Vector [Int]))) (Vector [Int]))]) (has-type (let ([tmp3 (has-type (vector-set! (has-type (var tmp1) (Vector [Int])) 0 (has-type (let ([tmp2 (has-type 2 Int)]) (has-type (+ (has-type (var tmp2) Int) (has-type 1 Int)) Int)) Int)) Void)]) (has-type (vector-ref (has-type (var tmp1) (Vector [Int])) 0) Int)) Int)) Int)) |}]

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
    Ex1: (program ((locals . ())) ((start . (seq (assign tmp8 (has-type (global-value free_ptr) Int)) (seq (assign tmp9 (has-type 24 Int)) (seq (assign tmp19 (+ tmp8 tmp9)) (seq (assign tmp20 (has-type (global-value fromspace_end) Int)) (if (has-type (< tmp19 tmp20) Bool) block_t3 block_f4))))))
    (block_t3 . (goto block_t1))
    (block_f2 . (seq (collect 24) (goto block_body0)))
    (block_body0 . (seq (assign tmp4 (has-type (allocate 1 (Vector [Int; Bool])) (Vector [Int; Bool]))) (seq (assign tmp11 (has-type 1 Int)) (seq (assign tmp6 (has-type (vector-set! tmp4 0 tmp11) Void)) (seq (assign tmp13 (has-type t Bool)) (seq (assign tmp5 (has-type (vector-set! tmp4 1 tmp13) Void)) (seq (assign tmp15 (has-type 42 Int)) (seq (assign tmp2 (has-type (vector-set! tmp4 0 tmp15) Void)) (seq (assign tmp17 (has-type f Bool)) (seq (assign tmp3 (has-type (vector-set! tmp4 1 tmp17) Void)) (return (has-type (vector-ref tmp4 0) Int))))))))))))
    (block_t1 . (seq (assign tmp7 (has-type (void) Void)) (goto block_body0)))
    (block_f4 . (goto block_f2)))
    |}]

let%expect_test "Ex1 uncover locals" =
  let module M =
    Ex1
      (TransformLet
         (Shrink
            (ExposeAllocation
               (RemoveComplex
                  (ExplicateControl
                     (R3_Collect_Pretty ())
                     (UncoverLocals (C2_Pretty))
                     ()))))) in
  Format.printf "Ex1: %s\n" M.res;
  [%expect
    {|
    Ex1: (program ((locals . ((tmp2 . Void) (tmp3 . Void) (tmp4 . (Vector [Int; Bool])) (tmp5 . Void) (tmp6 . Void) (tmp7 . Void) (tmp8 . Int) (tmp9 . Int) (tmp11 . Int) (tmp13 . Bool) (tmp15 . Int) (tmp17 . Bool) (tmp20 . Int)))) ((start . (seq (assign tmp8 (global-value free_ptr)) (seq (assign tmp9 24) (seq (assign tmp19 (+ tmp8 tmp9)) (seq (assign tmp20 (global-value fromspace_end)) (if (< tmp19 tmp20) block_t3 block_f4))))))
    (block_t3 . (goto block_t1))
    (block_f2 . (seq (collect 24) (goto block_body0)))
    (block_body0 . (seq (assign tmp4 (allocate 1 (Vector [Int; Bool]))) (seq (assign tmp11 1) (seq (assign tmp6 (vector-set! tmp4 0 tmp11)) (seq (assign tmp13 t) (seq (assign tmp5 (vector-set! tmp4 1 tmp13)) (seq (assign tmp15 42) (seq (assign tmp2 (vector-set! tmp4 0 tmp15)) (seq (assign tmp17 f) (seq (assign tmp3 (vector-set! tmp4 1 tmp17)) (return (vector-ref tmp4 0))))))))))))
    (block_t1 . (seq (assign tmp7 (void)) (goto block_body0)))
    (block_f4 . (goto block_f2)))
    |}]

(* Utility function for printing integers as binary for testing the tag creation *)
let int2bin =
  let int_size = Sys.int_size in
  let buf = Bytes.create int_size in
  fun n ->
    for i = 0 to int_size - 1 do
      let pos = int_size - 1 - i in
      Bytes.set buf pos (if n land (1 lsl i) != 0 then '1' else '0')
    done;
    (* skip leading zeros *)
    match Bytes.index_opt buf '1' with
    | None -> "0b0"
    | Some i -> "0b" ^ Bytes.sub_string buf i (int_size - i)

let%expect_test "Tag for vector 1" =
  let open R3_Types in
  let typ =
    Vector [ Vector [ Int ]; Int; Vector [ Bool; Void ]; Bool; Void; Vector [] ]
  in
  let tag = R3_Types.mk_tag typ in
  Format.printf "Tag: %s" (int2bin tag);
  [%expect {| Tag: 0b1001010001101 |}]

let%expect_test "Ex2 allocate registers" =
  let module M =
    Ex2
      (TransformLet
         (Shrink
            (ExposeAllocation
               (RemoveComplex
                  (R3_Collect_Annotate_Types
                     (ExplicateControl
                        (R3_Collect_Pretty ())
                        (UncoverLocals
                           (SelectInstructions
                              (C2_Pretty)
                              (UncoverLive
                                 (BuildInterference
                                    (BuildMoves
                                       (AllocateRegisters
                                          (PatchInstructions (X86_2_Printer))))))))
                        ())))))) in
  Format.printf "Ex2: %s" M.res;
  [%expect
    {|
    Ex2: .global main
    .text
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
      addq $8, %r15
    start:

      movq free_ptr(%rip), %rcx
      movq $24, %rbx
      addq %rbx, %rcx
      movq fromspace_end(%rip), %rbx
      cmpq %rbx, %rcx
      jl block_t8
      jmp block_f9
    block_t8:

      jmp block_t6
    block_f9:

      jmp block_f7
    block_t6:

      movq $0, %rbx
      jmp block_body5
    block_f7:

      movq %r15, %rdi
      movq $24, %rsi
      callq collect
      jmp block_body5
    block_body5:

      movq free_ptr(%rip), %rax
      movq %rax, -8(%r15)
      addq $16, free_ptr(%rip)
      movq -8(%r15), %r11
      movq $131, (%r11)
      movq free_ptr(%rip), %rcx
      movq $16, %rbx
      addq %rbx, %rcx
      movq fromspace_end(%rip), %rbx
      cmpq %rbx, %rcx
      jl block_t3
      jmp block_f4
    block_t3:

      jmp block_t1
    block_f4:

      jmp block_f2
    block_t1:

      movq $0, %rbx
      jmp block_body0
    block_f2:

      movq %r15, %rdi
      movq $16, %rsi
      callq collect
      jmp block_body0
    block_body0:

      movq free_ptr(%rip), %rbx
      addq $16, free_ptr(%rip)
      movq %rbx, %r11
      movq $3, (%r11)
      movq $42, %rcx
      movq %rbx, %r11
      movq %rcx, 8(%r11)
      movq $0, %rcx
      movq -8(%r15), %r11
      movq %rbx, 8(%r11)
      movq $0, %rbx
      movq -8(%r15), %r11
      movq 8(%r11), %rbx
      movq %rbx, %r11
      movq 8(%r11), %rax
      jmp block_exit
    block_exit:

      popq %r14
      popq %r13
      popq %rbx
      popq %r12
      movq %rbp, %rsp
      popq %rbp
      subq $8, %r15
      retq
    |}]

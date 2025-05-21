module R4_Types = struct
  include Chapter5.R3_Types

  type typ =
    [ Chapter5.R3_Types.typ
    | `Fn of typ list * typ
    ]
  [@@deriving show]
end

module type LIMIT = sig
  module HList : Chapter5.HLIST
  open HList

  type _ limit =
    | LX :
        'a el * 'b el * 'c el * 'd el * 'e el * ('f * 'g) el
        -> ('a * ('b * ('c * ('d * ('e * ('f * 'g)))))) limit
    | L6 :
        'a el * 'b el * 'c el * 'd el * 'e el * 'f el
        -> ('a * ('b * ('c * ('d * ('e * ('f * unit)))))) limit
    | L5 :
        'a el * 'b el * 'c el * 'd el * 'e el
        -> ('a * ('b * ('c * ('d * ('e * unit))))) limit
    | L4 :
        'a el * 'b el * 'c el * 'd el
        -> ('a * ('b * ('c * ('d * unit)))) limit
    | L3 : 'a el * 'b el * 'c el -> ('a * ('b * ('c * unit))) limit
    | L2 : 'a el * 'b el -> ('a * ('b * unit)) limit
    | L1 : 'a el -> ('a * unit) limit
    | L0 : unit limit

  type convert = { f : 'a. 'a hlist -> 'a el }
  val transform : convert -> 't hlist -> 't limit
end

module LimitFn (HList : Chapter5.HLIST) = struct
  module HList = HList
  open HList

  type _ limit =
    | LX :
        'a el * 'b el * 'c el * 'd el * 'e el * ('f * 'g) el
        -> ('a * ('b * ('c * ('d * ('e * ('f * 'g)))))) limit
    | L6 :
        'a el * 'b el * 'c el * 'd el * 'e el * 'f el
        -> ('a * ('b * ('c * ('d * ('e * ('f * unit)))))) limit
    | L5 :
        'a el * 'b el * 'c el * 'd el * 'e el
        -> ('a * ('b * ('c * ('d * ('e * unit))))) limit
    | L4 :
        'a el * 'b el * 'c el * 'd el
        -> ('a * ('b * ('c * ('d * unit)))) limit
    | L3 : 'a el * 'b el * 'c el -> ('a * ('b * ('c * unit))) limit
    | L2 : 'a el * 'b el -> ('a * ('b * unit)) limit
    | L1 : 'a el -> ('a * unit) limit
    | L0 : unit limit

  type convert = { f : 'a. 'a hlist -> 'a el }

  let transform (type t) conv (xs : t hlist) : t limit =
    match xs with
    | [ a; b; c; d; e; f ] -> L6 (a, b, c, d, e, f)
    | a :: b :: c :: d :: e :: f :: g -> LX (a, b, c, d, e, conv.f (f :: g))
    | [ a; b; c; d; e ] -> L5 (a, b, c, d, e)
    | [ a; b; c; d ] -> L4 (a, b, c, d)
    | [ a; b; c ] -> L3 (a, b, c)
    | [ a; b ] -> L2 (a, b)
    | [ a ] -> L1 a
    | [] -> L0
end

module type R4_Shrink = sig
  include Chapter5.R3_Shrink
  module ExpLimitList : LIMIT with module HList = ExpHList
  module VarHList : Chapter5.HLIST with type 'a el = 'a var
  module VarLimitList : LIMIT with module HList = VarHList
  type 'a def

  val app : ('tup -> 'a) exp -> 'tup ExpLimitList.limit -> 'a exp
  val define :
    ('tup -> 'a) var -> 'tup VarLimitList.limit -> 'a exp -> 'b def -> 'b def
  val body : 'a exp -> 'a def
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
      realized : 'r UnitHList.hlist;
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
    'r UnitHList.hlist -> ('r VarHList.hlist -> 'a exp) -> ('r, 'a) Wrapped.t
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
  let program e = F.program (body e)
end

module R3_of_R4 (F : R4) = struct
  include F
  let program e = F.program (body e)
end

module R3_of_F1_Collect (F : F1_Collect) = struct
  include F
  let program e = F.program (body e)
end

module R4_Shrink_R_T (R : Chapter1.Reader) (F : R4_Shrink) = struct
  include Chapter5.R3_Shrink_R_T (R) (R3_of_R4_Shrink (F))
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = F.VarHList
  module VarLimitList = F.VarLimitList
  type 'a def = R.t -> 'a F.def

  let app e es r =
    let go : type t. t ExpLimitList.limit -> t F.ExpLimitList.limit = function
      | ExpLimitList.LX (a, b, c, d, e, f) ->
        F.ExpLimitList.LX (a r, b r, c r, d r, e r, f r)
      | ExpLimitList.L6 (a, b, c, d, e, f) ->
        F.ExpLimitList.L6 (a r, b r, c r, d r, e r, f r)
      | ExpLimitList.L5 (a, b, c, d, e) ->
        F.ExpLimitList.L5 (a r, b r, c r, d r, e r)
      | ExpLimitList.L4 (a, b, c, d) -> F.ExpLimitList.L4 (a r, b r, c r, d r)
      | ExpLimitList.L3 (a, b, c) -> F.ExpLimitList.L3 (a r, b r, c r)
      | ExpLimitList.L2 (a, b) -> F.ExpLimitList.L2 (a r, b r)
      | ExpLimitList.L1 e -> F.ExpLimitList.L1 (e r)
      | ExpLimitList.L0 -> F.ExpLimitList.L0
    in
    let e = e r in
    let es = go es in
    F.app e es

  let define v vs e rest r =
    let e = e r in
    let rest = rest r in
    F.define v vs e rest

  let body e r = F.body (e r)
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
    let go : type r. r ExpLimitList.limit -> r F.ExpLimitList.limit = function
      | ExpLimitList.LX (a, b, c, d, e, f) ->
        F.ExpLimitList.LX (bwd a, bwd b, bwd c, bwd d, bwd e, bwd f)
      | ExpLimitList.L6 (a, b, c, d, e, f) ->
        F.ExpLimitList.L6 (bwd a, bwd b, bwd c, bwd d, bwd e, bwd f)
      | ExpLimitList.L5 (a, b, c, d, e) ->
        F.ExpLimitList.L5 (bwd a, bwd b, bwd c, bwd d, bwd e)
      | ExpLimitList.L4 (a, b, c, d) ->
        F.ExpLimitList.L4 (bwd a, bwd b, bwd c, bwd d)
      | ExpLimitList.L3 (a, b, c) -> F.ExpLimitList.L3 (bwd a, bwd b, bwd c)
      | ExpLimitList.L2 (a, b) -> F.ExpLimitList.L2 (bwd a, bwd b)
      | ExpLimitList.L1 e -> F.ExpLimitList.L1 (bwd e)
      | ExpLimitList.L0 -> F.ExpLimitList.L0
    in
    fwd @@ F.app (bwd f) (go es)
  let define v vs body rest =
    X_def.fwd @@ F.define v vs (bwd body) (X_def.bwd rest)
  let body e = X_def.fwd @@ F.body (bwd e)
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

module F1_R_T (R : Chapter1.Reader) (F : F1) :
  F1
    with type 'a exp = R.t -> 'a F.exp
     and type 'a def = R.t -> 'a F.def
     and type 'a program = unit -> 'a F.program
     and type 'a var = 'a F.var
     and type 'a obs = 'a F.obs
     and module VarHList = F.VarHList = struct
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
  include F1_T (X_exp) (X_def) (X_program) (F)
  include Chapter5.R3_Collect_T (X_exp) (X_program) (R3_of_F1_Collect (F))
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
        realized : 'r UnitHList.hlist;
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
    let ( @> ) realized fn = Wrapped.{ realized; fn }
    let ( @@> ) realized fn = Wrapped2.{ realized; fn }

    let ( $ ) f es r =
      let f = f r in
      let rec go : type r. r ExpHList.hlist -> r F.ExpHList.hlist = function
        | ExpHList.(x :: xs) -> F.ExpHList.(x r :: go xs)
        | ExpHList.[] -> F.ExpHList.[]
      in
      let es = F.ExpLimitList.transform { f = (fun l -> F.vector l) } (go es) in
      F.app f es

    let var v r = r.R.to_exp (F.string_of_var v)

    let let_helper var f g r =
      let rec go : type r. r UnitHList.hlist -> r F.VarHList.hlist = function
        | UnitHList.(_ :: xs) -> F.VarHList.(F.fresh () :: go xs)
        | UnitHList.[] -> F.VarHList.[]
      in
      let params = go f.Wrapped.realized in
      let tuple_handler (type r) (l : r F.VarHList.hlist) : r F.var =
        let tuple_var = F.fresh () in
        let rec go : type a tup t.
            t F.VarHList.hlist * (a, tup) Chapter5.ptr -> unit = function
          | F.VarHList.(x :: xs), ptr ->
            let x : string = F.string_of_var x in
            let old_handler = r.R.to_exp in
            r.to_exp <-
              (fun v ->
                if Stdlib.( = ) x v then
                  F.vector_ref (F.var tuple_var) (Obj.magic ptr)
                else
                  old_handler v);
            go (xs, Chapter5.Next ptr)
          | F.VarHList.[], _ -> ()
        in
        go (l, Here);
        tuple_var
      in
      let params' = F.VarLimitList.transform { f = tuple_handler } params in
      let body = f.fn params r in
      let rest = g var r in
      F.define var params' body rest

    let ( let@ ) f g r = let_helper (F.fresh ()) f g r

    let ( let@@ ) f g r =
      let rec go : type r. r UnitHList.hlist -> r F.VarHList.hlist = function
        | UnitHList.(_ :: xs) -> F.VarHList.(F.fresh () :: go xs)
        | UnitHList.[] -> F.VarHList.[]
      in
      let vars = go f.Wrapped2.realized in
      let fns = f.fn vars in
      let rest = g vars r in
      let rec go : type r. r FnHList.hlist * r F.VarHList.hlist -> 'a F.def =
        function
        | FnHList.(wrapped :: xs), F.VarHList.(v :: vs) ->
          let_helper v wrapped (fun _ -> fun _ -> go (xs, vs)) r
        | FnHList.[], F.VarHList.[] -> rest
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
    let body e = F.define (F.var_of_string "main") L0 e (F.endd ())
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
    let define v params body rest is_function =
      StringHashtbl.add is_function (F.string_of_var v) ();
      let rest = rest is_function in
      let body = body is_function in
      F.define v params body rest
  end
end
module RevealFunctions (F : F1) : R4_Shrink with type 'a obs = 'a F.obs = struct
  module M = RevealFunctionsPass (F)
  include R4_Shrink_R_T (M.R) (F)
  include M.IDelta
end

module R4_Shrink_Pretty () = struct
  include Chapter5.R3_Pretty ()
  type 'a def = string
  module ExpLimitList = LimitFn (ExpHList)
  module VarHList = Chapter5.HListFn (struct
    type 'a t = 'a var
  end)
  module VarLimitList = LimitFn (VarHList)

  let rec showList = function
    | x :: xs -> " " ^ x ^ showList xs
    | [] -> ""

  let app fexp es =
    let go : type a. a ExpLimitList.limit -> string = function
      | ExpLimitList.LX (a, b, c, d, e, f) -> showList [ a; b; c; d; e; f ]
      | ExpLimitList.L6 (a, b, c, d, e, f) -> showList [ a; b; c; d; e; f ]
      | ExpLimitList.L5 (a, b, c, d, e) -> showList [ a; b; c; d; e ]
      | ExpLimitList.L4 (a, b, c, d) -> showList [ a; b; c; d ]
      | ExpLimitList.L3 (a, b, c) -> showList [ a; b; c ]
      | ExpLimitList.L2 (a, b) -> showList [ a; b ]
      | ExpLimitList.L1 e -> showList [ e ]
      | ExpLimitList.L0 -> showList []
    in
    "(" ^ fexp ^ go es ^ ")"

  let define v vs e rest =
    let go : type a. a VarLimitList.limit -> string = function
      | VarLimitList.LX (a, b, c, d, e, f) -> showList [ a; b; c; d; e; f ]
      | VarLimitList.L6 (a, b, c, d, e, f) -> showList [ a; b; c; d; e; f ]
      | VarLimitList.L5 (a, b, c, d, e) -> showList [ a; b; c; d; e ]
      | VarLimitList.L4 (a, b, c, d) -> showList [ a; b; c; d ]
      | VarLimitList.L3 (a, b, c) -> showList [ a; b; c ]
      | VarLimitList.L2 (a, b) -> showList [ a; b ]
      | VarLimitList.L1 e -> showList [ e ]
      | VarLimitList.L0 -> showList []
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

module Ex1 (F : R4_Let) = struct
  open F

  let res =
    observe @@ program
    @@
    let@ map_vec =
      [ (); () ] @> fun [ f; v ] ->
      vector
        [
          var f $ [ vector_ref (var v) Here ];
          var f $ [ vector_ref (var v) (Next Here) ];
        ]
    in
    let@ add1 = [ () ] @> fun [ x ] -> var x + int 1 in
    body
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
          [ () ] @> fun [ v ] ->
          if_ (var v = int 0) t (var is_odd $ [ var v - int 1 ])
        end;
        begin
          [ () ] @> fun [ v ] ->
          if_ (var v = int 0) f (var is_even $ [ var v - int 1 ])
        end;
      ]
    in
    body (var is_even $ [ int 24 ])
end

module Ex3 (F : R4_Let) = struct
  open F
  let res =
    observe @@ program
    @@
    let@ add =
      [ (); (); (); (); (); (); () ] @> fun [ a; b; c; d; e; f; g ] ->
      var a + var b + var c + var d + var e + var f + var g
    in
    body (var add $ [ int 1; int 2; int 3; int 4; int 5; int 6; int 7 ])
end

let%expect_test "Example 1 RemoveLet, Shrink, and RevealFunctions" =
  let module M = Ex1 (TransformLet (Shrink (RevealFunctions (F1_Pretty ())))) in
  Format.printf "Ex1: %s" M.res;
  [%expect
    {|
    Ex1: (program
    (define (tmp0 tmp2 tmp1)
      (vector ((var tmp2) (vector-ref (var tmp1) 0)) ((var tmp2) (vector-ref (var tmp1) 1))))
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
    (define (tmp1 tmp2)
      (if (= (var tmp2) 0) t ((fun-ref tmp0) (+ (var tmp2) (- 1)))))
    (define (tmp0 tmp3)
      (if (= (var tmp3) 0) f ((fun-ref tmp1) (+ (var tmp3) (- 1)))))
    (define (main)
      ((fun-ref tmp1) 24))
    )
    |}]

let%expect_test "Example 3 RemoveLet, Shrink, and RevealFunctions" =
  let module M = Ex3 (TransformLet (Shrink (RevealFunctions (F1_Pretty ())))) in
  Format.printf "Ex3: %s" M.res;
  [%expect
    {|
    Ex3: (program
    (define (tmp0 tmp7 tmp6 tmp5 tmp4 tmp3 tmp8)
      (+ (+ (+ (+ (+ (+ (var tmp7) (var tmp6)) (var tmp5)) (var tmp4)) (var tmp3)) (vector-ref (var tmp8) 0)) (vector-ref (var tmp8) 1)))
    (define (main)
      ((fun-ref tmp0) 1 2 3 4 5 (vector 6 7)))
    )
    |}]

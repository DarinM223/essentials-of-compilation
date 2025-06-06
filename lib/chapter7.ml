module Ty = Chapter6.Ty

module type CLOSURE = sig
  module Limit : Chapter6.LIMIT
  open Limit

  type 'r closure = (unit * 'r) limit

  val fwd : convert -> unit HList.el -> 't Limit.HList.hlist -> 't closure
end

module ClosureFn (Limit : Chapter6.LIMIT) = struct
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

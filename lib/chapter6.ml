module R4_Types = struct
  include Chapter5.R3_Types

  type typ =
    [ Chapter5.R3_Types.typ
    | `Fn of typ list * typ
    ]
  [@@deriving show]
end

module type R4_Shrink = sig
  include Chapter5.R3_Shrink
  val ( $ ) : ('tup -> 'a) exp -> 'tup ExpHList.hlist -> 'a exp
  module VarHList : Chapter5.HLIST with type 'a el = 'a var
  type 'a def

  val define :
    ('tup -> 'a) var -> 'tup VarHList.hlist -> 'a exp -> 'b def -> 'b def
  val body : 'a exp -> 'a def

  val program : 'a def -> 'a program
end

module type R4 = sig
  include Chapter5.R3
  include R4_Shrink with type 'a exp := 'a exp
end

module type R4_Let = sig
  include Chapter2_definitions.R1_Let
  include R4 with type 'a exp := 'a exp and type 'a var := 'a var

  (* TODO: translate let@ into define in TransformLet pass *)
  val ( let@ ) :
    ('tup VarHList.hlist -> 'a exp) -> (('tup -> 'a) var -> 'b def) -> 'b def
end

module Ex1 (F : R4_Let) = struct
  open F

  let res =
    program
    @@
    let@ map_vec =
     fun [ f; v ] ->
      vector
        [
          var f $ [ vector_ref (var v) Here ];
          var f $ [ vector_ref (var v) (Next Here) ];
        ]
    in
    let@ add1 = fun [ x ] -> var x + int 1 in
    body
    @@ vector_ref
         (var map_vec $ [ var add1; vector [ int 0; int 41 ] ])
         (Next Here)
end

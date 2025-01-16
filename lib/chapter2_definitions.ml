module type R1 = sig
  include Chapter1.R0

  type 'a var
  val var : 'a var -> 'a exp
  val ( let* ) : 'a exp -> ('a var -> 'b exp) -> 'b exp
end

module R1_T (X : Chapter1.TRANS) (F : R1 with type 'a exp = 'a X.from) = struct
  include Chapter1.R0_T (X) (F)
  open X
  type 'a var = 'a F.var
  let var v = fwd @@ F.var v
  let ( let* ) e f = fwd @@ F.( let* ) (bwd e) (fun v -> bwd (f v))
end

module R1_Partial (F : R1) = struct
  module M = Chapter1.R0_Partial_Pass (F)
  include R1_T (M.X) (F)
  include M.IDelta
end

module R1_Pretty = struct
  include Chapter1.R0_Pretty
  type 'a var = string
  let var v = "(var " ^ v ^ ")"

  let fresh =
    let c = ref (-1) in
    fun () ->
      incr c;
      !c

  let ( let* ) e f =
    let v = "tmp" ^ string_of_int (fresh ()) in
    "(let ([" ^ v ^ " " ^ e ^ "]) " ^ f v ^ ")"
end

module R1_Interp = struct
  type 'a typ =
    | TInt : int typ
    | TBool : bool typ
    | TUnit : unit typ

  type 'a exp = 'a typ * 'a
  type 'a var = 'a typ * int

  let int x = (TInt, x)
  let read () =
    print_endline "Enter integer: ";
    (TInt, read_int ())
  let neg (TInt, i) = (TInt, -i)
  let ( + ) (TInt, a) (TInt, b) = (TInt, a + b)

  type 'a program = 'a
  let program (_, i) = i

  let fresh =
    let counter = ref (-1) in
    fun () ->
      incr counter;
      !counter

  let int_env : (int, int exp) Hashtbl.t = Hashtbl.create 100
  let bool_env : (int, bool exp) Hashtbl.t = Hashtbl.create 100
  let unit_env : (int, unit exp) Hashtbl.t = Hashtbl.create 100

  let lookup_env : type a. a var -> a exp =
   fun (ty, v) ->
    match ty with
    | TInt -> Hashtbl.find int_env v
    | TBool -> Hashtbl.find bool_env v
    | TUnit -> Hashtbl.find unit_env v

  let add_env : type a. a var -> a exp -> unit =
   fun (ty, v) e ->
    match ty with
    | TInt -> Hashtbl.add int_env v e
    | TBool -> Hashtbl.add bool_env v e
    | TUnit -> Hashtbl.add unit_env v e

  let remove_env : type a. a var -> unit =
   fun (ty, v) ->
    match ty with
    | TInt -> Hashtbl.remove int_env v
    | TBool -> Hashtbl.remove bool_env v
    | TUnit -> Hashtbl.remove unit_env v

  let var v = lookup_env v

  let ( let* ) ((ty, _) as e) f =
    let i = fresh () in
    let v = (ty, i) in
    add_env v e;
    let result = f v in
    remove_env v;
    result
end

module type C0 = sig
  type var = string

  type 'a arg

  val int : int -> int arg
  val var : var -> 'a arg

  type 'a exp

  val arg : 'a arg -> 'a exp
  val read : unit -> int exp
  val neg : int arg -> int exp
  val ( + ) : int arg -> int arg -> int exp

  type stmt
  val assign : var -> 'a exp -> stmt

  type tail
  val return : 'a exp -> tail
  val ( @> ) : stmt -> tail -> tail

  type program
  type info = { locals : string list }
  val program : info -> (string * tail) list -> program
end

module C0_Pretty = struct
  type var = string
  type 'a arg = string
  let int = string_of_int
  let var = Fun.id

  type 'a exp = string
  let arg = Fun.id
  let read () = "(read)"
  let neg e = "(neg " ^ e ^ ")"
  let ( + ) a b = "(+ " ^ a ^ " " ^ b ^ ")"

  type stmt = string
  let assign v e = "(assign " ^ v ^ " " ^ e ^ ")"

  type tail = string
  let return e = "(return " ^ e ^ ")"
  let ( @> ) stmt rest = "(seq " ^ stmt ^ " " ^ rest ^ ")"

  type program = string
  type info = { locals : string list }
  let program info body =
    let locals = String.concat " " info.locals in
    let pair (label, tail) = "(" ^ label ^ " . " ^ tail ^ ")" in
    let body = String.concat "\n" (List.map pair body) in
    "(program ((locals . (" ^ locals ^ "))) (" ^ body ^ ")"
end

module Ex1 (F : R1) = struct
  open F

  let res =
    program
    @@
    let* x = int 12 + int 20 in
    int 10 + var x
end

module Ex2 (F : R1) = struct
  open F

  let res =
    program
    @@
    let* x = int 32 in
    (let* x = int 10 in
     var x)
    + var x

  let check =
    program
    @@
    let* x1 = int 32 in
    (let* x2 = int 10 in
     var x2)
    + var x1
end

module Ex3 (F : R1) = struct
  open F
  let res =
    program
    @@
    let* x = read () in
    let* y = read () in
    var x + neg (var y)
end

module C0_Ex1 (F : C0) = struct
  open F

  let res =
    program { locals = [] }
      [
        ( "start",
          assign "x_1" (arg (int 20))
          @> assign "x_2" (arg (int 22))
          @> assign "y" (var "x_1" + var "x_2")
          @> return (arg (var "y")) );
      ]
end

let run () =
  let module M = Ex1 (R1_Interp) in
  Format.printf "Ex1: %d\n" M.res;
  let module M = Ex2 (R1_Interp) in
  Format.printf "Ex2: Result: %d Expected: %d\n" M.res M.check;
  (* Enter 52, then 10, should produce 42, not -42 *)
  let module M = Ex3 (R1_Interp) in
  Format.printf "Ex3: %d\n" M.res;
  let module M = Ex1 (R1_Partial (R1_Interp)) in
  Format.printf "Ex1 with partial pass: %d\n" M.res;
  let module M = Ex3 (R1_Pretty) in
  Format.printf "Ex3 pretty: %s\n" M.res

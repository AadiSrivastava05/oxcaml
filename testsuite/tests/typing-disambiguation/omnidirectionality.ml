(* TEST
   expect;
*)

(* Constructor disambiguation under omndirectional type inference *)

type t = A | B of int
type u = A | B of bool | C
[%%expect {|
type t = A | B of int
type u = A | B of bool | C
|}];;


(* Stage 1 good defaulting (i.e top-level defaults work) *)

let a1 = A;;
[%%expect {|
val a1 : u = A
|}];;

let[@warning "+41"] a2 = A;;
[%%expect {|
Line 1, characters 25-26:
1 | let[@warning "+41"] a2 = A;;
                             ^
Warning 41 [ambiguous-name]: "A" belongs to several types: "u" "t".
  The first one was selected. Please disambiguate if this is wrong.

val a2 : u = A
|}];;

(* The argument does not take part in disambiguation.
   [B] defaults to [u.B] and the argument is then rejected. *)
let a3 = B 1;;
[%%expect {|
Line 1, characters 11-12:
1 | let a3 = B 1;;
               ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

let a4 = C;;
[%%expect {|
val a4 : u = C
|}];;

let a5 = Some A;;
[%%expect {|
val a5 : u option = Some A
|}];;

let a6 = [A; B true];;
[%%expect {|
val a6 : u list = [A; B true]
|}];;

let a8 x = (x, A);;
[%%expect {|
val a8 : 'a -> 'a * u = <fun>
|}];;

(* Omnidirectional application *)

(* Currently the compiler will default [A] to [u.A]. *)
let apply f x = f x;;
let rev_apply x f = f x;;
[%%expect {|
val apply : ('a -> 'b) -> 'a -> 'b = <fun>
val rev_apply : 'a -> ('a -> 'b) -> 'b = <fun>
|}];;

let b11 = (fun (x : t) -> x) A;;
let b12 = apply (fun (x : t) -> x) A;;
[%%expect {|
val b11 : t = A
val b12 : t = A
|}, Principal{|
val b11 : t = A
Line 2, characters 35-36:
2 | let b12 = apply (fun (x : t) -> x) A;;
                                       ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

val b12 : t = A
|}];;

let b21 = A |> (fun (x : t) -> x);;
let b22 = rev_apply A (fun (x : t) -> x);;
[%%expect {|
Line 1, characters 20-27:
1 | let b21 = A |> (fun (x : t) -> x);;
                        ^^^^^^^
Error: This pattern matches values of type "t"
       but a pattern was expected which matches values of type "u"
|}];;

let b31 = B 1 |> (fun (x : t) -> x);;
let b32 = rev_apply (B 1) (fun (x : t) -> x);;
[%%expect {|
Line 1, characters 12-13:
1 | let b31 = B 1 |> (fun (x : t) -> x);;
                ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

let unify x y = ignore (x = y);;
[%%expect {|
val unify : 'a -> 'a -> unit = <fun>
|}]

let b4 x = unify x A; (x : t);;
[%%expect {|
Line 1, characters 23-24:
1 | let b4 x = unify x A; (x : t);;
                           ^
Error: The value "x" has type "u" but an expression was expected of type "t"
|}];;

let b5 b = if b then B 1 else (A : t);;
[%%expect {|
Line 1, characters 23-24:
1 | let b5 b = if b then B 1 else (A : t);;
                           ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

let b6 = match B 1 with (x : t) -> x;;
[%%expect {|
Line 1, characters 17-18:
1 | let b6 = match B 1 with (x : t) -> x;;
                     ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

let b7 = [A; B 1; C];;
[%%expect {|
Line 1, characters 15-16:
1 | let b7 = [A; B 1; C];;
                   ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

(* Chaining of suspended constraints *)
type t2 = D of t;;
type u2 = D of u;;
[%%expect {|
type t2 = D of t
type u2 = D of u
|}];;

let c1 = D A;;
[%%expect {|
val c1 : u2 = D A
|}];;

let c2 = D (B 1);;
[%%expect {|
Line 1, characters 14-15:
1 | let c2 = D (B 1);;
                  ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}]

let c3 : t2 = D (B 1);;
[%%expect {|
val c3 : t2 = D (B 1)
|}];;

let c4 = D (B 1) |> (fun (x : t2) -> x);;
[%%expect {|
Line 1, characters 14-15:
1 | let c4 = D (B 1) |> (fun (x : t2) -> x);;
                  ^
Error: The constant "1" has type "int" but an expression was expected of type
         "bool"
|}];;

let c5 x y = unify x y; unify x A; (z : t);;
[%%expect {|
Line 1, characters 36-37:
1 | let c5 x y = unify x y; unify x A; (z : t);;
                                        ^
Error: Unbound value "z"
|}];;

(* Exhaustiveness checking *)

(* Should fail. We could mimic the notion of 'pressure' from polymorphic variants.
   But this would be complex and not worth it imo *)
let d1 = function A -> 0 | B _ -> 1;;
[%%expect {|
Line 1, characters 9-35:
1 | let d1 = function A -> 0 | B _ -> 1;;
             ^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
  Here is an example of a case that is not matched: "C"

val d1 : u -> int = <fun>
|}];;

let d2 x = match x with (A : t) -> 0 | B _ -> 1;;
[%%expect {|
val d2 : t -> int = <fun>
|}, Principal{|
Line 1, characters 39-40:
1 | let d2 x = match x with (A : t) -> 0 | B _ -> 1;;
                                           ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

val d2 : t -> int = <fun>
|}];;

let d3 x = match x with A -> 0 | (B _ : t) -> 1;;
[%%expect {|
Line 1, characters 33-42:
1 | let d3 x = match x with A -> 0 | (B _ : t) -> 1;;
                                     ^^^^^^^^^
Error: This pattern matches values of type "t"
       but a pattern was expected which matches values of type "u"
|}];;

(* No eager decisions on the argument type *)
let d4 x = match x with B n -> n + 1 | (A : t) -> 0;;
[%%expect {|
Line 1, characters 39-46:
1 | let d4 x = match x with B n -> n + 1 | (A : t) -> 0;;
                                           ^^^^^^^
Error: This pattern matches values of type "t"
       but a pattern was expected which matches values of type "u"
|}];;

let d5 x = match x with B n when n > 0 -> true | (_ : t) -> false;;
[%%expect {|
Line 1, characters 49-56:
1 | let d5 x = match x with B n when n > 0 -> true | (_ : t) -> false;;
                                                     ^^^^^^^
Error: This pattern matches values of type "t"
       but a pattern was expected which matches values of type "u"
|}];;

let d6 (A | B _ as x) = (x : t);;
[%%expect {|
Line 1, characters 25-26:
1 | let d6 (A | B _ as x) = (x : t);;
                             ^
Error: The value "x" has type "u" but an expression was expected of type "t"
|}];;

let d7 x y = match x, y with A, A -> 0 | ((B _ : t), C) -> 1 | _ -> 2;;
[%%expect {|
Line 1, characters 42-51:
1 | let d7 x y = match x, y with A, A -> 0 | ((B _ : t), C) -> 1 | _ -> 2;;
                                              ^^^^^^^^^
Error: This pattern matches values of type "t"
       but a pattern was expected which matches values of type "u"
|}];;

(* Fails. Must list out [v]'s constructors *)
type v = A | B of string | E;;
let d8 x = match x with A -> 0 | (B _ : v) -> 1;;
[%%expect {|
type v = A | B of string | E
Line 2, characters 11-47:
2 | let d8 x = match x with A -> 0 | (B _ : v) -> 1;;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
  Here is an example of a case that is not matched: "E"

val d8 : v -> int = <fun>
|}];;

(* Errors *)
let e1 x = unify x C; unify x A; unify x (B 1 : t);;
[%%expect {|
Line 1, characters 41-50:
1 | let e1 x = unify x C; unify x A; unify x (B 1 : t);;
                                             ^^^^^^^^^
Error: This expression has type "t" but an expression was expected of type "u"
|}, Principal{|
Line 1, characters 30-31:
1 | let e1 x = unify x C; unify x A; unify x (B 1 : t);;
                                  ^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

Line 1, characters 41-50:
1 | let e1 x = unify x C; unify x A; unify x (B 1 : t);;
                                             ^^^^^^^^^
Error: This expression has type "t" but an expression was expected of type "u"
|}];;

let e2 x = unify x A; unify x 1;;
[%%expect {|
Line 1, characters 30-31:
1 | let e2 x = unify x A; unify x 1;;
                                  ^
Error: The constant "1" has type "int" but an expression was expected of type "v"
|}];;

(* Stage 1 defaulting *)

let rec f1 () = A
and f2 () = f1 ()
;;
[%%expect {|
val f1 : unit -> v = <fun>
val f2 : unit -> v = <fun>
|}];;

let f2 = let x = A in x;;
[%%expect {|
val f2 : v = A
|}];;

(* Fails. [A] is defaulted to [u.A] *)
let f3 = let x = A in (x : t);;
[%%expect {|
Line 1, characters 23-24:
1 | let f3 = let x = A in (x : t);;
                           ^
Error: The value "x" has type "v" but an expression was expected of type "t"
|}];;

(* Defaults [x] unnecessarily to [u.A] *)
let f4 x = unify x A; let y = 1 in (x : t);;
[%%expect {|
Line 1, characters 36-37:
1 | let f4 x = unify x A; let y = 1 in (x : t);;
                                        ^
Error: The value "x" has type "v" but an expression was expected of type "t"
|}];;

let f5 x = let () = unify x A in (x : t);;
[%%expect {|
Line 1, characters 34-35:
1 | let f5 x = let () = unify x A in (x : t);;
                                      ^
Error: The value "x" has type "v" but an expression was expected of type "t"
|}];;

(* Stage 2 defaulting *)

let g1 x = unify x A; let y = 1 in (x : t);;
[%%expect {|
Line 1, characters 36-37:
1 | let g1 x = unify x A; let y = 1 in (x : t);;
                                        ^
Error: The value "x" has type "v" but an expression was expected of type "t"
|}];;

let g2 x = let () = unify x A in (x : t);;
[%%expect {|
Line 1, characters 34-35:
1 | let g2 x = let () = unify x A in (x : t);;
                                      ^
Error: The value "x" has type "v" but an expression was expected of type "t"
|}];;

let g3 x = unify x A; let id y = y in (id x : t);;
[%%expect {|
Line 1, characters 39-43:
1 | let g3 x = unify x A; let id y = y in (id x : t);;
                                           ^^^^
Error: This expression has type "v" but an expression was expected of type "t"
|}];;

let g4 x = unify x A; let y = x in (y : t);;
[%%expect {|
Line 1, characters 36-37:
1 | let g4 x = unify x A; let y = x in (y : t);;
                                        ^
Error: The value "y" has type "v" but an expression was expected of type "t"
|}];;

(* Stage 3 generalization *)

let h1 x = let y = unify x (D A) in ignore (x : t2); y;;
[%%expect {|
Line 1, characters 44-45:
1 | let h1 x = let y = unify x (D A) in ignore (x : t2); y;;
                                                ^
Error: The value "x" has type "u2" but an expression was expected of type "t2"
|}];;

let h2 x = let () = unify x (D C) in (x : t2);;
[%%expect {|
Line 1, characters 38-39:
1 | let h2 x = let () = unify x (D C) in (x : t2);;
                                          ^
Error: The value "x" has type "u2" but an expression was expected of type "t2"
|}];;

let h3 old =
  let g = fun x -> 1 + old (B x) in
  let y = g 0 in
  ignore (old : t -> int);
  y
;;
[%%expect {|
Line 3, characters 12-13:
3 |   let y = g 0 in
                ^
Error: The constant "0" has type "int" but an expression was expected of type
         "string"
|}];;

(* Some nasty edge cases *)

type t_alias = t;;
let z1 = B 1 |> (fun (x : t_alias) -> x);;
[%%expect {|
type t_alias = t
Line 2, characters 11-12:
2 | let z1 = B 1 |> (fun (x : t_alias) -> x);;
               ^
Error: The constant "1" has type "int" but an expression was expected of type
         "string"
|}];;

type x = Foo of y
and y = Foo of x;;
[%%expect {|
type x = Foo of y
and y = Foo of x
|}];;

(* Constructs a cycle of suspended constraints between x and y. *)
let z2 x y = unify x (Foo y); unify y (Foo x); (x : x);;
[%%expect {|
val z2 : x -> y -> x = <fun>
|}, Principal{|
Line 1, characters 39-42:
1 | let z2 x y = unify x (Foo y); unify y (Foo x); (x : x);;
                                           ^^^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

val z2 : x -> y -> x = <fun>
|}];;

let z3 x y = unify x (Foo y); unify y (Foo x); (x : y);;
[%%expect {|
Line 1, characters 48-49:
1 | let z3 x y = unify x (Foo y); unify y (Foo x); (x : y);;
                                                    ^
Error: The value "x" has type "x" but an expression was expected of type "y"
|}, Principal{|
Line 1, characters 39-42:
1 | let z3 x y = unify x (Foo y); unify y (Foo x); (x : y);;
                                           ^^^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

Line 1, characters 48-49:
1 | let z3 x y = unify x (Foo y); unify y (Foo x); (x : y);;
                                                    ^
Error: The value "x" has type "x" but an expression was expected of type "y"
|}];;

(* Should fail. This currently succeeds because there is a lexical order of
   defaulting. This should be extremely rare. *)
let z4 x y = unify x (Foo y); unify y (Foo x);;
[%%expect {|
val z4 : x -> y -> unit = <fun>
|}, Principal{|
Line 1, characters 39-42:
1 | let z4 x y = unify x (Foo y); unify y (Foo x);;
                                           ^^^
Warning 18 [not-principal]: this type-based constructor disambiguation is not
  principal.

val z4 : x -> y -> unit = <fun>
|}];;

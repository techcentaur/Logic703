(* Assignment0 *)

(* Data-type *)
type prop = T | F 
			| L of string 
            | Not of prop
            | And of prop * prop 
            | Or of prop * prop 
            | Impl of prop * prop 
            | Iff of prop * prop;;

(* Get height as integer *)
let rec height arg = match arg with
	T -> 0
	| F -> 0
	| L a -> 0
	| Not a -> 1 + (height a);
	| And(a1, a2) -> 1 + max (height a1) (height a2)
	| Or(a1, a2) -> 1 + max (height a1) (height a2)
	| Impl(a1, a2) -> 1 + max (height a1) (height a2)
	| Iff(a1, a2) -> 1 + max (height a1) (height a2);;

(* Get size as integer *)
let rec size arg = match arg with
	T -> 1
	| F -> 1
	| L a -> 1
	| Not a -> 1
	| And(a1, a2) -> 1 + (size a1) + (size a2)
	| Or(a1, a2) -> 1 + (size a1) + (size a2)
	| Impl(a1, a2) -> 1 + (size a1) + (size a2)
	| Iff(a1, a2) -> 1 + (size a1) + (size a2);;

(* test-cases *)
let l1 = And(T,Or(F, L("st")));;
height l1;;
size l1;;



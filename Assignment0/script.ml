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


(* Get letters as a string set: (set would be a built-in data structure) and more functions of set *)
let rec letters arg = match arg with
	T -> []
	| F -> []
	| L a -> [a]
	| Not a -> (letters a)
	| And(a1, a2) -> (letters a1) @ (letters a2)
	| Or(a1, a2) -> (letters a1) @ (letters a2)
	| Impl(a1, a2) -> (letters a1) @ (letters a2)
	| Iff(a1, a2) -> (letters a1) @ (letters a2);;


let and_function x y = match (x, y) with
	(true, true) -> true
	| (x, y) -> false;;


let or_function x y = match (x, y) with
	(false, false) -> false
	| (x, y) -> true;;


let imp_function x y = match (x, y) with
	(true, false) -> false
	| (x, y) -> false;;

(* 
let iff_function x y =
		x = y;; *)

let iff_function x y = match (x, y) with
	_ -> and_function (imp_function x y) (imp_function y x);;


(* Define rho as string->bool mapping *)
let rho s = match s with
	"st" -> false
	| z -> true;;

(* truth value function (string->bool)->bool *)
let rec truth rho exp = match exp with
	T -> true
	| F -> false
	| L a -> (rho a)
	| Not a -> not (truth rho a)
	| And(a1, a2) -> and_function (truth rho a1) (truth rho a2)
	| Or(a1, a2) -> or_function (truth rho a1) (truth rho a2)
	| Impl(a1, a2) -> imp_function (truth rho a1) (truth rho a2)
	| Iff(a1, a2) -> iff_function (truth rho a1) (truth rho a2);;

(* test-cases *)
let l1 = And(T,Or(F, L("st")));;
height l1;;
size l1;;
letters l1;;
truth rho l1;;
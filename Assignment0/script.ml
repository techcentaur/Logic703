(* Assignment0 *)

(* Exceptions *)
exception NotSubProp;;

(* Data-types *)
type prop = T | F 
			| L of string 
            | Not of prop
            | And of prop * prop 
            | Or of prop * prop 
            | Impl of prop * prop 
            | Iff of prop * prop;;

type 'a set = Set of ('a list);;

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
	| Not a -> 1 + (size a)
	| And(a1, a2) -> 1 + (size a1) + (size a2)
	| Or(a1, a2) -> 1 + (size a1) + (size a2)
	| Impl(a1, a2) -> 1 + (size a1) + (size a2)
	| Iff(a1, a2) -> 1 + (size a1) + (size a2);;

(* Let's write set: Data type *)
let insert_into m s = match List.mem m s with 
	true -> s 
	| false -> (s @ m :: []);;

let insert m s = match s with
	Set l -> Set (insert_into m l);;

let member m s = match s with
	Set s1 -> List.mem m s1;;

let rec union s1 s2 = match s1 with
	Set [] -> s2
	| Set (m::rest) -> if member m s2 then (union (Set rest) s2) else (union (Set rest) (insert m  s2));;

let rec intersection s1 s2 = match s1 with
	Set [] -> Set []
	| Set (m::rest) -> if member m s2 then insert m (intersection (Set rest) s2) else (intersection (Set rest) s2);;

let rec difference s1 s2 = match s1 with
	Set [] -> Set []
	| Set (m::rest) -> if member m s2 then (difference (Set rest) s2) else insert m (difference (Set rest) s2);;

(* s1.length() <= s2.length() *)
let rec subset s1 s2 = match s1 with
	Set [] -> true
	| Set (m::rest) -> if member m s2 then subset (Set rest) s2 else false;;

let length s = match s with
	Set [] -> 0
	| Set l -> List.length l;;

let equal s1 s2 = ((subset s1 s2) && (subset s2 s1));;

(* Get letters as a string set *)
let rec letters arg = match arg with
	T -> Set []
	| F -> Set []
	| L a -> Set [a]
	| Not a -> (letters a)
	| And(a1, a2) -> union (letters a1) (letters a2)
	| Or(a1, a2) -> union (letters a1) (letters a2)
	| Impl(a1, a2) -> union (letters a1) (letters a2)
	| Iff(a1, a2) -> union (letters a1) (letters a2);;

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


(* Negation Normal Form (NNF): prop->prop*)
let rec nnf exp = match exp with
	L a -> exp
	| T -> exp
	| F -> exp
	| Not a1 -> (match a1 with
				| L b -> Not a1
				| T -> F
				| F -> T 
				| Not b -> nnf b
				| And(b1, b2) -> Or (nnf (Not b1), nnf (Not b2))
				| Or(b1, b2) -> And (nnf (Not b1), nnf (Not b2))
				| Impl(b1, b2) -> And (nnf b1, nnf (Not b2))
				| Iff(b1, b2) -> Or (And (nnf b1, nnf (Not b2)), And (nnf b2, nnf (Not b1))))
	| And(a1, a2) -> And(nnf a1, nnf a2)
	| Or(a1, a2) -> Or(nnf a1, nnf a2)
	| Impl(a1, a2) -> Or (nnf (Not a1), nnf a2)
	| Iff(a1, a2) -> And (nnf (Impl (a1, a2)), nnf(Impl (a1, a2)));;


(* CNF helper functions *)
let rec go_on_distribute_cnf exp1 exp2 = match (exp1, exp2) with
	(a1, And (a11, a12)) -> And ((go_on_distribute_cnf a1 a11), (go_on_distribute_cnf a1 a12))
	| (And (a11, a12), a1) -> And ((go_on_distribute_cnf a11 a1), (go_on_distribute_cnf a12 a1))
	| (a1, a2) -> Or (a1, a2);;

let rec convert_cnf exp = match exp with
	L a -> exp
	| T -> exp
	| F -> exp
	| Not a -> exp
	| And (a1, a2) -> And ((convert_cnf a1), (convert_cnf a2))
	| Or (a1, a2) -> go_on_distribute_cnf (convert_cnf a1) (convert_cnf a2);;

(* CNF: Conjuctive Normal Form: prop->prop *)
let cnf exp = match exp with
	_ -> (convert_cnf (nnf exp));;


(* DNF helper functions *)
let rec go_on_distribute_dnf exp1 exp2 = match (exp1, exp2) with
	(a1, Or (a11, a12)) -> Or ((go_on_distribute_dnf a1 a11), (go_on_distribute_dnf a1 a12))
	| (Or (a11, a12), a1) -> Or ((go_on_distribute_dnf a11 a1), (go_on_distribute_dnf a12 a1))
	| (a1, a2) -> And (a1, a2);;

let rec convert_dnf exp = match exp with
	L a -> exp
	| T -> exp
	| F -> exp
	| Not a -> exp
	| Or (a1, a2) -> Or ((convert_dnf a1), (convert_dnf a2))
	| And (a1, a2) -> go_on_distribute_dnf (convert_dnf a1) (convert_dnf a2);;

(* DNF: Disjunctive Normal Form: prop->prop *)
let dnf exp = match exp with
	_ -> (convert_dnf (nnf exp));;

(* 
NOTE:
DNF and CNF can further simply using unit laws and idempotence *)

(* test-cases *)
let l1 = And(T,Or(F, L("st")));;
height l1;;
size l1;;
letters l1;;
truth rho l1;;
cnf l1;;
dnf l1;;

let rec newprop p1 p2 l s =
	(
	if p1=p2 then (union (Set [l]) s)
	else match p1 with 
		| T -> s
		| F -> s 
		| L a -> s
		| Not a -> newprop a p2 (l@[-1]) s 
		| And(a1, a2)-> ( let x = newprop a1 p2 (l @ [0]) s in 
				newprop a2 p2 (l @ [1]) x)
		| Or(a1, a2)-> ( let x = newprop a1 p2 (l @ [0]) s in 
				newprop a2 p2 (l @ [1]) x)
		| Impl(a1, a2)-> ( let x = newprop a1 p2 (l @ [0]) s in 
				newprop a2 p2 (l @ [1]) x)
		| Iff(a1, a2)-> ( let x = newprop a1 p2 (l @ [0]) s in 
				newprop a2 p2 (l @ [1]) x)
	);;

let subprop_at p1 p2 = (let x = (newprop (p1) (p2) ([]) (Set([]))) in 
					(if length x = 0 then raise NotSubProp else x));;

let p1 = And(T, F);;
let p2 = And(T, T);;
let p21 = And(F, T);;
let p22 = And(F, F);;
let p3 = Or(T, F);;
let p4 = Or(F, F);;
let p5 = Impl(T, F);;
let p6 = Impl(F, T);;
let p7 = Or(T, L "x");;
let p71 = Or(L "x",  F);;
let p9 = Impl(T, L "y");;
let p10 = Iff(F, L "z");;
let p11 = Impl(p1, p2);;
let p111 = Impl(p1, p4);;
let p12 = Not(Iff(p4, p5));;
let p13 = Impl(p10, p9);;
let p14 = Not(Or(p5, p7));;
let p15 = Iff(And(p5, p6), p6);;
let p16 = Impl(Iff(p15, p9), p14);;
let p17 = Not(And(Iff(p7, p2), Or(p16, p10)));;

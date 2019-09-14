(* Assignment3: Natural Deduction Proof Style System *)

(* Let's write set: Data type *)

type 'a set = Set of ('a list);;

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


(* required points 
1. type of ndprooftree
2. valid_ndprooftree
3. pad
4. prune
5. graft
*)
type prop = T | F 
			| L of string 
            | Not of prop
            | And of prop * prop 
            | Or of prop * prop 
            | Impl of prop * prop 
            | Iff of prop * prop;;

type judgement = Agree of (prop set) * prop;;

type antecedents = Ant of judgement;;

type ndprooftree = End of judgement
	| IntroImp of antecedents * ndprooftree
	| ElimImp of (antecedents list) * ndprooftree
	| Int of antecedents * ndprooftree
	| Class of antecedents * ndprooftree
	| IntroAnd of (antecedents list) * ndprooftree
	| ElimAnd of (antecedents * ndprooftree) list
	| IntroOr of (antecedents * ndprooftree) list
	| ElimOr of (antecedents list) * ndprooftree;;

let rec check_if_concl_in_ass ass concl = match ass with
	Set (a::rest) -> if a=concl then true else check_if_concl_in_ass (Set (rest)) concl
	| Set ([]) -> false;; 
 

let rec valid_ndprooftree pt = match pt with
	End( Agree (ass, concl)) -> if concl=T then true
								else (if (check_if_concl_in_ass ass concl) then true else false)
	| Int (Ant (Agree (ass, concl)), childpt) -> if concl=F then valid_ndprooftree
	

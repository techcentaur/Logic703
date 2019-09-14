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
type consequent = Con of judgement;;

type ndprooftree = End of judgement
	| IntroImp of antecedents * consequent * ndprooftree
	| ElimImp of (antecedents list) * consequent * ndprooftree
	| Int of antecedents * consequent * ndprooftree
	| Class of antecedents * consequent * ndprooftree
	| IntroAnd of (antecedents list) * consequent * ndprooftree
	| ElimAnd of (antecedents * consequent * ndprooftree) list
	| IntroOr of (antecedents * consequent * ndprooftree) list
	| ElimOr of (antecedents list) * consequent * ndprooftree;;

let rec check_if_concl_in_ass ass concl = match ass with
	Set (a::rest) -> if a=concl then true else check_if_concl_in_ass (Set (rest)) concl
	| Set ([]) -> false;; 
 
let rec valid_ndprooftree pt g = match pt with
	End (Agree (ass, concl)) -> if(g=ass) then 
									(if concl=T then true
									else (if (check_if_concl_in_ass ass concl) then true else false))
								else false
	| Int (Ant (Agree (ass1, concl1)), Con (Agree (ass2, concl2)), cpt) -> 
			(equal ass1 ass2) && (equal ass1 g) && (concl1=F) &&  (valid_ndprooftree cpt g)
	| Class (Ant (Agree ((Set(Not (r)::ass1)), concl1)), Con (Agree (ass2, concl2)), cpt) ->
			(equal (Set (Not (r)::ass1)) g) && (concl1=F) && (equal ass2 (Set(ass1))) && (r=concl2) && (valid_ndprooftree cpt ass2)
	| IntroImp (Ant (Agree (ass1, concl1)), Con (Agree (ass2, concl2)), cpt) ->
			(equal ass1 g) &&
				(match ass1 with Set(r::rest) -> (if (concl2=Impl(r, concl1) && (equal (Set(rest)) ass2)) 
													then (valid_ndprooftree cpt ass2) else false))
	| ElimImp (([Ant (Agree (ass1, Impl(p, q))); Ant (Agree (ass2, p1))]), Con (Agree (ass3, q1)), cpt) ->
		(equal ass1 ass2) && (equal ass2 ass3) && 
			(if (p=p1 && q=q1) then (valid_ndprooftree cpt ass3) else false)
	| IntroAnd (([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), Con (Agree (ass3, And(p1, q1))), cpt) ->
		(equal ass1 ass2) && (equal ass2 ass3) && (p1=p && q1=q) && (valid_ndprooftree cpt ass3)
	| ElimAnd ([(Ant (Agree (ass1, And(p, q))), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, And(p2, q2))), Con (Agree (ass4, q3)), cpt2)]) ->
		(equal ass1 ass2) && (equal ass3 ass4) && (equal ass3 ass2) && (p=p1 && q2=q3 && p=p2 && q=q2)
		&& (valid_ndprooftree cpt1 ass2) && (valid_ndprooftree cpt2 ass2)
	| ElimOr (([Ant (Agree (ass1, And(p, q))); Ant (Agree (Set (p1::ass2), r1)); Ant (Agree (Set(q1::ass3), r2))]), Con (Agree (ass4, r3)), cpt) ->
		(equal ass1 (Set (ass2))) && (equal (Set(ass2)) (Set(ass3))) & (equal (Set(ass3)) ass4)
			& (p=p1 && q=q1 && r1=r2 && r2=r3) & (valid_ndprooftree cpt ass1)
	| IntroOr ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, Or(p1, q1))), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, Or(p2, q2))), cpt2)]) ->
		(equal ass1 ass2) && (equal ass3 ass4) && (equal ass3 ass2) && (p1=p2 && q1=q2)
		&& (((p=p1) && valid_ndprooftree cpt1 ass2) || ((q=q2) && valid_ndprooftree cpt2 ass2));;

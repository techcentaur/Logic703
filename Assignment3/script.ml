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
	| IntroImp of  consequent * antecedents * ndprooftree
	| ElimImp of consequent * (antecedents list) * ndprooftree
	| Int of consequent * antecedents * ndprooftree
	| Class of  consequent * antecedents * ndprooftree
	| IntroAnd of  consequent * (antecedents list) * ndprooftree
	| ElimAnd of (consequent * antecedents * ndprooftree) list
	| IntroOr of (consequent * antecedents * ndprooftree) list
	| ElimOr of  consequent * (antecedents list) * ndprooftree
	| Start of (prop set) * ndprooftree;;

let rec check_if_concl_in_ass ass concl = match ass with
	Set (a::rest) -> if a=concl then true else check_if_concl_in_ass (Set (rest)) concl
	| Set ([]) -> false;; 
 
let rec _valid_ndprooftree_ pt g = match pt with
	| Start (init_g, pt) -> _valid_ndprooftree_ pt init_g 
	| End (Agree (ass, concl)) -> if(g=ass) then 
									(if concl=T then true
									else (if (check_if_concl_in_ass ass concl) then true else false))
								else false
	| Int (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> 
			(equal ass1 ass2) && (equal ass1 g) && (concl2=F) &&  (_valid_ndprooftree_ cpt g)
	| Class (Con (Agree (ass1, concl1)), Ant (Agree ((Set(Not(p)::ass2)), concl2)), cpt) ->
			(equal ass1 g) && (concl2=F) && (equal ass1 (Set(ass2))) && (concl1=p) && (_valid_ndprooftree_ cpt (Set(Not(p)::ass2)))
	| IntroImp (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
			(equal ass2 g) &&
				(match ass2 with Set(r::rest) -> (if (concl1=Impl(r, concl2) && (equal (Set(rest)) ass1)) 
													then (_valid_ndprooftree_ cpt ass2) else false))
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, Impl(p, q))); Ant (Agree (ass3, p1))]), cpt) ->
		(equal ass1 ass2) && (equal ass2 ass3) && 
			(if (p=p1 && q=q1) then (_valid_ndprooftree_ cpt ass3) else false)
	| IntroAnd (([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), Con (Agree (ass3, And(p1, q1))), cpt) ->
		(equal ass1 ass2) && (equal ass2 ass3) && (p1=p && q1=q) && (_valid_ndprooftree_ cpt ass3)
	| ElimAnd ([(Ant (Agree (ass1, And(p, q))), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, And(p2, q2))), Con (Agree (ass4, q3)), cpt2)]) ->
		(equal ass1 ass2) && (equal ass3 ass4) && (equal ass3 ass2) && (p=p1 && q2=q3 && p=p2 && q=q2)
		&& (_valid_ndprooftree_ cpt1 ass2) && (_valid_ndprooftree_ cpt2 ass2)
	| ElimOr (([Ant (Agree (ass1, And(p, q))); Ant (Agree (Set (p1::ass2), r1)); Ant (Agree (Set(q1::ass3), r2))]), Con (Agree (ass4, r3)), cpt) ->
		(equal ass1 (Set (ass2))) && (equal (Set(ass2)) (Set(ass3))) & (equal (Set(ass3)) ass4)
			& (p=p1 && q=q1 && r1=r2 && r2=r3) & (_valid_ndprooftree_ cpt ass1)
	| IntroOr ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, Or(p1, q1))), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, Or(p2, q2))), cpt2)]) ->
		(equal ass1 ass2) && (equal ass3 ass4) && (equal ass3 ass2) && (p1=p2 && q1=q2)
		&& (((p=p1) && _valid_ndprooftree_ cpt1 ass2) || ((q=q2) && _valid_ndprooftree_ cpt2 ass2));;



(* 
let rec append_delta pt del = match pt with
	| Start (init_g, cpt) -> Start(union init_g del,  (append_delta cpt del))
	| End(Agree(ass, concl)) -> End(Agree(union ass del, concl))
	| Int (Ant(Agree(ass, concl)), Con(Agree(ass1, concl1)), cpt) -> 
			Int(Ant(Agree(union ass del, concl)), Con(Agree(union ass1 del, concl1)), (append_delta cpt del))
	| Class (Ant(Agree(ass, concl)), Con(Agree(ass1, concl1)), cpt) -> 
			Class(Ant(Agree(union ass del, concl)), Con(Agree(union ass1 del, concl1)), (append_delta cpt del))
	| IntroImp (Ant (Agree (ass1, concl1)), Con (Agree (ass2, concl2)), cpt) ->
			IntroImp (Ant (Agree (union ass1 del, concl1)), Con (Agree (union ass2 del, concl2)), (append_delta cpt del))
	| ElimImp (([Ant (Agree (ass1, p1)); Ant (Agree (ass2, p2))]), Con (Agree (ass3, q1)), cpt) ->
			ElimImp (([Ant (Agree (union ass1 del, p1)); Ant (Agree (union ass2 del, p2))]), Con (Agree (union ass3 del, q1)), (append_delta cpt del))
	| IntroAnd (([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), Con (Agree (ass3, r)), cpt) ->
			IntroAnd (([Ant (Agree (union ass1 del, p)); Ant (Agree (union ass2 del, q))]), Con (Agree (union ass3 del, r)), (append_delta cpt del))
	| ElimAnd ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, q3)), cpt2)]) ->
			ElimAnd ([(Ant (Agree (union ass1 del, p)), Con ( Agree(union ass2 del, p1)), cpt1) ; (Ant (Agree (union ass3 del, q)), Con (Agree (union ass4 del, q3)), (append_delta cpt2 del))])
	| ElimOr (([Ant (Agree (ass1, p)); Ant (Agree (ass2, r1)); Ant (Agree (ass3, r2))]), Con (Agree (ass4, r3)), cpt) ->
			ElimOr (([Ant (Agree (union ass1 del, p)); Ant (Agree (union ass2 del, r1)); Ant (Agree (union ass3 del, r2))]), Con (Agree (union ass4 del, r3)), (append_delta cpt del))
	| IntroOr ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, q2)), cpt2)]) ->
			IntroOr ([(Ant (Agree (union ass1 del, p)), Con ( Agree(union ass2 del, p1)), cpt1) ; (Ant (Agree (union ass3 del, q)), Con (Agree (union ass4 del, q2)), (append_delta cpt2 del))]);;

 *)(* 
let rec get_delta pt = match pt with
	| Start (g, cpt) -> (get_delta cpt)
	| End(Agree(ass, concl)) -> [concl]
	| Int (Ant(Agree(ass, concl)), Con(Agree(ass1, concl1)), cpt) -> 
			get_delta cpt
	| Class (Ant(Agree(ass, concl)), Con(Agree(ass1, concl1)), cpt) -> 
			get_delta cpt
	| IntroImp (Ant (Agree (ass1, concl1)), Con (Agree (ass2, concl2)), cpt) ->
			get_delta cpt
	| ElimImp (([Ant (Agree (ass1, p1)); Ant (Agree (ass2, p2))]), Con (Agree (ass3, q1)), cpt) ->
			get_delta cpt
	| IntroAnd (([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), Con (Agree (ass3, r)), cpt) ->
			IntroAnd (([Ant (Agree (union ass1 del, p)); Ant (Agree (union ass2 del, q))]), Con (Agree (union ass3 del, r)), (append_delta cpt del))
	| ElimAnd ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, q3)), cpt2)]) ->
			ElimAnd ([(Ant (Agree (union ass1 del, p)), Con ( Agree(union ass2 del, p1)), cpt1) ; (Ant (Agree (union ass3 del, q)), Con (Agree (union ass4 del, q3)), (append_delta cpt2 del))])
	| ElimOr (([Ant (Agree (ass1, p)); Ant (Agree (ass2, r1)); Ant (Agree (ass3, r2))]), Con (Agree (ass4, r3)), cpt) ->
			ElimOr (([Ant (Agree (union ass1 del, p)); Ant (Agree (union ass2 del, r1)); Ant (Agree (union ass3 del, r2))]), Con (Agree (union ass4 del, r3)), (append_delta cpt del))
	| IntroOr ([(Ant (Agree (ass1, p)), Con ( Agree(ass2, p1)), cpt1) ; (Ant (Agree (ass3, q)), Con (Agree (ass4, q2)), cpt2)]) ->
			IntroOr ([(Ant (Agree (union ass1 del, p)), Con ( Agree(union ass2 del, p1)), cpt1) ; (Ant (Agree (union ass3 del, q)), Con (Agree (union ass4 del, q2)), (append_delta cpt2 del))]);;
	
		 *)
(* required function definitions *)
let valid_ndprooftree pt = (_valid_ndprooftree_ pt (Set([])));;

(* let pad pt delta = append_delta pt delta;; *)

(* let prune pt = pruning pt [];;*)
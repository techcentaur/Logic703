(* Assignment3: Natural Deduction Proof Style System  *)

(* Let's write set: Data type *)


(* corretions *)
(* 135-line: Wrong: Or in place of And *)


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


(* s1 - s2 *)
let rec diff s1 s2 = match s1 with
	Set (r::rest) -> (match s2 with Set(x) -> if List.mem r x then diff (Set rest) s2 else r::(diff (Set rest) s2))
	| Set ([]) -> [];;

let difference s1 s2 = match s1 with 
	| s1 -> (let x = (diff s1 s2) in Set(x));;

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
	| ElimImp of consequent * (antecedents list) * (ndprooftree list)
	| Int of consequent * antecedents * ndprooftree
	| Class of  consequent * antecedents * ndprooftree
	| IntroAnd of  consequent * (antecedents list) * (ndprooftree list)
	| ElimAndL of consequent * antecedents * ndprooftree
	| ElimAndR of consequent * antecedents * ndprooftree
	| IntroOrL of consequent * antecedents * ndprooftree
	| IntroOrR of consequent * antecedents * ndprooftree
	| ElimOr of  consequent * (antecedents list) * (ndprooftree list)
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
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, Impl(p, q))); Ant (Agree (ass3, p1))]), [cpt1; cpt2]) ->
		(equal ass1 ass2) && (equal ass2 ass3) && 
			(if (p=p1 && q=q1) then (_valid_ndprooftree_ cpt1 ass3) && (_valid_ndprooftree_ cpt2 ass3) else false)

	| IntroAnd (Con (Agree (ass3, And(p1, q1))), ([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), [cpt1; cpt2]) ->
		(equal ass1 ass2) && (equal ass2 ass3) && (p1=p && q1=q)
		&& (_valid_ndprooftree_ cpt1 ass3) && (_valid_ndprooftree_ cpt2 ass3)

	| ElimAndL (Con(Agree(ass1, p)), Ant(Agree(ass2, And(p1, q1))), cpt) ->
		(equal ass1 ass2) && (p=p1) && (_valid_ndprooftree_ cpt ass2)

	| ElimAndR (Con(Agree(ass1, p)), Ant(Agree(ass2, And(q1, p1))), cpt) ->
		(equal ass1 ass2) && (p=p1) && (_valid_ndprooftree_ cpt ass2)

	| ElimOr (Con (Agree (ass1, r)), ([Ant (Agree (ass2, And(p, q))); Ant (Agree (Set (p1::ass3), r1)); Ant (Agree (Set(q1::ass4), r2))]), [cpt1; cpt2; cpt3]) ->
		(equal ass1 ass2) && (equal (Set(ass3)) (Set(ass4))) && (equal (Set(ass3)) ass1)
			&& (p=p1 && q=q1 && r1=r2 && r=r1)
			&& (_valid_ndprooftree_ cpt1 ass2) && (_valid_ndprooftree_ cpt2 (Set (p1::ass3))) && (_valid_ndprooftree_ cpt3 (Set (q1::ass4)))

	| IntroOrL (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, p2)), cpt1) ->
		(equal ass1 ass2) &&(p1=p2) && (_valid_ndprooftree_ cpt1 ass1)

	| IntroOrR (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, q2)), cpt1) ->
		(equal ass1 ass2) &&(q1=q2) && (_valid_ndprooftree_ cpt1 ass1);;




let rec append_delta pt del = match pt with
	| Start (init_g, cpt) -> Start(union init_g del,  (append_delta cpt del))
	| End(Agree(ass, concl)) -> End(Agree(union ass del, concl))
	| Int (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> 
		Int (Con (Agree (union ass1 del, concl1)), Ant (Agree (union ass2 del, concl2)), append_delta cpt del)
	| Class (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
		Class (Con (Agree (union ass1 del, concl1)), Ant (Agree (union ass2 del, concl2)), append_delta cpt del)
	| IntroImp (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
		IntroImp (Con (Agree (union ass1 del, concl1)), Ant (Agree (union ass2 del, concl2)), append_delta cpt del)
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, Impl(p, q))); Ant (Agree (ass3, p1))]), [cpt1; cpt2]) ->
		ElimImp (Con (Agree (union ass1 del, q1)), ([Ant (Agree (union ass2 del, Impl(p, q))); Ant (Agree (union ass3 del, p1))]), [append_delta cpt1 del; append_delta cpt2 del])
	| IntroAnd (Con (Agree (ass3, And(p1, q1))), ([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), [cpt1; cpt2]) ->
		IntroAnd (Con (Agree (union ass3 del, And(p1, q1))), ([Ant (Agree (union ass1 del, p)); Ant (Agree (union ass2 del, q))]), [append_delta cpt1 del; append_delta cpt2 del])
	| ElimAndL (Con(Agree(ass1, p)), Ant(Agree(ass2, And(p1, q1))), cpt) ->
		ElimAndL (Con(Agree(union ass1 del, p)), Ant(Agree(union ass2 del, And(p1, q1))), append_delta cpt del)
	| ElimAndR (Con(Agree(ass1, p)), Ant(Agree(ass2, And(q1, p1))), cpt) ->
		ElimAndR (Con(Agree(union ass1 del, p)), Ant(Agree(union ass2 del, And(q1, p1))), append_delta cpt del)
	| ElimOr (Con (Agree (ass1, r)), ([Ant (Agree (ass2, And(p, q))); Ant (Agree (ass3, r1)); Ant (Agree (ass4, r2))]), [cpt1; cpt2; cpt3]) ->
		ElimOr (Con (Agree (union ass1 del, r)), ([Ant (Agree (union ass2 del, And(p, q))); Ant (Agree (union ass3 del, r1)); Ant (Agree (union ass4 del, r2))]), [append_delta cpt1 del; append_delta cpt2 del; append_delta cpt3 del])
	| IntroOrL (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, p2)), cpt1) ->
		IntroOrL (Con(Agree(union ass1 del, Or(p1, q1))), Ant(Agree(union ass2 del, p2)), append_delta cpt1 del)
	| IntroOrR (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, q2)), cpt1) ->
		IntroOrR (Con(Agree(union ass1 del, Or(p1, q1))), Ant(Agree(union ass2 del, q2)), append_delta cpt1 del);;


 
let rec get_delta pt = match pt with
	| Start (g, cpt) -> (get_delta cpt)
	| End(Agree(ass, concl)) -> Set([concl])
	| Int (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> (get_delta cpt)
	| Class (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> (get_delta cpt)
	| IntroImp (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> (get_delta cpt)
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, Impl(p, q))); Ant (Agree (ass3, p1))]), [cpt1; cpt2]) ->
		union (get_delta cpt1) (get_delta cpt2)
	| IntroAnd (Con (Agree (ass3, And(p1, q1))), ([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), [cpt1; cpt2]) ->
		union (get_delta cpt1) (get_delta cpt2)
	| ElimAndL (Con(Agree(ass1, p)), Ant(Agree(ass2, And(p1, q1))), cpt) -> (get_delta cpt)
	| ElimAndR (Con(Agree(ass1, p)), Ant(Agree(ass2, And(q1, p1))), cpt) -> (get_delta cpt)
	| ElimOr (Con (Agree (ass1, r)), ([Ant (Agree (ass2, And(p, q))); Ant (Agree (ass3, r1)); Ant (Agree (ass4, r2))]), [cpt1; cpt2; cpt3]) ->
		union (get_delta cpt1) (union (get_delta cpt2) (get_delta cpt3))
	| IntroOrL (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, p2)), cpt1) -> (get_delta cpt1)
	| IntroOrR (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, q2)), cpt1) -> (get_delta cpt1);;
		

let rec replace_2_delta pt del = match pt with 
	| Start (g, cpt) -> let x = (intersection g del) in Start(x, replace_2_delta cpt x) 
	| End(Agree(ass, concl)) -> End(Agree(del, concl))
	| Int (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
		Int (Con (Agree (del, concl1)), Ant (Agree (del, concl2)), replace_2_delta cpt del) 
	| Class (Con (Agree (ass1, concl1)), Ant (Agree (Set(p::ass2), concl2)), cpt) ->
		let x = (union (Set(p::[])) del) in
		Class (Con (Agree (del, concl1)), Ant (Agree (x, concl2)), replace_2_delta cpt x)
	| IntroImp (Con (Agree (ass1, concl1)), Ant (Agree (Set(p::ass2), concl2)), cpt) ->
		let x = (union (Set(p::[])) del) in 
			IntroImp (Con (Agree (del, concl1)), Ant (Agree (x, concl2)), replace_2_delta cpt x)
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, Impl(p, q))); Ant (Agree (ass3, p1))]), [cpt1; cpt2]) ->
		ElimImp (Con (Agree (del, q1)), ([Ant (Agree (del, Impl(p, q))); Ant (Agree (del, p1))]), [replace_2_delta cpt1 del; replace_2_delta cpt2 del])
	| IntroAnd (Con (Agree (ass3, And(p1, q1))), ([Ant (Agree (ass1, p)); Ant (Agree (ass2, q))]), [cpt1; cpt2]) ->
		IntroAnd (Con (Agree (del, And(p1, q1))), ([Ant (Agree (del, p)); Ant (Agree (del, q))]), [replace_2_delta cpt1 del; replace_2_delta cpt2 del])
	| ElimAndL (Con(Agree(ass1, p)), Ant(Agree(ass2, And(p1, q1))), cpt) ->
		ElimAndL (Con(Agree(del, p)), Ant(Agree(del, And(p1, q1))), replace_2_delta cpt del)
	| ElimAndR (Con(Agree(ass1, p)), Ant(Agree(ass2, And(q1, p1))), cpt) ->
		ElimAndR (Con(Agree(del, p)), Ant(Agree(del, And(q1, p1))), replace_2_delta cpt del)
	| ElimOr (Con (Agree (ass1, r)), ([Ant (Agree (ass2, And(p, q))); Ant (Agree (Set(xx::ass3), r1)); Ant (Agree (Set(yy::ass4), r2))]), [cpt1; cpt2; cpt3]) ->
		let x = (union del (Set(xx::[]))) in let y = (union del (Set(yy::[]))) in 
			ElimOr (Con (Agree (del, r)), ([Ant (Agree (del, And(p, q))); Ant (Agree (x, r1)); Ant (Agree (y, r2))]), [replace_2_delta cpt1 del; replace_2_delta cpt2 x; replace_2_delta cpt3 y])
	| IntroOrL (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, p2)), cpt1) ->
		IntroOrL (Con(Agree(del, Or(p1, q1))), Ant(Agree(del, p2)), replace_2_delta cpt1 del)
	| IntroOrR (Con(Agree(ass1, Or(p1, q1))), Ant(Agree(ass2, q2)), cpt1) ->
		IntroOrR (Con(Agree(del, Or(p1, q1))), Ant(Agree(del, q2)), replace_2_delta cpt1 del);;

exception NothingInHere;;
let get_del pt = match pt with
	| Start(g, cpt) -> g
	| _ -> raise NothingInHere;;

let get_gamma ptlist = match ptlist with
	| (Start(g, cpt)::rest) -> g
	| [] -> raise NothingInHere;;


let rec give_me_root pt = match pt with
	| Start (g, cpt) -> give_me_root pt
	| Int (Con (Agree (ass1, concl1)), p, cpt) -> concl1
	| Class (Con (Agree (ass1, concl1)), p, cpt) -> concl1
	| IntroImp (Con (Agree (ass1, concl1)), p, cpt) -> concl1
	| ElimImp (Con (Agree (ass1, q1)), ([p; q]), [cpt1; cpt2]) -> q1
	| IntroAnd (Con (Agree (ass1, p1)), ([p; q]), [cpt1; cpt2]) -> p1
	| ElimAndL (Con(Agree(ass1, p)), q, cpt) -> p
	| ElimAndR (Con(Agree(ass1, p)), q, cpt) -> p
	| ElimOr (Con (Agree (ass1, r)), ([q1; q2; q3]), [cpt1; cpt2; cpt3]) -> r
	| IntroOrL (Con(Agree(ass1, p)), q, cpt1) -> p
	| IntroOrR (Con(Agree(ass1, q)), p, cpt1) -> q;;


exception Cantbetrue;;
let rec give_me_gamma_tree concl ptlist = match ptlist with
	r::rest -> if (give_me_root r)=concl then r else (give_me_gamma_tree concl rest) 
	| [] -> raise Cantbetrue;;
	
let rec grafting pt ptlist del gam = match pt with
	| Start (g, cpt) -> let x = (union gam (difference g del)) in Start(x, grafting cpt ptlist del gam) 
	| End(Agree(ass, concl)) -> let prooft = give_me_gamma_tree concl ptlist in (
									match prooft with 
									Start(g1, cpt1) -> cpt1
								)
	| Int (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
		Int (Con (Agree (union gam (difference ass1 del), concl1)), Ant (Agree (union gam (difference ass2 del), concl2)), grafting cpt ptlist del gam) 
	| Class (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) ->
		Class (Con (Agree (union gam (difference ass1 del), concl1)), Ant (Agree (union gam (difference ass2 del), concl2)), grafting cpt ptlist del gam)
	| IntroImp (Con (Agree (ass1, concl1)), Ant (Agree (ass2, concl2)), cpt) -> 
		IntroImp (Con (Agree (union gam (difference ass1 del), concl1)), Ant (Agree (union gam (difference ass2 del), concl2)), grafting cpt ptlist del gam)		
	| ElimImp (Con (Agree (ass1, q1)), ([Ant (Agree (ass2, q2)); Ant (Agree (ass3, p1))]), [cpt1; cpt2]) ->
		ElimImp (Con (Agree (union gam (difference ass1 del), q1)), ([Ant (Agree (union gam (difference ass2 del), q2)); Ant (Agree (union gam (difference ass3 del), p1))]), [grafting cpt1 ptlist del gam; grafting cpt2 ptlist del gam])
	| IntroAnd (Con (Agree (ass1, p1)), ([Ant (Agree (ass2, p)); Ant (Agree (ass3, q))]), [cpt1; cpt2]) ->
		IntroAnd (Con (Agree (union gam (difference ass1 del), p1)), ([Ant (Agree (union gam (difference ass2 del), p)); Ant (Agree (union gam (difference ass3 del), q))]), [grafting cpt1 ptlist del gam; grafting cpt2 ptlist del gam])
	| ElimAndL (Con(Agree(ass1, p)), Ant(Agree(ass2, q)), cpt) ->
		ElimAndL (Con(Agree(union gam (difference ass1 del), p)), Ant(Agree(union gam (difference ass2 del), q)), grafting cpt ptlist del gam)
	| ElimAndR (Con(Agree(ass1, p)), Ant(Agree(ass2, q)), cpt) ->
		ElimAndR (Con(Agree(union gam (difference ass1 del), p)), Ant(Agree(union gam (difference ass2 del), q)), grafting cpt ptlist del gam)
	| ElimOr (Con (Agree (ass1, r)), ([Ant (Agree (ass2, p)); Ant (Agree (ass3, r1)); Ant (Agree (ass4, r2))]), [cpt1; cpt2; cpt3]) ->
		ElimOr (Con (Agree (union gam (difference ass1 del), r)), ([Ant (Agree (union gam (difference ass2 del), p)); Ant (Agree (union gam (difference ass3 del), r1)); Ant (Agree (union gam (difference ass4 del), r2))]), [grafting cpt1 ptlist del gam; grafting cpt2 ptlist del gam; grafting cpt3 ptlist del gam])
	| IntroOrL (Con(Agree(ass1, p)), Ant(Agree(ass2, p2)), cpt1) ->
		IntroOrL (Con(Agree(union gam (difference ass1 del), p)), Ant(Agree(union gam (difference ass2 del), p2)), grafting cpt1 ptlist del gam)
	| IntroOrR (Con(Agree(ass1, q)), Ant(Agree(ass2, q2)), cpt1) ->
		IntroOrR (Con(Agree(union gam (difference ass1 del), q)), Ant(Agree(union gam (difference ass2 del), q2)), grafting cpt1 ptlist del gam);;



(* required function definitions *)
let valid_ndprooftree pt = (_valid_ndprooftree_ pt (Set([])));;
let pad pt delta = append_delta pt delta;;
let prune pt = replace_2_delta pt (get_delta pt);;
let graft pt ptlist = grafting pt ptlist (get_del pt) (get_gamma ptlist);;


(* Test Case 1 - Hyp, ImpInt*)
(* let a = IntroImp(Agree([], Impl(L("x"),L("x"))), End(Agree([L("x")], L("x"))));;
valid_ndprooftree a;;
let b = pad a ([L("y")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;

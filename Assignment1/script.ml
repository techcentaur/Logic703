(* Assignment1 *)

(* Functions needed to be implemented *)
(* 
`contrad_path` that given a partially developed tableau detects a contradiction on a path and marks it closed (excluding it from further consideration).
`valid_tableau` that given a partially (or fully) developed tableau, checks whether or not it is a legitimate development from the root of the tableau, according to the rules specified.
`select_node` that selects an unexamined node on an open path as a candidate for further development.
`step_develop` that given a selected node on a path, develops the tableau according to the rules specified above.
`find_assignments`, that given a root node, finds all satisfying/falsifying truth assignments (valuations) for that prop-bool pair. 
`check_tautology` and `check_contradiction`, which return a tableaux proof that a proposition is a tautology [respectively contradiction] if it so, and a counter-example valuation otherwise. 
 *)


(* Data-types *)
type prop = T | F 
			| L of string 
            | Not of prop
            | And of prop * prop 
            | Or of prop * prop 
            | Impl of prop * prop 
            | Iff of prop * prop;;

type node = Node of prop * bool;;

(* L leaf, A alpha, B beta *)
type tableau = Empty
		| Leaf of prop * bool
		| Contrad of node
		| Confirm of node
		| Alpha of node * tableau
		| InternalNode of node * tableau
		| NotNode of node * tableau
		| Beta of node * tableau * tableau;;

type assignments = Unsat of ((string*bool) list) | Sat of ((string*bool) list);;

let rec isexists rho p = match rho with
	(m1, m2)::rest -> if m1=p then true else isexists rest p
	| [] -> false;;

let rec check_value rho p = match rho with
	(m1, m2)::rest -> if m1=p then m2 else check_value rest p 
	| [] -> false;;

let rec run_tableau tab rho = match tab with
	[] -> Leaf (T, true)
	| m::rest  -> (match m with
		Leaf (Impl (p1, p2), b) -> if b=false then
								Alpha ((Node (Impl(p1, p2), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, false))::rest) rho))
							else
								Beta ((Node (Impl(p1, p2), b)), (run_tableau (Leaf (p1, false)::rest) rho), (run_tableau (Leaf (p2, true)::rest) rho))
		| Leaf (And (p1, p2), b) -> if b=false then
								Beta ((Node ((And(p1, p2)), b)), (run_tableau (Leaf (p1, false)::rest) rho), (run_tableau (Leaf (p2, false)::rest) rho))
							else
								Alpha ((Node (Impl(p1, p2), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, true))::rest) rho))
		| Leaf (Or (p1, p2), b) -> if b=false then
								Alpha ((Node (Impl(p1, p2), b)), (run_tableau ((Leaf (p1, false))::(Leaf (p2, false))::rest) rho))
							else
								Beta ((Node (And(p1, p2), b)), (run_tableau (Leaf (p1, true)::rest) rho), (run_tableau (Leaf (p2, true)::rest) rho))
		| Leaf (Iff (p1, p2), b) -> run_tableau ((Leaf (And (Impl (p1, p2), Impl (p2, p1)), b))::rest) rho
		| Leaf (Not(p1), b) -> NotNode (Node (Not (p1), b), run_tableau (Leaf (p1, (not b))::rest) rho)
		| Leaf ((L p1), b) -> (let y = (isexists rho p1) in
								(if y=true then 
									let x = (check_value rho p1) in 
										(if x = b then (
														if List.length rest = 0 then
															(Confirm (Node (L (p1), b)))
														else
															(InternalNode (Node (L (p1), b), (run_tableau rest rho)))
														)
										else Contrad (Node (L (p1), b)))
									else (
										if List.length rest = 0 then
											(Confirm (Node (L (p1), b)))
										else
											 InternalNode (Node (L (p1), b), (run_tableau (rest) ((p1, b)::rho)))
										) 
								))
		| Leaf(T, b) -> (if b=false then Contrad (Node (T, false))
						else Confirm (Node (T, true)))
		| Leaf(F, b) -> (if b=false then Confirm (Node (F, false))
						else Contrad (Node (F, true)))

	);;

let rec mark_it_examine rem p b = match rem with
	[] -> []
	| (p1, b1, false)::rest -> if p1=p && b1=b then (mark_it_examine rest p b)
								else (p1, b1, false)::(mark_it_examine rest p b)  
	| (p1, b1, true)::rest -> mark_it_examine rest p b;;

let check_if_p_exists rem p b = (List.mem (p, b, false) rem);;

let rec check_if_in_rho rho s = match rho with
	(s1, v)::rest -> if s1=s then true else (check_if_in_rho rest s)
	| [] -> false;;

let rec get_value_from_rho rho s = match rho with
	(s1, v)::rest -> if s1=s then v else (get_value_from_rho rest s);;


let rec _valid_tableau_ tab rem rho = match tab with
	Beta (Node (p, b1), t1, t2) -> if (check_if_p_exists rem p b1)
										then ( let newrem = (mark_it_examine rem p b1) in ( 
													if b1 = true then
													( match p with 
														Or (p1, p2) -> ((_valid_tableau_ t1 ((p1, true, false)::newrem) rho) && (_valid_tableau_ t2 ((p2, true, false)::newrem) rho))
														| Impl (p1, p2) -> ((_valid_tableau_ t1 ((p1, false, false)::newrem) rho) && (_valid_tableau_ t2 ((p2, true, false)::newrem) rho)))
													else
													( match p with	
														And (p1, p2) -> ((_valid_tableau_ t1 ((p1, false, false)::newrem) rho) && (_valid_tableau_ t2 ((p2, false, false)::newrem) rho)))
											))
									else false
	| Alpha (Node (p, b1), t1) -> if (check_if_p_exists rem p b1) then
									(let newrem = (mark_it_examine rem p b1) in 
										(if b1 = true then
										(match p with
											And (p1, p2) -> _valid_tableau_ t1 ((p1, true, false)::(p2, true, false)::newrem) rho
										)
										else
										(match p with
											Or (p1, p2) -> _valid_tableau_ t1 ((p1, false, false)::(p2, false, false)::newrem) rho
											| Impl (p1, p2) -> _valid_tableau_ t1 ((p1, true, false)::(p2, false, false)::newrem) rho
										)
									))
								else false
	| NotNode (Node (p, b1), t) -> if (check_if_p_exists rem p b1) then 
									( let newrem = (mark_it_examine rem p b1) in 
										(_valid_tableau_ t ((p, not b1, false)::newrem) rho)
									)
									else false
	| InternalNode (Node(L s, b1), t) -> if (check_if_p_exists rem (L s) b1) then
										 (let newrem = (mark_it_examine rem (L s) b1) in 
											if (check_if_in_rho rho s) then 
												(if b1 = (get_value_from_rho rho s) then
													(_valid_tableau_ t newrem rho)
												else false
												)
											else (_valid_tableau_ t newrem ((s, b1)::rho))
										)
									else false
	| Confirm (Node (L s, b1)) -> if (check_if_in_rho rho s) then
									(if b1 = (get_value_from_rho rho s) then true
									 else false
									)
								  else true
	| Contrad (Node (L s, b1)) -> if (check_if_in_rho rho s) then
									(if b1 = (not (get_value_from_rho rho s)) then true
									 else false
									)
								else true
	| _ -> true;;


let rec _contrad_path_ tab rho = match tab with
	Beta (Node (p, b1), t1, t2) -> Beta (Node (p, b1), (_contrad_path_ t1 rho), (_contrad_path_ t2 rho))
	| Alpha (Node (p, b1), t1) ->  Alpha (Node (p, b1), (_contrad_path_ t1 rho))
	| NotNode (Node (p, b1), t) -> NotNode (Node (p, b1), (_contrad_path_ t rho))
	| InternalNode (Node(L s, b1), t) -> if (check_if_in_rho rho s) then 
												(if b1 = (get_value_from_rho rho s) then
													InternalNode (Node (L s, b1), (_contrad_path_ t rho))
												else Contrad (Node(L s, b1)))
										else InternalNode (Node (L s, b1), (_contrad_path_ t ((s, b1)::rho)))
	| Confirm (Node (L s, b1)) -> if (check_if_in_rho rho s) then
									(if b1 = (get_value_from_rho rho s) then Confirm (Node (L s, b1))
									 else Contrad (Node (L s, b1))
									)
								  else Confirm (Node (L s, b1))
	| Contrad (Node (L s, b1)) -> Contrad (Node (L s, b1));;



let rec _find_assignments_ tab rho = match tab with
	| m::rest  -> (match m with
		Leaf (Impl (p1, p2), b) -> if b=false then
								(_find_assignments_ ((Leaf (p1, true))::(Leaf (p2, false))::rest) rho)
								else
								(_find_assignments_ (Leaf (p1, false)::rest) rho) @ (_find_assignments_ (Leaf (p2, true)::rest) rho)
		| Leaf (And (p1, p2), b) -> if b=false then
								(_find_assignments_ (Leaf (p1, false)::rest) rho) @ ((_find_assignments_ (Leaf (p2, false)::rest) rho))
								else
								(_find_assignments_ ((Leaf (p1, true))::(Leaf (p2, true))::rest) rho)
		| Leaf (Or (p1, p2), b) -> if b=false then
								(_find_assignments_ ((Leaf (p1, false))::(Leaf (p2, false))::rest) rho)
							else
								(_find_assignments_ (Leaf (p1, true)::rest) rho) @ (_find_assignments_ (Leaf (p2, true)::rest) rho)
		| Leaf (Iff (p1, p2), b) -> (_find_assignments_ ((Leaf (And (Impl (p1, p2), Impl (p2, p1)), b))::rest) rho)
		| Leaf (Not(p1), b) -> (_find_assignments_ (Leaf (p1, (not b))::rest) rho)
		| Leaf ((L p1), b) -> (let y = (isexists rho p1) in
									(if y=true then 
									(let x = (check_value rho p1) in 
										(if x = b then (
														if List.length rest = 0 then
															(Sat (((p1, b)::rho))::[])
														else
															(_find_assignments_ rest rho)
														)
										else (Unsat (((p1, b)::rho))::[])))
									else (
										if List.length rest = 0 then
											(Sat (((p1, b)::rho))::[])
										else
											(_find_assignments_ rest ((p1, b)::rho))
										) 
								))
		| Leaf(T, b) -> (if b=false then (Unsat (("T", b)::rho))::[]
						else (Sat ((("T", true)::rho))::[]))
		| Leaf(F, b) -> (if b=false then (Sat ((("F", false)::rho))::[])
						else (Unsat ((("F", true)::rho))::[])));;



let rec check_if_sat_assign_absent assigns = match assigns with
	| [] -> true
	| (Sat (rho))::rest -> false
	| (Unsat (rho))::rest -> check_if_sat_assign_absent rest;;

let rec give_me_all_sat_assigs assigns = match assigns with
	| [] -> []
	| (Sat (rho))::rest -> rho :: (give_me_all_sat_assigs rest)
	| (Unsat (rho))::rest -> (give_me_all_sat_assigs rest);;

let rec check_if_unsat_assign_absent assigns = match assigns with
	| [] -> true
	| (Sat (rho))::rest -> check_if_unsat_assign_absent rest
	| (Unsat (rho))::rest -> false;;

let rec give_me_all_unsat_assigs assigns = match assigns with
	| [] -> []
	| (Sat (rho))::rest -> (give_me_all_unsat_assigs rest)
	| (Unsat (rho))::rest -> rho :: (give_me_all_unsat_assigs rest);;



exception NoNode;;
exception NoLeafInDevelopedTableau;;

(* Required Functions *)

let contrad_path tab = _contrad_path_ tab [];;

let rec valid_tableau tab = match tab with
	Beta (Node (p, b), t1, t2) -> _valid_tableau_ tab ((p, b, false)::[]) []
	| Alpha (Node (p, b), t1) -> _valid_tableau_ tab ((p, b, false)::[]) []
	| NotNode (Node (p, b), t1) -> _valid_tableau_ tab ((p, b, false)::[]) []
	| InternalNode (Node (p, b), t1) -> _valid_tableau_ tab ((p, b, false)::[]) []
	| Confirm (Node (p, b)) -> true
	| Contrad (Node (p, b)) -> false
	| Leaf (p, b) -> raise NoLeafInDevelopedTableau
	| Empty -> true;;

let select_node unexamnodes = match unexamnodes with
	r::rest -> r
	| [] -> raise NoNode;;

let step_develop imnode = match imnode with
	(p, b) -> (run_tableau ([Leaf (p, b)]) []);;

let find_assignments rootnode = match rootnode with
	(p, b) -> _find_assignments_ [Leaf (p, b)] [];;


let check_tautology inp_prop = (let x = (find_assignments (inp_prop, false	)) in
									(if (check_if_sat_assign_absent x) then
										((step_develop (inp_prop, false)), ([]))
									else ((Empty), (give_me_all_sat_assigs x))
									)
								);;

let check_contradiction inp_prop = (let x = (find_assignments (inp_prop, true)) in
									(if (check_if_sat_assign_absent x) then
										((step_develop (inp_prop, true)), ([]))
									else ((Empty), (give_me_all_sat_assigs x))
									)
								);; 


(* examples *)

let prop1 = (Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1"));;

let x = run_tableau [(Leaf (Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1"), false))] [];;
let y = valid_tableau x;;

let  z : tableau =
  Alpha (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false),
   Beta (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true),
    Alpha (Node (Impl (L "x1", L "x2"), false),
     InternalNode (Node (L "x1", true),
      InternalNode (Node (L "x2", false), Contrad (Node (L "x1", false))))),
    InternalNode (Node (L "x1", true), Confirm (Node (L "x1", false)))))
(* let y = valid_tableau z;; *)

let x3 = find_assignments (prop1, true);;
let x4 = find_assignments (prop1, false);;

let x1 = check_tautology prop1;;
let x2 = check_contradiction prop1;;

let z1 = contrad_path z;;
let z2 = contrad_path x;;
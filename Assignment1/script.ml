(* Assignment1 *)

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
type tableau = Leaf of prop * bool
		| Contrad of node
		| Confirm of node
		| Alpha of node * tableau
		| InternalNode of node * tableau
		| NotNode of node * tableau
		| Beta of node * tableau * tableau;;

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



let rec valid_tableau tab = match tab with
	Beta (Node (p, b), t1, t2) -> _valid_tableau_ tab ((p, b, false)::[]) []
	| Alpha (Node (p, b), t1) -> _valid_tableau_ tab ((p, b, false)::[]) [];;

(* 
val x : tableau =
  Alpha (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false),
   Beta (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true),
    Alpha (Node (Impl (L "x1", L "x2"), false),
     InternalNode (Node (L "x1", true),
      InternalNode (Node (L "x2", false), Contrad (Node (L "x1", false))))),
    InternalNode (Node (L "x1", true), Contrad (Node (L "x1", false)))))
 *)

let x = run_tableau [(Leaf (Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1"), false))] [];;

let y = valid_tableau x;;
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
type tableau = Leaf of prop*bool
		| Contrad of prop*bool
		| Confirm of prop*bool
		| Alpha of node * tableau
		| LeafNode of node * tableau
		| Beta of node * tableau * tableau;;

let rec isexists rho p = match rho with
	(m1, m2)::rest -> if m1=p then true else isexists rest p
	| [] -> false;;

let rec check_value rho p = match rho with
	(m1, m2)::rest -> if m1=p then m2 else check_value rest p 
	| [] -> false;;

let rec run_tableau tab rho = match tab with
	m::[] -> (match m with
		Leaf (Impl(p1, p2), b) -> if b=false then
								Alpha ((Node ((Impl(p1, p2)), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, false))::[]) rho))
							else
								Beta ((Node ((Impl(p1, p2)), b)), (run_tableau (Leaf (p1, false)::[]) rho), (run_tableau (Leaf (p2, true)::[]) rho)) 
		| Leaf ((L p1), b) -> (let y = (isexists rho p1) in
								(if y=true then 
									let x = (check_value rho p1) in 
										(if x = b then Confirm (L (p1), true)
										else Contrad (L (p1), b)) 
								else Confirm (L (p1), b))))
	| m::rest  -> (match m with
		Leaf (Impl (p1, p2), b) -> if b=false then
								Alpha ((Node ((Impl(p1, b)), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, false))::rest) rho))
							else
								Beta ((Node ((Impl(p1, p2)), b)), (run_tableau (Leaf (p1, false)::rest) rho), (run_tableau (Leaf (p2, true)::rest) rho))
		| Leaf (And (p1, p2), b) -> if b=false then
								Beta ((Node ((And(p1, p2)), b)), (run_tableau (Leaf (p1, false)::rest) rho), (run_tableau (Leaf (p2, false)::rest) rho))
							else
								Alpha ((Node ((Impl(p1, p2)), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, true))::rest) rho))
		| Leaf (Or (p1, p2), b) -> if b=false then
								Alpha ((Node ((Impl(p1, p2)), b)), (run_tableau ((Leaf (p1, false))::(Leaf (p2, false))::rest) rho))
							else
								Beta ((Node ((And(p1, p2)), b)), (run_tableau (Leaf (p1, true)::rest) rho), (run_tableau (Leaf (p2, true)::rest) rho))
		| Leaf (Iff (p1, p2), b) -> run_tableau (Leaf (And (Impl (p1, p2), Impl (p2, p1)), b))::rest rho
		| Leaf ((L p1), b) -> (let y = (isexists rho p1) in
								(if y=true then 
									let x = (check_value rho p1) in 
										(if x = b then (LeafNode (Node(L (p1), true), (run_tableau rest rho)))
										else Contrad (L (p1), b))
									else LeafNode (Node(L (p1), b), (run_tableau (rest) ((p1, b)::rho))) )));;


 
let x = run_tableau [(Leaf (Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1"), false))] [];;
(* Alpha((Leaf(x1->false), Alpha()), false) *)


(* type table = Leaf of (Node, int, (string*bool) list) | Alpha of node*table | Beta of node*table*table


	m::[] -> (match m with
		Leaf (Impl(p1, p2), b) -> if b=false then
								Alpha ((Node ((Impl(p1, p2)), b)), (run_tableau ((Leaf (p1, true))::(Leaf (p2, false))::[]) rho))
							else
								Beta ((Node ((Impl(p1, p2)), b)), (run_tableau (Leaf (p1, false)::[]) rho), (run_tableau (Leaf (p2, true)::[]) rho)) 
		| Leaf ((L p1), b) -> (let y = (isexists rho p1) in
								(if y=true then 
									let x = (check_value rho p1) in 
										(if x = b then Confirm (L (p1), true)
										else Contrad (L (p1), b)) 
								else Confirm (L (p1), b))))

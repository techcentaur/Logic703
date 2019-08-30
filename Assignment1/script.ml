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
type exam = Ex of node;;

type tableau = L of prop * bool;;
		| A of node * node * bool;; 
		| B of node * node * bool;; 

let contrad_path tab rho = match tab with 
	L (Leaf (p, b)) -> Let x = (isexists rho p)
						in match x with
							true -> let y = (lookup rho p) in if y=b then 0 else 1
							| false ->  2 (* not in rho *)
	| _ -> false;;

let rec run_tableau tab = match tab with
	m::rest -> match m with 
		Ex (p, true) -> run_tableau rest
		| Ex (p, false) -> match p with 
			(T, true) ->
			(T, false) ->
			(F, true) ->
			(F, false) ->
			(L s, b) ->
			(Not p1, b) ->
			(And(p1, p2), false) ->
			(And(p1, p2), true) ->
			(Or(p1, p2), false) ->
			(Or(p1, p2), true) ->
			(Iff(p1, p2), true) ->
	[] -> 
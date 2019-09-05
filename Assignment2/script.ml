(* Assignment-2 Logic703 
on Hilbert 
 *)

(* Data-types *)
type prop = T | F 
			| L of string 
            | Not of prop
            | And of prop * prop 
            | Or of prop * prop 
            | Impl of prop * prop 
            | Iff of prop * prop;;

type gamma = G of (prop list);;

type judgement = J of gamma * (prop);;

type hprooftree = Root of judgement * hprooftree 
			| MP of  judgement * judgement * judgement * hprooftree * hprooftree
			| Ass of judgement
			| K of judgement
			| S of judgement
			| R of judgement;;

let rec check_if_p_in_g g p = match g with
	G (g1::rest) -> if g1=p then true else check_if_p_in_g (G(rest)) p 
	| G([]) -> false;;

let rec _valid_hrprooftree_ tree gam = match tree with
	| MP (J (g1, p11), J(g2, Impl(p21, p12)), J(g3, p22), h1, h2) when (g1=g2 && g2=g3 && p11=p12 && p21=p22) -> 
		if g1=gam then ((_valid_hrprooftree_ h1 gam) && (_valid_hrprooftree_ h2 gam))
		else false
	| Ass (J (g, p)) -> 
		if g=gam then (
			if check_if_p_in_g g p then true else false)
		else false
	| K (J (g, Impl(p1, Impl(q, p2)))) when (p1=p2)-> 
		if g=gam then true else false
	| S (J (g, Impl(Impl(p1, Impl(q1, r1)), Impl(Impl(p2, q2), Impl(p3, r2))))) when (p1=p2 && p2=p3 && q1=q2 && r1=r2) ->
		if g=gam then true else false
	| R (J (g, Impl(Impl(Not(p1), Not(q1)), Impl(Impl(Not(p2), q2), p3)))) when (p1=p2 && p2=p3 && q1=q2) ->
		if g=gam then true else false
	| _ -> false;;


let rec do_union t1 t2 = match (t1, t2) with
	| (G p1, G p2) -> (match p1 with 
			| [] -> G p2
			| r::rest-> (do_union (G rest) (G (r::p2))));;
exception SomethingWrong;;
let rec _pad_ tree union = match tree with
	| Root (J (g, p), h) -> Root ( J (union, p), (_pad_ h (do_union g union)))
	| MP (J (g1, p11), J(g2, Impl(p21, p12)), J(g3, p22), h1, h2) ->
		MP (J (union, p11), J(union, Impl(p21, p12)), J(union, p22), (_pad_ h1 union), (_pad_ h2 union))
	| Ass (J (g, p)) -> 
		Ass (J (union, p))
	| K (J (g, Impl(p1, Impl(q, p2))))-> 
		K (J (union, Impl(p1, Impl(q, p2))))
	| S (J (g, Impl(Impl(p1, Impl(q1, r1)), Impl(Impl(p2, q2), Impl(p3, r2))))) ->
		S (J (union, Impl(Impl(p1, Impl(q1, r1)), Impl(Impl(p2, q2), Impl(p3, r2)))))
	| R (J (g, Impl(Impl(Not(p1), Not(q1)), Impl(Impl(Not(p2), q2), p3)))) -> 
		R (J (union, Impl(Impl(Not(p1), Not(q1)), Impl(Impl(Not(p2), q2), p3))))
	| _ -> raise SomethingWrong;;

let rec _prune_ tree -> 


(* main required functions *)

let rec valid_hrpooftree tree = match tree with
	| Root (J (g, p), h) -> _valid_hrprooftree_ h g
	| _ -> false;;


let pad tree delta = _pad_ tree (G delta);;

let prune tree = _prune_ tree;;
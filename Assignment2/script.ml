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

type gamma = G of (prop) list;;

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


let rec valid_hrpooftree tree = match tree with
	| Root (J (g, p), h) -> _valid_hrprooftree_ h g;;
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

type gamma = G of (prop * bool) list;;

type judgement = J of gamma * (prop);;

type hprooftree = Root of judgement * hprooftree 
			| MP of  judgement * hprooftree * hprooftree
			| Ass of judgement
			| K of judgement
			| S of judgement
			| R of judgement;;

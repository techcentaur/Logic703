(* Example *)
let p = L "p";;
let q = L "q";;

(* Example 5 *)

let gamma1 = Set [F; p];;
let gamma2 = Set [F];;

let part1 = Class(Con(Agree(gamma1, q)), Ant (Agree(gamma1, F)), End(Agree(gamma1, F)));;
let part2 = Class(Con(Agree(gamma2, p)), Ant (Agree(gamma2, F)), End(Agree(gamma2, F)));;

let ant1 = Ant(Agree(gamma1, q));;
let cos1 =  Con(Agree(gamma2, Impl(p, q)));;
let part3 = IntroImp(cos1, ant1, part1);;


let ant2 = [Ant(Agree(gamma2, Impl(p, q))); Ant(Agree(gamma2, p))];;
let part4 = ElimImp(Con(Agree(gamma2, q)), ant2, [part3; part2]);;

let part5 = Start(gamma2, part4);;
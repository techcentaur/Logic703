(* Test Case 1 - Hyp, ImpInt*)

let a1 = Agree(Set [], Impl(L "x", L "x"));;
let ca1 = Con(a1);;
let cb1 = Ant(Agree(Set [L "x"], L "x"));;

let a = IntroImp(ca1, cb1, End(Agree(Set [L "x"], L "x")));;
valid_ndprooftree (Start(Set [], a));;

let b = pad a (Set [L("y")]);;
let bb = Start(Set [L("y")], b);;

valid_ndprooftree bb;;
valid_ndprooftree (prune bb);;

(* Test Case 2 - ImpEli, OrEli*)

let _g1 = Set [L "y"; Impl(L "y", L "x")]
let _antlist = [Ant(Agree(_g1, Impl(L "y", L "x"))); Ant(Agree(_g1, L "y"))]
let _endlist = [End(Agree(_g1, Impl(L "y", L "x"))); End(Agree(_g1, L "y"))]
let _a1 = ElimImp(Con(Agree(_g1, L "x")), _antlist, _endlist);;
let __a1 = Start(_g1, _a1);;
valid_ndprooftree __a1;;

let _b1 = pad _a1 (Set [L("z")]);;

let _g11 = Set [L "z"; L "y"; Impl(L "y", L "x")];;
let _bb1 = Start(_g11, _b1);;

valid_ndprooftree _bb1;;


let __g1 = Set [L "yy"; Impl(L "y", L "x")]
let __antlist = [Ant(Agree(__g1, Impl(L "y", L "x"))); Ant(Agree(__g1, L "y"))]
let __endlist = [End(Agree(__g1, Impl(L "y", L "x"))); End(Agree(__g1, L "y"))]
let __a1 = ElimImp(Con(Agree(__g1, L "x")), __antlist, __endlist);;
let ____a1 = Start(__g1, __a1);;
valid_ndprooftree ____a1;;

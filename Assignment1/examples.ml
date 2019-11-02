let p1 = And(T, F);;
let p2 = And(T, T);;
let p3 = Or(T, F);;
let p4 = Or(F, F);;
let p5 = Impl(T, F);;
let p6 = Impl(F, T);;

let p7 = Or(T, L "a");;
let p8 = And(F, L "b");;
let p9 = Impl(F, L "c");;
let p10 = Iff(T, L "d");;

let p11 = Impl(p1, p2);;
let p12 = Not(Iff(p3, p4));;

let p13 = Iff(p10, p9);;

let p14 = Not(And(p7, p8));;
let p15 = Iff(Or(p7, p8), p9);;
let p16 = Impl(Iff(p10, p9), p2);;
let p17 = Not(And(Iff(p7, p8), Or(p8, p10)));;

let p18 = And(Or(L "a", L "b"), And(T, L "c"));;


let t1 = check_tautology p1;;
let t2 = check_tautology p2;;
let t3 = check_tautology p3;;	
let t4 = check_tautology p4;;
let t5 = check_tautology p5;;
let t6 = check_tautology p6;;
let t7 = check_tautology p7;;
let t8 = check_tautology p8;;
let t9 = check_tautology p9;;
let t10 = check_tautology p10;;
let t11 = check_tautology p11;;
let t12 = check_tautology p12;;
let t13 = check_tautology p13;;
let t14 = check_tautology p14;;
let t15 = check_tautology p15;;
let t16 = check_tautology p16;;
let t17 = check_tautology p17;;
let t18 = check_tautology p18;;

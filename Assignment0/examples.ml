(* Examples *)

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


height p1;;
height p2;;
height p3;;
height p4;;
height p5;;
height p6;;
height p7;;
height p8;;
height p9;;
height p10;;
height p11;;
height p12;;
height p13;;
height p14;;
height p15;;
height p16;;
height p17;;

size p1;;
size p2;;
size p3;;
size p4;;
size p5;;
size p6;;
size p7;;
size p8;;
size p9;;
size p10;;
size p11;;
size p12;;
size p13;;
size p14;;
size p15;;
size p16;;
size p17;;

letters p7;;
letters p8;;
letters p9;;
letters p10;;
letters p13;;
letters p14;;
letters p15;;
letters p16;;
letters p17;;



let prop1 = Or(Or(And(L "a", L "b"), And(L "c", L "d")), And(L "e", L "f"));;


let prop2 = 
And                                                                        
 (And                                                                      
   (And (Or (Or (L "a", L "c"), L "e"), Or (Or (L "b", L "c"), L "e")),    
    And (Or (Or (L "a", L "d"), L "e"), Or (Or (L "b", L "d"), L "e"))),   
  And                                                                      
   (And (Or (Or (L "a", L "c"), L "f"), Or (Or (L "b", L "c"), L "f")),    
    And (Or (Or (L "a", L "d"), L "f"), Or (Or (L "b", L "d"), L "f"))))   
;;

let prop3 = And(And(Or(L "a", L "b"), Or(L "c", L "d")), And(L "e", L "f"));;

nnf p17;;
nnf p16;;

cnf p17;;
cnf p16;;
cnf prop1;;
cnf prop2;;

dnf p17;;
dnf p16;;
dnf prop1;;
dnf prop2;;

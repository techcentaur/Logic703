(*8  - examples*)


let s1 = S[("a", 0); ("f", 2); ("g", 1); ("b", 0)];;
let s2 = S[("b", -1); ("f", 2); ("g", 1)];;
let s3 = S[("d", 5); ("f", 2); ("g", 3)];;
let s4 = S[("a", 0); ("f", 2); ("g", 1); ("g", 1)];;
let s5 = S[];;
let s6 = S[("a", 3); ("f", 2); ("g", 1); ("b", 2)];;


check_sig s1;;
check_sig s2;;
check_sig s3;;
check_sig s4;;
check_sig s5;;

let t = Node("c", [V("g")]);;
let u = Node ("b", [t; V("a")]);;
let v = Node ("a", [u;u;t]);;
let w = Node ("a", [v; u; V("x")]);;

wfterm (u,s1);;
wfterm (v,s6);;

ht t;;
ht u;;
ht v;;
ht w;;

size t;;
size u;;
size v;;
size w;;


let sx1 = [("a",V "b");("x",w)];;

subst sx1 t;;
subst sx1 u;;
subst sx1 v;;
subst sx1 w;;

let sx2 = [("b",w);("x",V "a")];;


let sx3 = composition sx1 sx2;;

let sx4 = composition sx1 sx2;;

let x = V "x";;
let a = Node ("a", []);;
let b = Node ("b", []);;
let hxa = Node ("h", [x;a]);;
let hba = Node ("h", [b;a]);;
let mgu5 = mgu hxa hba;;
subst mgu5 hxa = subst mgu5 hba;;

let hbx = Node ("h", [b;x]);;
let z = V "z";;
let hxz = Node ("h",[x;z]);;
let mgu6 = mgu hbx hxz;;
subst mgu6 hbx = subst mgu6 hxz;;

let gh = Node ("g", [hxa; hbx]);;
let ghh = Node ("g", [hba; hxz]);;
let mgu7 = mgu gh ghh;;
subst mgu7 gh = subst mgu7 ghh;;


let formK p q g = (K(J(g, Impl(p, Impl(q, p)))));;
let formS p q r g = (S(J(g, Impl(Impl(p, Impl(q, r)), Impl(Impl(p, q), Impl(p, r))))));;
let formAss p g = Ass(J(g, p));;

let g = G [];;
let p1 = L "p";;
(* let pn = L "a" *)
let q1 = Impl(p1, p1);;

let r1 = p1;;
let k1 = formK p1 q1 g;;
let s1 = formS p1 q1 r1 g;;
let rem1 = Impl(Impl(p1, q1), Impl(p1, r1))
let j1 = J (g, Impl (L "p", Impl (Impl (L "p", L "p"), L "p")))
let j2 = J (g, Impl (Impl (L "p", Impl (Impl (L "p", L "p"), L "p")), Impl (Impl (L "p", Impl (L "p", L "p")), Impl (L "p", L "p"))))

let h1 = Root(J(g, rem1), MP(J(g, rem1), j2, j1, s1, k1));;

let o1 = Impl(p1, q1);;
let k2 = formK p1 p1 g;;

let h11 = MP(J (G [],Impl (Impl (L "p", Impl (L "p", L "p")),Impl (L "p", L "p"))),J (G [], Impl (Impl (L "p", Impl (Impl (L "p", L "p"), L "p")), Impl (Impl (L "p", Impl (L "p", L "p")), Impl (L "p", L "p")))), J (G [], Impl (L "p", Impl (Impl (L "p", L "p"), L "p"))), S(J (G [],Impl (Impl (L "p", Impl (Impl (L "p", L "p"), L "p")),Impl (Impl (L "p", Impl (L "p", L "p")),Impl (L "p", L "p"))))),K (J (G [], Impl (L "p", Impl (Impl (L "p", L "p"), L "p")))))
let h2 = Root(J(g, q1), MP(J(g, q1), J(g, rem1), J(g, o1), h11, k2));;

let h3 = Root(J (G [], Impl (L "p", Impl (L "p", L "p"))), k2);;

valid_hprooftree h3;;
valid_hprooftree h1;;
valid_hprooftree h2;;

let s1 = [L "q"];;
let new_h2 = pad h2 s1;;
let pruned_h2 = prune new_h2;;

let g2 = G [rem1];;

let ass_n = formAss rem1 g2;;

let k_new = formK p1 q1 g2;;
let h_3 = Root(J(g2, q1), MP(J(g2, q1), J(g2, rem1), J(g2, o1), ass_n, k_new));;

let getrem withroot = match withroot with
	| Root (J (g, p), h) -> h;;

let himp = (getrem h1);;
let proofl = [h1];;
let g_tree = graft h_3 proofl;;


(* ded thm *)

let z1 = L "z1";;
let y1 = L "y1";;
let z2 = L "z2";;

let gam = G [L "k"; z2; Impl(z2, Impl(z1, y1))];;

let h5 = Root(J(gam, Impl(z1, y1)), MP(J(gam, Impl(z1, y1)), J(gam, Impl(z2, Impl(z1, y1))), J(gam, z2), Ass(J(gam, Impl(z2, Impl(z1, y1)))), Ass(J(gam, z2))));;
let h6 = getrem h5;;

let newj = J (G [L "z2"; Impl (L "z2", Impl (L "z1", L "y1"))], Impl (L "k", Impl (L "z1", L "y1")));;

let h7 = dedthm h6;;

let hh7 = (Root(newj, h7));;

let gemm = G [L "z2"; Impl (L "z2", Impl (L "z1", L "y1"))];;
let h8 = (Root(J(gemm, Impl(z1, y1)), h7));;
valid_hprooftree h8;;

 


(* Types*)
type symbol = string;;
type variable = string;;
type signature = S of (symbol*int) list;;
type term = V of variable | Node of symbol*(term list);;


let remove_elt e l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when e = x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l [];;

let remove_duplicates l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt x xs) (x::acc)
  in go l [];;

(*1*)
let rec check_arity s = match s with
	S((x,y)::xs) -> if y<0 then false else check_arity (S(xs))
	| S([]) -> true;;

let rec check_sym s = match s with
	S([]) -> []
	| S((x,y)::xs) -> [x] @ check_sym (S(xs));; 

let rec check_symList s = match s with
	[]-> true
	| x::xs ->  if (List.mem x xs) then false else check_symList xs;;

let check_sig s = if check_arity s then (check_symList (check_sym(s))) else false;;

exception InvalidSignature;;

let rec arity (t,s) = match (t,s) with
	(t,S((x,y)::xs))-> if x=t then y else arity (t,S(xs)) | 
	_-> raise InvalidSignature;;

(*2*)
let rec checkPresent (sym,s) = match (sym,s) with 
	(sym,S[]) -> false |
	(sym,S((x,y)::l)) -> if x=sym then true else checkPresent (sym,S(l));;

let rec termchecker (t,s) = match (t,s) with
	(V(x),s) -> true |
	(Node(x,[]),s) -> checkPresent (x,s) | 
	(Node(x,l'::l),s) -> termchecker ((l'),s);;

let wfterm (t,s) = match (t,s) with
	(V(x),s) -> true |
	(Node(x,y),s) -> if  List.length y = arity (x,s) then (termchecker (Node(x,y),s)) else false;;


(*3*)
(*Map, foldr, foldl*)
let rec map f l = match l with []->[] | x::xs -> (f x)::(map f xs);;

let rec fold_left f acc l =
  match l with
    [] -> acc
  | x :: xs -> fold_left f (f acc x) xs;;


let rec varsc term = match term with
	(V(x)) -> [x]|
	(Node(sym,x)) -> (match x with []-> [] | x'::xs -> (varsc x') @ varsc (Node(sym,xs)));; 

let vars t = match t with
	_-> remove_duplicates (varsc t);;

let add a b = a +b ;;

let rec size term = match term with
	(V(x)) -> 1 |
	(Node(sym,x)) -> (match x with
					| [] -> 1
					| x'::xs-> 1+ (fold_left add 0 (map size x)));;

let my_max l = match l with
    [] -> 0  | x::xs -> List.fold_left max x xs;;

let rec ht term = match term with
	(V(x)) -> 0 |
	(Node(sym,x)) -> (match x with
					| [] -> 0
					| x'::xs -> 1 + my_max (map (ht) x));;


(*4*)
type substitution = (variable*term) list;;

(*6*)

let rec search l x = match l with
| [] -> V (x)
| (p,q)::xs -> if (p=x) then q else search xs x;;

let rec subst sigma t = match t with
	V(x) -> search sigma x |
	Node(x,[]) -> Node(x,[]) |
	Node(x,l) -> Node(x,(List.map (subst sigma) l));;

(*5*)
let rec isexists v t = match t with
	V x -> v=x |
	Node(_,l) -> List.mem true (map (isexists v) l);; 

let rec replace t1 v2 t2 = match t2 with
 V x -> if x=v2 then t1 else t2
| Node (f,l) -> Node(f, List.map (replace t1 v2) l);;

let rec isVexistinS v s = match s with
| (x,t)::s' -> if (List.mem v (vars t)) then true else isVexistinS v s'
| _ -> false

let rec isavail l e = match (l,e) with
| [],xs -> false
| (x,y)::l, (p,q) -> if (x=p) then true else isavail l e;;

let composition s1 s2 = (
	let rec s3 s1 s2 = 
		(
		match (s1,s2) with
		([],[]) -> []| 
		(s1,[]) -> s1 |
		([],s2) -> s2 |
		((v1,t1)::s1,s2) -> (v1, subst s2 t1)::(s3 s1 s2)) in
			
			(let rec s4 ss1 ss2 = (
				match (ss1,ss2) with
				| (ss1, []) -> []
				| (ss1,x::ss2) -> if not (isavail ss1 x) then x::(s4 ss1 ss2)
				else s4 ss1 ss2) in (s4 (s3 s1 s2) s2)@(s3 s1 s2)));;


(*7*)
exception NOT_UNIFIABLE;;

let rec mgu t1 t2= match (t1,t2) with
	(V x, V y) -> if x=y then [] else [(x,V y)] |
	(V x, n) -> if isexists x n then raise NOT_UNIFIABLE else [(x, n)] |
	(n, V x) -> if isexists x n then raise NOT_UNIFIABLE else [(x, n)] |
	(Node(f,[]),Node(g,[])) -> if f=g then [] else raise NOT_UNIFIABLE |
	(Node(f,l1'::l1),Node(g,l2'::l2)) -> if f=g then (
		match ((mgu l1' l2'),List.length l1) with
			(s,0) -> s |
			(s,_) -> composition s (mgu (Node(f,(map (subst s) l1))) (Node(f,(map (subst s) l2))))
	) else raise NOT_UNIFIABLE | 
	_-> raise NOT_UNIFIABLE;;



(* -------------------------------- *)
(* part-2: resolution *)


(* `set` data type *)

type 'a set = Set of ('a list);;

let insert_into m s = match List.mem m s with 
	true -> s 
	| false -> (s @ m :: []);;

let insert m s = match s with
	Set l -> Set (insert_into m l);;

let member m s = match s with
	Set s1 -> List.mem m s1;;

let rec union s1 s2 = match s1 with
	Set [] -> s2
	| Set (m::rest) -> if member m s2 then (union (Set rest) s2) else (union (Set rest) (insert m s2));;

let rec intersection s1 s2 = match s1 with
	Set [] -> Set []
	| Set (m::rest) -> if member m s2 then insert m (intersection (Set rest) s2) else (intersection (Set rest) s2);;

(* s1 - s2 *)
let rec diff s1 s2 = match s1 with
	Set (r::rest) -> (match s2 with Set(x) -> if List.mem r x then diff (Set rest) s2 else r::(diff (Set rest) s2))
	| Set ([]) -> [];;

let difference s1 s2 = match s1 with 
	| s1 -> (let x = (diff s1 s2) in Set(x));;

(* s1.length() <= s2.length() *)
let rec subset s1 s2 = match s1 with
	Set [] -> true
	| Set (m::rest) -> if member m s2 then subset (Set rest) s2 else false;;

let length s = match s with
	Set [] -> 0
	| Set l -> List.length l;;

let equal s1 s2 = ((subset s1 s2) && (subset s2 s1));;

(* -------------------- *)


type literal = L of term | Not of term;;

let rec makeASet s result = match s with
	r::rest -> let x = (insert r result) in (makeASet rest x)
	| [] -> result;;

let rec firstClause c1 l1 mguval = match c1 with
	Set(r::rest) -> if r=l1 then firstClause (Set rest) l1 mguval else
				[(match r with L p1 -> L (subst mguval p1) | Not p2 -> Not (subst mguval p2))]@(firstClause (Set rest) l1 mguval)
	| Set([]) -> [];;

let rec secondClause c2 l2 mguval = match c2 with
	Set(r::rest) -> if r=l2 then secondClause (Set rest) l2 mguval else
			[(match r with L p1 -> L (subst mguval p1) | Not p2 -> Not (subst mguval p2))] @(secondClause (Set rest) l2 mguval)
	| Set([]) -> [];;

let resolvedClause c1 c2 l1 l2 mguval = (firstClause c1 l1 mguval) @ (secondClause c2 l2 mguval);;

let rec secondliteral l1 c_2 c1 c2 = match c_2 with
	Set(l2::rest) -> (match (l1, l2) with
			(L (t1), Not (t2)) -> (let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
									(match x with
										| Some(z) -> (let y = (resolvedClause c1 c2 (L t1) (Not t2) z) in (makeASet y (Set []), true))
										| None -> (secondliteral l1 (Set rest) c1 c2)
									)
								) 
			| (Not t1, L t2) ->  (let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
									(match x with
										| Some(z)-> let y = (resolvedClause c1 c2 (Not t1) (L t2) z) in (makeASet y (Set []), true)
										| None -> secondliteral l1 (Set rest) c1 c2
									)
								)
			| (Not t1, Not t2) -> secondliteral l1 (Set rest) c1 c2
			| (L t1, L t2) -> secondliteral l1 (Set rest) c1 c2)
	| Set [] -> (Set [], false);;

let rec firstliteral c_1 c1 c2 = match c_1 with
	Set(l1::rest) -> let (x, y) = (secondliteral l1 c2 c1 c2) in 
				(if y 
					then [x] @ (firstliteral (Set rest) c1 c2)
				else (firstliteral (Set rest) c1 c2)
				)
	| Set([]) -> [];;


let rec selectSecondClause c1 rest nw = match rest with
	Set [] -> nw
	| Set(c2::rest2) -> (let x = (firstliteral c1 c1 c2) in 	
							(if (List.length x) = 0
								then (selectSecondClause c1 (Set rest2) nw) 
							else (
								let y = (makeASet x (Set [])) in
									(selectSecondClause c1 (Set rest2) (union nw y))
							)
						));;

let rec selectFirstClause prop total = match prop with
	Set ([]) -> total
	| Set (c1::rest) -> (let x = (selectSecondClause c1 (Set rest) total) in(
								let y = (union total x) in 
								(selectFirstClause (Set rest) y)
							)
						);;

let rec _resolution prop = (let x = (selectFirstClause prop prop) in
							(if length x = length prop
								then prop
							else _resolution (union prop x)));;

let rec _contains_empty p = match p with
	Set(r::rest) -> if length r = 0 then true else (_contains_empty (Set rest))
	| Set([]) -> false;;

let contains_empty p = (if length p = 0 then true else (if (_contains_empty p) then false else true));;

let rec resolution prop = (contains_empty (_resolution prop));;


let rec secondliteral____ l1 c_2 c1 c2 = match c_2 with
	Set(l2::rest) -> (match (l1, l2) with
			(L (t1), Not (t2)) -> (let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
									(match x with
										| Some(z) -> 1
										| None -> (secondliteral____ l1 (Set rest) c1 c2)
									)
								) 
			| (Not t1, L t2) ->  (let x = (try Some(mgu t1 t2) with NOT_UNIFIABLE -> None) in
									(match x with
										| Some(z)-> 1
										| None -> secondliteral____ l1 (Set rest) c1 c2
									)
								)
			| (Not t1, Not t2) -> secondliteral____ l1 (Set rest) c1 c2
			| (L t1, L t2) -> secondliteral____ l1 (Set rest) c1 c2)
	| Set [] -> 0

let rec firstliteral____ c_1 c1 c2 = match c_1 with
	Set(l1::rest) -> let x = (secondliteral____ l1 c2 c1 c2) in 
				(if x = 1
					then 1
				else (firstliteral____ (Set rest) c1 c2)
				)
	| Set([]) -> 0;;


let rec selectSecondClause____ c1 rest = match rest with
	Set [] -> []
	| Set(c2::rest2) -> (let x = (firstliteral____ c1 c1 c2) in 	
							(if x = 0
								then (selectSecondClause____ c1 (Set rest2)) 
							else ([c1; c2])
						));;

let rec selectFirstClause____ prop = match prop with
	Set ([]) -> []
	| Set (c1::rest) -> (let x = (selectSecondClause____ c1 (Set rest)) in(
								if List.length x = 0 then
									(selectFirstClause____ (Set rest))
								else x
							)
						);;

exception NotFound;;
let select_clauses setset = (let x = selectFirstClause____ setset in (if List.length x = 2 then x else raise NotFound));;

let one_step_resolution c1 c2 l1 l2 mggg = resolvedClause c1 c2 l1 l2 mggg;;

(* 5 - examples*)

let p = V ("x");;	
let q = V ("y");;

let p1 = L (p);;
let q1 = L (q);;
let p2 = Not (p);;
let q2 = Not (q);;

(* let c1 = Set [p1; q1];;
let c2 = Set [p2; q1];;
let c3 = Set [p1; q2];;
let c4 = Set [p2; q2];;

let cs = Set [c2; c3; c4];;
let r0 = resolution cs;;
 *)

let c1 = Set [p1];;
let c2 = Set [q1];;
let c3 = Set [p2; q2];;
let cs1 = Set [c1; c2; c3];;
let r1 = resolution cs1;;

let sc = select_clauses cs1;;

let cc1 = Set [L (V "x")];;
let cc2 = Set [Not (V "x"); Not (V "y")];;

let ll1 = L (V "x");;
let ll2 = Not (V "x");;

one_step_resolution cc1 cc2 ll1 ll2 (mgu (V "x") (V "x"));;



(* Example 1 *)
(* 
let c1 = Set [p1];;
let c2 = Set [q1];;
let c3 = Set [p2; q2];;
let cs1 = Set [c1; c2; c3];;
let r1 = resolution cs1;;
 *)
(* Example 2 *)

(* let a = (V "a");;
let h = (V "h");;
let i = (V "i");;
let m = (V "m");;

let a1 = L (a);;
let a2 = Not (a);;
let h1 = L (h);;
let h2 = Not (h);;


let i1 = L (i);;
let i2 = Not (i);;
let m1 = L (m);;
let m2 = Not (m);;


let c1 = Set [a2; h1];;
let c2 = Set [h2];;
let c3 = Set [i2; h1];;
let c4 = Set [m1; a1];;
let c5 = Set [m2; i1];;

let cl2 = Set [c1; c2; c3; c4; c5];;
let r2 = resolution cl2;;

 *)

(* Example 3 *)
(* let r = V "r";;
let r1 = L (r);;
let r2 = Not (r);;

let c1 = Set [p1];;
let c2 = Set [p2; q1];;
let c3 = Set [p2; q2; r1];;
let c4 = Set [r2];;

let cl3 = Set [c1; c2; c3; c4];;
let r3 = resolution cl3;;
 *)
(* Example 4 *)

(* Name change for lily-fufu example *)

let jon = Node("jon", []);;
let ygritte = Node("ygritte", []);;

let t1 = Node("catelyn", [jon; ygritte]);;
let x = V ("x");;
let y = V ("y");;

let t2 = Node("catelyn", [x; y]);;
let t3 = Node("parent", [x; y]);;

let t4 = Node("wight", [x]);;
let t5 = Node("dead", [x; y]);;
let t6 = Node("wight", [jon]);;
let t7 = Node("dead", [jon; ygritte]);;

let l1 = L (t1);;
let l2 = Not (t2);;
let l3 = L (t3);;
let l4 = Not (t3);;
let l5 = Not (t4);;
let l6 = L (t5);;
let l7 = L (t6);;
let l8 = Not (t7);;

let c1 = Set [l1];;
let c2 = Set [l2; l3];;
let c3 = Set [l4; l5; l6];;
let c4 = Set [l7];;
let c5 = Set [l8];;

let cl4 = Set [c1; c2; c3; c4; c5];;
let r4 = resolution cl4;;

(* For mgu only example *)
let t1 = (Node("F", [V "X"; Node("G", [V "Z"])]));;
let t2 = (Node("F", [V "Y"; Node("G", [Node("H", [V "Y"])])]));;
let c2 = mgu t1 t2;;


(* 6 *)

(* Yes, my algorithm will always terminate. Because there are a finite number of possible resolution even if each step adds one resolution.
This means that any literal can or can not occur in a clause, and thus the algorithm will go on only a finite number of steps,
even if the clauses are not Horn. *)
 
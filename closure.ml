(* A simple interpreter for the lambda calculus *)

open Il1

(* 
A closure will be a tuple with a field over all possible variables of a program. 
See main.pdf to get a gist of what's going on.
*)

let id =  ref 0
let fresh x = 
  id := !id + 1;
  ("$"^x)^(string_of_int (!id))

let rec make_fresh x n : var list =
  if n <= 0 then
    []
  else
    (fresh x) :: (make_fresh x (n-1))

let rec expand_xi xs n g c : c =
  match xs with
  | x::tl ->
    Let(x, g n, expand_xi tl (n+1) g c)
  | [] ->
    c

let gindex p n =
  Index(n+1, p)

(* bij: partial bijection between var and int, n the number of elements in var*)
let rec close_v (bij:var -> int) (n:int) (v:v) (p:v) : e =
  match v with
  | Int n -> Val v
  | Var x -> Index(bij x,p)
  | Halt -> Val v
  | Lam(x,c) -> 
    let k = bij x in
	let r = fresh "r" in
    let p' = fresh "p'"  and y = fresh "y" and p'' = fresh "p''" in
	let xs = make_fresh "x" n in
	let c' = close_c bij n c (Var p'') in
	let c' = Let(p'', Tuple(List.map (fun x -> Var x) xs), c') in
	let c' = Let(List.nth xs k, Val (Var y), c') in
	let c' = expand_xi xs 0 (gindex (Var p')) c' in
	let c' = Let(y, Index(2,Var r), c') in
	let c' = Let(p', Index(1,Var r), c') in
	Tuple([p; Lam(r,c')])
  | Fun(x,k,c) -> 
    let a = bij x in
	let b = bij k in
	let r = fresh "r" in
    let p' = fresh "p'"  and y = fresh "y" and p'' = fresh "p''" in
	let xs = make_fresh "x" n in
	let c' = close_c bij n c (Var p'') in
	let c' = Let(p'', Tuple(List.map (fun x -> Var x) xs), c') in
	let c' = Let(List.nth xs b, Val (Var k), c') in
	let c' = Let(List.nth xs a, Val (Var y), c') in
	let c' = expand_xi xs 0 (gindex (Var p')) c' in
	let c' = Let(y, Index(2,Var r), c') in
	let c' = Let(p', Index(1,Var r), c') in
	Tuple([p; Fun(r,k,c')])
and close_c (bij:var -> int) (n:int) (c:c) (p:v) : c =
  failwith "implement me!"
and close_e (bij:var -> int) (n:int) (e:e) (p:v) : (var * e) list * e =
  match e with
  | Val v -> ([], close_v bij n v p)
  | Plus(v1,v2) -> 
    let x0 = fresh "x" and x1 = fresh "x" in
	([(x0,close_v bij n v1 p); (x1,close_v bij n v2 p)], Plus(Var x0, Var x1))
	
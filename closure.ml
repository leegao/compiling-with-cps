(* A simple interpreter for the lambda calculus *)

open Il1

(* 
Explicit abstraction as closures
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

let rec close_v (g:var -> int) (v:v) (rhos:var list) : v =
  match v with
  | Int n -> v
  | Var x -> Var (List.nth rhos ((g x)-1))
  | Halt -> v
  | Fun(x,k,[],c) -> 
    let px = List.nth rhos ((g x)-1) in
	let pk = List.nth rhos ((g k)-1) in
    Fun(x,k,rhos, Let(px, Val (Var x), Let(pk, Val(Var k), close_c g c rhos)))
and close_e (g:var -> int) (e:e) (rhos:var list) : e =
  match e with
  | _ -> failwith "close_e"
and close_c (g:var -> int) (c:c) (rhos:var list) : c =
  match c with
  | _ -> failwith "close_c"
  
(* calculate all variables of e (no including ps) *)
let rec vs_c (c:c) : VarSet.t = 
  match c with 
  | Let(x,e',c') -> 
    VarSet.union (VarSet.union (vs_e e') ((vs_c c'))) (VarSet.singleton x)
  (*| App(v1,v2)  -> 
    VarSet.union (vs_v v1) (vs_v v2)*)
  | Call(v1,v2,v3,ps) -> 
    VarSet.union (VarSet.union (vs_v v1) (vs_v v2)) (vs_v v3)
and vs_e (e:e) : VarSet.t =
  match e with
  | Val v -> vs_v v
  | Plus(v1,v2) -> VarSet.union (vs_v v1) (vs_v v2)
  | Tuple(vs) ->
    List.fold_left (fun a v -> VarSet.union a (vs_v v)) VarSet.empty vs
  | Index(n,v) ->
    vs_v v
and vs_v (v:v) : VarSet.t =
  match v with
  | Var x -> VarSet.singleton x
  (*| Lam(x,c) -> VarSet.union (vs_c c) (VarSet.singleton x)*)
  | Fun(x,k,ps,c) -> VarSet.union (VarSet.union (vs_c c) (VarSet.singleton x)) (VarSet.singleton k)
  | _ -> VarSet.empty

let build_g c =
  let vs = VarSet.elements (vs_c c) in
  let rec helper n vs x =
    match vs with
    | y::tl ->
      if x = y then n else helper (n+1) tl x
    | [] ->
      failwith "not found" in
  (helper 1 vs, List.length vs)

let close c =
  let (g,n) = build_g c in
  let rhos = make_fresh "rho" n in
  let rec helper n c =
    if n <= 0 then c else Let(List.nth rhos (n-1), Val Halt, helper (n-1) c) in
  let c' = close_c g c rhos in
  helper n c'
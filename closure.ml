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
  | Halt -> 
    (* Halt is a fuction! *)
    Tuple([p; Halt])
  | Lam(x,c) -> 
    let k = bij x in
    let r = fresh "r" in
    let p' = fresh "p'"  and y = fresh "y" and p'' = fresh "p''" in
    let xs = make_fresh "x" n in
    let c' = close_c bij n c (Var p'') in
    let c' = Let(p'', Tuple(List.map (fun x -> Var x) xs), c') in
    let c' = Let(List.nth xs (k-1), Val (Var y), c') in
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
    let c' = Let(List.nth xs (b-1), Val (Var k), c') in
    let c' = Let(List.nth xs (a-1), Val (Var y), c') in
    let c' = expand_xi xs 0 (gindex (Var p')) c' in
    let c' = Let(y, Index(2,Var r), c') in
    let c' = Let(p', Index(1,Var r), c') in
    Tuple([p; Fun(r,k,c')])
and close_e (bij:var -> int) (n:int) (e:e) (p:v) : (var * e) list * e =
  match e with
  | Val v -> ([], close_v bij n v p)
  | Plus(v1,v2) -> 
    let x0 = fresh "x" and x1 = fresh "x" in
    ([(x0,close_v bij n v1 p); (x1,close_v bij n v2 p)], Plus(Var x0, Var x1))
  | Tuple(vs) ->
    let rec helper vs xs = 
      match vs with
      | v::tl ->
        let x = fresh "x" in
        let (defs,e') = helper tl (Var x::xs) in
        ((x,close_v bij n v p)::defs, e')
      | [] ->
        ([], Tuple(List.rev xs)) in
    helper vs []
  | Index(i,v) ->
    let x = fresh "x" in
    ([x,close_v bij n v p], Index(i, Var x))
and close_c (bij:var -> int) (n:int) (c:c) (p:v) : c =
  match c with
  | Let(x,e,c') ->
    let (lets, e') = close_e bij n e p in
    let y = fresh "y" and xs = make_fresh "x" n
    and p' = fresh "p'" in
    let c'' = close_c bij n c' (Var p') in
    let c'' = Let(p', Tuple(List.map (fun x -> Var x) xs), c'') in
    let c'' = Let(List.nth xs ((bij x) - 1), Val (Var y), c'') in
    let c'' = expand_xi xs 0 (gindex p) c'' in
    let c'' = Let(y, e', c'') in
    let rec helper lets c =
      match lets with
      | (xi,ei)::tl -> 
        Let(xi, ei, helper tl c)
      | [] ->
        c in
    helper lets c''
  | App(v0,v1) ->
    let fn = fresh "fn" and p' = fresh "p'" and f = fresh "f" and v' = fresh "v'"
    and arg = fresh "arg" in
    let c' = App(Var f, Var arg) in
    let c' = Let(arg, Tuple([Var p'; Var v']), c') in
    let c' = Let(v', close_v bij n v1 p, c') in
    let c' = Let(f, Index(2,Var fn), c') in
    let c' = Let(p', Index(1,Var fn), c') in
    Let(fn, close_v bij n v0 p, c')
  | Call(v0,v1,v2) ->
    let fn = fresh "fn" and p' = fresh "p'" and f = fresh "f" and v' = fresh "v'"
    and arg = fresh "arg" and k = fresh "k" in
    let c' = Call(Var f, Var arg, Var k) in
    let c' = Let(k, close_v bij n v2 p, c') in
    let c' = Let(arg, Tuple([Var p'; Var v']), c') in
    let c' = Let(v', close_v bij n v1 p, c') in
    let c' = Let(f, Index(2,Var fn), c') in
    let c' = Let(p', Index(1,Var fn), c') in
    Let(fn, close_v bij n v0 p, c')
  
(* calculate all variables of e *)
let rec vs_c (c:c) : VarSet.t = 
  match c with 
  | Let(x,e',c') -> 
    VarSet.union (VarSet.union (vs_e e') ((vs_c c'))) (VarSet.singleton x)
  | App(v1,v2)  -> 
    VarSet.union (vs_v v1) (vs_v v2)
  | Call(v1,v2,v3) -> 
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
  | Lam(x,c) -> VarSet.union (vs_c c) (VarSet.singleton x)
  | Fun(x,k,c) -> VarSet.union (VarSet.union (vs_c c) (VarSet.singleton x)) (VarSet.singleton k)
  | _ -> VarSet.empty

let build_bij c =
  let vs = VarSet.elements (vs_c c) in
  let rec helper n vs x =
    match vs with
    | y::tl ->
      if x = y then n else helper (n+1) tl x
    | [] ->
      failwith "not found" in
  (helper 1 vs, List.length vs)

let close c =
  let (bij,n) = build_bij c in
  let rec helper n =
    if n <= 0 then [] else Halt :: helper (n-1) in
  let p = fresh "p" in
  let c' = close_c bij n c (Var p) in
  Let(p, Tuple(helper n), c')
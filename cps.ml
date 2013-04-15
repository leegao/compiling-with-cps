(* A simple interpreter for the lambda calculus *)

open Types

exception Fail of string

let id =  ref 0
let fresh x = 
  id := !id + 1;
  ("$"^x)^(string_of_int (!id))

let rec translate1 (e:exp) (k:Il1.v): Il1.c =
  match e with
  | Var x -> Il1.App(k, Il1.Var x)
  | Num n -> Il1.App(k, Il1.Int n)
  | Lambda (x, e') -> 
    let k' = fresh "k" in
    Il1.App(k, Il1.Fun(x, k', translate1 e' (Il1.Var k')))
  | App(e1,e2) ->
    let f = fresh "f" in
    let v = fresh "v" in
    translate1 e1 (
      Il1.Lam(f, translate1 e2 (
        Il1.Lam(v, Il1.Call(Il1.Var f, Il1.Var v, k))
      ))
    )
  | Let(x,e1,e2) ->
    translate1 e1 (Il1.Lam(x, translate1 e2 k))
  | Plus(e1,e2) ->
    let n1 = fresh "n" and n2 = fresh "m" and z = fresh "z" in
    translate1 e1 (Il1.Lam(n1, translate1 e2 (Il1.Lam(n2, Il1.Let(z, Il1.Plus(Il1.Var n1, Il1.Var n2), Il1.App(k, Il1.Var z))))))

(* IL1 Optimization *)
let rec cp_c (c:Il1.c) : Il1.c =
  match c with
  | Il1.Let(x,e',c') ->
    Il1.Let(x, cp_e e', cp_c c')
  | Il1.Call(v0,v1,v2) ->
    Il1.Call(cp_v v0, cp_v v1, cp_v v2)
  | Il1.App(Il1.Lam(x,c'), Il1.Var y) ->
    (*Copy Propagate*)
    if x = y then
      cp_c c'
    else
      cp_c (Il1.subst_c (Il1.Var y) x c')
  | Il1.App(v0,v1) ->
    Il1.App(cp_v v0, cp_v v1)
and cp_e (e:Il1.e) : Il1.e =
  match e with
  | Il1.Val(v) -> Il1.Val(cp_v v)
  | Il1.Plus(v1,v2) -> Il1.Plus(cp_v v1, cp_v v2)
and cp_v (v:Il1.v) : Il1.v = 
  match v with
  | Il1.Fun (x,k,c) -> Il1.Fun (x,k,cp_c c)
  | Il1.Lam (x,c) -> Il1.Lam (x,cp_c c)
  | _ -> v

let rec lp_c (c:Il1.c) : Il1.c =
  match c with
  | Il1.Let(x,e',c') ->
    Il1.Let(x, lp_e e', lp_c c')
  | Il1.Call(v0,v1,v2) ->
    Il1.Call(lp_v v0, lp_v v1, lp_v v2)
  | Il1.App(Il1.Lam(x,c'), v) ->
    (*Let Propagate*)
    Il1.Let(x, Il1.Val (lp_v v), lp_c c')
  | Il1.App(v0,v1) ->
    Il1.App(lp_v v0, lp_v v1)
and lp_e (e:Il1.e) : Il1.e =
  match e with
  | Il1.Val(v) -> Il1.Val(lp_v v)
  | Il1.Plus(v1,v2) -> Il1.Plus(lp_v v1, lp_v v2)
and lp_v (v:Il1.v) : Il1.v = 
  match v with
  | Il1.Fun (x,k,c) -> Il1.Fun (x,k,lp_c c)
  | Il1.Lam (x,c) -> Il1.Lam (x,lp_c c)
  | _ -> v

let rec ep_c (c:Il1.c) : Il1.c =
  match c with
  | Il1.Let(x,e',c') ->
    Il1.Let(x, ep_e e', ep_c c')
  | Il1.Call(v0,v1,v2) ->
    Il1.Call(ep_v v0, ep_v v1, ep_v v2)
  | Il1.App(v0,v1) ->
    Il1.App(ep_v v0, ep_v v1)
and ep_e (e:Il1.e) : Il1.e =
  match e with
  | Il1.Val(v) -> Il1.Val(ep_v v)
  | Il1.Plus(v1,v2) -> Il1.Plus(ep_v v1, ep_v v2)
and ep_v (v:Il1.v) : Il1.v = 
  match v with
  | Il1.Fun (x,k,c) -> Il1.Fun (x,k,ep_c c)
  | Il1.Lam (x, Il1.App(v, Il1.Var y)) ->
    if x = y then
      (* Eta reduce *)
      ep_v v
    else
      Il1.Lam (x,ep_c (Il1.App(v, Il1.Var y)))
  | Il1.Lam (x,c) -> Il1.Lam (x,ep_c c)
  | _ -> v

(* 
  Lambda Hoisting
    The point is to lift all lambdas
*)
let rec hoist_c (c:Il1.c) : Il1.c * Il1.def list =
  match c with
  | Il1.Let(x,e',c') ->
    let (e'', l1) = hoist_e e' in 
    let (c'', l2) = hoist_c c' in
    (Il1.Let(x,e'',c''), l1 @ l2)
  | Il1.Call(v1,v2,v3) ->
    let (v1', l1) = hoist_v v1 in
    let (v2', l2) = hoist_v v2 in
    let (v3', l3) = hoist_v v3 in
    (Il1.Call(v1',v2',v3'), l1@l2@l3)
  | Il1.App(v1,v2) ->
    let (v1', l1) = hoist_v v1 in
    let (v2', l2) = hoist_v v2 in
    (Il1.App(v1',v2'), l1@l2)
and hoist_e (e:Il1.e) : Il1.e * Il1.def list =
  match e with
  | Il1.Val v ->
    let (v',l) = hoist_v v in
    (Il1.Val v', l)
  | Il1.Plus (v1,v2) ->
    let (v1', l1) = hoist_v v1 in
    let (v2', l2) = hoist_v v2 in
    (Il1.Plus(v1',v2'), l1@l2)
and hoist_v (v:Il1.v) : Il1.v * Il1.def list =
  match v with
  | Il1.Var x -> 
    (v, [])
  | Il1.Int n ->
    (v, [])
  | Il1.Halt ->
    (v, [])
  | Il1.Lam(x,c) ->
    let (c', l) = hoist_c c in
    (* generate a new fresh name for this guy *)
    let f = fresh "fun" in
    (* replace this lambda by f (no capturing of variables) *)
    let l' = ((f, Il1.Lam(x,c')))::l in
    (Il1.Var f, l')
  | Il1.Fun(x,k,c) ->
    let (c', l) = hoist_c c in
    (* generate a new fresh name for this guy *)
    let f = fresh "fun" in
    (* replace this lambda by f (no capturing of variables) *)
    let l' = ((f, Il1.Fun(x,k,c')))::l in
    (Il1.Var f, l')
  
(* Implement this! *)
let translate(e: exp): tprog =
  let c = translate1 e Il1.Halt in
  
  let c = cp_c c in
  let c = lp_c c in
  let c = ep_c c in
  
  let (c', defs) = hoist_c c in
  Il1.print_c c' 0;
  Il1.pp "\n";
  match e with
    _ -> raise (Fail "Implement me!")



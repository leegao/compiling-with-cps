(* A simple interpreter for the lambda calculus *)

open Types
open Optimize

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
    
(* 
  Lambda Hoisting without closure conversion
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



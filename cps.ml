(* A simple interpreter for the lambda calculus *)

open Types
open Optimize

exception Fail of string

let fresh = Closure.fresh

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
  | Tuple(lst) ->
    let rec helper l (tp:Il1.v list) : Il1.c =
      match l with
      | hd::tl ->
        let v = fresh "v" in
        translate1 hd (Il1.Lam(v, helper tl ((Il1.Var v)::tp)))
      | [] ->
        let t = fresh "t" in
        Il1.Let(t, Il1.Tuple (List.rev tp), Il1.App(k, Il1.Var t)) in
    helper lst []
  | Index(n, e') -> 
    let t = fresh "t" in
    let y = fresh "y" in
    translate1 e' (Il1.Lam(t, Il1.Let(y, Il1.Index(n,Il1.Var t), Il1.App(k, Il1.Var y))))
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
  | Il1.Tuple (vs) ->
    let (vs', defs) = List.fold_left (
      fun a v -> 
        let (vs, defs) = a in
        let (v0,def0) = hoist_v v in 
        ((v0)::(vs), (def0)@(defs))
    ) ([],[]) vs in
    (Il1.Tuple (List.rev vs'), defs)
  | Il1.Index(n,v) ->
    let (v',l) = hoist_v v in
    (Il1.Index(n,v'), l)
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

let rec expand (l: (var * Il1.e) list) c : Il1.c = 
  match l with
  | (x,e)::tl ->
    Il1.Let(x,e,expand tl c)
  | [] ->
    c
    
let rec lower_v (v:Il1.v) : (var * Il1.e) list * var =
  match v with
  | Il1.Var x ->
    ([], x)
  | _ ->
    let x = fresh "n" in
    ([x,Il1.Val v], x)
and lower_e e : (var * Il1.e) list * Il1.e =
  match e with
  | Il1.Val v ->
    ([], e)
  | Il1.Plus(v0,v1) ->
    let (l0,x0) = lower_v v0 and (l1,x1) = lower_v v1 in
    (l0@l1, Il1.Plus(Il1.Var x0, Il1.Var x1))
  | Il1.Tuple(vs) ->
    let rec helper vs =
      match vs with
      | v::tl ->
        let (l,x) = lower_v v in
        let (defs, tup) = helper tl in
        (l@defs, (Il1.Var x)::tup)
      | [] ->
        ([], []) in
    let (l,tup) = helper vs in
    (l, Il1.Tuple tup)
  | Il1.Index(n,v) ->
    let (l,x) = lower_v v in
    (l, Il1.Index(n, Il1.Var x))
and lower_c c : Il1.c =
  match c with 
  | Il1.Let(x,e,c) ->
    let (l,e') = lower_e e in
    expand l (Il1.Let(x,e', lower_c c))
  | Il1.App(v0,v1) ->
    let (l0,x) = lower_v v0 in
    let (l1,y) = lower_v v1 in
    expand l0 (expand l1 (Il1.App(Il1.Var x, Il1.Var y)))
  | Il1.Call(v0,v1,v2) ->
    let (l0,x) = lower_v v0 in
    let (l1,y) = lower_v v1 in
    let (l2,z) = lower_v v2 in
    expand l0 (expand l1 (expand l2 (Il1.Call(Il1.Var x, Il1.Var y, Il1.Var z))))

let rec lower_defs defs =
  match defs with
  | (x,Il1.Lam(y,c))::tl -> 
    (x,Il1.Lam(y,lower_c c))::lower_defs tl
  | (x,Il1.Fun(y,k,c))::tl ->
    (x,Il1.Fun(y,k,lower_c c))::lower_defs tl
(* Implement this! *)
let translate(e: exp): tprog =
  let c = translate1 e Il1.Halt in
  let c' = Closure.close c in
  let (c'', defs) = hoist_c c' in
  Il1.print_c c 0;
  Il1.pp "\n";
  Il1.print_c c'' 0;
  Il1.pp "\n";
  match e with
    _ -> raise (Fail "Implement me!")



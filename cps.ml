(* A simple interpreter for the lambda calculus *)

open Types

exception Fail of string

let fresh = Closure.fresh

(* this is the "continuation" slot in continuations.
   obviously not going to be used *)
let kap = fresh "kappa"

let rec translate1 (e:exp) (k:Il1.v): Il1.c =
  match e with
  | Num n -> Il1.Call(k, Il1.Int n, Il1.Int 0, [])
  | Var x -> Il1.Call(k, Il1.Var x, Il1.Int 0, [])
  | Lambda(x,e) -> let k' = fresh "k'" in
    Il1.Call(k, (Il1.Fun(x,k',[], translate1 e (Il1.Var k'))), Il1.Int 0, [])
  | App(e0,e1) -> let v = fresh "v" and f = fresh "f" in
    translate1 e0 (Il1.Fun(f,kap,[], translate1 e1 (Il1.Fun(v,kap,[], Il1.Call(Il1.Var f, Il1.Var v, k, [])))))
  | Tuple(es) -> 
    let rec helper es xs =
      match es with
      | e::tl ->
        let x = fresh "x" in
        translate1 e (Il1.Fun(x,kap,[], helper tl (Il1.Var x::xs)))
      | [] ->
        let p = fresh "p" in
        Il1.Let(p, Il1.Tuple(List.rev xs), Il1.Call(k, Il1.Var p, Il1.Int 0, [])) in
    helper es []
  | Index(n,e) ->
    let p = fresh "p" in
    translate1 e (Il1.Fun(p,kap,[], Il1.Let(p, Il1.Index(n, Il1.Var p), Il1.Call(k, Il1.Var p, Il1.Int 0, []))))
  | Plus(e0,e1) ->
    let x0 = fresh "x0" and x1 = fresh "x1" and n = fresh "n" in
    translate1 e0 (Il1.Fun(x0,kap,[], translate1 e1 (Il1.Fun(x1,kap,[], 
      Il1.Let(n, Il1.Plus(Il1.Var x0, Il1.Var x1), Il1.Call(k, Il1.Var n, Il1.Int 0, []))
    ))))
  | Let(x,e1,e2) ->
    translate1 e1 (Il1.Fun(x,kap,[], translate1 e2 k))
  | Ifp(e0,e1,e2) ->
    let b = fresh "b" and k' = fresh "k'" and f = fresh "f" in
    let kap = fresh "kap" in
    (*translate1 e0 (Il1.Fun(b,kap,[], translate1 e1 (Il1.Fun(v1,kap,[], translate1 e2 
      (Il1.Fun(v2,kap,[], Il1.Let(b, Il1.Ifp(Il1.Var b, Il1.Var v1,Il1.Var v2), Il1.Call(k, Il1.Var b, Il1.Halt, []))))
    ))))*)
    let f0 = Il1.Fun(kap,kap,[], translate1 e1 (Il1.Var k')) and
        f1 = Il1.Fun(kap,kap,[], translate1 e2 (Il1.Var k')) in
    Il1.Let(k', Il1.Val k, translate1 e0 (Il1.Fun(b,kap,[], Il1.Let(f, Il1.Ifp(Il1.Var b, f0, f1), Il1.Call(Il1.Var f, Il1.Int 0, Il1.Int 0, [])))))
  | Cwcc(e) ->
    let k' = fresh "k" and f = fresh "f" in
    match k with
    | Il1.Var k'' ->
      let k' = k'' in
      translate1 e (Il1.Fun(f,kap,[], Il1.Call(Il1.Var f, Il1.Var k', Il1.Var k', [])))
    | _ ->
      Il1.Let(k',Il1.Val k, translate1 e (Il1.Fun(f,kap,[], Il1.Call(Il1.Var f, Il1.Var k', Il1.Var k', []))))
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
  | Il1.Call(v1,v2,v3,ps) ->
    let (v1', l1) = hoist_v v1 in
    let (v2', l2) = hoist_v v2 in
    let (v3', l3) = hoist_v v3 in
    (Il1.Call(v1',v2',v3',ps), l1@l2@l3)
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
    let rec helper vs =
      match vs with
      | v::tl ->
        let (vs',defs') = helper tl in
        let (v', defs) = hoist_v v in
        (v'::vs', defs@defs')
      | _ ->
        ([],[]) in
    let (vs',defs) = helper vs in
    (Il1.Tuple vs', defs)
  | Il1.Index(n,v) ->
    let (v',l) = hoist_v v in
    (Il1.Index(n,v'), l)
  | Il1.Ifp(v0,v1,v2) ->
    let (v0',l0) = hoist_v v0 in
    let (v1',l1) = hoist_v v1 in
    let (v2',l2) = hoist_v v2 in
    (Il1.Ifp(v0',v1',v2'), l0@l1@l2)
and hoist_v (v:Il1.v) : Il1.v * Il1.def list =
  match v with
  | Il1.Var x -> 
    (v, [])
  | Il1.Int n ->
    (v, [])
  | Il1.Halt ->
    (v, [])
  | Il1.Fun(x,k,ps,c) ->
    let (c', l) = hoist_c c in
    (* generate a new fresh name for this guy *)
    let f = fresh "fun" in
    (* replace this lambda by f (no capturing of variables) *)
    let l' = l @ [((f, Il1.Fun(x,k,ps,c')))] in
    (Il1.Var f, l')

let rec expand (l: (var * Il1.e) list) c : Il1.c = 
  match l with
  | (x,e)::tl ->
    Il1.Let(x,e,expand tl c)
  | [] ->
    c

let halt' = fresh "halt"
    
let rec lower_v (v:Il1.v) : (var * Il1.e) list * var =
  match v with
  | Il1.Var x ->
    ([], x)
  | Il1.Int n ->
    let x = fresh "n" in
    ([x,Il1.Val v], x)
  | Il1.Halt ->
    ([halt', Il1.Val v], halt')
  | _ -> raise (Fail "cannot have functions in lower, should have been hoisted already")
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
  | Il1.Ifp(v0,v1,v2) ->
    let (l0,x0) = lower_v v0 in
    let (l1,x1) = lower_v v1 in
    let (l2,x2) = lower_v v2 in
    (l0@l1@l2, Il1.Ifp(Il1.Var x0, Il1.Var x1, Il1.Var x2))
and lower_c c : Il1.c =
  match c with 
  | Il1.Let(x,e,c) ->
    let (l,e') = lower_e e in
    expand l (Il1.Let(x,e', lower_c c))
  | Il1.Call(v0,v1,v2,ps) ->
    let (l0,x) = lower_v v0 in
    let (l1,y) = lower_v v1 in
    let (l2,z) = lower_v v2 in
    expand l0 (expand l1 (expand l2 (Il1.Call(Il1.Var x, Il1.Var y, Il1.Var z,ps))))

let rec lower_defs defs =
  match defs with
  | (x,Il1.Fun(y,k,ps,c))::tl ->
    (x,Il1.Fun(y,k,ps,lower_c c))::lower_defs tl
  | [] ->
    []
  | _ ->
    raise (Fail "fail at lower_defs")

let rec tv v : var =
  match v with
  | Il1.Var x ->
    x
  | _ ->
    raise (Fail "fail at translating var")
and te e : texp =
  match e with
  | Il1.Val (Il1.Var x) ->
    TVar x
  | Il1.Val (Il1.Int n) ->
    TNum n
  | Il1.Val (Il1.Halt) ->
    THalt
  | Il1.Plus(v0,v1) ->
    TPlus(tv v0, tv v1)
  | Il1.Tuple(vs) ->
    TTuple(List.map (fun v -> tv v) vs)
  | Il1.Index(n,v) ->
    TIndex(n, tv v)
  | Il1.Ifp(v0, v1, v2) ->
    TIfp(tv v0, tv v1, tv v2)
  | Il1.Val _ ->
    raise (Fail "fail at translating expression values")
and tc c : tcom =
  match c with
  | Il1.Let(x,e,c) ->
    TCLet(x, te e, tc c)
  | Il1.Call(v0,v1,v2,ps) ->
    TApp([tv v0; tv v1; tv v2]@ps)
    
let rec translate_to_IL2 defs cc : tprog = 
  match defs with
  | (x,Il1.Fun(y,k,ps,c))::tl ->
    TPLet(x, y::k::ps, tc c, translate_to_IL2 tl cc)
  | [] ->
    TCom cc
  | _ ->
    raise (Fail "fail at translation to IL2")
    
(* Implement this! *)
let translate(e: exp): tprog =
  let c = (translate1 e Il1.Halt) in
  let c' = Closure.close c in
  let (c'', defs) = hoist_c c' in
  let c''' = lower_c c'' and defs' = lower_defs defs in
  translate_to_IL2 defs' (tc c''')



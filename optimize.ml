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


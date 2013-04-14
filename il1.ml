(* A simple interpreter for the lambda calculus *)

type var = string
type v = Int of int | Var of var | Fun of var * var * c | Halt | Lam of var * c
and  e = Val of v | Plus of v * v
and  c = Let of var * e * c | Call of v * v * v | App of v * v

module VarSet = Set.Make(struct
  type t = var
  let compare = Pervasives.compare
end)
type varset = VarSet.t

(* calculate free variables of e *)
let rec fvs_c (c:c) : VarSet.t = 
  match c with 
  | Let(x,e',c') -> 
    VarSet.union (fvs_e e') (VarSet.remove x (fvs_c c'))
  | App(v1,v2)  -> 
    VarSet.union (fvs_v v1) (fvs_v v2)
  | Call(v1,v2,v3) -> 
    VarSet.union (VarSet.union (fvs_v v1) (fvs_v v2)) (fvs_v v3)
and fvs_e (e:e) : VarSet.t =
  match e with
  | Val v -> fvs_v v
  | Plus(v1,v2) -> VarSet.union (fvs_v v1) (fvs_v v2)
and fvs_v (v:v) : VarSet.t =
  match v with
  | Var x -> VarSet.singleton x
  | Lam(x,c) -> VarSet.remove x (fvs_c c)
  | Fun(x,k,c) -> VarSet.remove k (VarSet.remove x (fvs_c c))
  | _ -> VarSet.empty

(* generate a variable that is similar to x but fresh for vs *)
let rec fresh (x:var) (vs:VarSet.t) : var = 
  let rec aux (x:var) (n:int) : var = 
    let x_n = x ^ "_" ^ string_of_int n in 
    if VarSet.mem x_n vs then 
      aux x (succ n) 
    else x_n in 
  aux x 0

let rec subst_c (v:v) (x:var) (c:c) : c =
  match c with
  | Let(y,e',c') ->
    let xs = fvs_v v in
    if x = y then Let(y, subst_e v x e', c')
    else if VarSet.mem y xs then
      let y' = fresh y xs in
      let c'' = subst_c (Var y') y c' in
      Let (y', subst_e v x e', subst_c v x c'')
    else Let(y, subst_e v x e', subst_c v x c')
  | App(v1,v2) -> 
    App(subst_v v x v1, subst_v v x v2)
  | Call(v1,v2,v3) -> 
    Call(subst_v v x v1, subst_v v x v2, subst_v v x v3)
and subst_e (v:v) (x:var) (e:e) : e =
  match e with
  | Val v' -> Val(subst_v v x v')
  | Plus(v1,v2) -> Plus(subst_v v x v1, subst_v v x v2)
and subst_v (v':v) (x:var) (v:v) : v =
  match v with
  | Var y -> if x = y then v' else v
  | Halt -> Halt
  | Int n -> Int n
  | Lam(y,c) -> 
    let xs = fvs_v v' in 
    if x = y then v 
    else if VarSet.mem y xs then 
      let y' = fresh y xs in 
      let c' = subst_c (Var y') y c in 
      Lam(y',subst_c v' x c')
    else Lam(y,subst_c v' x c)
  | Fun(y,k,c) ->
    (* y \ne k ever from program generation *)
    if y = k then
      failwith "dammit"
    else
      let xs = fvs_v v' in 
      if x = y || x =y then v 
      else if VarSet.mem y xs || VarSet.mem k xs then 
        let y' = fresh y xs in 
        let c' = subst_c (Var y') y c in 
        let k' = fresh k xs in
        let c' = subst_c (Var k') k c' in
        Fun(y',k',subst_c v' x c')
      else Fun(y,k,subst_c v' x c)
    
  




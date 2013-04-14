
(* we represent variables as strings *)
type var = string

(* The source language *)
type exp =
    Var of var
  | Lambda of var * exp
  | App of exp * exp
  | Num of int
  | Plus of exp * exp
  | Let of var * exp * exp   

(* The target language: no lambdas! (prefix stands for "Target" *)
type texp =
    TVar of var
  | TNum of int
  | TPlus of var * var
  | THalt

type tcom =
    TCLet of var * texp * tcom     (* let x = e in c *)
  | TApp of var list

type tprog =
    TPLet of var * var list * tcom * tprog  (* let x = \ x1 ... xn. c in P *)
  | TCom of tcom


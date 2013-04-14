type var = string
type v = Int of int | Var of var | Fun of var * var * c | Halt | Lam of var * c
and  e = Val of v | Plus of v * v
and  c = Let of var * e * c | Call of v * v * v | App of v * v



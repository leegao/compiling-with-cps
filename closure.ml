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

(* bij: partial bijection between var and int, n the number of elements in var*)
let rec close_v (bij:var -> int) (n:int) (v:v) (p:v) : e =
  match v with
  | Int n -> Val v
  | Var x -> Index(bij x,p)
  | Halt -> Val v
  | Lam(x,c) -> 
    let p' = fresh "p'"  and y = fresh "y" and p'' = fresh "p''" in
	let xs = make_fresh "x" n in
	let c' = close_c in failwith ""
and close_c (bij:var -> int) (n:int) (c:c) (p:v) : c =
  failwith "implement me!"
and close_e (bij:var -> int) (n:int) (e:e) (p:v) : (var * e) list * e =
  failwith "implement me!"
	
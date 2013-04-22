(* evaluate target language programs. Uses a big step semantics *)

open Types

let pp = Pprint.pp

type fnclosure =
    TFnClosure of var * (var list) * tcom * (fnclosure list)

type tval = 
    TVFn of var list * tcom * (fnclosure list)
  | TVTup of tval list
  | TVNum of int
  | TVHalt


let rec ppTV tv = 
  match tv with
    TVFn(formals, body, fncontextlex) -> 
      let rec ppvarlist = function
        [] -> ()
        | a::b::t -> (pp a; pp ", "; ppvarlist (b::t))
        | b::[] -> (pp b)
      in
      (pp "function( "; ppvarlist formals; pp ")"; Pprint.ppTCom body)
    | TVTup(vs) -> (pp"("; 
		  let rec pptupl = function
		      [] -> ()
		    |	a::b::t -> (ppTV a; pp ", "; pptupl (b::t))
		    |	b::[] -> (ppTV b)
		  in
		  pptupl vs;
		  pp ")")
    | TVNum(i) -> print_int i
    | TVHalt -> pp "halt"

exception EvalError of string
exception EvalHalt of tval


let rec evalVar fncontext context x = 
  (* look for x in context, and then in fncontext *)
  match context with
    (y,e)::l -> if x=y then e else evalVar fncontext l x
  | [] -> 
      match fncontext with 
	TFnClosure(y, args, b, c)::l -> if x=y then TVFn(args,b,c) else evalVar l [] x
      |	[] -> raise (EvalError("Variable " ^ x ^ " not bound"))
	

let evalExp fncontext context exp = 
  match exp with
    TVar(x) -> evalVar fncontext context x
  | TTuple(xs) -> TVTup(List.map (evalVar fncontext context) xs)
  | TNum(i) -> TVNum(i)
  | THalt -> TVHalt
  | TIndex(i, x) -> 
      let v = evalVar fncontext context x in
      (match v with
	TVTup(xs) -> 
	  (* return the evalutation of vth element of cs, first index is 1 *)
	  List.nth xs (i-1)
      | _ ->  raise (EvalError("Index of non-tuple")))
  | TPlus(x,y) ->
      let v1 = evalVar fncontext context x in
      let v2 = evalVar fncontext context y in
      (match (v1, v2) with 
	TVNum(i), TVNum(j) -> TVNum(i + j)
      | _ ->  
      raise (EvalError("Adding non-numbers")))
  | TIfp(x, y, z) ->
      let v = evalVar fncontext context x in
      (match v with 
	TVNum(i) -> evalVar fncontext context (if i > 0 then y else z)
      | _ ->  raise (EvalError("ifp test on a non-number")))

let rec evalCom fncontext (context:(var * tval) list) com =
  let rec buildContext formals args =
    match formals,args with
      [],[] -> []
    | x::formals',e::args'->
	    let v = evalVar fncontext context e in
	    (x,v)::(buildContext formals' args')
    | _ -> 
      raise (EvalError("Incorrect number of args for fn"))
  in
  match com with
    TCLet(x, e, com') -> 
      let v = evalExp fncontext context e in
      evalCom fncontext ((x,v)::context) com'
  | TApp(f :: args) -> 
      let fn = evalVar fncontext context f in
      pp f;
      pp ":\n";
      ppTV fn;
      pp "\n\n\n\n\n";
      (match fn with 
      | TVFn(formals, body, fncontextlex) -> 
        let newcontext:(var * tval)list = buildContext formals args in
        evalCom fncontextlex newcontext body
          | TVHalt -> 
        raise (EvalHalt(evalVar fncontext context (List.nth args 0)))
          | _ -> raise (EvalError("Application to non function")))
      | TApp([]) -> raise (EvalError("Empty app"))
	
	    
let eval p = 
  (* build up the function context *)
  let rec eval' fncontext p =
    match p with
      TPLet (x, args, body, p') -> 
	    eval' (TFnClosure(x, args, body, fncontext)::fncontext) p'
    | TCom (com) -> evalCom fncontext [] com
  in
  try 
    eval' [] p
  with
    EvalHalt(v) ->  v
    

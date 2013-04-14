(* pretty printing code *)

open Types
open Format
  
  
(* Precedence for src expressions *)
let src_precedence e =
   match e with
   Var _ -> 5
   | Num _ -> 5
   | Plus(_,_) -> 4
   | App(_,_) -> 2
   | Let(_,_,_) -> 2
   | Lambda(_,_) -> 1


let pp = print_string

let pparen newPrec oldPrec c = if (newPrec >= oldPrec) then () else pp c 

let rec ppSrcExp prec e = 
  let newPrec = src_precedence e in
  match e with
    Var v -> pp  v
  | Num i -> print_int  i
  | Lambda(v, e) -> 
      (open_box 2;
       pparen newPrec prec "(";
       pp "^";
       pp v;
       pp ".";
       print_break  1 2;
       ppSrcExp newPrec e;
       pparen newPrec prec ")";
       close_box() 
      )
  | App (e0,e1) -> 
      (open_box 0;
       pparen newPrec prec "(";
       ppSrcExp newPrec e0;
       print_break 1 0;
       ppSrcExp (newPrec+1) e1;
       pparen newPrec prec ")";
       close_box() )
  | Let (x,e0,e1) -> 
      (open_box 0;
       pparen newPrec prec "(";
       pp "let ";
       pp x;
       pp "=";
       ppSrcExp newPrec e0;
       print_break 1 0;
       pp "in";
       print_break 1 0;
       ppSrcExp newPrec e1;
       pparen newPrec prec ")";
       close_box() )
  | Plus (e0,e1) -> 
      (open_box 0;
       pparen newPrec prec "(";
       ppSrcExp newPrec e0;
       print_break 1 0;
       pp "+";
       print_break 1 0;
       ppSrcExp newPrec e1;
       pparen newPrec prec ")";
       close_box() )
  


(* Precedence for trg expressions *)
let rec ppTExp e = 
  match e with
    TVar v -> pp  v 
  | TNum i -> print_int  i
  | THalt -> pp "halt"
  | TPlus (x0,x1) -> 
      (open_box 0;
       pp x0;
       print_break 1 0;
       pp "+";
       print_break 1 0;
       pp x1;
       close_box() )

let rec ppTCom e = 
  match e with
    TApp (es) -> 
      let rec ppAppList = function
	  [] -> ()
	  | x::[] -> pp x
	  | x::l -> (pp x;  print_break 1 0; ppAppList l) in
      (open_box 0;
       ppAppList es;
       close_box() )
  | TCLet (x,e,e') -> 
      (open_box 0;
       pp "let ";
       pp x;
       pp "=";
       ppTExp e;
       print_break 1 0;
       pp "in";
       close_box();
       force_newline(); 
       ppTCom e')

let rec ppTProg p = 
  match p with
    TCom (c) ->
      (open_box 0;
       ppTCom c;
       close_box() )
  | TPLet (x,args,c,p') ->
      let rec ppArgList = function
	  [] -> ()
	  | x::[] -> pp x
	  | x::l -> (pp x; pp ",";  print_break 1 0; ppArgList l)
      in
      (open_box 0;
       pp "let ";
       pp x;
       pp " =";
       print_break 1 3;
       pp "^";
       ppArgList args;
       pp ".";
       print_break 1 0;
       ppTCom c;
       print_break 1 0;
       pp "in";
       close_box();
       force_newline(); 
       ppTProg p' )
    

let ppS e = (ppSrcExp 0 e; pp "\n"; print_flush())
let ppTP e = (ppTProg e; pp "\n"; print_flush())


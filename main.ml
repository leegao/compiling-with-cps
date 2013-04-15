open Types
open Pprint
open Format
open Eval

(* Use to parse a file in the source language *)
let load_src filename =
  let h = open_in filename in
  let lexbuf = Lexing.from_channel h in
  SrcParser.parse SrcLexer.lex lexbuf


(* Use to just print a source program *)
let print_src filename =
  let e = load_src filename in
  ppS e

(* Use to translate a program from the source language to the target language *)
let translate_src filename =
  let e = load_src filename in
  let t = Cps.translate e in
  (ppTP t)

let rec ppTV tv = 
  match tv with
    TVFn(formals, body, fncontextlex) -> 
      let rec ppvarlist = function
	  [] -> ()
	| a::b::t -> (pp a; pp ", "; ppvarlist (b::t))
	| b::[] -> (pp b)
      in
      (pp "function( "; ppvarlist formals; pp ")"; ppTCom body)
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

(* Use to translate and execute program from the source language *)
let exec_src filename =
  let e = load_src filename in
  let t = Cps.translate e in
  let v = Eval.eval t in
  (ppTV v; pp "\n")

let main () =
    let fn = ref translate_src in    
    let set_parse () = (fn := print_src) in
    let set_exec () = (fn := exec_src) in
    let run s = (!fn) s in
    Arg.parse [("-parse", Arg.Unit set_parse, "only parse the given source file");
               ("-exec", Arg.Unit set_exec, "translate and execute the given source file")] 
      run 
      "usage: cps [-parse] [-exec] <file.lam>"

let _ = main()


{
open SrcParser
let lineno = ref 1
}

let alpha = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let ws = [' ' '\t']
let newline = ('\r'| '\n'| "\r\n")

rule lex =
  parse
        '/''/'[^ '\n' '\r']*newline { lineno := !lineno + 1; lex lexbuf }
      | newline     { lineno := !lineno + 1; lex lexbuf }
      | ws+        { lex lexbuf }
      | "+"        { PLUS }
      | "("        { LPAREN }
      | ")"        { RPAREN }
      | "fun"        { LAM }
      | "->"        { DOT }
      | "let"      { LET }
      | "="        { EQUALS }
      | "in"       { IN }
      | alpha+     { VAR(Lexing.lexeme lexbuf) }
      | '-'?digit+ { INT(int_of_string(Lexing.lexeme lexbuf)) }
      | eof        { EOF }
      |	_          {raise (Failure ("Invalid character found during lexing:"^(Lexing.lexeme lexbuf)))}

{
}









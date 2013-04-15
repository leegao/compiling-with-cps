type token =
  | INT of (int)
  | VAR of (string)
  | PLUS
  | POUND
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | LAM
  | DOT
  | LET
  | EQUALS
  | IN
  | IFP
  | THEN
  | ELSE
  | CWCC
  | EOF

val parse :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Types.exp

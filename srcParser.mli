type token =
  | INT of (int)
  | VAR of (string)
  | PLUS
  | LPAREN
  | RPAREN
  | LAM
  | DOT
  | LET
  | EQUALS
  | IN
  | EOF

val parse :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Types.exp

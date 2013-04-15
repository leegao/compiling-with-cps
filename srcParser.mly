%{
open Types
%}

%token <int> INT
%token <string> VAR
%token PLUS 
%token POUND
%token COMMA
%token LPAREN RPAREN
%token LBRACK RBRACK
%token LAM DOT
%token LET EQUALS IN
%token IFP THEN ELSE
%token CWCC
%token EOF

%nonassoc LPAREN RPAREN
%nonassoc LBRACK RBRACK
%nonassoc PRECLAM
%nonassoc PRECLET
%nonassoc PRECAPP
%nonassoc PRECIFP
%left PLUS
%nonassoc INT VAR

%type <Types.exp> parse
%type <Types.exp> expr

%start parse

%%

parse: expr EOF           { $1 }

expr : INT                                           { Num $1 }
     | VAR                                           { Var $1 }
     | expr PLUS expr                                { Plus($1, $3) }
     | IFP expr THEN expr ELSE expr   %prec PRECIFP  { Ifp ($2, $4, $6) }
     | LET VAR EQUALS expr IN expr    %prec PRECLET  { Let ($2, $4, $6)  }
     | LAM VAR DOT expr               %prec PRECLAM  { Lambda ($2, $4) }
     | LPAREN expr expr RPAREN        %prec PRECAPP  { App ($2, $3) }
     | LBRACK expr_list RBRACK                       { Tuple ($2) }
     | POUND INT  expr                               { Index ($2, $3) }
     | LPAREN expr RPAREN                            { $2 }
     | CWCC expr                                     { Cwcc ($2) }
     ;

expr_list : 
       expr                                          {[$1]}
     | expr_list COMMA expr                          {List.rev ($3::(List.rev $1)) }
     ;

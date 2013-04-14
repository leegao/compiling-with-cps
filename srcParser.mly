%{
open Types
%}

%token <int> INT
%token <string> VAR
%token PLUS 
%token LPAREN RPAREN
%token LAM DOT
%token LET EQUALS IN
%token EOF

%nonassoc LPAREN RPAREN
%nonassoc PRECLAM
%nonassoc PRECLET
%nonassoc PRECAPP
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
     | LET VAR EQUALS expr IN expr    %prec PRECLET  { Let ($2, $4, $6)  }
     | LAM VAR DOT expr               %prec PRECLAM  { Lambda ($2, $4) }
     | LPAREN expr expr RPAREN        %prec PRECAPP  { App ($2, $3) }
     | LPAREN expr RPAREN                            { $2 }
     ;

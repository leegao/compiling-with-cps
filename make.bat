set top=""
set ocamlc=%top%ocamlc
set ocamllex=%top%ocamllex
set ocamlyacc=%top%ocamlyacc
set includes=-I %top%
set ocamlflags=-g

%ocamlc% %ocamlflags% -c types.mli
%ocamlc% %ocamlflags% -c il1.mli
%ocamlc% %ocamlflags% -c pprint.ml
%ocamlyacc% srcParser.mly
%ocamlc% %ocamlflags% -c srcParser.mli
%ocamlc% %ocamlflags% -c srcParser.ml
%ocamllex% srcLexer.mll
%ocamlc% %ocamlflags% -c srcLexer.ml

%ocamlc% %ocamlflags% -c cps.mli
%ocamlc% %ocamlflags% -c cps.ml
%ocamlc% %ocamlflags% -c eval.ml
%ocamlc% %ocamlflags% -c main.ml

%ocamlc% -o cps.exe %ocamlflags% pprint.cmo srcParser.cmo srcLexer.cmo cps.cmo eval.cmo main.cmo

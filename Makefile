OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc

OCAMLFLAGS = -g
OCAMLOPTFLAGS = 
INCLUDE = -I .
PROG = cps
DEPOBJS =  types.cmi pprint.cmo srcParser.cmi srcParser.cmo srcLexer.cmo cps.cmi cps.cmo eval.cmo main.cmo
OBJS =  pprint.cmo srcParser.cmo srcLexer.cmo cps.cmo eval.cmo main.cmo
GEN = srcParser.ml srcParser.mli srcLexer.ml srcParser.output

$(PROG): $(DEPOBJS)
	$(OCAMLC) -o $(PROG) $(OCAMLFLAGS) $(OBJS)

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.mll.ml: 
	$(OCAMLLEX) $<

.mly.mli: 
	$(OCAMLYACC) $<

.mly.ml: 
	$(OCAMLYACC) $<

clean:
	-rm -f $(PROG) *.cm[iox] $(GEN)


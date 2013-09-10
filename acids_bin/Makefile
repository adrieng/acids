.PHONY: all

OCR=$(shell which ocamlrun)

all:
	@which ocamlrun>/dev/null \
	|| (echo You need the OCaml runtime to run Acid Synchrone; exit 1)
	sed -i -e 's:^.*ocamlrun:#!$(OCR):' asc.byte solve.byte
	ocamlrun asc.byte -nopervasives pervasives.as
	@which glpsol>/dev/null \
	|| (echo You need GLPK to run Acid Synchrone; exit 1)

# From Acid Synchrone, (c) Adrien Guatto 2013

UNAME := $(shell uname)

NCPU := 1

ifeq ($(UNAME), Linux)
  NCPU := $(shell grep -c processor /proc/cpuinfo)
endif
ifeq ($(UNAME), Darwin)
  NCPU := $(shell sysctl -n hw.ncpu)
endif
ifeq ($(UNAME), FreeBSD)
  NCPU := $(shell sysctl -n hw.ncpu)
endif

OCAMLBUILDOPTS=-j $(NCPU) -use-menhir -use-ocamlfind -classic-display \
	-I common -I compiler/global -I compiler/frontend -I compiler/backend

TARGETS= \
	 compiler/asc.byte

.PHONY: clean all toprun test unit_test doc
.SUFFIX:

all: $(TARGETS)
	ocamlbuild $(OCAMLBUILDOPTS) $(TARGETS)

# doc:
# 	$(MAKE) -C doc

%.conflicts: %.mly
	ocamlbuild $(OCAMLBUILDOPTS) $@

clean:
	ocamlbuild -clean

# test:	all
# 	$(MAKE) -C tests

%.byte:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.native:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.cma:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.cmxa:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.inferred.mli:
	ocamlbuild ${OCAMLBUILDOPTS} $@

.FORCE:
asc.native asc.byte: .FORCE

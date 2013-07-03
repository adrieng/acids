# From Acid Synchrone, (c) Adrien Guatto 2013
PREF=byte

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

OCAMLBUILDOPTS=-j $(NCPU) -use-menhir -use-ocamlfind -classic-display

COMPILER=compiler/asc.$(PREF)
SOLVER=quicksolve/solve.$(PREF)

TARGETS=$(SOLVER) $(COMPILER)

.PHONY: clean all toprun test unit_test doc
.SUFFIX:

all: $(TARGETS)

$(COMPILER): OCAMLBUILDOPTS += -I compiler/global \
                               -I compiler/frontend \
                               -I compiler/backend

$(SOLVER): OCAMLBUILDOPTS += -I resolution

%.conflicts: %.mly
	ocamlbuild $(OCAMLBUILDOPTS) $@

clean:
	ocamlbuild -clean

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

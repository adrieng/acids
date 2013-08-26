# From Acid Synchrone, (c) Adrien Guatto 2013
PREF=native

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

.PHONY: clean all toprun test unit_test doc lib
.SUFFIX:

all: $(TARGETS) lib

$(COMPILER): OCAMLBUILDOPTS += -I compiler/global \
                               -I compiler/frontend \
                               -I compiler/frontend/asts \
                               -I compiler/frontend/parsing \
                               -I compiler/frontend/misc_passes \
                               -I compiler/frontend/typing \
                               -I compiler/frontend/lowering \
                               -I compiler/frontend/utils \
                               -I compiler/middleend \
                               -I compiler/middleend/asts \
                               -I compiler/middleend/utils \
                               -I compiler/backend

$(SOLVER): OCAMLBUILDOPTS += -I resolution

%.conflicts: %.mly
	ocamlbuild $(OCAMLBUILDOPTS) $@

clean:
	ocamlbuild -clean
	rm -f $(wildcard lib/*.aso)
	rm -f $(wildcard examples/*.aso)
	make -C tests clean

realclean: clean
	rm -f $(TARGETS)
	make -C tests realclean

%.byte: .FORCE
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.native: .FORCE
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.cma:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.cmxa:
	ocamlbuild ${OCAMLBUILDOPTS} $@

%.inferred.mli:
	ocamlbuild ${OCAMLBUILDOPTS} $@

lib: $(COMPILER)
	./asc -nopervasives lib/pervasives.as

.FORCE:

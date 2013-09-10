# Acid Synchrone, (c) Adrien Guatto 2013
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

RELEASE_DIR=acids_bin

.PHONY: clean clean_release all toprun test unit_test doc lib release
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
                               -I compiler/middleend/transformations \
                               -I compiler/backend

$(SOLVER): OCAMLBUILDOPTS += -I mllp -I resolution

%.conflicts: %.mly
	ocamlbuild $(OCAMLBUILDOPTS) $@

clean_release:
	rm -f $(RELEASE_DIR)/*.{byte,native,as,asi}
	rm -rf $(RELEASE_DIR)/examples

clean: clean_release
	ocamlbuild -clean
	rm -f $(wildcard lib/*.aso)
	rm -f $(wildcard examples/*.aso)
	rm -f $(wildcard acids-*.tar.bz2)
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

release: clean_release
	make PREF=byte all
	cp asc.byte solve.byte lib/*.as $(RELEASE_DIR)/
	mkdir $(RELEASE_DIR)/examples
	cp examples/*.as $(RELEASE_DIR)/examples
	tar cjf acids-`git rev-parse HEAD`.tar.bz2 $(RELEASE_DIR)/
	scp acids-`git rev-parse HEAD`.tar.bz2 ludics:public_html

.FORCE:

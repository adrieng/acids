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

RELEASE_DIR=acids_release

.PHONY: clean clean_release all toprun test unit_test doc lib release
.SUFFIX:

all: $(TARGETS) lib

doc:
	$(MAKE) -C doc

# In theory, the following options should only be passed to ocamlbuild
# when building asc. In practice, giving different options when building
# solve and asc causes systematic full rebuilds. To avoid this, I currently
# add these directories to all commands (which is very unsatisfying).
OCAMLBUILDOPTS += -I compiler/global \
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
                  -I compiler/backend \
                  -I compiler/backend/asts \
                  -I compiler/backend/utils \
                  -I compiler/backend/targets \
                  -I compiler/backend/transformations

%.conflicts: %.mly
	ocamlbuild $(OCAMLBUILDOPTS) $@

clean_release:
	rm -f $(RELEASE_DIR)/*.{byte,native,as,aso}
	rm -rf $(RELEASE_DIR)/{lib,examples}

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
	cp asc.byte solve.byte $(RELEASE_DIR)/
	sed -i -e 's:^.*ocamlrun:#!/usr/bin/env ocamlrun:' \
		$(RELEASE_DIR)/{asc,solve}.byte
	mkdir $(RELEASE_DIR)/lib
	cp lib/*.as $(RELEASE_DIR)/lib/
	mkdir $(RELEASE_DIR)/examples
	cp examples/*.as $(RELEASE_DIR)/examples
	tar cjf "acids-`git rev-parse HEAD`_`date +%F-%Hh%M`.tar.bz2" $(RELEASE_DIR)/
	scp "acids-`git rev-parse HEAD`_`date +%F-%Hh%M`.tar.bz2" ludics:public_html

.FORCE:

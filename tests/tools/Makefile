#***************************************************************************#
#*                                Lucy-n                                   *#
#*                                                                         *#
#*                                                                         *#
#* Authors: Louis Mandel (louis.mandel@lri.fr)                             *#
#*          Florence Plateau (florence.plateau@lri.fr)                     *#
#*                                                                         *#
#*                                                                         *#
#* Creation date: September 2011                                           *#
#*                                                                         *#
#***************************************************************************#

# $Id$

OCAMLBUILD= ocamlbuild -I lib -no-links -classic-display \
		-libs str,unix \
		-tags debug,annot

TARGET=native
ALL=split.out run_test.out asc_test.out

.PHONY: all native opt byte clean realclean
.SUFFIXES:

all: $(ALL)

native: TARGET := native
native: all
opt: native

byte: TARGET := byte
byte: all

%.out: FORCE
	$(OCAMLBUILD) $*.$(TARGET)
	cp _build/$*.$(TARGET) $*

clean:
	ocamlbuild -clean

realclean: clean
	rm -f *~ $(subst .out,,$(ALL)) *.out

FORCE:


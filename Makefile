# From Acid Synchrone, (c) Adrien Guatto 2013
BUILD=ocp-build

.PHONY: all clean distclean
.SUFFIX:

all:
	$(BUILD)

clean:
	$(BUILD) -clean
	$(MAKE) -C doc clean
	$(MAKE) -C tests clean

realclean: clean
	rm -f asc.{byte,asm} *.old
	$(MAKE) -C doc realclean
	$(MAKE) -C tests realclean

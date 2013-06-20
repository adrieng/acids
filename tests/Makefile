VERBOSE=0
EXT=.as

SPLIT=tools/split
RUN_TEST=tools/run_test
ASC_TEST=tools/asc_test

TOOLS=$(SPLIT) $(RUN_TEST) $(ASC_TEST)

SPLIT_CMD=$(SPLIT) -ext $(EXT)
RUN_TEST_CMD=$(RUN_TEST) -verbose $(VERBOSE) -ext $(EXT)

SPLIT_FILES=$(wildcard *.split)

.PHONY: all split test clean realclean regen

all: test

test: $(RUN_TEST)
	$(RUN_TEST_CMD) $(wildcard *.as)

split: $(SPLIT) $(SPLIT_FILES)
	$(SPLIT_CMD) $(SPLIT_FILES)

$(TOOLS): FORCE
	make -C tools all

clean:
	rm -f *.as *.log*
	make -C tools clean

realclean: clean
	make -C tools realclean

regen: $(ASC_TEST) split
	for i in *.as; do tools/asc_test -regen -def -opts "-ann full -nopervasives" $$i; done

FORCE:

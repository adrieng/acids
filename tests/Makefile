VERBOSE=0
EXT=.as

SPLIT=tools/split
RUN_TEST=tools/run_test

TOOLS=$(SPLIT) tools/run_test

SPLIT_CMD=$(SPLIT) -ext $(EXT)
RUN_TEST_CMD=$(RUN_TEST) -verbose $(VERBOSE) -ext $(EXT)

SPLIT_FILES=$(wildcard *.split)

.PHONY: all split test clean realclean

all: test

test:
	$(RUN_TEST_CMD) $(wildcard *.as)

split: $(SPLIT) $(SPLIT_FILES)
	$(SPLIT_CMD) $(SPLIT_FILES)

$(TOOLS):
	make -C tools

clean:
	rm -f *.as
	make -C tools clean

realclean: clean
	make -C tools realclean

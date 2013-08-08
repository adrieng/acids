VERBOSE=0
EXTS=.as

SPLIT=tools/split
RUN_TEST=tools/run_test
ASC_TEST=tools/asc_test

TOOLS=$(SPLIT) $(RUN_TEST) $(ASC_TEST)

SPLIT_CMD=$(SPLIT) $(foreach EXT,$(EXTS),-ext $(EXT))
RUN_TEST_CMD=$(RUN_TEST) -verbose $(VERBOSE) $(foreach EXT,$(EXTS),-ext $(EXT))

DIRS=\
	code \
	sys

SPLIT_FILES=$(foreach DIR,$(DIRS),$(wildcard $(DIR)/*.split))

.PHONY: all split test clean realclean regen

all: test

test: $(RUN_TEST)
	$(RUN_TEST_CMD) $(foreach DIR,$(DIRS),$(wildcard $(DIR)/*.as))

split: $(SPLIT) $(SPLIT_FILES)
	$(SPLIT_CMD) $(SPLIT_FILES)

$(TOOLS): FORCE
	make -C tools all

clean:
	rm -f $(foreach DIR,$(DIRS),$(wildcard $(DIR)/*.as) $(wildcard $(DIR)/*.log*) $(wildcard $(DIR)/*.aso))
	make -C tools clean

realclean: clean
	make -C tools realclean

regen: $(ASC_TEST) split
	for i in *.as; do tools/asc_test -regen -def -opts "-ann full -nopervasives" $$i; done

FORCE:

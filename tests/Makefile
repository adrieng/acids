TESTS=$(wildcard *.as)

.PHONY: all clean regen

all: $(TESTS)
	./run_test.pl $^

clean:
	rm -f *.{log}

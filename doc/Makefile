OUT_DIR=build

PDFLATEX=xelatex

TARGET=acids.pdf

.PHONY: all clean realclean

all: $(TARGET)

acids.pdf: $(wildcard *.tex)

%.pdf:	%.tex
	[ -d $(OUT_DIR) ] || mkdir $(OUT_DIR)
	$(PDFLATEX) -output-dir $(OUT_DIR) $<
	$(PDFLATEX) -output-dir $(OUT_DIR) $<
	cp $(OUT_DIR)/$@ .

clean:
	rm -f $(OUT_DIR)/*
	rm -rf auto

realclean: clean
	rm $(TARGET)

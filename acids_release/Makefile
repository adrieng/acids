ASC=./asc.byte

ASCFLAGS+=

.PHONY: all

LIBS= \
			lib/pervasives.aso

all: $(LIBS)

lib/pervasives.aso: ASCFLAGS+=-nopervasives

%.aso: %.as
	$(ASC) $(ASCFLAGS) $^

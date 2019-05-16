LIBS=lib/coq-bits lib/coq-ssrlib
COQMAKEFILE=Makefile.coq
MAKE=make

.PHONY: default libs

default:
	$(MAKE) -f $(COQMAKEFILE)

libs:
	for lib in $(LIBS); do \
		$(MAKE) -C $$lib; \
	done

all: libs default

clean:
	make -f $(COQMAKEFILE) clean

distclean:
	for lib in $(LIBS); do \
		make -C $$lib clean; \
	done
	make -f $(COQMAKEFILE) clean
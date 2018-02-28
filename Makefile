COQPROJECT_EXISTS := $(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default clean

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f website/*html

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


website: Makefile.coq
	+make -f Makefile.coq html
	mv html/*html website
	rm -rf html

.PHONY: all clean website


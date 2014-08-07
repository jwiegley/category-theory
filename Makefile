#COQFLAGS = "-I $(HOME)/src/category-theory/Endo"
COQFLAGS = "-Q . Hask"

all: Makefile.coq html
	make -f Makefile.coq COQFLAGS=$(COQFLAGS)

html: Makefile.coq
	make -f Makefile.coq COQFLAGS=$(COQFLAGS) html

Makefile.coq: *.v
	coq_makefile -f _CoqProject  . *.v > Makefile.coq
	sed -i -e 's#cd "./." && .(MAKE) all#cd ./. ; echo $(MAKE) all#' Makefile.coq

clean:
	rm -f *.d *.vo *.glob Makefile.coq
	rm -fr html

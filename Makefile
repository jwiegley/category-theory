MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

#COQFLAGS = "-I $(HOME)/src/category-theory/Endo"
COQFLAGS = "-Q . Hask"

MISSING = find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v |	\
		xargs egrep -i -Hn '(admit|abort)' | \
		egrep -v 'local axiom'

all: Makefile.coq
	make -f Makefile.coq COQFLAGS=$(COQFLAGS)
	$(MISSING) > /dev/null && \
	    (echo "Work still to be done!"; $(MISSING); exit 1)

book: html Book.pdf

html: Makefile.coq
	make -f Makefile.coq COQFLAGS=$(COQFLAGS) gallinahtml

Makefile.coq: *.v
	coq_makefile -f _CoqProject  . *.v > Makefile.coq
	sed -i -e 's#cd "./." && .(MAKE) all#cd ./. ; echo $(MAKE) all#' Makefile.coq

%.v.tex: Makefile %.v %.glob
	coqdoc --interpolate --latex --utf8 --body-only --light			\
		--external https://github.com/jwiegley/category-theory Hask	\
		-s $*.v -o $*.v.tex

Book.pdf: Book.tex $(TEX) Book.bib coqdoc.sty
	perl -i -pe 's/\\~{}/∼/g;' *.v.tex
	perl -i -pe 's/\\\^{}\\coqdocvar{op}/\\textsuperscript{op}/g;' *.v.tex
	perl -i -pe 's#\\\^{}\\coqexternalref{op}{https://github.com/jwiegley/category-theory/Hask.Category}{\\coqdocdefinition{op}}#\\textsuperscript{op}#g;' *.v.tex
	perl -i -pe 's/textit/texttt/;' coqdoc.sty
	xelatex Book
	xelatex Book
	bibtex Book
	makeindex Book
	xelatex Book
	xelatex Book

clean:
	rm -f *.d *.vo *.glob Makefile.coq .*.aux
	rm -fr .coq-native
	rm -fr html
	rm -f Book.aux Book.bbl Book.blg Book.idx Book.ilg Book.ind
	rm -f Book.log Book.out Book.pdf Book.toc
	rm -f *.aux *.v.tex *.log

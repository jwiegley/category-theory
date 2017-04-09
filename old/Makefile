MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

COQFLAGS = ""

MISSING = find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v |	\
		xargs egrep -i -Hn '(admit|abort)'

all: Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	$(MISSING) || exit 0

book: Book.pdf

upload: all html book
	rsync --checksum -av --delete html/ jw2:/srv/ftp/pub/hasq/
	scp Book.pdf jw2:/srv/ftp/pub/hasq/Hasq.pdf
	ssh jw2 chown -R nginx:nginx /srv/ftp/pub/hasq
	ssh jw2 chmod -R ugo+rX /srv/ftp/pub/hasq
	ssh jw2 chcon -R -u system_u -t httpd_sys_content_t /srv/ftp/pub/hasq

html: Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS) gallinahtml

Makefile.coq: *.v
	coq_makefile -f _CoqProject > Makefile.coq
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

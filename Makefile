TIMECMD=time

all: Makefile.coq
	@for i in $$(find . -name '*.v' | sed 's/^\.\///'); do	\
	    if ! grep -q $$i _CoqProject; then			\
		echo NOT IN _CoqProject: $$i;			\
	    fi;							\
	done
	if [ "$(JOBS)" = "" ]; then					\
		make -f Makefile.coq $(CMD) TIMECMD="$(TIMECMD)";	\
	else								\
		make -f Makefile.coq $(CMD) -j$(JOBS);			\
	fi

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

install: _CoqProject Makefile.coq
	if [ "$(COQLIB)" = "" ]; then				\
		make -f Makefile.coq install;			\
	else							\
		make -f Makefile.coq COQLIB=$(COQLIB) install;	\
	fi

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	@find . \( -name '*.glob' -o				\
		   -name '.*.aux' -o				\
		   -name '*.v.d' -o				\
		   -name '*.v.tex' -o				\
		   -name '*.vio' -o				\
		   -name '*.vo' -o				\
		   -name '*.vok' -o				\
		   -name '*.vos' -o				\
		   -name '*.cma' -o				\
		   -name '*.cmi' -o				\
		   -name '*.cmo' -o				\
		   -name '*.cmx' -o				\
		   -name '*.cmxa' -o				\
		   -name '*.cmxs' -o				\
		   -name '.lia.cache' -o			\
		   -name '.lra.cache' -o			\
		   -name '.nia.cache' -o			\
		   -name '.nra.cache' -o			\
		   -name '.coq-native' -o			\
		   -name '*.hi' -o				\
		   -name '*.o' -o				\
		   -name '.*.aux' -o				\
		   -name '*.hp' -o				\
		   -name 'result' -o				\
		   -name 'dist' \) -print0 | xargs -0 rm -fr

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -fr .coqdeps.d .Makefile.d

todo:
	@find . \( \( -name coq-haskell -o -name fiat \) -prune \)   \
	  -o -name '*.v'					   | \
		xargs egrep -i -Hn '(abort|admit|undefined|jww)'   | \
		      egrep -v '(Definition undefined|DEFERRED)'   | \
		      egrep -v '(old|new|research|Pending)/'	     \
	    || echo "No pending tasks!"

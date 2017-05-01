MISSING	 =									\
	find . \( \( -name coq-haskell -o -name fiat \) -prune \)		\
	  -o -name '*.v'						|	\
		xargs egrep -i -Hn '(admit|undefined|jww)'		|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research|Pending)/'

all: Makefile.coq
	make -f Makefile.coq
	-@$(MISSING) || exit 0

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	find . \( -name '*.glob' -o				\
		  -name '*.v.d' -o				\
		  -name '*.vo' -o				\
		  -name '*.hi' -o				\
		  -name '*.o' -o				\
		  -name '.*.aux' -o				\
		  -name '*.hp' -o				\
		  -name 'result' -o				\
		  -name 'dist' \) -print0 | xargs -0 rm -fr

fullclean: clean
	rm -f Makefile.coq

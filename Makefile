MISSING	 =									\
	find . \( \( -name coq-haskell -o -name fiat \) -prune \)		\
	  -o -name '*.v'						|	\
		xargs egrep -i -Hn '(abort|admit|undefined|jww)'	|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: Makefile.coq
	make -f Makefile.coq
	-@$(MISSING) || exit 0

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux

fullclean: clean
	rm -f Makefile.coq

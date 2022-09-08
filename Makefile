MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
		  -print \)						|	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined|jww)'	|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: category-theory

category-theory: Makefile.coq $(wildcard *.v)
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

todo:
	-@$(MISSING) || exit 0

clean: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq install

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force

all: Makefile.coq
	@for i in $$(find . -name '*.v' | sed 's/^\.\///'); do	\
	    if ! grep -q $$i _CoqProject; then			\
		echo NOT IN _CoqProject: $$i;			\
	    fi;							\
	done
	@+$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

fullclean: clean
	rm -f Makefile.coq

todo:
	@find . \( \( -name coq-haskell -o -name fiat \) -prune \)   \
	  -o -name '*.v'					   | \
		xargs egrep -i -Hn '(abort|admit|undefined|jww)'   | \
		      egrep -v '(Definition undefined|DEFERRED)'   | \
		      egrep -v '(old|new|research|Pending)/'	     \
	    || echo "No pending tasks!"

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force todo

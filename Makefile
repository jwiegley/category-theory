MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
	       \) -print						|	\
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

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

PARALLEL = parallel
COQ_TOOLS = $(HOME)/src/coq-tools

minimize-requires:
	@if [ ! -f $(COQ_TOOLS)/minimize-requires.py ]; then \
	    echo "Need https://github.com/JasonGross/coq-tools"; \
	fi
	@$(PARALLEL) -j1 --progress -- \
	    $(COQ_TOOLS)/minimize-requires.py -i -R . Category {} ::: \
	    $$(find . -name '*.v')

lint: todo
	@echo "Lint checks complete."

format-check:
	@echo "Checking for trailing whitespace..."
	@if find . -name '*.v' -print0 | xargs -0 grep -n '[[:blank:]]$$' 2>/dev/null | head -20; then \
		echo "ERROR: Trailing whitespace found in .v files"; \
		exit 1; \
	fi
	@echo "Format check passed."

format:
	@echo "Fixing trailing whitespace in .v files..."
	@find . -name '*.v' -exec perl -pi -e 's/[ \t]+$$//' {} +
	@echo "Done."

admitted-count:
	@find . -name '*.v' -print0 | xargs -0 grep -ciE '(Admitted\.|[^_]admit\b|Abort\.)' 2>/dev/null \
		| awk -F: '{s+=$$2} END {print s}'

admitted-check:
	@current=$$($(MAKE) -s admitted-count); \
	baseline=$$(cat .admitted-baseline 2>/dev/null || echo 0); \
	if [ "$$current" -gt "$$baseline" ]; then \
		echo "ERROR: Admitted proof count increased ($$current > $$baseline)"; \
		echo "If intentional, update .admitted-baseline"; \
		exit 1; \
	fi
	@echo "Admitted proof count within baseline."

timing: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=1 2>&1 | tee build-timing.log
	@echo "Timing saved to build-timing.log"

timing-report: build-timing.log
	@echo "Slowest files:"
	@grep 'real:' build-timing.log 2>/dev/null | sort -t'(' -k2 -rn | head -20

build-strict: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-w +default"

check: format-check admitted-check category-theory
	@echo "All checks passed."

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force lint format-check format admitted-count admitted-check
.PHONY: timing timing-report build-strict check

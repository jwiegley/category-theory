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

lint: todo bench-config-check
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

# Guard against reintroducing the build configuration that broke the Coq
# bench in issue #158 (the dune switch from PR #156). The bench runs
# `opam install`, which builds via make/coq_makefile -- it never creates
# dune's _build/default tree -- so the load path must stay `-R . Category`,
# _CoqProject must carry no _build/-Q directives, and the opam build must
# invoke make. See https://github.com/jwiegley/category-theory/issues/158.
bench-config-check:
	@echo "Checking bench build config (issue #158)..."
	@first=$$(grep -vE '^[[:space:]]*(#|$$)' _CoqProject | grep -E '^[[:space:]]*-' | head -1); \
	if [ "$$first" != "-R . Category" ]; then \
		echo "ERROR: _CoqProject first load-path must be '-R . Category' but is '$$first'"; \
		echo "  (PR #156 set '-R _build/default Category', breaking the make/coq_makefile bench)"; \
		exit 1; \
	fi
	@if grep -n '_build' _CoqProject; then \
		echo "ERROR: _CoqProject references '_build' (dune-only path absent under make/coq_makefile)"; \
		exit 1; \
	fi
	@if grep -nE '(^|[[:space:]])-Q([[:space:]]|$$)' _CoqProject; then \
		echo "ERROR: _CoqProject has -Q directive(s) shadowing '-R . Category' (overriding-logical-loadpath)"; \
		exit 1; \
	fi
	@bi=$$(grep -E '^[[:space:]]*(build|install):' coq-category-theory.opam); \
	if printf '%s\n' "$$bi" | grep -qw 'dune'; then \
		echo "ERROR: coq-category-theory.opam build/install invokes dune; the bench requires make"; \
		printf '%s\n' "$$bi"; \
		exit 1; \
	fi; \
	if ! printf '%s\n' "$$bi" | grep -qw make; then \
		echo "ERROR: coq-category-theory.opam build/install must invoke make"; \
		printf '%s\n' "$$bi"; \
		exit 1; \
	fi
	@for f in dune dune-project; do \
		if [ -e "$$f" ]; then \
			echo "ERROR: $$f present at repo root; this repo builds with make/coq_makefile, not dune"; \
			exit 1; \
		fi; \
	done
	@echo "Bench config check passed."

# Self-test for the issue #158 guard: prove bench-config-check actually
# REJECTS each broken PR #156 facet, not merely that it accepts the current
# tree. Each scenario writes a throwaway copy of this Makefile into a temp
# dir with one facet broken and asserts the guard fails there; then it
# asserts the guard passes on the real tree. Wired into CI so the failure
# path is exercised on Linux, not only on a developer's machine.
bench-config-check-selftest:
	@echo "Self-testing bench-config-check (issue #158)..."
	@mk='$(CURDIR)/$(firstword $(MAKEFILE_LIST))'; rc=0; \
	mkgood() { \
		printf '%s\n' '-R . Category' 'Theory/Category.v' > "$$1/_CoqProject"; \
		printf '%s\n' 'build: [make "-j"]' 'install: [make "install"]' > "$$1/coq-category-theory.opam"; \
	}; \
	expect_reject() { \
		cp "$$mk" "$$1/Makefile"; \
		if $(MAKE) -C "$$1" -s bench-config-check >/dev/null 2>&1; then \
			echo "  FAIL: guard ACCEPTED a broken config ($$2)"; rc=1; \
		else \
			echo "  ok: rejected $$2"; \
		fi; \
		rm -rf "$$1"; \
	}; \
	t=$$(mktemp -d); mkgood "$$t"; printf '%s\n' '-R _build/default Category' 'Theory/Category.v' > "$$t/_CoqProject"; expect_reject "$$t" "guard 1: -R _build/default (PR #156)"; \
	t=$$(mktemp -d); mkgood "$$t"; printf '%s\n' '-R . Category' '-arg _build/default' 'Theory/Category.v' > "$$t/_CoqProject"; expect_reject "$$t" "guard 2: _build token"; \
	t=$$(mktemp -d); mkgood "$$t"; printf '%s\n' '-R . Category' '-Q Lib Category.Lib' 'Theory/Category.v' > "$$t/_CoqProject"; expect_reject "$$t" "guard 3: -Q directive"; \
	t=$$(mktemp -d); mkgood "$$t"; printf '%s\n' 'build: ["dune" "build" "-p" name "-j" jobs]' > "$$t/coq-category-theory.opam"; expect_reject "$$t" "guard 4: opam invokes dune"; \
	t=$$(mktemp -d); mkgood "$$t"; : > "$$t/dune"; expect_reject "$$t" "guard 5: stray dune file"; \
	if [ $$rc -ne 0 ]; then echo "Self-test FAILED."; exit 1; fi
	@$(MAKE) -s bench-config-check >/dev/null || { echo "  FAIL: guard rejected the current (fixed) tree"; exit 1; }
	@echo "  ok: accepted the current tree"
	@echo "Self-test passed."

timing: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=1 2>&1 | tee build-timing.log
	@echo "Timing saved to build-timing.log"

timing-report: build-timing.log
	@echo "Slowest files:"
	@grep 'real:' build-timing.log 2>/dev/null | sort -t'(' -k2 -rn | head -20

build-strict: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-w +default"

check: format-check admitted-check bench-config-check category-theory
	@echo "All checks passed."

# Print Print-Assumptions output for the library's key definitions.
# See docs/AXIOMS.md for the expected output ("Closed under the global
# context" for all except ZX-instance definitions, which list the 3
# user-supplied Phase parameters).
print-assumptions: category-theory
	@echo "============================================================"
	@echo "Print Assumptions audit"
	@echo "============================================================"
	@{ \
	  echo 'Require Import Category.Lib.'; \
	  echo 'Require Import Category.Structure.Monoidal.Hypergraph.'; \
	  echo 'Require Import Category.Structure.Monoidal.CompactClosed.'; \
	  echo 'Require Import Category.Construction.PROP.'; \
	  echo 'Require Import Category.Construction.Cospan.HypergraphInstance.'; \
	  echo 'Require Import Category.Construction.DecoratedCospan.Hypergraph.'; \
	  echo 'Require Import Category.Structure.Monoidal.Hypergraph.Spider.'; \
	  echo 'Require Import Category.Instance.ZX.'; \
	  echo 'Print Assumptions Hypergraph.'; \
	  echo 'Print Assumptions PROP.'; \
	  echo 'Print Assumptions Cospan_Hypergraph.'; \
	  echo 'Print Assumptions DecoratedCospan_Hypergraph.'; \
	  echo 'Print Assumptions spider_collapse.'; \
	  echo 'Print Assumptions spider_frobenius.'; \
	  echo 'Print Assumptions ZX_Cat.'; \
	} > /tmp/print_assumptions.v
	@coqc -R . Category /tmp/print_assumptions.v 2>&1 | grep -vE '^Warning|^\[' | grep -vE '^$$' || true
	@rm -f /tmp/print_assumptions.v /tmp/print_assumptions.vo /tmp/print_assumptions.vok /tmp/print_assumptions.vos /tmp/print_assumptions.glob

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force lint format-check format admitted-count admitted-check
.PHONY: bench-config-check bench-config-check-selftest timing timing-report build-strict check print-assumptions

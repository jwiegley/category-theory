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
	@ws=`find . -name '*.v' -print0 | xargs -0 grep -n '[[:blank:]]$$' 2>/dev/null | head -20`; \
	if [ -n "$$ws" ]; then \
		printf '%s\n' "$$ws"; \
		echo "ERROR: Trailing whitespace found in .v files"; \
		exit 1; \
	fi
	@echo "Format check passed."

format:
	@echo "Fixing trailing whitespace in .v files..."
	@find . -name '*.v' -exec perl -pi -e 's/[ \t]+$$//' {} +
	@echo "Done."

# Count only the harmless aborted-sketch markers ([admit] inside an
# [Abort.]-terminated proof, and the [Abort.]s themselves).  A live proof
# hole is caught separately and unconditionally by [admitted-check] below,
# so it is deliberately excluded from this count.
admitted-count:
	@find . -name '*.v' -print0 | xargs -0 grep -ciE '([^_]admit\b|Abort\.)' 2>/dev/null \
		| awk -F: '{s+=$$2} END {print s}'

# Two independent gates, kept apart so a safe construct is never scored the
# same as an unsafe one:
#   1. Zero tolerance for a live [Admitted.].  In Coq a real proof hole
#      always closes with [Admitted.] -- both a direct [Admitted.] and an
#      [admit]/[give_up] tactic require it; only an [Abort.]-terminated
#      proof carries an [admit] with no [Admitted.].  Failing on any
#      [Admitted.] therefore catches every hole, including an
#      [Abort.] -> [Admitted.] swap that leaves the aborted-sketch count
#      unchanged.
#   2. A budget on aborted sketches, so their number cannot quietly grow.
admitted-check:
	@holes=`find . -name '*.v' -print0 \
		| xargs -0 grep -lE '^[[:space:]]*Admitted\.' 2>/dev/null`; \
	if [ -n "$$holes" ]; then \
		echo "ERROR: live Admitted. proof hole(s) found in:"; \
		printf '%s\n' "$$holes"; \
		exit 1; \
	fi; \
	echo "No Admitted. proof holes."
	@current=$$($(MAKE) -s admitted-count); \
	baseline=$$(cat .admitted-baseline 2>/dev/null || echo 0); \
	if [ "$$current" -gt "$$baseline" ]; then \
		echo "ERROR: aborted-sketch count rose ($$current > $$baseline)"; \
		echo "These are Abort.-terminated and introduce no axiom;"; \
		echo "if the growth is intentional, update .admitted-baseline."; \
		exit 1; \
	fi; \
	echo "Aborted-sketch count within baseline ($$current <= $$baseline)."

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

check: format-check admitted-check bench-config-check category-theory print-assumptions
	@echo "All checks passed."

# Print Print-Assumptions output for the library's key definitions.
# See docs/AXIOMS.md for the expected output ("Closed under the global
# context" for all except ZX-instance definitions, which list the 3
# user-supplied Phase parameters).
print-assumptions: category-theory
	@echo "============================================================"
	@echo "Print Assumptions audit"
	@echo "============================================================"
	@d=`mktemp -d`; { \
	  echo 'Require Import Category.Lib.'; \
	  echo 'Require Import Category.Structure.Monoidal.Hypergraph.'; \
	  echo 'Require Import Category.Structure.Monoidal.CompactClosed.'; \
	  echo 'Require Import Category.Construction.PROP.'; \
	  echo 'Require Import Category.Construction.Cospan.HypergraphInstance.'; \
	  echo 'Require Import Category.Construction.DecoratedCospan.Hypergraph.'; \
	  echo 'Require Import Category.Structure.Monoidal.Hypergraph.Spider.'; \
	  echo 'Require Import Category.Instance.ZX.'; \
	  echo 'Require Import Category.Theory.Lambek.'; \
	  echo 'Require Import Category.Instance.Grp.'; \
	  echo 'Require Import Category.Functor.Product.Fixed.'; \
	  echo 'Require Import Category.Instance.Grp.Epi.'; \
	  echo 'Require Import Category.Instance.Top.'; \
	  echo 'Require Import Category.Instance.Top.Closed.'; \
	  echo 'Require Import Category.Instance.Grp.TwoFunctors.'; \
	  echo 'Require Import Category.Construction.Free.TwoFunctors.'; \
	  echo 'Require Import Category.Adjunction.GAFT.'; \
	  echo 'Require Import Category.Adjunction.Diagonal.Coproduct.'; \
	  echo 'Require Import Category.Monad.Monadicity.Beck.'; \
	  echo 'Require Import Category.Construction.Grothendieck.RoundTrip.'; \
	  echo 'Require Import Category.Structure.Monoidal.Markov.Fox.'; \
	  echo 'Require Import Category.Structure.SubobjectClassifier.'; \
	  echo 'Require Import Category.Structure.Topos.'; \
	  echo 'Require Import Category.Theory.Bicategory.Mates.'; \
	  echo 'Require Import Category.Adjunction.Conjugate.'; \
	  echo 'Require Import Category.Structure.Abelian.'; \
	  echo 'Require Import Category.Structure.Limit.Creation.'; \
	  echo 'Require Import Category.Monad.Eilenberg.Moore.Limit.'; \
	  echo 'Require Import Category.Theory.Skeleton.'; \
	  echo 'Require Import Category.Theory.Skeleton.Separation.'; \
	  echo 'Require Import Category.Instance.FinSet.Skeleton.'; \
	  echo 'Require Import Category.Instance.Proset.Skeletal.'; \
	  echo 'Require Import Category.Construction.Quotient.'; \
	  echo 'Require Import Category.Construction.Free.Quiver.Presented.'; \
	  echo 'Require Import Category.Instance.Proset.Limit.'; \
	  echo 'Require Import Category.Construction.Elements.'; \
	  echo 'Require Import Category.Instance.Pos.'; \
	  echo 'Require Import Category.Instance.Proset.Galois.'; \
	  echo 'Require Import Category.Instance.Ab.'; \
	  echo 'Require Import Category.Theory.Size.'; \
	  echo 'Require Import Category.Construction.PreorderReflection.'; \
	  echo 'Require Import Category.Theory.Diagram.'; \
	  echo 'Require Import Category.Theory.Diagram.Examples.'; \
	  echo 'Require Import Category.Instance.Sets.Powerset.'; \
	  echo 'Require Import Category.Instance.Sets.Products.'; \
	  echo 'Require Import Category.Instance.Sets.Complete.'; \
	  echo 'Require Import Category.Adjunction.GAFT.Sets.'; \
	  echo 'Require Import Category.Theory.Morphisms.'; \
	  echo 'Require Import Category.Instance.Two.'; \
	  echo 'Require Import Category.Instance.FinSet.Regular.'; \
	  echo 'Require Import Category.Instance.Sets.Split.'; \
	  echo 'Require Import Category.Instance.Sets.Regular.'; \
	  echo 'Require Import Category.Theory.Shapes.'; \
	  echo 'Require Import Category.Structure.Groupoid.'; \
	  echo 'Require Import Category.Structure.Groupoid.Connected.'; \
	  echo 'Require Import Category.Structure.Groupoid.Inversion.'; \
	  echo 'Require Import Category.Structure.Groupoid.Basepoint.'; \
	  echo 'Require Import Category.Construction.Deloop.Transform.'; \
	  echo 'Require Import Category.Theory.Concrete.'; \
	  echo 'Require Import Category.Instance.Concrete.'; \
	  echo 'Require Import Category.Construction.Free.Quiver.Concrete.'; \
	  echo 'Require Import Category.Theory.Functor.'; \
	  echo 'Require Import Category.Theory.Equivalence.'; \
	  echo 'Require Import Category.Theory.Concrete.Morphisms.'; \
	  echo 'Require Import Category.Construction.Subcategory.'; \
	  echo 'Require Import Category.Construction.Subcategory.Finite.'; \
	  echo 'Require Import Category.Instance.FinSet.Skeleton.'; \
	  echo 'Require Import Category.Structure.Cartesian.Closed.Adjunction.'; \
	  echo 'Require Import Category.Instance.Sets.Cartesian.Closed.Adjunction.'; \
	  echo 'Require Import Category.Instance.Proset.Transform.'; \
	  echo 'Require Import Category.Instance.Sets.Pointed.'; \
	  echo 'Require Import Category.Instance.Sets.Pointed.Part.'; \
	  echo 'Require Import Category.Theory.Natural.Transformation.Arrows.'; \
	  echo 'Require Import Category.Instance.FdVect.'; \
	  echo 'Require Import Category.Instance.FdVect.DoubleDual.'; \
	  echo 'Require Import Category.Instance.FdVect.NonNatural.'; \
	  echo 'Require Import Category.Instance.FdVect.Tensor.'; \
	  echo 'Require Import Category.Instance.Rng.Mod.'; \
	  echo 'Require Import Category.Instance.Rep.'; \
	  echo 'Require Import Category.Instance.Ab.ModFunctor.'; \
	  echo 'Require Import Category.Instance.Field.'; \
	  echo 'Require Import Category.Instance.Roster.'; \
	  echo 'Require Import Category.Instance.Ab.Graded.'; \
	  echo 'Require Import Category.Instance.Matr.FunExercises.'; \
	  echo 'Require Import Category.Theory.TwoCategory.'; \
	  echo 'Require Import Category.Instance.Cat.TwoCategory.'; \
	  echo 'Require Import Category.Structure.Cartesian.Closed.Natural.'; \
	  echo 'Require Import Category.Instance.FinSet.Decategorify.'; \
	  echo 'Require Import Category.Instance.Cat.Exponential.'; \
	  echo 'Require Import Category.Theory.EckmannHilton.'; \
	  echo 'Require Import Category.Functor.Hom.Induced.'; \
	  echo 'Require Import Category.Theory.Centre.'; \
	  echo 'Require Import Category.Construction.Slice.Terminal.'; \
	  echo 'Require Import Category.Construction.Comma.Special.'; \
	  echo 'Require Import Category.Construction.Comma.Diagram.'; \
	  echo 'Require Import Category.Construction.Comma.Natural.Transformation.'; \
	  echo 'Require Import Category.Construction.Comma.Functorial.'; \
	  echo 'Require Import Category.Instance.Rng.Algebras.'; \
	  echo 'Require Import Category.Theory.OGraph.'; \
	  echo 'Require Import Category.Construction.Free.Quiver.Examples.'; \
	  echo 'Require Import Category.Theory.Universal.Arrow.'; \
	  echo 'Require Import Category.Instance.Coq.Monoid.Free.'; \
	  echo 'Require Import Category.Construction.Free.Quiver.Constructions.'; \
	  echo 'Require Import Category.Construction.Free.Groupoid.'; \
	  echo 'Require Import Category.Instance.Grp.Free.'; \
	  echo 'Require Import Category.Instance.Square.'; \
	  echo 'Require Import Category.Instance.Square.Product.'; \
	  echo 'Require Import Category.Instance.Square.Rectangle.'; \
	  echo 'Require Import Category.Theory.Universal.Arrow.Dual.'; \
	  echo 'Require Import Category.Theory.Universal.Arrow.Dual.Examples.'; \
	  echo 'Require Import Category.Theory.Universal.Element.'; \
	  echo 'Require Import Category.Theory.Universal.Element.Elements.'; \
	  echo 'Require Import Category.Theory.Universal.Element.Examples.'; \
	  echo 'Require Import Category.Structure.Kernel.'; \
	  echo 'Require Import Category.Structure.Kernel.Universal.'; \
	  echo 'Require Import Category.Structure.Kernel.Universal.Examples.'; \
	  echo 'Require Import Category.Instance.Mod.'; \
	  echo 'Require Import Category.Instance.FdVect.'; \
	  echo 'Require Import Category.Instance.Mod.Free.'; \
	  echo 'Require Import Category.Instance.Vect.Free.'; \
	  echo 'Require Import Category.Instance.Mod.Tensor.'; \
	  echo 'Require Import Category.Instance.Vect.Tensor.'; \
	  echo 'Require Import Category.Instance.Field.'; \
	  echo 'Require Import Category.Instance.Rng.Frac.'; \
	  echo 'Require Import Category.Instance.Field.Frac.'; \
	  echo 'Require Import Category.Instance.Rng.Polynomial.'; \
	  echo 'Require Import Category.Instance.Rng.Pointed.'; \
	  echo 'Require Import Category.Instance.Mod.Representable.'; \
	  echo 'Print Assumptions Hypergraph.'; \
	  echo 'Print Assumptions PROP.'; \
	  echo 'Print Assumptions Cospan_Hypergraph.'; \
	  echo 'Print Assumptions DecoratedCospan_Hypergraph.'; \
	  echo 'Print Assumptions spider_collapse.'; \
	  echo 'Print Assumptions spider_frobenius.'; \
	  echo 'Print Assumptions ZX_Cat.'; \
	  echo 'Print Assumptions Hypergraph_CompactClosed.'; \
	  echo 'Print Assumptions lambek.'; \
	  echo 'Print Assumptions Grp.'; \
	  echo 'Print Assumptions Grp_Forget.'; \
	  echo 'Print Assumptions Grp_Zero.'; \
	  echo 'Print Assumptions fixed_product_functor.'; \
	  echo 'Print Assumptions fixed_product_transform.'; \
	  echo 'Print Assumptions fixed_product_transform_faithful.'; \
	  echo 'Print Assumptions alt_transform.'; \
	  echo 'Print Assumptions alt_is_inj_left.'; \
	  echo 'Print Assumptions Grp_fixed_product.'; \
	  echo 'Print Assumptions Grp_fixed_product_transform.'; \
	  echo 'Print Assumptions Grp_fixed_product_transform_not_id.'; \
	  echo 'Print Assumptions Grp_Z2_zero_not_iso.'; \
	  echo 'Print Assumptions grp_not_epic_of_witness.'; \
	  echo 'Print Assumptions grp_epic_image_dense.'; \
	  echo 'Print Assumptions grp_surjective_is_epic.'; \
	  echo 'Print Assumptions grp_epic_iff_surjective.'; \
	  echo 'Print Assumptions stability_is_the_conclusion.'; \
	  echo 'Print Assumptions weaker_is_the_conclusion.'; \
	  echo 'Print Assumptions transposition_decides_image.'; \
	  echo 'Print Assumptions grp_two_incl_not_epic.'; \
	  echo 'Print Assumptions grp_two_incl_monic.'; \
	  echo 'Print Assumptions grp_two_incl_image_acts_trivially.'; \
	  echo 'Print Assumptions grp_two_sym3_image_acts_nontrivially.'; \
	  echo 'Print Assumptions grp_two_sym3_not_epic.'; \
	  echo 'Print Assumptions grp_two_epic_monic_incomparable.'; \
	  echo 'Print Assumptions Top.'; \
	  echo 'Print Assumptions top_epic_iff.'; \
	  echo 'Print Assumptions complement_natural.'; \
	  echo 'Print Assumptions S3_two_functors_distinct.'; \
	  echo 'Print Assumptions S3_two_functors_weakly_equal.'; \
	  echo 'Print Assumptions Grp_op_twist_is_Id.'; \
	  echo 'Print Assumptions free_two_functors_distinct.'; \
	  echo 'Print Assumptions GAFT.'; \
	  echo 'Print Assumptions beck_monadicity.'; \
	  echo 'Print Assumptions monadic_creates.'; \
	  echo 'Print Assumptions RoundTrip_Equivalence.'; \
	  echo 'Print Assumptions markov_all_deterministic_iff_cartesian.'; \
	  echo 'Print Assumptions classifier_classifies.'; \
	  echo 'Print Assumptions relations_iso.'; \
	  echo 'Print Assumptions mate_iso.'; \
	  echo 'Print Assumptions Conjugate.'; \
	  echo 'Print Assumptions conjugate_characterizations.'; \
	  echo 'Print Assumptions conjugate_bijection.'; \
	  echo 'Print Assumptions image_mediator_epic.'; \
	  echo 'Print Assumptions CreatesLimit.'; \
	  echo 'Print Assumptions creation_preserves_limit.'; \
	  echo 'Print Assumptions creates_limits_Complete.'; \
	  echo 'Print Assumptions em_forget_CreatesAllLimits.'; \
	  echo 'Print Assumptions EM_Complete.'; \
	  echo 'Print Assumptions skeleton_inclusion_is_equivalence.'; \
	  echo 'Print Assumptions skeletons_are_isomorphic.'; \
	  echo 'Print Assumptions skeletons_isomorphic_iff_equivalent.'; \
	  echo 'Print Assumptions skeletal_equivalence_is_isomorphism.'; \
	  echo 'Print Assumptions skeleton0_skeletal_forces_UIP.'; \
	  echo 'Print Assumptions skeletality_is_not_equivalence_invariant.'; \
	  echo 'Print Assumptions FinSet_Skeletal.'; \
	  echo 'Print Assumptions Proset_Skeletal_iff_Antisymmetric.'; \
	  echo 'Print Assumptions CongClosure_Congruence.'; \
	  echo 'Print Assumptions cc_least.'; \
	  echo 'Print Assumptions cc_kernel.'; \
	  echo 'Print Assumptions presented_universal.'; \
	  echo 'Print Assumptions ord3_relation_holds.'; \
	  echo 'Print Assumptions QuotientCongLift.'; \
	  echo 'Print Assumptions free_square_diagonals_distinct.'; \
	  echo 'Print Assumptions presented_no_eqns_separates.'; \
	  echo 'Print Assumptions proset_limit_iff_glb.'; \
	  echo 'Print Assumptions proset_colimit_iff_lub.'; \
	  echo 'Print Assumptions proset_Complete_iff_all_meets.'; \
	  echo 'Print Assumptions proset_Cocomplete_iff_all_joins.'; \
	  echo 'Print Assumptions Nat_no_Terminal.'; \
	  echo 'Print Assumptions Elements.'; \
	  echo 'Print Assumptions Elements_proj.'; \
	  echo 'Print Assumptions Elements_Comma.'; \
	  echo 'Print Assumptions Diagonal_Coproduct_Adjunction.'; \
	  echo 'Print Assumptions coproduct_unit_is_unit.'; \
	  echo 'Print Assumptions coproduct_counit_is_counit.'; \
	  echo 'Print Assumptions coproduct_unit_components.'; \
	  echo 'Print Assumptions sets_coproduct_diagonal.'; \
	  echo 'Print Assumptions Pos.'; \
	  echo 'Print Assumptions Pos_Forget.'; \
	  echo 'Print Assumptions MonotoneAsFunctor.'; \
	  echo 'Print Assumptions GaloisAdjunction.'; \
	  echo 'Print Assumptions GaloisOfAdjunction.'; \
	  echo 'Print Assumptions galois_round_trip.'; \
	  echo 'Print Assumptions thin_side_condition.'; \
	  echo 'Print Assumptions Ab.'; \
	  echo 'Print Assumptions Ab_Zero.'; \
	  echo 'Print Assumptions ab_monic_iff_injective.'; \
	  echo 'Print Assumptions ab_epic_iff_surjective.'; \
	  echo 'Print Assumptions Small.'; \
	  echo 'Print Assumptions LocallySmall.'; \
	  echo 'Print Assumptions locally_small_ambient.'; \
	  echo 'Print Assumptions One_Small.'; \
	  echo 'Print Assumptions ArrowQuiverOfCat.'; \
	  echo 'Print Assumptions PreorderReflect.'; \
	  echo 'Print Assumptions preorder_reflect_thin.'; \
	  echo 'Print Assumptions Reflect.'; \
	  echo 'Print Assumptions commutative_shape_factors.'; \
	  echo 'Print Assumptions factors_commutative_shape.'; \
	  echo "Print Assumptions factors_commutative_shape'."; \
	  echo 'Print Assumptions commutative_factors.'; \
	  echo 'Print Assumptions loop_commutative_iff.'; \
	  echo 'Print Assumptions commutes_iff_factors.'; \
	  echo 'Print Assumptions shape_factor_functor.'; \
	  echo 'Print Assumptions ThinLift.'; \
	  echo 'Print Assumptions ThinLift_unique.'; \
	  echo 'Print Assumptions sq_endo_paths_are_nil.'; \
	  echo 'Print Assumptions tri_endo_paths_are_nil.'; \
	  echo 'Print Assumptions Commutative.'; \
	  echo 'Print Assumptions CommutativeShape.'; \
	  echo 'Print Assumptions dpath.'; \
	  echo 'Print Assumptions commutative_iff_shape.'; \
	  echo 'Print Assumptions shape_iff_commutative.'; \
	  echo 'Print Assumptions functor_of_diagram_of_functor.'; \
	  echo 'Print Assumptions diagram_of_functor_of_diagram.'; \
	  echo 'Print Assumptions faithful_reflects_commutative.'; \
	  echo 'Print Assumptions faithful_reflects_commutative_shape.'; \
	  echo 'Print Assumptions functor_preserves_commutative.'; \
	  echo 'Print Assumptions square_commutative_iff.'; \
	  echo 'Print Assumptions triangle_commutative_iff.'; \
	  echo 'Print Assumptions naturality_square_commutative_iff.'; \
	  echo 'Print Assumptions commutative_dterm.'; \
	  echo 'Print Assumptions coq_square_commutative.'; \
	  echo 'Print Assumptions coq_square_not_commutative.'; \
	  echo 'Print Assumptions Powerset.'; \
	  echo 'Print Assumptions Powerset_op.'; \
	  echo 'Print Assumptions Powerset_Singleton.'; \
	  echo 'Print Assumptions Powerset_injective_reflects.'; \
	  echo 'Print Assumptions Powerset_merges_fibre.'; \
	  echo 'Print Assumptions Powerset_direct_ne_inverse.'; \
	  echo 'Print Assumptions Powerset_Prop.'; \
	  echo 'Print Assumptions Powerset_Prop_Singleton.'; \
	  echo 'Print Assumptions Powerset_Prop_Monad_statement.'; \
	  echo 'Print Assumptions Powerset_Prop_FAlg.'; \
	  echo 'Print Assumptions Powerset_Prop_singletons_distinct.'; \
	  echo 'Print Assumptions Powerset_truncate.'; \
	  echo 'Print Assumptions Sets_HasIndexedProducts.'; \
	  echo 'Print Assumptions Sets_HasIndexedCoproducts.'; \
	  echo 'Print Assumptions Sets_Complete.'; \
	  echo 'Print Assumptions Sets_exponent_IsIndexedProduct.'; \
	  echo 'Print Assumptions Sets_constant_iprod_exponent.'; \
	  echo 'Print Assumptions Sets_iprod_bool.'; \
	  echo 'Print Assumptions Sets_iprod_nat.'; \
	  echo 'Print Assumptions Sets_icoprod_bool.'; \
	  echo 'Print Assumptions Sets_icoprod_nat.'; \
	  echo 'Print Assumptions Sets_endo_iprod_ump.'; \
	  echo 'Print Assumptions GAFT_at_Sets_Id.'; \
	  echo 'Print Assumptions GAFT_at_Sets_Id_is_Id.'; \
	  echo 'Print Assumptions Sets_HasEqualizers.'; \
	  echo 'Print Assumptions split_pair_idempotent.'; \
	  echo 'Print Assumptions split_idem_Idempotent.'; \
	  echo 'Print Assumptions RegularMorphism.'; \
	  echo 'Print Assumptions regular_of_section.'; \
	  echo 'Print Assumptions regular_of_retraction.'; \
	  echo 'Print Assumptions regular_composites_idempotent.'; \
	  echo 'Print Assumptions regular_epic_retraction.'; \
	  echo 'Print Assumptions regular_monic_section.'; \
	  echo 'Print Assumptions finset_regular.'; \
	  echo 'Print Assumptions finset_regular_not_split.'; \
	  echo 'Print Assumptions finset_split_pair_nontrivial.'; \
	  echo 'Print Assumptions finset_empty_to_one_not_regular.'; \
	  echo 'Print Assumptions finset_every_epi_splits.'; \
	  echo 'Print Assumptions two_epic_not_regular.'; \
	  echo 'Print Assumptions sets_split_pair_not_iso.'; \
	  echo 'Print Assumptions sets_split_mono_not_iso.'; \
	  echo 'Print Assumptions sets_split_epi_not_iso.'; \
	  echo 'Print Assumptions sets_two_card.'; \
	  echo 'Print Assumptions sets_three_card.'; \
	  echo 'Print Assumptions sets_coarsen_regular_iff_dec.'; \
	  echo 'Print Assumptions sets_coarsen_not_regular_absurd.'; \
	  echo 'Print Assumptions blanket_regularity_entails_splitting.'; \
	  echo 'Print Assumptions blanket_splitting_entails_LEM.'; \
	  echo 'Print Assumptions blanket_regularity_entails_LEM.'; \
	  echo 'Print Assumptions Point_point_of_strict.'; \
	  echo 'Print Assumptions Walk_arrow_of_strict.'; \
	  echo 'Print Assumptions Two_Fun_Arrow.'; \
	  echo 'Print Assumptions Functor_of_Pair_of_Functor.'; \
	  echo 'Print Assumptions two_three_enumeration.'; \
	  echo 'Print Assumptions Sets_point_separates.'; \
	  echo 'Print Assumptions connected_deloop_equiv.'; \
	  echo 'Print Assumptions connected_iff_deloop_equiv.'; \
	  echo 'Print Assumptions deloop_groupoid_iff.'; \
	  echo 'Print Assumptions deloop_nat_not_groupoid.'; \
	  echo 'Print Assumptions deloop_bool_groupoid.'; \
	  echo 'Print Assumptions conjugation_iso.'; \
	  echo 'Print Assumptions core_is_groupoid.'; \
	  echo 'Print Assumptions Inversion_iso.'; \
	  echo 'Print Assumptions deloop_ff_moniso.'; \
	  echo 'Print Assumptions connected_vertex_moniso.'; \
	  echo 'Print Assumptions Bool_Wide_vertex_moniso.'; \
	  echo 'Print Assumptions transform_iff_conjugate.'; \
	  echo 'Print Assumptions transform_iff_conjugate_SWAPPED.'; \
	  echo 'Print Assumptions transform_iff_intertwines.'; \
	  echo 'Print Assumptions transform_intertwiner_iso.'; \
	  echo 'Print Assumptions transform_conjugator_iso.'; \
	  echo 'Print Assumptions transform_conjugator_hom.'; \
	  echo 'Print Assumptions Fun_IsGroupoid.'; \
	  echo 'Print Assumptions Deloop_Fun_IsGroupoid.'; \
	  echo 'Print Assumptions abelian_conjugates_agree.'; \
	  echo 'Print Assumptions S3_conjugating_transform.'; \
	  echo 'Print Assumptions S3_conjugation_needs_nonabelian.'; \
	  echo 'Print Assumptions Deloop_S3_two_objects.'; \
	  echo 'Print Assumptions Deloop_Fun_S3_not_deloop.'; \
	  echo 'Print Assumptions Concrete.'; \
	  echo 'Print Assumptions Concrete_of_Separator.'; \
	  echo 'Print Assumptions Concrete_of_WellPointed.'; \
	  echo 'Print Assumptions Sets_Concrete.'; \
	  echo 'Print Assumptions Sets_Concrete_Points.'; \
	  echo 'Print Assumptions Coq_Concrete.'; \
	  echo 'Print Assumptions CMon_Concrete.'; \
	  echo 'Print Assumptions Rel_Concrete.'; \
	  echo 'Print Assumptions Rel_hom_is_not_a_function.'; \
	  echo 'Print Assumptions Rel_subsingleton_not_Faithful.'; \
	  echo 'Print Assumptions QuiverVertices_not_Faithful.'; \
	  echo 'Print Assumptions QuiverArrows_not_Faithful.'; \
	  echo 'Print Assumptions QuiverElements_faithful_under_NodeUIP.'; \
	  echo 'Print Assumptions SetQuiver_Concrete.'; \
	  echo 'Print Assumptions Full_Compose.'; \
	  echo 'Print Assumptions Faithful_Compose.'; \
	  echo 'Print Assumptions faithful_reflects_monic.'; \
	  echo 'Print Assumptions faithful_reflects_epic.'; \
	  echo 'Print Assumptions EssentiallySurjective_Compose.'; \
	  echo 'Print Assumptions Incl_Faithful.'; \
	  echo 'Print Assumptions Full_Functor_Implies_Full_upto.'; \
	  echo 'Print Assumptions Full_Functor_Implies_Full.'; \
	  echo 'Print Assumptions concrete_injective_monic.'; \
	  echo 'Print Assumptions concrete_surjective_epic.'; \
	  echo 'Print Assumptions Coq_bool_to_nat_Monic.'; \
	  echo 'Print Assumptions Coq_pred_Epic.'; \
	  echo 'Print Assumptions Coq_bool_to_nat_Monic_reflected.'; \
	  echo 'Print Assumptions Coq_pred_Epic_reflected.'; \
	  echo 'Print Assumptions FinSets_Full_Functor.'; \
	  echo 'Print Assumptions FinSets_Faithful.'; \
	  echo 'Print Assumptions FinSets_Full_roundtrip.'; \
	  echo 'Print Assumptions FinSets_two_arrows.'; \
	  echo 'Print Assumptions FinSets_negb_Monic.'; \
	  echo 'Print Assumptions FinSet_Setf_Equivalence.'; \
	  echo 'Print Assumptions FinSet_skeletal.'; \
	  echo 'Print Assumptions setf_cardinality_iso_invariant.'; \
	  echo 'Print Assumptions Exp_Functor.'; \
	  echo 'Print Assumptions eval_natural.'; \
	  echo 'Print Assumptions Curry_Adjunction.'; \
	  echo 'Print Assumptions Curry_Representable.'; \
	  echo 'Print Assumptions Sets_prod_preserves_colimits.'; \
	  echo 'Print Assumptions proset_transform_iff.'; \
	  echo 'Print Assumptions proset_transform_unique.'; \
	  echo 'Print Assumptions proset_out_not_unique.'; \
	  echo 'Print Assumptions PointedSets.'; \
	  echo 'Print Assumptions PointedSets_Zero.'; \
	  echo 'Print Assumptions pointed_balanced.'; \
	  echo 'Print Assumptions pointed_monic_iff.'; \
	  echo 'Print Assumptions pointed_epic_iff.'; \
	  echo 'Print Assumptions pointed_part_equivalence.'; \
	  echo 'Print Assumptions Transform_to_Arrows_to_Transform.'; \
	  echo 'Print Assumptions Arrows_to_Transform_to_Arrows.'; \
	  echo 'Print Assumptions FdVect_Matr_Equivalence.'; \
	  echo 'Print Assumptions double_dual_natural.'; \
	  echo 'Print Assumptions double_dual_iso.'; \
	  echo 'Print Assumptions sigma_not_natural.'; \
	  echo 'Print Assumptions sigma_categorical_not_natural.'; \
	  echo 'Print Assumptions diag_transform_zero.'; \
	  echo 'Print Assumptions diag_transform_zero_Q.'; \
	  echo 'Print Assumptions ModTotal.'; \
	  echo 'Print Assumptions ModFibred.'; \
	  echo 'Print Assumptions ModFibredProj.'; \
	  echo 'Print Assumptions ModProj.'; \
	  echo 'Print Assumptions Restrict.'; \
	  echo 'Print Assumptions ModIndexed.'; \
	  echo 'Print Assumptions OpModIndexed.'; \
	  echo 'Print Assumptions Rep_Fun_equiv.'; \
	  echo 'Print Assumptions thin_group_functor_trivial.'; \
	  echo 'Print Assumptions sign_rep_nontrivial.'; \
	  echo 'Print Assumptions RMod_AbFun_equiv.'; \
	  echo 'Print Assumptions DeloopRing_AbEnriched.'; \
	  echo 'Print Assumptions AbFunAdd_proper.'; \
	  echo 'Print Assumptions Field.'; \
	  echo 'Print Assumptions field_hom_distinct.'; \
	  echo 'Print Assumptions field_every_monic.'; \
	  echo 'Print Assumptions Q_hom_monic.'; \
	  echo 'Print Assumptions Q_endo_id.'; \
	  echo 'Print Assumptions Mon_Sets.'; \
	  echo 'Print Assumptions Graded_Fun_equiv.'; \
	  echo 'Print Assumptions GradedAb.'; \
	  echo 'Print Assumptions GradedAb_shift.'; \
	  echo 'Print Assumptions matrix_similarity_iso.'; \
	  echo 'Print Assumptions matrix_equivalence_iso.'; \
	  echo 'Print Assumptions matrix_equivalence_iso_Fun.'; \
	  echo 'Print Assumptions equivalence_is_weaker_than_similarity.'; \
	  echo 'Print Assumptions Cat_TwoCategory.'; \
	  echo 'Print Assumptions TwoCategory_to_Strict.'; \
	  echo 'Print Assumptions twocategory_def3.'; \
	  echo 'Print Assumptions NatSq_not_a_two_category.'; \
	  echo 'Print Assumptions NatPlus_StrictBase.'; \
	  echo 'Print Assumptions exp_prod_l_natural.'; \
	  echo 'Print Assumptions exp_prod_r_natural.'; \
	  echo 'Print Assumptions prod_coprod_r_natural.'; \
	  echo 'Print Assumptions exp_coprod_natural.'; \
	  echo 'Print Assumptions Card_Groupoid.'; \
	  echo 'Print Assumptions nat_exp_coprod.'; \
	  echo 'Print Assumptions Cat_exp_prod_l_natural.'; \
	  echo 'Print Assumptions eckmann_hilton.'; \
	  echo 'Print Assumptions hom_action.'; \
	  echo 'Print Assumptions centre_monoid.'; \
	  echo 'Print Assumptions centre_commutative.'; \
	  echo 'Print Assumptions centre_commutative_EH.'; \
	  echo 'Print Assumptions centre_interchange.'; \
	  echo 'Print Assumptions centre_interchange_forces_commutative.'; \
	  echo 'Print Assumptions centre_Sets_trivial.'; \
	  echo 'Print Assumptions centre_Coq_trivial.'; \
	  echo 'Print Assumptions Slice_Terminal.'; \
	  echo 'Print Assumptions Coslice_Initial.'; \
	  echo 'Print Assumptions Comma_Discrete_Hom.'; \
	  echo 'Print Assumptions Comma_Discrete_Hom_eq.'; \
	  echo 'Print Assumptions comma_discrete_iso_forces_UIP.'; \
	  echo 'Print Assumptions Blur_no_discrete_iso.'; \
	  echo 'Print Assumptions slice_terminal_not_strict.'; \
	  echo 'Print Assumptions Comma_to_Arrow.'; \
	  echo 'Print Assumptions comma_diagram_dom.'; \
	  echo 'Print Assumptions comma_diagram_cod.'; \
	  echo 'Print Assumptions comma_diagram_ump.'; \
	  echo 'Print Assumptions comma_mediator_unique.'; \
	  echo 'Print Assumptions comma_diagram_self.'; \
	  echo 'Print Assumptions comma_diagram_self_via_ump.'; \
	  echo 'Print Assumptions Huq_roundtrip.'; \
	  echo 'Print Assumptions huq_compatible_iff.'; \
	  echo 'Print Assumptions huq_witness_separates.'; \
	  echo 'Print Assumptions Comma_Transform_witness_shift.'; \
	  echo 'Print Assumptions Comma_Functor_proj1_strict.'; \
	  echo 'Print Assumptions Comma_Functor_Comma_Transform.'; \
	  echo 'Print Assumptions Comma_map_left.'; \
	  echo 'Print Assumptions Comma_map_right.'; \
	  echo 'Print Assumptions Comma_map_exchange.'; \
	  echo 'Print Assumptions Comma_Bifunctor.'; \
	  echo 'Print Assumptions Comma_Bifunctor_Iso.'; \
	  echo 'Print Assumptions Comma_reindex.'; \
	  echo 'Print Assumptions Comma_reindex_recovers_Comma_map.'; \
	  echo 'Print Assumptions KAlg.'; \
	  echo 'Print Assumptions KAlg_Coslice_strict_iso.'; \
	  echo 'Print Assumptions KAlg_Coslice_iso.'; \
	  echo 'Print Assumptions KAlg_Comma_iso.'; \
	  echo 'Print Assumptions Int_KAlg.'; \
	  echo 'Print Assumptions Q_KAlg.'; \
	  echo 'Print Assumptions Z_KAlg.'; \
	  echo 'Print Assumptions OGrph.'; \
	  echo 'Print Assumptions OGraph_prod.'; \
	  echo 'Print Assumptions OGrph_Monoidal.'; \
	  echo 'Print Assumptions OMonoid.'; \
	  echo 'Print Assumptions MonoidOfCat.'; \
	  echo 'Print Assumptions CategoryOfOMonoid.'; \
	  echo 'Print Assumptions category_is_monoid_in_OGrph.'; \
	  echo 'Print Assumptions ocat_roundtrip_iso.'; \
	  echo 'Print Assumptions OGrph_Quiver_Faithful.'; \
	  echo 'Print Assumptions Monoid_of_MonObject.'; \
	  echo 'Print Assumptions coarse_respectfulness_entails_UIP.'; \
	  echo 'Print Assumptions graded_free_thin.'; \
	  echo 'Print Assumptions arrow_free.'; \
	  echo 'Print Assumptions ordinal_free.'; \
	  echo 'Print Assumptions ordinal_free_Cat.'; \
	  echo 'Print Assumptions chain_free.'; \
	  echo 'Print Assumptions linear_hom_iff.'; \
	  echo 'Print Assumptions Ordinal_2_strict_iso.'; \
	  echo 'Print Assumptions universal_arrow_unique.'; \
	  echo 'Print Assumptions auniversal_arrow_unique.'; \
	  echo 'Print Assumptions free_monoid_universal.'; \
	  echo 'Print Assumptions free_monoid_adjunction.'; \
	  echo 'Print Assumptions free_monoid_unique_iso.'; \
	  echo 'Print Assumptions free_monoid_counit_epic.'; \
	  echo 'Print Assumptions AMon_initial_universal_arrow.'; \
	  echo 'Print Assumptions insert_Transform.'; \
	  echo 'Print Assumptions QuiverOp.'; \
	  echo 'Print Assumptions QuiverProd.'; \
	  echo 'Print Assumptions QuiverOp_invol.'; \
	  echo 'Print Assumptions Forgetful_preserves_op.'; \
	  echo 'Print Assumptions Forgetful_preserves_prod.'; \
	  echo 'Print Assumptions Forgetful_preserves_op_fmap.'; \
	  echo 'Print Assumptions QuiverPair_Fst.'; \
	  echo 'Print Assumptions QuiverPair_unique.'; \
	  echo 'Print Assumptions FreeGroupoid.'; \
	  echo 'Print Assumptions FreeGroupoid_IsGroupoid.'; \
	  echo 'Print Assumptions FreeGroupoidUnit.'; \
	  echo 'Print Assumptions FreeGroupoidFunctor.'; \
	  echo 'Print Assumptions FreeGroupoidFunctor_unique.'; \
	  echo 'Print Assumptions free_groupoid_universal.'; \
	  echo 'Print Assumptions fg_restrict_recovers.'; \
	  echo 'Print Assumptions fg_restrict_recovers_strict.'; \
	  echo 'Print Assumptions fg_extend_restrict.'; \
	  echo 'Print Assumptions free_signed_not_groupoid.'; \
	  echo 'Print Assumptions free_signed_no_cancellation.'; \
	  echo 'Print Assumptions fg_proj_not_faithful.'; \
	  echo 'Print Assumptions loop_generator_not_identity.'; \
	  echo 'Print Assumptions FreeGrpObject.'; \
	  echo 'Print Assumptions fg_insert.'; \
	  echo 'Print Assumptions free_group_universal.'; \
	  echo 'Print Assumptions free_group_AUniversalArrow.'; \
	  echo 'Print Assumptions FreeGrp.'; \
	  echo 'Print Assumptions free_group_adjunction.'; \
	  echo 'Print Assumptions free_group_counit_evaluates.'; \
	  echo 'Print Assumptions free_group_triangle_left.'; \
	  echo 'Print Assumptions free_group_triangle_right.'; \
	  echo 'Print Assumptions free_group_fmap_generators.'; \
	  echo 'Print Assumptions free_group_two_generators_nonabelian.'; \
	  echo 'Print Assumptions free_group_two_generators_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Square.Square.'; \
	  echo 'Print Assumptions Category.Instance.Square.wsq_classify.'; \
	  echo 'Print Assumptions Category.Instance.Square.Square_Thin.'; \
	  echo 'Print Assumptions Category.Instance.Square.wsq_pairs_sound.'; \
	  echo 'Print Assumptions Category.Instance.Square.wsq_pairs_complete.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_arrow_total_9.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_identity_total_4.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_nonidentity_total_5.'; \
	  echo 'Print Assumptions Category.Instance.Square.free_square_arrow_total_10.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_quotient_merges_one.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_commutes.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_universal.'; \
	  echo 'Print Assumptions Category.Instance.Square.wsq_path_rank.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_hom_length.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_length_invariant.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_no_collapse.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_diagonal_is_two_steps.'; \
	  echo 'Print Assumptions Category.Instance.Square.square_no_diagonal_edge.'; \
	  echo 'Print Assumptions Category.Instance.Square.Product.Square_2x2_iso.'; \
	  echo 'Print Assumptions Category.Instance.Square.Product.prod22_arrow_total_9.'; \
	  echo 'Print Assumptions Category.Instance.Square.Product.square_22_counts_agree.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.paste_squares.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.rect_outer_commutes.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.rect_outer_two_ways.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.RectFunctor.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.rect_arrow_total_18.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.rect_identity_total_6.'; \
	  echo 'Print Assumptions Category.Instance.Square.Rectangle.rect_nonidentity_total_12.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.CouniversalArrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.coarrow_obj.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.coarrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.ump_couniversal_arrows.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_from_UMP.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_terminal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_of_terminal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.terminal_is_initial_op.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.cua_med.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_iso.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_unique.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.RightAdjointFunctorFromCouniversalArrows.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.AdjunctionFromCouniversalArrows.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.counit_couniversal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.ACouniversalArrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.couniversal_arrow_couniversal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.acouniversal_arrow_unique.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.ACouniversalArrow_of_CouniversalArrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.CouniversalArrow_of_ACouniversalArrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.product_CUA.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.product_terminal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.product_via_couniversal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.product_via_couniversal_is_product.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.Sets_product_CUA.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Arrow.Dual.Examples.Sets_product_via_couniversal.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.UniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElementEquiv.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement_of_UniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.UniversalElement_of_AUniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.global_element.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.global_elements_iso.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.ue_mate.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.ue_transform.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.ue_representation.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement_of_repr.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.aue_inverse.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.aue_mate_IsIso.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement_of_mate.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.ue_yoneda_obj.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.rby_agrees.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_yoneda.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_representation.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.representation_of_universal_element.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_of_representation.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.UniversalElement_of_Representable.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Representable_of_UniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.ue_med.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_iso.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_unique.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement_of_AUniversalArrow.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalArrow_of_AUniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.HomAfter.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalElement_of_hom.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.AUniversalArrow_of_hom.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.universal_element_arrow_subsumption.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.subsumption_composite.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Elements.Elements_Initial.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Elements.AUniversalElement_of_Elements_Initial.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Elements.UniversalElement_of_Elements_Initial.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Examples.nat_UniversalElement.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Examples.nat_ue_factor.'; \
	  echo 'Print Assumptions Category.Theory.Universal.Element.Examples.nat_Elements_Initial.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.ZeroMorphisms.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.ZeroMorphisms_of_ZeroObject.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.KillPresheaf.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.IsKernelOf.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_aue.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.aue_kernel.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_round_mediator.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.aue_kernel_round_mediator.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_universal_element_iso.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_UniversalElement.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_Representable.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_representation.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_iff_representable.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_universal_element.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kernel_representable.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.ForkPresheaf.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.equalizer_aue.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.aue_equalizer.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.equalizer_universal_element_iso.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.equalizer_Representable.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.kill_fork_iso.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_kernel_IsKernel.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_kernel_aue.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_kernel_Representable.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_kernel_representation.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_kernel_round.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_parity.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_parity_med.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.ab_parity_universal_element.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.Rng_no_hom_zero_to_Z.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.Rng_no_zero_morphisms.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.Rng_no_zero_object.'; \
	  echo 'Print Assumptions Category.Structure.Kernel.Universal.Examples.Rng_fork_presheaf.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.FreeModObject.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_insert.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_extend.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_extend_unique.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_universal.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_AUniversalArrow.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.FreeMod.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_adjunction.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_counit_evaluates.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_fmap_generators.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_transpose_extend.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_extend_transpose.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_naturality_in_set.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_naturality_in_module.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_triangle_left.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_triangle_right.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.fv_normal_form.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_scalars_faithful.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_basis_injective.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.free_module_two_independent.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.int_free_basis_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.int_free_two_independent.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Free.int_free_scalars_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.Vct_Forget.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.FreeVectObject.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_insert.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_universal.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_AUniversalArrow.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.FreeVect.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_adjunction.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_counit_evaluates.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_fmap_generators.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_naturality_in_set.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_naturality_in_space.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_triangle_left.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_triangle_right.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_finite_combination.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_basis_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_basis_independent.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Free.free_vect_half_not_one.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.RBilinear.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_zero_l.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_zero_r.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_neg_l.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_neg_r.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_commutator.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_commutator_annihilates.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.rbl_commutator_from_commutativity.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.TensorMod.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_gen.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_balanced.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_zero_l.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_zero_r.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_neg_l.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_neg_r.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_commutator.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_med.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_med_respects.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_hom_ext.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.Bilin.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_UniversalElement.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_factor.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_factor_commutes.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.tensor_factor_unique.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.Int_mul_bilinear.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.int_tensor_gen_nonzero.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.int_tensor_gen_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.int_tensor_unit.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Tensor.Int_tensor_iso.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.VctBilinear.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.VctBilin.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.VctTensor.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_gen.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_UniversalElement.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_factor.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_factor_commutes.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_tensor_factor_unique.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.vct_commutator_vacuous.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.Q_Vct.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.Q_mul_bilinear.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.q_tensor_gen_nonzero.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.q_tensor_half_distinct.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.q_tensor_smul_half.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.q_tensor_smul_half_moves.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.q_tensor_unit.'; \
	  echo 'Print Assumptions Category.Instance.Vect.Tensor.Q_tensor_iso.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.field_dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.IntDom_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.Field_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.StableField.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.StableField_IntDom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.StableField_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.Field_IntDom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_hom_den_nonzero.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_extend.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_extend_embed.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_embed_den.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_extend_unique.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_ump.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.DomZeroDec.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.dom_zero_dec_eq_dec.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.FracField.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.FracField_stable.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.FracStableField.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_unit.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_universal.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.ZtoF2.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.ZtoF2_not_injective.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_DomHom_Z_F2.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.IntDom_Dom_not_Full.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.IntDom_Incl_not_Full.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_field_over_Q_and_F2.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_field_maps_to_all_fields.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_universal_arrow_Z_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_auniversal_arrow_Z_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_universal_arrow_Z_Dom_stable.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.no_auniversal_arrow_Z_Dom_stable.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.Int_zero_dec.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.Frac_Z.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.ZtoQ_Dom.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_universal_over_monos_not_over_all.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_extend_Z_half.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_extend_Z_three.'; \
	  echo 'Print Assumptions Category.Instance.Field.Frac.frac_embed_Z_not_surjective.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.PTerm.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.pt_eq.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.pt_refl.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.pt_Setoid.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.pe_mul_zero_l.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.pe_const_neg.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.PolyRig.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.PolyRing.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_comm.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_const.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_x.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.peval.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.peval_comm.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.peval_respects.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_extend.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_extend_unique.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.rig_iter_central.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zring_central.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.PolyAlg.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.KAlg_Forget.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.kalg_eval.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_representation.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_representable.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_auniversal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.ZPoly.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_eval.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_hom_const.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_representation.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_representable.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_auniversal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.rng_monic_injective.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.rng_monic_iff_injective.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_hom_value_central.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_const_injective.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_const_monic.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.poly_x_not_constant.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_x_not_constant.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_x_nonzero.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Polynomial.zpoly_x_not_one.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.CRng_Forget.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.CRngPt.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.CRngPt_Forget.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.PolyCRng.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.PolyPt.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_universal.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.PolyPointed.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_adjunction.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_unit.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_transpose_is_evaluation.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_adj_transpose_evaluates.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.poly_pointed_fmap_const.'; \
	  echo 'Print Assumptions Category.Instance.Rng.Pointed.zpoly_pointed_eval.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.rmod_by_element.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.rmod_out_of_ring.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.ring_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.rmod_representation.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.rmod_representable.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.ring_auniversal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.ring_universal_arrow.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.free_one_universal_element.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.free_one_generator_iso.'; \
	  echo 'Print Assumptions Category.Instance.Mod.Representable.free_one_generator_iso_unique.'; \
	} > $$d/pa.v; \
	coqc -R . Category $$d/pa.v > $$d/pa.out 2>&1; rc=$$?; \
	grep -vE '^Warning|^\[|^$$' $$d/pa.out || true; \
	if [ $$rc -ne 0 ]; then \
	  echo "ERROR: print-assumptions failed to compile (axiom audit broken)"; \
	  rm -rf $$d; exit 1; \
	fi; \
	unexpected=`grep -E '^[A-Za-z][A-Za-z0-9_.'"'"']* :' $$d/pa.out \
	  | grep -vE '(^|\.)(Phase|phase_zero|phase_add) :' || true`; \
	rm -rf $$d; \
	if [ -n "$$unexpected" ]; then \
	  echo "ERROR: unexpected axiom dependency in an audited definition:"; \
	  printf '%s\n' "$$unexpected"; \
	  echo "(only the 3 documented ZX Phase parameters are permitted)"; \
	  exit 1; \
	fi; \
	echo "Axiom audit passed: only the documented ZX Phase parameters appear."

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force lint format-check format admitted-count admitted-check
.PHONY: bench-config-check bench-config-check-selftest timing timing-report build-strict check print-assumptions

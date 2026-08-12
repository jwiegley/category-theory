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
	  echo 'Require Import Category.Monad.Monadicity.Beck.'; \
	  echo 'Require Import Category.Construction.Grothendieck.RoundTrip.'; \
	  echo 'Require Import Category.Structure.Monoidal.Markov.Fox.'; \
	  echo 'Require Import Category.Structure.SubobjectClassifier.'; \
	  echo 'Require Import Category.Structure.Topos.'; \
	  echo 'Require Import Category.Theory.Bicategory.Mates.'; \
	  echo 'Require Import Category.Adjunction.Conjugate.'; \
	  echo 'Require Import Category.Structure.Abelian.'; \
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

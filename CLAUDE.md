# CLAUDE.md

This codebase is a comprehensive formalization of category theory in Coq/Rocq. It contains 933 proof files (the `_CoqProject` build set — 937 `.v` files exist on disk, the difference being three unbuilt probes under `doc/plan/books/probes/` plus the unregistered `Structure/Limit/Preservation/Shapes.v`; the previous figures of 563/566 were long stale, and the stated reason was incomplete as well as the numbers) with over 170,000 lines implementing core categorical concepts with zero axioms in the core theory — spanning the classical canon from categories, functors, and adjunctions through monadicity, the adjoint functor theorems, enriched and higher structures (bicategories, pseudo double categories), Lawvere theories, multicategories and operads, and elementary topos theory.

"Zero axioms in the core theory" is narrower than it sounds, and docs/AXIOMS.md is the authority for exactly how narrow. Two separate facts hold. First, the only `Axiom`/`Parameter` declarations anywhere in the library are the three `Phase` parameters of the ZX-calculus instance, all in `Instance/ZX.v`. Second, `Print Assumptions` reports "Closed under the global context" for an ENUMERATED list of headline definitions, audited by `make print-assumptions`. That second fact is *not* a claim about every definition in the library — docs/AXIOMS.md says so in terms — and no directory-wide certification of `Theory/`, `Structure/`, or `Construction/` has been run. The concrete instance layers (`Instance/`, `Theory/Coq/`) do use stdlib axioms, enumerated there. Separately, many of the advanced flagship theorems are proven *parametrically* — as axiom-free conditionals over an abstract structure — and only some are instantiated by a concrete in-tree model; docs/INHABITATION.md records which.

## Commands

### Building the Library

```bash
# Build the entire library (default: Rocq 9.1)
make

# Build for specific version (if using Nix)
nix-shell -p coqPackages_9_1.coq --run make

# Build using Nix flake (the default package is category-theory_9_1)
nix build
# ...or select a version explicitly, e.g. nix build .#category-theory_8_20

# Clean build artifacts
make clean
make fullclean  # removes Makefile.coq as well

# Install library
make install

# Check for admitted proofs or TODOs
make todo

# Guard the preamble's file counts against _CoqProject and the tree
make claude-md-counts-check

# Guard docs/INDEX.md's five section headings (an Edit has eaten one twice)
make index-check
```

### Single File Development

```bash
# Compile a single file
coqc -R . Category Theory/Category.v

# Interactive development (in coqide/vscoq)
# Ensure _CoqProject is loaded with: -R . Category
```

### Proof Development Patterns

The library uses custom tactics in `Lib/Tactics.v`:
- `cat` - standard simplification for category proofs
- `cat_simpl` - more aggressive simplification with program obligations
- `proper` - for proving morphism respectfulness
- `equivalence` - for proving equivalence relations

## Architecture

### Core Abstraction Hierarchy

The library implements category theory through **setoid-based morphisms** where morphisms form equivalence classes rather than using strict equality. This fundamental design choice cascades through the entire architecture:

```
Category (homsets are setoids with ≈ equivalence)
    ↓
Functor (preserves equivalence, not just equality)
    ↓
Natural Transformation (naturality respects ≈)
    ↓
Adjunction/Monad/Kan Extension
```

### Universe Polymorphism Strategy

The library uses three universe parameters `{o h p}` throughout:
- `o` - objects universe level
- `h` - hom-sets universe level
- `p` - proof/proposition universe level
- Constraint: `h <= p` ensures morphism proofs can reference morphisms

This allows categories of categories at any level without universe inconsistencies.

### Duality Architecture

**Key insight**: Duality is built into definitions so `C^op^op = C` by reflexivity.

This requires symmetric laws in core definitions:
- `comp_assoc` AND `comp_assoc_sym` in Category
- `naturality` AND `naturality_sym` in Natural transformations

Benefits:
- Comonads are one line: `Definition Comonad := @Monad (C^op) (M^op)`
- Dual proofs are often automatic
- No code duplication for dual concepts

### Proof Obligation Management

The library uses Coq's Program mechanism extensively:
1. Definitions use `Program Instance` to defer proof obligations
2. `Obligation Tactic := cat_simpl` automates most proofs
3. Remaining obligations proven with specific tactics
4. This separates mathematical content from proof details

### Instance Resolution Strategy

Categories are discovered through:
1. Type classes for concepts (Category, Functor, etc.)
2. `Existing Instance` for conditional instances
3. Notation-driven inference with category hints
4. Explicit category parameters when inference fails

Example: `f ∘[C] g` specifies category C when needed.

## Key Files and Concepts

The per-development index of the library's headline developments lives in
**docs/INDEX.md**: one bullet per landed development, about 250 of them,
each stating what was delivered, at what strength (`eq_refl`, `≈`, `Cat`
against `StrictCat`), what was measured and by what criterion, and what was
NOT delivered. It was this file's "Key Files and Concepts" section until
2026-09-09 and every bullet is unchanged. Any `.v` header, commit message,
plan document or issue checkbox written before that date that refers to the
CLAUDE.md Key Files index, to a bullet or figure in it ("the CLAUDE.md
bullet", what "CLAUDE.md records" or "carries"), or to a count of
occurrences in CLAUDE.md, means the entry or the count in docs/INDEX.md.

Rules of use:
- Before editing a file, grep its basename in docs/INDEX.md (some bullets
  spell paths relative to their section) and read its bullet if it has one:
  it records the strength of every claim and the traps already met (universe
  pins, `Qed`-opaque donors, notation shadowing, false-passing probes).
  About a third of the `.v` files head a bullet of their own (just over 300
  of 926 on 2026-09-09, counting distinct bold heads), so absence is not a
  signal.
- New work appends ONE bullet to docs/INDEX.md under the heading its sibling
  developments already sit under. The index's sections are thematic, not
  per-directory (`Structure/Topos.v` sits under Theory Core), and `Solver/`,
  `Tools/`, `Lib/` and `Test/` have no section there. An `Edit` that inserts
  a bullet has twice eaten the heading after it, so check BOTH
  `grep -c '^- \*\*' docs/INDEX.md` and `grep -c '^## ' docs/INDEX.md`
  before and after; `make index-check` (run by lefthook and CI) fails if the
  five headings are not all present in order. The map below changes only
  when a new directory or family of files appears.
- Every figure in a bullet is a measurement with its criterion stated
  (which files, which pattern, which command); a number that cannot be
  re-measured from the sentence does not go in. Corrections are recorded in
  place as corrections ("an earlier revision said X; measured Y"), never
  silently.

The map — where the headline developments live; the bullets carry the
detail. A directory followed by an asterisk stands for all the files under
it, and a root file followed by a parenthesised "+" glob names the file
together with its satellites. The headings below group the map by directory;
they are not the index's sections. Every file in `_CoqProject` is reachable
from an exact path or a glob below.

### Theory Core (`Theory/`, `Natural/`, `Functor/`, `Adjunction/`, `Monad/`, `Comonad/`)
- `Theory/Category.v`, `Theory/Functor.v`, `Theory/Natural/Transformation.v` (+ `Theory/Natural/Transformation/Arrows.v`), `Natural/Transformation/*` (monoidal, strong and applicative-functor transformations, the opposite of a transformation), `Theory/Isomorphism.v`, `Theory/Morphisms.v` (+ `Theory/Morphisms/*`): setoid-based categories and functors (Full/Faithful closure and reflection), natural transformations in the componentwise and arrows-only presentations, the monic/epic calculus and the discipline of deriving duals through `C^op`.
- `Theory/Shapes.v`, `Theory/Diagram.v` (+ `Theory/Diagram/Examples.v`), `Construction/PreorderReflection.v`: functors out of the walking shapes, diagrams as quiver homomorphisms with path-general commutativity, the universal thin quotient.
- `Theory/Adjunction.v` and `Adjunction/*`: hom-set and unit/counit adjunctions; conjugates, mates and adjoint squares (`Adjunction/Conjugate.v`, `Adjunction/Square.v`, `Adjunction/Map.v`, `Adjunction/Choice.v`), adjunctions with a parameter (`Adjunction/Parameter.v`), composition (`Adjunction/Compose.v`), RAPL/LAPC (`Adjunction/Continuity.v`), additivity (`Adjunction/Additive.v`), Paré's splitting criterion (`Adjunction/Pare.v`), adjoints on the right (`Adjunction/Right.v`), determination by counits (`Adjunction/Determination.v`), representability (`Adjunction/Representability.v`), fullness and faithfulness by unit and counit (`Adjunction/Fullness.v`, `Adjunction/FullFaithful.v`), left-adjoint-left-inverses (`Adjunction/LeftInverse.v`), the adjoints of the diagonal (`Adjunction/Diagonal/*`), GAFT and SAFT (`Adjunction/GAFT.v`, `Adjunction/SAFT.v`, `Adjunction/GAFT/*`), unitalization (`Adjunction/Unitalization.v`), enveloping algebras (`Adjunction/Enveloping.v`), the cokernel-pair/equalizer adjunction (`Adjunction/CokernelPair.v`).
- `Instance/Adj.v` (+ `Instance/Adj/*`), `Instance/Adjoints.v`: the category of adjunctions with conjugate pairs as arrows, its two forgetful functors, and the bicategory of categories, adjunctions and conjugate pairs.
- `Theory/Monad.v`, `Monad/*`, `Comonad/*`: monads, strength, Kleisli and Eilenberg–Moore resolutions and their limits, monadicity (Beck's precise and crude forms), Dubuc lifting, graded and commutative monads, transformers; comonads by duality with the co-Kleisli and coalgebra API.
- `Theory/Kan/Extension.v`, `Structure/Limit/Kan/Pointwise.v`: Kan extensions, global and local, and the pointwise (co)limit formula.
- `Functor/Hom.v`, `Functor/Hom/Yoneda.v` (+ `Functor/Hom/Yoneda/*`), `Functor/Representable.v` (+ `Functor/Representable/Functorial.v`), `Functor/Hom/Induced.v`, `Functor/Hom/Limit.v`, `Functor/Hom/Transfer.v`, `Functor/Construction/Postcompose.v`, `Functor/Bifunctor/Partial.v`, `Functor/Product/Fixed.v`: Yoneda as an isomorphism of bifunctors, representably isomorphic objects, functoriality of representations, hom-functors preserving limits, the transfer lemma, bifunctors from partial functors, the fixed-factor product.
- `Theory/Universal/Element.v` (+ `Theory/Universal/Element/*`), `Theory/Universal/Arrow.v` (+ `Theory/Universal/Arrow/*`), `Theory/Density.v`, `Construction/Elements/Kan.v`: universal elements and arrows in both variances with their worked examples, every set-valued functor as a colimit of representables, Kan's coyoneda form.
- `Theory/Category/Raw.v`, `Theory/Category/Semi.v`, `Theory/Naturality.v`, `Theory/Concrete/Morphisms.v`: the law-free `RawCategory` data, semigroupoids, the `Naturality` type class that computes a family's naturality statement from its type, underlying injections and surjections in a concrete category. None heads a bullet of its own in the index.
- `Theory/Equivalence.v` (+ `Theory/Equivalence/*`), `Theory/Skeleton.v` (+ `Theory/Skeleton/Separation.v`), `Construction/Subcategory/Dense.v`: equivalences (FF+ESO, adjoint, strict), their composition, and transport of limits, colimits, pullbacks, terminal objects, adjunctions and monoidal structure; skeletons; iso-dense full subcategories are reflective.
- `Theory/Bicategory.v` (+ `Theory/Bicategory/*`), `Theory/TwoCategory.v`, `Instance/Cat/TwoCategory.v`, `Theory/DoubleCategory.v` (+ `Theory/DoubleCategory/Companion.v`), `Construction/Sq.v`, `Construction/Cospan/Double.v`, `Instance/Cat/Bicategory.v` (+ `Instance/Cat/Bicategory/*`): bicategories, pseudofunctors, lax transformations, modifications, adjunctions and mates; strict 2-categories in the globular and arrows-only presentations; pseudo double categories with companions and conjoints.
- `Theory/Algebra/Rig.v` (+ `Theory/Algebra/Rig/Connections.v`), `Theory/Algebra/Monoid.v` (+ `Theory/Algebra/Monoid/*`), `Theory/Algebra/Group/Hom.v`, `Theory/Category/Monoid.v`, `Theory/OGraph.v`, `Theory/EckmannHilton.v`, `Theory/Centre.v`: rigs and rings, internal monoids and groups with their categories and finite products, categories as monoids in O-graphs, Eckmann–Hilton over a bare setoid, the centre of a category.
- `Theory/Algebra/Comonoid.v` (+ `Theory/Algebra/Comonoid/*`), `Theory/Algebra/CommutativeMonoid.v`, `Theory/Algebra/CommutativeComonoid.v`, `Theory/Algebra/Frobenius.v`, `Theory/Algebra/CommutativeFrobenius.v`, `Theory/Algebra/SpecialCommutativeFrobenius.v`, `Theory/Algebra.v`: internal comonoids with their homomorphisms and tensor comonoids, commutative monoids and comonoids, Frobenius algebras through the special commutative ones, and categorified high-school algebra in a bicartesian closed category. None heads a bullet of its own in the index.
- `Theory/Metacategory.v`, `Theory/Metacategory/*`: arrows-only metacategories, the elementary theory ETAC with the duality principle.
- `Theory/Lawvere.v` (+ `Theory/Lawvere/*`), `Theory/Multicategory.v` (+ `Theory/Multicategory/*`): Lawvere theories, models and the PROP bridge; symmetric multicategories, operads and their algebras.
- `Theory/Concrete.v`, `Theory/Connected/Components.v`, `Theory/Size.v`, `Theory/Sieve.v`, `Theory/WeaklyInitial.v` (+ `Theory/WeaklyInitial/Wide.v`): concrete categories, π₀ and connected components, size vocabulary, sieves, Freyd's initial-object construction.
- `Functor/Structure/Monoidal.v` (+ `Functor/Structure/Monoidal/*`), `Functor/Structure/Cartesian.v` (+ `Functor/Structure/Cartesian/Closed.v`), `Functor/Structure/Terminal.v`, `Functor/Structure/Constant.v`, `Functor/Applicative.v`, `Functor/Traversable.v` (+ `Functor/Traversable/Product.v`), `Functor/Strong.v` (+ `Functor/Strong/Product.v`), `Functor/Bifunctor.v`, `Functor/Diagonal.v`, `Functor/Opposite.v`, `Functor/Product.v` (+ `Functor/Product/Internal.v`), `Functor/Coproduct.v`, `Functor/Construction/Product.v` (+ `Functor/Construction/Product/*`), `Functor/Hom/Internal.v`, `Functor/Twist.v`: the functor-structure layer the `Theory/Coq/*` results are built on — lax, strict and braided monoidal functors (`MonoidalFunctor`/`LaxMonoidalFunctor` are `Functor/Structure/Monoidal.v`), cartesian, terminal and constant functors, applicative, traversable and strong functors, the diagonal, opposite, product, coproduct and internal-hom functors, twisting a functor by a family of isomorphisms. None of these files heads a bullet of its own in the index.

### Structures (`Structure/`)
- `Structure/Terminal.v`, `Structure/Initial.v`, `Structure/ZeroObject.v`, `Structure/Cartesian.v` (+ `Structure/Cartesian/*`, among them the product of categories as a cartesian category), `Structure/Cocartesian.v`, `Structure/Cartesian/Closed.v` (+ `Structure/Cartesian/Closed/*`), `Structure/BiCCC.v` (+ `Structure/BiCCC/Strict.v`), `Structure/UniversalProperty.v` (+ `Structure/UniversalProperty/*`): terminal and initial objects with uniqueness in three strengths, products, exponentials with the currying adjunction, naturality of the exponential laws, internal composition and self-enrichment, strict initiality, universal properties.
- `Structure/Bicartesian.v`, `Structure/Distributive.v`, `Structure/Discrete.v`, `Structure/Constant.v`, `Structure/Span.v`: bicartesian and distributive categories, the discreteness property (its reconstruction theorem is `Instance/Discrete/Reconstruct.v`), constants as global elements, spans as `Roof`-shaped diagrams. None heads a bullet of its own in the index.
- `Structure/Limit.v` (+ `Structure/Limit/*`), `Structure/Cone.v` (+ `Structure/Cone/*`: constant cones, cones as natural transformations out of the diagonal), `Structure/Complete.v`: limits and colimits — cone-level preservation, reflection and creation (`Structure/Limit/Preservation.v`, `Structure/Limit/Creation.v`), essential uniqueness with legs (`Structure/Limit/Unique.v`), limits from products and equalizers (`Structure/Limit/FromProducts.v`), finite index categories and finite limits (`Structure/Limit/Finite.v`), limits by evaluation at an initial index (`Structure/Limit/Initial.v`), indexed products and coproducts, finite products, powers and copowers (`Structure/Limit/Product.v`, `Structure/Limit/Coproduct.v`, `Structure/Limit/Product/Finite.v`, `Structure/Limit/Power.v`, `Structure/Limit/Power/*`, `Structure/Limit/Indexed/Hom.v`), constant diagrams over connected shapes (`Structure/Limit/Constant.v`), limits over coproducts of shapes (`Structure/Limit/Components.v`), weighted limits (`Structure/Limit/Weighted.v`).
- `Structure/Pullback.v` (+ `Structure/Pullback/*`), `Structure/Pushout.v` (+ `Structure/Pushout/Split.v`), `Structure/Equalizer.v` (+ `Structure/Equalizer/*`), `Structure/Coequalizer.v` (+ `Structure/Coequalizer/*`): the finite-limit generators and their interdefinability, wide variants, split and reflexive coequalizers.
- `Structure/Monoidal.v` (+ `Structure/Monoidal/*`), `Structure/Premonoidal.v` (+ `Structure/Premonoidal/*`), `Structure/Binoidal.v` (+ `Structure/Binoidal/Central.v`): monoidal, braided, symmetric, closed monoidal (`Structure/Monoidal/Closed.v`) and star-autonomous categories, the dual-object self-adjunction, the Drinfeld centre, copy/discard and Markov categories with Fox's theorem, premonoidal and Freyd categories. `Structure/Closed.v` is an Eilenberg–Kelly stub: its `Class Closed` is commented out and only `Curry` and `Flip` are live.
- `Structure/Ring.v`, `Structure/Lattice.v`, `Structure/Monoid.v`, `Structure/Group.v` (+ `Structure/Group/*`): internal semirings, rings and lattices, monoid and group objects and their functor-of-points characterisation.
- `Structure/AbCategory.v`, `Structure/Preadditive.v`, `Structure/Semiadditive.v`, `Structure/Additive.v`, `Structure/Biproduct.v` (+ `Structure/Biproduct/Cartesian.v`), `Structure/Kernel.v` (+ `Structure/Kernel/*`), `Structure/Abelian.v`, `Structure/Bicartesian/Matrix.v`: the additive spine from Ab-enrichment through biproducts and kernels to abelian categories, with the matrix calculus from coproducts to products.
- `Structure/Factorization.v` (+ `Structure/Factorization/StrongEpi.v`), `Structure/Regular.v` (+ `Structure/Regular/Factorization.v`), `Theory/Orthogonality.v`: orthogonal factorization systems, strong epis, regular categories with the image factorization.
- `Structure/Topos.v` (+ `Structure/Topos/*`), `Structure/SubobjectClassifier.v` (+ `Structure/SubobjectClassifier/Natural.v`), `Theory/Subobject.v` (+ `Theory/Subobject/Functor.v`), `Theory/Sheaf.v` (+ `Theory/Sheaf/Category.v`): subobjects, classifiers, elementary toposes with power objects and their finite colimits, sheaves.
- `Structure/Dagger.v`, `Structure/Groupoid.v` (+ `Structure/Groupoid/*`), `Construction/Groupoid.v`, `Structure/Thin.v`: dagger categories, groupoids as a property with the connected-groupoid structure theorem, the core construction `Groupoid C` (the maximal subgroupoid), thin categories.
- `Structure/Coend.v`, `Structure/End.v`, `Structure/Wedge.v`, `Theory/Coend/*`, `Theory/Dinatural.v`, `Theory/Profunctor.v` (+ `Theory/Profunctor/Adjunction.v`, `Construction/Profunctor/*`), `Construction/Day.v`: the (co)end calculus, ninja Yoneda, Fubini, profunctors and Day convolution.

### Constructions (`Construction/`)
- `Construction/Opposite.v` (+ `Construction/Opposite/Monoidal.v`), `Construction/Product.v` (+ `Construction/Product/*`), `Construction/Coproduct.v` (+ `Construction/Coproduct/Indexed.v`), `Instance/Cat/Opposite.v`, `Instance/Cat/Coproduct.v`, `Instance/Cat/Pullback.v`: duality as a functor, products and set-indexed products and coproducts of categories with their limits, fibre products.
- `Construction/Comma.v` (+ `Construction/Comma/*`), `Construction/Slice.v` (+ `Construction/Slice/*`), `Construction/Arrow.v` (+ `Construction/Arrow/*`), `Construction/Cylinder.v` (+ `Construction/Cylinder/Arrow.v`): comma categories (functoriality, Huq's correspondence, the commuting diagram, discrete-hom special cases), slices with the projection adjunctions and base change, the arrow category and its limits, the cylinder.
- `Construction/Free.v`, `Construction/Free/Quiver.v` (+ `Construction/Free/Quiver/*`), `Construction/Free/Groupoid.v`, `Construction/Free/TwoFunctors.v`, `Construction/FreeMonoidal.v` (+ `Construction/FreeMonoidal/*`), `Construction/PROP.v` (+ `Construction/PROP/*`), `Construction/ColouredPROP.v` (+ `Construction/ColouredPROP/*`), `Construction/Funny.v` (+ `Construction/Funny/*`): free categories on quivers with the worked identifications, presented categories, free groupoids, the free monoidal category with coherence, free and coloured PROPs, the funny tensor.
- `Construction/Deloop.v` (+ `Construction/Deloop/*`), `Construction/Elements.v`, `Construction/Karoubi.v` (+ `Construction/Karoubi/Universal.v`), `Construction/Quotient.v`, `Construction/Cayley.v`: delooping and the monoid dictionary, categories of elements, Karoubi envelopes, hom-congruence quotients, the Cayley representation of a category (no bullet of its own in the index).
- `Construction/Subcategory.v` (+ `Construction/Subcategory/*`), `Construction/Reflective.v` (+ `Construction/Reflective/*`), `Construction/Localization.v` (+ `Construction/Localization/Universal.v`): subcategories, reflective subcategories and idempotent monads, limit creation by reflective inclusions, fixed points of adjunctions, orthogonal localization.
- `Construction/Grothendieck.v` (+ `Construction/Grothendieck/*`), `Theory/Displayed.v`, `Theory/Fibration.v`, `Construction/Displayed/*`, `Construction/Indexed.v`: displayed categories, fibrations, the Grothendieck construction and its round trip with indexed categories.
- `Construction/FAlg.v`, `Construction/FCoalg.v`, `Construction/Chain.v`, `Theory/Lambek.v`, `Theory/Recursion.v`, `Theory/Adamek.v` (+ `Theory/Adamek/Corollaries.v`): F-(co)algebras, Lambek's lemma, cata/anamorphisms, Adámek's theorem.
- `Construction/Enriched.v` (+ `Construction/Enriched/*`): enriched categories, functors and transformations; enrichment over Sets, the walking arrow and Ab.
- `Construction/Span/Category.v`, `Construction/Cospan/*`, `Construction/DecoratedCospan.v` (+ `Construction/DecoratedCospan/*`): the span and cospan categories, braided and symmetric monoidal structure on cospans, corelations (`Construction/Cospan/Corelation.v`), special commutative Frobenius algebras (`Construction/Cospan/SCFA.v`), the hypergraph instance `Cospan_Hypergraph` (`Construction/Cospan/HypergraphInstance.v`), Fong's decorated cospans with their monoidal, braided, symmetric and hypergraph structure, and the black-boxing functor (`Construction/Cospan/BlackBox.v`). None of these files heads a bullet of its own in the index; docs/INHABITATION.md records their inhabitation status.

### Concrete Instances (`Instance/`)
- Sets and types: `Instance/Sets.v` (+ `Instance/Sets/*`: products, complete and cocomplete, the cone-set limit, inverse limits, quotients, coequalizers, pullbacks, pushouts, cokernel pairs, powersets, classifiers, topos, Karoubi, streams, pointed sets), `Instance/Coq.v` (+ `Instance/Coq/*`), `Instance/Ens.v`, `Instance/EnsV.v`, `Instance/FinSet.v` (+ `Instance/FinSet/*`), `Instance/Powerset.v` (+ `Instance/Powerset/*`), `Instance/Discrete.v` (+ `Instance/Discrete/Reconstruct.v`), `Instance/Indiscrete.v`.
- Algebra: `Instance/Grp.v` (+ `Instance/Grp/*`), `Instance/Ab.v` (+ `Instance/Ab/*`), `Instance/CMon.v` (+ `Instance/CMon/*`), `Instance/Mon/*`, `Instance/Monoid/Translation.v`, `Instance/Mod.v` (+ `Instance/Mod/*`), `Instance/Rng.v` (+ `Instance/Rng/*`), `Instance/Rg.v`, `Instance/Field.v` (+ `Instance/Field/Frac.v`), `Instance/FdVect.v` (+ `Instance/FdVect/*`), `Instance/Vect/*`, `Instance/Matr.v` (+ `Instance/Matr/*`), `Instance/Lie.v`, `Instance/InnerProduct/Galois.v`, `Instance/Rep.v`: groups, abelian groups, monoids, modules, rings, fields, vector spaces, matrices, Lie algebras and representations, each with the constructions the bullets record (quotients and isomorphism theorems, free objects and their adjunctions, tensors and tensor-hom, limits and colimits, Galois connections).
- Order: `Instance/Proset.v` (+ `Instance/Proset/*`), `Instance/Pos.v`, `Instance/Ord.v` (+ `Instance/Ord/Poset.v`), `Instance/Poset.v`, `Instance/Two.v` (+ `Instance/Two/*`), `Instance/Ordinal.v`, `Instance/Omega.v`, `Instance/Simplex.v`.
- Topology and metric spaces: `Instance/Top.v` (+ `Instance/Top/*`), `Instance/Met.v` (+ `Instance/Met/*`). No development file outside `Instance/Top/*` and `Instance/Met*` requires the stdlib reals directly — nine files do, named in the `Instance/Top/FundamentalGroupoid.v` bullet of docs/INDEX.md, and `Instance/Top.v` itself is not among them; `Instance/Roster.v` reaches them through `Instance/Top/Homotopy.v`, and docs/AXIOMS.md carries the per-constant axiom footprint.
- Categories of categories and functor categories: `Instance/Cat.v` (+ `Instance/Cat/*`), `Instance/StrictCat.v` (+ `Instance/StrictCat/*`), `Instance/Fun.v` (+ `Instance/Fun/*`: terminal object and indexed products, cartesian structure pointwise (`Instance/Fun/Cartesian.v`), exponentials for presheaf categories only (`Instance/Fun/Exponential.v`) with `Instance/Fun/Closed.v` proving that cartesian closure is NOT inherited in general, pullbacks, monos and epis, classifier, topos, group objects, discrete shapes, actions), `Instance/Cones.v` (+ `Instance/Cones/*`: the cone category's limit, and cones as the comma category `Δ ↓ F`).
- Presented and finite shapes: `Instance/Square.v` (+ `Instance/Square/*`), `Instance/Presented/*`, `Instance/WalkingIso.v`, `Instance/Parallel.v` (+ `Instance/Parallel/Wide.v`), `Instance/Roof.v`, `Instance/Zero.v`, `Instance/One.v` (+ `Instance/One/Diagonal.v`).
- Others: `Instance/Rel.v` (+ `Instance/Rel/Dagger.v`), `Instance/Props.v` (propositions under implication), `Instance/Theory/Lindenbaum.v`, `Instance/Lambda.v` (+ `Instance/Lambda/*`), `Instance/AST.v` (the free bicartesian closed category as a term model), `Instance/Fact.v` (the factorization category of a morphism), `Instance/Shapes.v` (shape-indexed tries; its `Shape` is unrelated to `Theory/Shapes.v`), `Instance/Roster.v` (the roster of standard large categories with their forgetful functors), `Instance/Concrete.v`, `Instance/Comp.v`, `Instance/ZX.v` (the only file with `Axiom`/`Parameter` declarations). Of these, only `Instance/Theory/Lindenbaum.v` and `Instance/Roster.v` head a bullet of their own in the index (`Instance/Lambda/*` heads one as a directory).

### Applied Programming and Tooling (`Theory/Coq/`, `Solver/`, `Tools/`, `Lib/`, `Test/`)
- `Theory/Coq/*` (+ the aggregator `Theory/Coq.v`): bridges pure theory with practical Coq programming — applicative functors via monoidal functors, traversable functors with laws, and monad transformers with coherence conditions (`MonadTransformer` and `MonadTransformerLaws` are in `Monad/Transformer.v`, not under `Theory/Coq/`).
- `Solver/*` (+ the umbrella `Solver.v`): the reflective solver for categorical equations — abstract syntax (`Solver/Expr.v`), reification of a goal (`Solver/Reify.v`), normalization (`Solver/Normal.v`), denotation back into the category (`Solver/Denote.v`) and the sound decision procedure the tactics consume (`Solver/Decide.v`) — with no bullets in the index.
- `Tools/Abstraction.v`, `Tools/Represented.v`: compiling Coq functions to cartesian-closed combinators, and representing Coq data types in the free bicartesian closed category — with no bullets in the index.
- `Lib.v` and `Lib/*`: the foundation. Every file in `_CoqProject` requires `Category.Lib` except the umbrellas `Theory.v` and `Solver.v` (which re-export modules that do), three files inside `Lib/` itself, and `Instance/Lambda/Ltac.v` (pure Ltac, requiring nothing from `Category.*`). `Lib.v` sets the eight project-wide flags every file inherits (primitive projections, universe polymorphism, uniform inductive parameters, `Default Proof Using "Type"`, the `!` goal selector, opaque `Program` obligations, no intuition negation unfolding, no universe minimization to `Set`); the index cites `Lib.v:10` and `Lib.v:12` as the causes of two recorded traps. `Lib/*` holds the setoid layer and `≈` (`Lib/Setoid.v`, `Lib/Datatypes.v`, `Lib/Foundation.v`), the tactics of the Proof Development Patterns section above (`Lib/Tactics.v`, `Lib/Tactics2.v`), the typed lists (`Lib/TList.v`, `Lib/NETList.v`, `Lib/IList.v`) and the finite-map helpers (`Lib/FMapExt.v`, `Lib/MapDecide.v`). Neither has bullets of its own in the index.
- `Test/*`: the `Fail`-probe files that pin each development's measured boundaries — `Test/Probe<Topic>.v`, most carrying the number of the issue they guard and most named in that development's bullet — plus the regression and smoke-test files `Test/Issue*.v`, `Test/FullIssue118.v`, `Test/HypergraphPROPResolution.v`, `Test/Poset.v` and `Test/Size.v`. All are in `_CoqProject` and built by `make`; none heads a bullet of its own, and `make todo` counts their `Fail` commands.

## Critical Design Patterns

### Equivalence Over Equality
Never use `=` for morphisms. Always use `≈`:
```coq
(* WRONG *)
Lemma foo : f ∘ id = f.

(* RIGHT *)
Lemma foo : f ∘ id ≈ f.
```

### Proper Morphisms
All operations must respect equivalence:
```coq
Program Instance Foo_Proper {C : Category} :
  Proper (equiv ==> equiv ==> equiv) (@foo C).
```

### Notation Precedence
- `~>` morphisms (level 90)
- `∘` composition (level 40, left associative)
- `⟶` functors between categories
- `⟹` natural transformations

### Proof Automation
Standard proof pattern:
```coq
Proof.
  intros.
  cat.          (* tries simplification + rewriting *)
  proper.       (* if proving Proper *)
  equivalence.  (* if proving Equivalence *)
Qed.
```

## Common Development Tasks

### Adding a New Category Instance
1. Define objects and morphisms
2. Define equivalence relation on morphisms (setoid)
3. Prove it forms a category (id, compose, laws)
4. Place in Instance/ directory
5. Add to _CoqProject

### Proving Functoriality
1. Define object mapping F_obj
2. Define morphism mapping F_map
3. Prove F_map respects equivalence
4. Prove F preserves id and composition
5. Use `Program Instance` to manage obligations

### Establishing Adjunctions
1. Define functors F : C ⟶ D and G : D ⟶ C
2. Define unit η : Id ⟹ G ○ F
3. Define counit ε : F ○ G ⟹ Id
4. Prove triangle identities
5. Or use hom-set adjunction definition

## References and Learning

When working with specific concepts, reference:
- **nLab**: https://ncatlab.org/nlab/show/[concept_name]
- **README.md**: Contains detailed notation guide (the "Notations" section)
- **docs/AXIOMS.md**: the axiom audit — what each `Axiom`/`Parameter` is, which definitions are certified "Closed under the global context", and which stdlib axioms the concrete instance layers do use.
- **docs/INHABITATION.md**: which headline results carry a concrete in-tree witness of their distinctive premise, and which are proven parametrically as axiom-free conditionals awaiting a model. Consult it before citing a flagship theorem (GAFT, SAFT, the Sheaf theory, `image_mediator_epic`, the spider results, …) as demonstrated over a concrete object — several are conditional-only.
- **docs/INDEX.md**: the per-development index of the library's headline developments (the former "Key Files and Concepts" section of this file) — one bullet per landed development, with strengths, measurements and what was not delivered
- **In-file background essays**: beyond the definitional header most files carry, the flagship concept files across Theory/, Structure/, Construction/, Instance/, Adjunction/, and the Comonad development open with a background essay — the concept's history, purpose, cross-disciplinary use, and in-tree connections, each substantive claim cited to a primary source (nLab, the named papers, textbooks, or package documentation). Read that block first when approaching an unfamiliar file.

## Versioning

Default version: Rocq 9.1 (the `default` package in flake.nix)
Supported: Coq 8.19-8.20, Rocq 9.0-9.1
Equations dependency required for some parts (versions matched to Coq)

## Testing Individual Theorems

To test a specific construction:
```bash
# Extract just the files needed
coqdep -R . Category Theory/MyConstruction.v | grep -v "^#"

# Compile dependencies first
make Theory/Category.vo Theory/Functor.vo

# Then compile your file
coqc -R . Category Theory/MyConstruction.v
```
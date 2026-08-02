```yaml
title: "MacLane I.1: Commutative diagrams as first-class objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.1:def3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.1 ("Axioms for Categories"), printed p. 8 (PDF p. 18)
- Items: `maclane:I.1:def3`

## Background
Mac Lane defines a diagram as a graph of vertices labelled by objects and edges labelled by arrows, calling it commutative when any two directed paths between the same pair of vertices compose to the same arrow. This is the working language of all of category theory, yet it is usually left informal. See https://ncatlab.org/nlab/show/commutative+diagram.

## Current state in the library
Commutativity exists only instance-by-instance as `≈`-equations between composites. The operational core is formalized: `Solver/Expr.v:65` (`Inductive Term`) reifies composite-morphism expressions, with denotation in `Solver/Denote.v` and a decision procedure in `Solver/Decide.v`; `Construction/Free/Quiver.v:431` (`FreeOnQuiver`) renders paths in a directed graph as morphisms (`tlist edges`). What is missing (verified PARTIAL): a first-class "diagram over a directed graph" object with a commutativity predicate quantifying over all pairs of parallel paths — Mac Lane's actual definition is never stated.

## Work to be done
- Define, in a new `Theory/Diagram.v` (or as an extension of `Construction/Free/Quiver.v`), a diagram in `C` over a quiver `G` as a quiver homomorphism `G ⟶ C` (donor: `QuiverHomomorphism`, `Construction/Free/Quiver.v:205`).
- Define path denotation (composition of edge labels along a `tlist` path) and the predicate `Commutative`: for every pair of vertices and every two parallel paths, the denoted composites are `≈`-equal.
- Prove the bridge to the free category: a diagram is the same thing as a functor `FreeOnQuiver G ⟶ C`, and commutativity of the diagram corresponds to the functor identifying parallel path-morphisms.
- Sanity examples: a commuting square and a commuting triangle recover the usual two-composite `≈`-equations; connect to the Solver's `Term` denotation where convenient.

## Definition of Done
- [ ] Statement matches Mac Lane §I.1 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact (`Commutative`, the free-category bridge)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Diagram.v
# in a scratch file:
#   Require Import Category.Theory.Diagram. Print Assumptions Commutative.
# expect: Closed under the global context
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: check statement fidelity against Mac Lane §I.1, printed p. 8 (PDF p. 18) — the predicate must quantify over all pairs of parallel paths, not fixed shapes.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.1:def3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.1: Arrows-only metacategories and the equivalence of category presentations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.1:remark1, maclane:I.1:def4, maclane:I.1:prop1, maclane:I.8:remark1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.1 ("Axioms for Categories"), printed pp. 8–9 (PDF pp. 18–19); I.8 ("Hom-Sets"), printed p. 27 (PDF p. 37)
- Items: `maclane:I.1:remark1`, `maclane:I.1:def4`, `maclane:I.1:prop1`, `maclane:I.8:remark1`

## Background
Mac Lane gives three presentations of the category axioms — objects-and-arrows, arrows-only (a single sort of arrows with a partial composition and identities characterized by their unit behaviour), and hom-set-indexed — and asserts they are equivalent, with identity arrows uniquely determined and objects identifiable with identities. See https://ncatlab.org/nlab/show/single-sorted+definition+of+a+category.

## Current state in the library
One direction is machine-checked twice: `Theory/Metacategory/ArrowsOnly.v:37` (`Record Metacategory` over `N`-indexed arrows with an FMap composition table, `is_identity` at line 69 keeping Mac Lane's definedness guard) with `Category_from_Metacategory` at line 212; and `Theory/Metacategory.v:133` with `FromArrows` at line 261. Verified gaps: (a) both records fix the arrow sort to `nat`/`N` with a finite-map composition — there is no general-carrier arrows-only axiomatization; (b) the identity-existence axiom (iii) is mis-encoded (implication where a conjunction is needed) and is vacuously true — acknowledged by in-file TODOs (`ArrowsOnly.v:77–83`, `Metacategory.v:184–190`); (c) uniqueness of the flanking identities (Mac Lane's remark that `1_b` is uniquely determined) is stated nowhere, neither at the metacategory level nor as a lemma in `Theory/Category.v`; (d) no `Category ⟶ Metacategory` converse exists, so the equivalence of presentations (I.1 prop and I.8 remark) is one-directional; (e) the disjointness-restoring relabelling `{a} × hom(a,b) × {b}` of I.8 is not a construction (its effect is achieved structurally by dependent typing).

## Work to be done
- In `Theory/Metacategory/General.v` (new): an arrows-only metacategory record over an arbitrary arrow `Type` (partial composition as a relation or partial function), with axiom (iii) stated correctly as a conjunction.
- Prove uniqueness of the identities attached to an arrow (the content of `maclane:I.1:remark1`), and add the corresponding one-line `id_unique` corollary at `Category` level (an arrow with the two-sided unit property is `≈ id`).
- Construct `ToArrows : Category → Metacategory` (arrows = the total hom, composition = the composite when types match) and prove the two passages mutually inverse up to the appropriate notion of isomorphism — completing `maclane:I.1:prop1` and the I.8 equivalence remark.
- Optionally: the tagging construction restoring hom-disjointness, as a functorial relabelling.
- Keep the existing `N`/FMap development as the computable-model layer; fix or annotate its vacuous `identity_law` per the in-file TODOs.

## Definition of Done
- [ ] Statement matches Mac Lane §§I.1, I.8 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the round-trip theorems and `id_unique`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Metacategory/General.v
# Print Assumptions on: the corrected record's round-trip theorems, id_unique
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.1 pp. 8–9 (PDF 18–19) — axiom (iii) must be an existence statement forcing unique flanking identities — and §I.8 p. 27 (PDF 37).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.1:remark1","maclane:I.1:def4","maclane:I.1:prop1","maclane:I.8:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: A category is a monoid for the product over its object set"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:remark1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 10 (PDF p. 20)
- Items: `maclane:I.2:remark1`

## Background
Mac Lane observes that the set-based definition of a category says exactly that a category is a monoid for the product over its object set `A ×_O A` (composable pairs) — the germ of the notion of internal category and of monoids in spans. See https://ncatlab.org/nlab/show/internal+category.

## Current state in the library
Verified ABSENT. There is no internal-category definition (the only mentions are prose disclaimers at `Construction/Enriched.v:83–85` and `Theory/DoubleCategory.v:115`); `Structure/Span.v` is only the span diagram shape for pullbacks; monoid objects exist (`Structure/Monoid.v`, `Theory/Algebra/Monoid.v`) but nothing states that a category structure on a graph is a monoid structure for the pullback product over its objects.

## Work to be done
- In `Theory/Category/Monoid.v` (or `Construction/Span/Monoid.v`, new): fix an object type `O` and formalize two-sorted graphs `(A, dom, cod)` over `O` (in `Coq`/`Sets`), with the composable-pairs product `A ×_O A`.
- Show that giving identities and a composition making the I.2 axioms hold is precisely giving a unit `O → A` and multiplication `A ×_O A → A` satisfying monoid laws for `×_O` — i.e. a monoid in the monoidal-like structure of graphs/spans over `O` (donor: `MonoidObject`, `Structure/Monoid.v`).
- Round-trip with the library's `Category` class at the corresponding universe levels (a small category with `obj = O` yields such a monoid and conversely).

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the correspondence theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Category/Monoid.v
# Print Assumptions on the category-as-monoid correspondence
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 10 (PDF p. 20).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: Discrete categories are exactly sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 11 (PDF p. 21)
- Items: `maclane:I.2:construction2`

## Background
A category is discrete when every arrow is an identity; every set becomes a discrete category, and every discrete category is determined by its set of objects — a bijective correspondence between sets and discrete categories. See https://ncatlab.org/nlab/show/discrete+category.

## Current state in the library
Both halves of the vocabulary exist: `DiscreteCat` (`Instance/Discrete.v:37`), the predicate `Discrete` (`Structure/Discrete.v:28`, every morphism forces `x = y` and is the transported identity), connected one way by `DiscreteCat_Discrete` (`Instance/Discrete.v:65`). Verified gap: no reconstruction theorem — nothing proves that a category satisfying `Discrete` is isomorphic/equivalent (in Cat) to `DiscreteCat` of its object type, which is the book's "determined by its set of objects". The `Discrete` predicate's use of object equality is flagged in-file ("Equality is too much here") as a known coarseness.

## Work to be done
- In `Instance/Discrete.v` (extend): a reconstruction functor `C ⟶ DiscreteCat (obj C)` for `Discrete C`, and the isomorphism/equivalence closing the correspondence (in `StrictCat` where the equality-based predicate supports it, in `Cat` otherwise).
- Consider an iso-robust restatement of `Discrete` per the in-file caveat (subsingleton hom-setoids with all arrows invertible), proving it equivalent to the existing predicate for `DiscreteCat`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the reconstruction theorem
- [ ] New files registered in `_CoqProject` (if new files are added)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Discrete.v
# Print Assumptions on the reconstruction theorem
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 11 (PDF p. 21) — both directions of the sets ↔ discrete categories correspondence.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: Delooping monoids and groups into one-object categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction3, maclane:I.2:construction4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 11 (PDF p. 21)
- Items: `maclane:I.2:construction3`, `maclane:I.2:construction4`

## Background
A monoid is exactly a category with one object, and a group is a one-object category with all arrows invertible; conversely `hom(a, a)` is a monoid for every object `a`. This delooping dictionary underlies representation theory read functorially. See https://ncatlab.org/nlab/show/delooping.

## Current state in the library
Verified ABSENT (both items). There is no general monoid-to-one-object-category construction: `Theory/Bicategory/OneObject.v` deloops a *monoidal category* into a one-object bicategory (one level up); `Construction/Funny/Comparison.v:81` (`ListMon`) hard-codes a single one-object category from the free monoid on `bool` with no general construction or homomorphism correspondence; no lemma states that `hom(a, a)` is a monoid; `Structure/Group.v:109` (`GroupObject`) gives internal group objects only, and `Construction/Groupoid.v` is the core (maximal subgroupoid) of an existing category, not a delooping.

## Work to be done
- In `Construction/Deloop.v` (new): given a monoid (donor: monoid objects of `Theory/Algebra/Monoid.v` instantiated at `Sets`, or a direct carrier/op/unit record), build the one-object category `B M` (`obj := unit`, `hom := M`, composition = multiplication), with all category laws under the carrier's `≈`.
- Prove the converse observation: for any category `C` and object `a`, `hom(a, a)` carries a monoid structure (composition, identity).
- The group case (`maclane:I.2:construction4`): when the monoid is a group (donor: `Structure/Group.v` `GroupObject` at `Sets`, or `Instance/Comp.v:382` `Group`), every arrow of `B G` is invertible — a one-object groupoid.
- Functor-level dictionary (functors between deloopings = homomorphisms) is deliberately deferred to the `maclane:I.3:ex3` issue; keep this issue to the constructions.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `B` (delooping), the `hom(a,a)` monoid, and the group/groupoid lemma
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Construction/Deloop.v
# Print Assumptions on B, hom_monoid, B_group_invertible
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 11 (PDF p. 21) — both directions (monoid ⇒ one-object category; endo-hom ⇒ monoid).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction3","maclane:I.2:construction4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: The matrix category Matr_K"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction5]
deps_item_ids: [maclane:I.7:def1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 11 (PDF p. 21)
- Items: `maclane:I.2:construction5`

## Background
For a commutative ring `K`, `Matr_K` has the positive integers as objects and rectangular `m × n` matrices over `K` as arrows `n → m`, composed by matrix product — the classical skeleton of finitely generated free modules. See https://en.wikipedia.org/wiki/Category_of_matrices.

## Current state in the library
Verified ABSENT. All matrix mentions are prose (`Theory/Equivalence.v:87` cites the nat-and-matrices category as the classical equivalence example; `Functor/Hom/Yoneda.v:89–90`; `Instance/ZX.v:108,120,169` motivational remarks); no matrix category, and no ring structure exists in-tree at all (blocking ingredient).

## Work to be done
- In `Instance/Matr.v` (new): objects `nat`; `hom m n` := matrices with entries in `K` (e.g. `Fin.t n → Fin.t m → K`); composition = matrix product via finite sums over `K`'s additive commutative monoid; identity matrices; category laws (`≈` = entrywise `≈`).
- Parameterize over the ring vocabulary delivered by the `maclane:I.7:def1` issue (a semiring suffices for the category laws; the commutative-ring instance is the headline). Donor for the additive layer: `Instance/CMon.v`.
- Sanity: `Matr` at a one-element ring collapses; entrywise finite-sum lemmas kept reusable (they feed the GL_n/determinant issue).

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; instance-layer stdlib axioms per docs/AXIOMS.md if any, enumerated there)
- [ ] `Print Assumptions` closed (or documented per AXIOMS.md) for `Matr`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Matr.v
# Print Assumptions Matr
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 11 (PDF p. 21) — note the book's arrows `A : n → m` for `m × n` matrices; pick and document one orientation.

## Dependencies
Depends on: maclane:I.7:def1

<!-- catalog: {"ids":["maclane:I.2:construction5"],"deps":["maclane:I.7:def1"]} -->
---8<---
```yaml
title: "MacLane I.2: Ens_V, the category of sets within a set V"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction6]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 11 (PDF p. 21)
- Items: `maclane:I.2:construction6`

## Background
For any set `V` of sets, `Ens_V` is the category whose objects are the members of `V` and whose arrows are *all* functions between them — Mac Lane's device for set-sized sub-universes of the category of sets. See https://ncatlab.org/nlab/show/category+of+sets.

## Current state in the library
Verified PARTIAL. The namesake `Ens` (`Instance/Ens.v:34`) deliberately alters the morphisms — whole-carrier functions preserving *and reflecting* membership (`A = f⁻¹(B)`), with the header stating "This file does NOT build that classical category directly"; `EnsT` (`Instance/Ens.v:56`) fixes one carrier. The faithful "all sets bounded by a size parameter, all functions" categories exist only with the bound fixed at a universe level (`Instance/Coq.v:120`, `Instance/Sets.v:188`), not at an arbitrary member-family `V`.

## Work to be done
- In `Instance/Ens.v` (extend) or `Instance/EnsV.v` (new): a category parameterized by a family `V` rendered type-theoretically as a type of codes with decoding `El : V → Type` (or `→ SetoidObject`): objects the codes, `hom x y :=` all functions `El x → El y` (setoid maps in the `Sets` variant), usual composition.
- Relate to the existing categories: at the tautological family (`V := Type@{o}`, `El := id`) this recovers `Coq`; document that the existing `Ens` is a different construction and keep it, cross-linked.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the new category
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/EnsV.v
# Print Assumptions EnsV
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 11 (PDF p. 21) — morphisms must be ALL functions between members of `V`, not structure-preserving ones.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction6"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: Preorders as thin categories, with partial and linear orders"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction7, maclane:I.2:def4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 11 (PDF p. 21)
- Items: `maclane:I.2:construction7`, `maclane:I.2:def4`

## Background
A preorder is a category with at most one arrow between any two objects; reading off `p ≤ p'` from arrow existence gives a bijective correspondence between preordered sets and such thin categories. Partial orders add antisymmetry, linear orders add totality. See https://ncatlab.org/nlab/show/thin+category and https://en.wikipedia.org/wiki/Total_order.

## Current state in the library
Both single directions exist: `Proset` (`Instance/Proset.v:33`, any `PreOrder R` as a thin category with all parallel arrows identified) and `hom_preorder` (`Theory/Category.v:282`, every category's underlying preorder); `Poset` adds antisymmetry (`Instance/Poset.v:116`). At the 2-enriched level, `Enriched_Two_preorder` / `EnrichedFunctor_Two_monotone` (`Construction/Enriched/Two.v:165/183`) give the correspondence with maps in both directions, but state no round-trip. Verified gaps: no thinness predicate on categories ("thin" is prose-only); no theorem that `Proset` and `hom_preorder` are mutually inverse (the book's bijective correspondence); linear (total) orders are nowhere defined — no totality/trichotomy predicate exists (`Instance/Omega.v` cites Total_order in prose only).

## Work to be done
- In `Structure/Thin.v` (new) or `Instance/Proset.v` (extend): `Thin C := ∀ x y (f g : x ~> y), f ≈ g`; prove `Proset P` thin.
- Round-trip: `hom_preorder (Proset P)` is `P` (up to the obvious identification), and for thin `C`, `Proset (hom_preorder C)` is isomorphic/equivalent to `C` — the bijective correspondence of `maclane:I.2:construction7`.
- Linear orders (`maclane:I.2:def4`): a `TotalOrder` structure (preorder + antisymmetry + totality), with `nat ≤` as instance; its thin category via `Poset`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the round-trip theorems and `TotalOrder`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Structure/Thin.v
# Print Assumptions on the two round-trip theorems
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 11 (PDF p. 21) — the correspondence must be stated in both directions.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction7","maclane:I.2:def4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: Finite ordinals as categories and the chain ω"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction8]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed pp. 11–12 (PDF pp. 21–22)
- Items: `maclane:I.2:construction8`

## Background
Each ordinal `n`, viewed as the linearly ordered set of all smaller ordinals, is a category (a preorder); the finite categories 1, 2, 3 arise this way, and ω is the linear order `0 → 1 → 2 → ⋯`. See https://ncatlab.org/nlab/show/ordinal.

## Current state in the library
ω is fully present: `Omega` (`Instance/Omega.v:72`, objects `nat`, hom `le_t`, with `omega_step` at line 85) and also `(nat, ≤)` via `Proset`. The ordinals 0, 1, 2 exist as the bespoke categories `_0`/`_1`/`_2` (`Instance/Zero.v:28`, `Instance/One.v:25`, `Instance/Two.v:134`). Verified gaps: no uniform ordinal-to-category family — no `n ↦ [n]` construction on `Fin n`, no `_3` as an `Instance/` category (the only 3 lives in the self-contained `Theory/Metacategory.v:413` development), and no identification of an ordinal with its set of predecessors.

## Work to be done
- In `Instance/Ordinal.v` (new): the family `[n] :=` thin category on `Fin.t n` with `i ≤ j` (donor: `Instance/Proset.v`), for all `n`.
- Agreement isos: `[0] ≅ _0`, `[1] ≅ _1`, `[2] ≅ _2` (in `Cat` or `StrictCat`); define/export `_3 := [3]` for downstream use (the `maclane:I.3:ex2` issue).
- Embedding functors `[n] ⟶ [n+1]` and `[n] ⟶ Omega` realizing "an ordinal is the set of its predecessors" categorically.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `[n]`, the agreement isos, and the embeddings
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Ordinal.v
# Print Assumptions on the family and the agreement isos
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed pp. 11–12 (PDF 21–22).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction8"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: The simplicial category Delta"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.2:construction9]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.2 ("Categories"), printed p. 12 (PDF p. 22)
- Items: `maclane:I.2:construction9`

## Background
Δ has all finite ordinals as objects and the order-preserving functions as arrows; it is the indexing category of simplicial objects and is central to Mac Lane's Chapter VII. See https://ncatlab.org/nlab/show/simplex+category.

## Current state in the library
Verified ABSENT. All simplicial/simplex mentions are background-essay prose (`Instance/FinSet.v:87–89` on Δ embedding into FinSet, `Theory/Kan/Extension.v:47,91`, `Comonad/Core.v:103`, `Structure/Coend.v:113`, …); the `Delta` identifier in-tree is the duplication morphism of comonoids (ZX/CopyDiscard files); "monotone" appears only for `TwoPreorder` maps in `Construction/Enriched/Two.v:176`. Even the see-also categories `Ord`/`Pos` named in `Instance/Proset.v:20` / `Instance/Poset.v:22` prose do not exist.

## Work to be done
- In `Instance/Simplex.v` (new): objects `nat`; `hom m n :=` monotone functions `Fin.t m → Fin.t n` (function together with a monotonicity witness; hom-setoid compares the function part pointwise).
- Identity/composition preserve monotonicity; category laws.
- The wide (non-full) inclusion `Simplex ⟶ FinSet` forgetting monotonicity (donor: `Instance/FinSet.v:116`), shown faithful.
- Optional stretch (document if deferred): faces/degeneracies as generators and the simplicial identities, which Chapter VII will need.

## Definition of Done
- [ ] Statement matches Mac Lane §I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Simplex` and the inclusion functor
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Simplex.v
# Print Assumptions Simplex
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 12 (PDF p. 22) — objects are ALL finite ordinals (including 0), arrows all order-preserving maps.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.2:construction9"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.2: The roster of standard large categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.1:construction2, maclane:I.2:construction12]
deps_item_ids: [maclane:I.6:construction2, maclane:I.7:construction1, maclane:I.7:construction2, maclane:I.7:construction3, maclane:I.7:construction4, maclane:I.7:construction5, maclane:I.7:construction6]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.1 ("Axioms for Categories"), printed p. 9 (PDF p. 19); I.2 ("Categories"), printed p. 12 (PDF p. 22)
- Items: `maclane:I.1:construction2`, `maclane:I.2:construction12`

## Background
Mac Lane's standing roster of large categories of small structures — Set, Set*, Ens, Cat, Mon, Grp, Ab, Rng, CRng, R-Mod, Mod-R, K-Mod, Top, Toph, Top* (and, in I.1, the metacategories of groups, spaces, compact Hausdorff spaces, ringed spaces). See https://ncatlab.org/nlab/show/Grp and https://ncatlab.org/nlab/show/Top.

## Current state in the library
Present counterparts (verified): Set as `Coq` (`Instance/Coq.v:120`) and `Sets` (`Instance/Sets.v:188`); Cat as `Cat` (`Instance/Cat.v:142`, the Ho(Cat) presentation) and `StrictCat` (`Instance/StrictCat.v:56`, the textbook strict 1-category); `Ens` with disclosed non-classical morphisms (`Instance/Ens.v:34`); Mon as internal `Mon(C)` (`Theory/Algebra/Monoid/Hom.v:83`, not instantiated/named at `Sets`) plus `CMon` (`Instance/CMon.v:140`); Set* only via `Par`'s prose-claimed equivalence (`Instance/Coq/Par.v:53`, header lines 34–36). Verified missing: Grp, Ab, Rng, CRng, all module categories, Top, Toph, Top* (zero definitional hits tree-wide).

## Work to be done
This is the integration issue over the specific construction issues (see Dependencies). Residual work once they land:
- `CRng` as the full subcategory of commutative rings (if not already delivered by the Rng issue).
- `Mod-R` (right modules, via the opposite ring), `K-Mod`, and `R-Mod-S` bimodule variants over the R-Mod machinery.
- Name and export the `Sets` instantiation of the internal `Mon(C)` as the roster's `Mon`.
- A roster `Examples`/index file checking each named category exists with its evident forgetful functor, and a header disclosing which roster entries (compact Hausdorff spaces, ringed spaces) remain out of near-term scope and why.

## Definition of Done
- [ ] Statement matches Mac Lane §§I.1–I.2 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed (or documented per AXIOMS.md for instance-layer stdlib axioms) for each roster artifact added here
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Roster.v   # or the chosen index file
# Print Assumptions on each residual construction (CRng, Mod-R, K-Mod, Mon@Sets)
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.2, printed p. 12 (PDF p. 22) — every roster entry either exists in-tree or is explicitly disclosed as out of scope.

## Dependencies
Depends on: maclane:I.6:construction2
Depends on: maclane:I.7:construction1
Depends on: maclane:I.7:construction2
Depends on: maclane:I.7:construction3
Depends on: maclane:I.7:construction4
Depends on: maclane:I.7:construction5
Depends on: maclane:I.7:construction6

<!-- catalog: {"ids":["maclane:I.1:construction2","maclane:I.2:construction12"],"deps":["maclane:I.6:construction2","maclane:I.7:construction1","maclane:I.7:construction2","maclane:I.7:construction3","maclane:I.7:construction4","maclane:I.7:construction5","maclane:I.7:construction6"]} -->
---8<---
```yaml
title: "MacLane I.3: The covariant power-set functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.3:construction1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed p. 13 (PDF p. 23)
- Items: `maclane:I.3:construction1`

## Background
The power-set functor sends a set to its set of subsets and a function to its direct-image action on subsets — Mac Lane's first worked example of a functor. See https://ncatlab.org/nlab/show/power+set.

## Current state in the library
Verified ABSENT. The only `Pow` in-tree is the *internal* power object `Pow a := Ω ^ a` of an elementary topos (`Structure/Topos.v:129`, an object mapping with no functorial action); `Theory/Subobject/Functor.v`'s `Sub : C^op ⟶ Sets` is the *contravariant* pullback-reindexing subobject functor, not this covariant construction; `Instance/Ens.v` is a category of ensembles, not a functor; no endofunctor on `Sets`/`Coq` with direct-image action exists.

## Work to be done
- In `Instance/Sets/Powerset.v` (new): the sub-setoid/predicate setoid `P X` (predicates `X → Prop` respecting `≈`, compared by pointwise `iff`), and the functor action `P f` = direct image (`y ∈ P f S` iff some `x ∈ S` has `f x ≈ y`); prove `fmap_id`, `fmap_comp` under the predicate setoid — funext-free by design.
- Mind the universe placement: the predicate setoid lives one level up (donors: `PropSetoid`/`Setoid_Lift`, `Instance/Sets/Classifier.v:47/115`); state the functor at the honest cross-universe type (`Sets@{o} ⟶ Sets@{so}`) or document the chosen discipline in the header.
- Sanity: on `FinSet`-sized examples the direct image computes as expected.

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the power-set functor
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Sets/Powerset.v
# Print Assumptions PowersetFunctor
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 13 (PDF p. 23) — covariant, with direct image `S ↦ fS`.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.3:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.3: GL_n and the determinant as a natural transformation"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.3:construction2, maclane:I.4:construction1]
deps_item_ids: [maclane:I.2:construction5, maclane:I.6:construction2, maclane:I.7:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.3 ("Functors"), printed p. 14 (PDF p. 24); I.4 ("Natural Transformations"), printed p. 16 (PDF p. 26)
- Items: `maclane:I.3:construction2`, `maclane:I.4:construction1`

## Background
For each `n`, taking a commutative ring `K` to the group `GL_n(K)` of invertible `n × n` matrices is a functor `CRng ⟶ Grp`, and because the determinant is one polynomial formula uniform in the ring, `det : GL_n ⟹ (−)^*` (units) is Mac Lane's flagship first example of a natural transformation. See https://ncatlab.org/nlab/show/general+linear+group and https://en.wikipedia.org/wiki/Determinant.

## Current state in the library
Verified ABSENT (both items). No determinant or general-linear content anywhere (`GL`/`GL_n`/`determinant`: zero formal hits); no matrix category; neither the domain `CRng` nor the codomain `Grp` exists in-tree (`Structure/Group.v:109` is internal group objects only).

## Work to be done
Once the dependencies land (`CRng` from the Rng issue, `Grp`, and matrix algebra from `Matr`):
- In `Instance/Matr/GL.v` (new): the group of units of the `n × n` matrix monoid over `K`; entrywise functoriality of `GL_n f` for a ring map `f`; the functor `GL_n : CRng ⟶ Grp`.
- The units functor `(−)^* : CRng ⟶ Grp`.
- In `Instance/Matr/Determinant.v`: the determinant over a commutative ring (Leibniz-formula or expansion-based development), multiplicativity `det (A·B) ≈ det A · det B`, invertible iff `det` a unit, and commutation with ring maps — assembling `det : GL_n ⟹ (−)^*` as a `Transform`.

This is a substantial linear-algebra development; keep the determinant lemmas reusable (they also serve `maclane:I.4:ex6`).

## Definition of Done
- [ ] Statement matches Mac Lane §§I.3–I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; any instance-layer stdlib axioms enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed (or documented) for `GL_n`, the units functor, and `det`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Matr/Determinant.v
# Print Assumptions GL_n_Functor det_Transform
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 16 (PDF p. 26) — the naturality square `det_{K'} ∘ GL_n f ≈ f^* ∘ det_K`.

## Dependencies
Depends on: maclane:I.2:construction5
Depends on: maclane:I.6:construction2
Depends on: maclane:I.7:construction2

<!-- catalog: {"ids":["maclane:I.3:construction2","maclane:I.4:construction1"],"deps":["maclane:I.2:construction5","maclane:I.6:construction2","maclane:I.7:construction2"]} -->
---8<---
```yaml
title: "MacLane I.3: Commutator subgroup and abelianization functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.3:construction3, maclane:I.4:construction2]
deps_item_ids: [maclane:I.6:construction2, maclane:I.7:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.3 ("Functors"), printed p. 14 (PDF p. 24); I.4 ("Natural Transformations"), printed pp. 16–17 (PDF pp. 26–27)
- Items: `maclane:I.3:construction3`, `maclane:I.4:construction2`

## Background
The commutator subgroup `[G, G]` is functorial in `G` (homomorphisms carry commutators to commutators), and the factor-commutator quotient `G ↦ G/[G, G]` gives the abelianization functor `Grp ⟶ Ab`; the family of projections `p_G : G → G/[G, G]` is a natural transformation from the identity functor. See https://ncatlab.org/nlab/show/abelianization.

## Current state in the library
Verified ABSENT (both items). `commutator`/`factor-commutator`: zero hits; `abelianization` appears once as prose (`Construction/Localization.v:106`, listing classical reflective localizations); no category of groups or abelian groups exists to host the construction. The abstract fact that a reflection unit is natural exists (`Construction/Reflective.v`) but none of this item's concrete content does.

## Work to be done
Once `Grp` and `Ab` land:
- In `Instance/Grp/Abelianization.v` (new): the commutator subgroup as a sub-group-object (generated by commutators — a setoid-friendly inductive generation), functorial in `G`.
- Quotient groups: the setoid quotient of a group carrier by a normal subgroup (coset equivalence) — the main new infrastructure; keep it reusable (it also serves `maclane:I.5:ex5` and `maclane:I.7:prop1`).
- The abelianization functor `Grp ⟶ Ab` and the projection family `p` as a `Transform` from `Id` to the composite `Grp ⟶ Ab ⟶ Grp`.
- Optional stretch: abelianization as left adjoint to the inclusion `Ab ⟶ Grp` (ties into `Construction/Reflective.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §§I.3–I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the two functors and the natural projection
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Grp/Abelianization.v
# Print Assumptions Commutator_Functor Abelianization_Functor abel_projection
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed pp. 16–17 (PDF 26–27) — the naturality square `p_H ∘ f ≈ f' ∘ p_G`.

## Dependencies
Depends on: maclane:I.6:construction2
Depends on: maclane:I.7:construction1

<!-- catalog: {"ids":["maclane:I.3:construction3","maclane:I.4:construction2"],"deps":["maclane:I.6:construction2","maclane:I.7:construction1"]} -->
---8<---
```yaml
title: "MacLane I.3: The center of a group is not functorial"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.3:remark1, maclane:I.3:ex4]
deps_item_ids: [maclane:I.6:construction2, maclane:I.7:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed pp. 14–15 (PDF pp. 24–25)
- Items: `maclane:I.3:remark1`, `maclane:I.3:ex4`

## Background
The center `Z(G)` fails to be functorial: a homomorphism need not carry central elements to central elements, and (the exercise's stronger claim) *no* functor `Grp ⟶ Ab` has `G ↦ Z(G)` as its object function — the classical argument uses the retract `S₂ → S₃ → S₂` of symmetric groups. See https://en.wikipedia.org/wiki/Center_(group_theory).

## Current state in the library
Verified ABSENT (both items). Every `center`/`centre` hit in-tree is the premonoidal centre (`Structure/Binoidal/Central.v`, `Structure/Premonoidal/Centre.v`) or the Drinfeld monoidal centre (`Structure/Monoidal/Drinfeld.v`) — categorical centres, a different concept; the symmetric-group hits are PROP/braid machinery; no category of groups exists to host the statement.

## Work to be done
Once `Grp` and `Ab` land:
- Define `Z(G)` as an abelian subgroup of `G` (elements commuting with everything).
- Concrete finite symmetric groups `S₂`, `S₃` (permutations of `Fin.t n`; donors: `Instance/FinSet.v` and its mono/injection toolkit), with `Z(S₂) ≅ S₂` (order 2) and `Z(S₃)` trivial.
- The no-functor theorem: for any functor `T : Grp ⟶ Ab` with `T G = Z(G)` on objects, the retract `r ∘ i = id : S₂ → S₃ → S₂` forces `id` on a two-element group to factor through the trivial group — contradiction. (This works for an arbitrary arrow function, which is the honest reading of the exercise.)

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the no-functor theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Grp/Center.v
# Print Assumptions no_center_functor
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 15 (PDF p. 25) — the theorem must quantify over ALL functors with the center object function.

## Dependencies
Depends on: maclane:I.6:construction2
Depends on: maclane:I.7:construction1

<!-- catalog: {"ids":["maclane:I.3:remark1","maclane:I.3:ex4"],"deps":["maclane:I.6:construction2","maclane:I.7:construction1"]} -->
---8<---
```yaml
title: "MacLane I.3: Full and faithful functors, subcategories, and reflection of monics"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.3:def4, maclane:I.3:def5, maclane:I.3:def6, maclane:I.5:ex9]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.3 ("Functors"), printed pp. 14–15 (PDF pp. 24–25); I.5 ("Monics, Epis, and Zeros"), printed p. 21 (PDF p. 31)
- Items: `maclane:I.3:def4`, `maclane:I.3:def5`, `maclane:I.3:def6`, `maclane:I.5:ex9`

## Background
Full and faithful functors are the hom-surjective and hom-injective ones; both classes are closed under composition; a subcategory's inclusion is automatically faithful and a full subcategory is determined by its objects; faithful functors reflect monics. See https://ncatlab.org/nlab/show/full+functor and https://ncatlab.org/nlab/show/faithful+functor.

## Current state in the library
The definitions are exact: `Full` (`Theory/Functor.v:331`, split-surjectivity via `prefmap`/`fmap_sur`), `Faithful` (`Theory/Functor.v:342`, `fmap_inj`), and the subcategory apparatus `Subcategory`/`Sub`/`Incl`/`Full`/`Full_Implies_Full_Functor` (`Construction/Subcategory.v:31/50/59/69/74`, plus `Wide`:93, `Replete`:87). Verified gaps: (1) no composition-closure lemmas — a full enumeration of all `Full`/`Faithful` instances found none for a composite `F ◯ G`; (2) no general `Faithful (Incl S)` instance (faithfulness of inclusions is asserted only in the lines 25–27 comment; proven only for concrete cases such as `Sheaves_Faithful`, `Theory/Sheaf/Category.v:103`); (3) only one direction of "full subcategory iff full inclusion" (`Full_Implies_Full_Functor`, no converse); (4) faithful-reflects-monics is absent — the only Faithful+Monic result is the adjoint-transpose `adj_monic` (`Theory/Adjunction.v:311`), not the reflection, and `Monic (fmap ...)` has zero hits tree-wide; (5) the book's `Set_f ⊂ Set` full-subcategory example is absent.

## Work to be done
- In `Theory/Functor.v` (extend): `Full_Compose` and `Faithful_Compose` instances for `F ◯ G` (prefmap composes; `fmap_inj` twice).
- In `Construction/Subcategory.v` (extend): the general `Faithful (Incl S)` instance (trivial: `Sub`'s hom equivalence is projection-wise) and the converse bridge `Functor.Full Incl → Full S` completing the iff.
- In `Theory/Functor.v` or `Theory/Morphisms.v`: `faithful_reflects_monic : Faithful F → Monic (fmap[F] f) → Monic f` and the dual `faithful_reflects_epic`.
- A worked full-subcategory example of finite sets inside `Sets`/`Coq` (cross-reference the `maclane:I.4:construction4` skeleton issue; a simple `sobj := finiteness` witness suffices here).

## Definition of Done
- [ ] Statement matches Mac Lane §§I.3, I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the four lemma groups
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Functor.v && coqc -R . Category Construction/Subcategory.v
# Print Assumptions Full_Compose Faithful_Compose Incl_Faithful faithful_reflects_monic
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3 pp. 14–15 (PDF 24–25) and §I.5 exercise 9, p. 21 (PDF 31).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.3:def4","maclane:I.3:def5","maclane:I.3:def6","maclane:I.5:ex9"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.3: The field of quotients as a functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.3:ex1]
deps_item_ids: [maclane:I.7:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed p. 15 (PDF p. 25)
- Items: `maclane:I.3:ex1`

## Background
Exercise: exhibit the field of quotients of an integral domain, and the Lie algebra of a Lie group, as functors (choosing the right domain category in each case). See https://ncatlab.org/nlab/show/field+of+fractions.

## Current state in the library
Verified ABSENT. The only mentions are background-essay prose (`Theory/Universal/Arrow.v:44–45` lists the field of quotients among historical examples of universal arrows; `Theory/Lawvere.v:87`; `Structure/Group.v:46,93` for Lie groups); no integral domains, fields, Lie groups, or Lie algebras are formalized, and no category of rings exists (blocking ingredient).

## Work to be done
Once `Rng`/`CRng` land:
- Integral domains as a (full sub)category of `CRng`; the choice of morphisms matters for functoriality — develop over the category of integral domains with *monomorphisms* (the standard fix), and document why.
- The fraction-field construction `Frac D` as a setoid quotient of pairs (numerator, nonzero denominator), with the induced action on monomorphisms; functor laws.
- Optionally: the universal-arrow reading (donor: `Theory/Universal/Arrow.v`), fitting the essay already in that file.
- The Lie-algebra half requires smooth manifolds and is beyond this library's scope for the foreseeable future; the file header must disclose the descope (this issue covers the item with that disclosure).

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`); Lie half explicitly disclosed as descoped
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Frac` and its functoriality
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Rng/Frac.v
# Print Assumptions Frac_Functor
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 15 (PDF p. 25); confirm the domain-category choice (monomorphisms) is documented.

## Dependencies
Depends on: maclane:I.7:construction2

<!-- catalog: {"ids":["maclane:I.3:ex1"],"deps":["maclane:I.7:construction2"]} -->
---8<---
```yaml
title: "MacLane I.3: Functors out of 1, 2, and 3"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.3:ex2]
deps_item_ids: [maclane:I.2:construction8]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed p. 15 (PDF p. 25)
- Items: `maclane:I.3:ex2`

## Background
Functors from the ordinal categories 1, 2, 3 into `C` correspond exactly to objects, arrows, and composable pairs of arrows of `C` — the "walking shape" principle in its first three cases. See https://ncatlab.org/nlab/show/interval+category.

## Current state in the library
Verified PARTIAL. All three shapes exist — `_1` (`Instance/One.v:25`), `_2` (`Instance/Two.v:134`), and a `Three` in the arrows-only development (`Theory/Metacategory.v:413`) — and the arrow category exists as the comma `Arrow := (Id ↓ Id)` (`Construction/Arrow.v:110`). But none of the three correspondences is a formal theorem: the 1- and 2-cases are file-header prose only (`Instance/One.v:21–22`, `Instance/Two.v:18–21`), `Construction/Arrow.v:104–108` explicitly discloses the `[2, C]` comparison as "documentation-level", and no functor out of `Three` is developed (`FromThree` is a commented-out fragment, `Theory/Metacategory.v:532–560`).

## Work to be done
- In `Instance/Two/Functors.v` or a new `Theory/Shapes.v`:
  - objects of `C` ≃ functors `_1 ⟶ C` (setoid-level bijection; the dual `Cat_Terminal` already exists);
  - arrows of `C` ≃ functors `_2 ⟶ C`, and the comparison `[_2, C] ≅ Arrow C` closing `Construction/Arrow.v`'s disclosed gap;
  - composable pairs ≃ functors `[3] ⟶ C`, over the ordinal family delivered by `maclane:I.2:construction8`.
- Keep each correspondence stated as an explicit construction pair with round-trip laws (the library has no generic "bijection" carrier for object classes; a two-map presentation with both composites identified is the faithful form).

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the three correspondence theorems
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Shapes.v
# Print Assumptions on the three correspondences (objects/arrows/composable pairs)
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 15 (PDF p. 25).

## Dependencies
Depends on: maclane:I.2:construction8

<!-- catalog: {"ids":["maclane:I.3:ex2"],"deps":["maclane:I.2:construction8"]} -->
---8<---
```yaml
title: "MacLane I.3: Functors between preorders, groups, and representation categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.3:ex3]
deps_item_ids: [maclane:I.2:construction3, maclane:I.2:construction5]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed p. 15 (PDF p. 25)
- Items: `maclane:I.3:ex3`

## Background
Exercise: interpret "functor" between special categories — (a) between preorders, a functor is a monotone map; (b) between groups (as one-object categories), a group homomorphism; (c) out of a group `G`, a functor to Set is a permutation representation and a functor to `Matr_K` a matrix representation. See https://en.wikipedia.org/wiki/Permutation_representation.

## Current state in the library
Verified PARTIAL. Part (a) exists only in enriched rephrasing: `EnrichedFunctor_Two_monotone` (`Construction/Enriched/Two.v:183`, with `MonotoneMap` at 175 and `Enriched_Two_preorder` at 165) identifies 2-enriched functors with monotone maps; the ordinary-functor version between `Proset` categories (`Instance/Proset.v:33`) is not stated. Parts (b) and (c) have no counterpart: no general delooping exists (the ad hoc `ListMon`, `Construction/Funny/Comparison.v:81`, carries no homomorphism correspondence), no permutation-representation reading of functors `B G ⟶ Sets`, and no matrix category.

## Work to be done
Once the delooping (`maclane:I.2:construction3`/`construction4`) and `Matr` land:
- (a) Ordinary form: functors `Proset P ⟶ Proset Q` correspond to monotone maps (both directions, round trip up to the thin-category identification).
- (b) Functors `B M ⟶ B N` correspond to monoid homomorphisms; specialize to groups.
- (c) Functors `B G ⟶ Sets` correspond to `G`-actions on a setoid (permutation representations); functors `B G ⟶ Matr_K` to matrix representations (dimension = the chosen object).
- Suggested module: `Construction/Deloop/Functors.v` plus an `Instance/Proset` extension.

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the three interpretation theorems
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Construction/Deloop/Functors.v
# Print Assumptions on the (a)/(b)/(c) correspondence theorems
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 15 (PDF p. 25) — all three parts.

## Dependencies
Depends on: maclane:I.2:construction3
Depends on: maclane:I.2:construction5

<!-- catalog: {"ids":["maclane:I.3:ex3"],"deps":["maclane:I.2:construction3","maclane:I.2:construction5"]} -->
---8<---
```yaml
title: "MacLane I.3: Two distinct functors sharing the identity object function"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.3:ex5]
deps_item_ids: [maclane:I.6:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.3 ("Functors"), printed p. 15 (PDF p. 25)
- Items: `maclane:I.3:ex5`

## Background
Exercise: find two different functors `T : Grp ⟶ Grp` whose object function is the identity — showing a functor is not determined by its action on objects. See https://ncatlab.org/nlab/show/functor.

## Current state in the library
Verified ABSENT. No category of groups exists (the ambient setting is missing); searches for "distinct functors"/"same object function" find only `Construction/Funny/StrictEq.v:21`, a strict-equality extensionality lemma for functors out of the funny tensor, unrelated to exhibiting such a pair.

## Work to be done
Once `Grp` lands:
- Exhibit two functors `Grp ⟶ Grp` with the same (identity) object function but provably different arrow functions, and prove their distinctness in the strict functor setoid (`Functor_StrictEq_Setoid` sense) — note that in the weak `Cat` setoid naturally isomorphic functors are identified, so the statement lives at the strict level; document this reading.
- The construction is part of the exercise; the issue deliberately does not fix one (candidates in the literature use automorphism twists). Whatever witness is chosen, distinctness must be established on a concrete pair of morphisms.

## Definition of Done
- [ ] Statement matches Mac Lane §I.3 in substance (setoid discipline: `≈` on morphisms, never `=`; strict-vs-weak functor equality documented)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the distinctness theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Grp/TwoFunctors.v
# Print Assumptions on the two functors and the distinctness theorem
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.3, printed p. 15 (PDF p. 25).

## Dependencies
Depends on: maclane:I.6:construction2

<!-- catalog: {"ids":["maclane:I.3:ex5"],"deps":["maclane:I.6:construction2"]} -->
---8<---
```yaml
title: "MacLane I.4: Character groups and duality of finite abelian groups"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.4:construction3, maclane:I.4:remark1]
deps_item_ids: [maclane:I.7:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 17 (PDF p. 27)
- Items: `maclane:I.4:construction3`, `maclane:I.4:remark1`

## Background
The character group `D(G) = hom(G, ℝ/ℤ)` is contravariant, its square `DD` is a covariant endofunctor of Ab, and the evaluation family `τ_G : G → DD(G)` is natural — an isomorphism when `G` is finite. By contrast, each finite abelian `G` is isomorphic to `D(G)` only via a choice of decomposition, and Mac Lane makes the non-naturality precise on the iso-only subcategory. See https://ncatlab.org/nlab/show/Pontryagin+duality.

## Current state in the library
Verified PARTIAL (at the generous edge). Only the abstract skeleton exists, in star-autonomous form over an *uninhabited* class: the contravariant dual functor (`Structure/Monoidal/StarAutonomous.v:229`), `double_dual` (:252), and the class fields `star_double_dual`/`star_natural` (:269/:273) — where the double-dual iso is *posited* rather than constructed (header's own deviation note, lines 71–79), and docs/INHABITATION.md records `StarAutonomous` as doubly uninhabited. Nothing concrete: no Ab, no characters, no evaluation map, no finiteness argument; the book's example appears as prose in `Theory/Natural/Transformation.v:44–54`.

## Work to be done
Once `Ab` lands:
- Finite abelian groups `Ab_f` as a full subcategory (finiteness as data on the carrier).
- The character group `D(G) := hom-group into the circle`; for finite `G`, `ℚ/ℤ` receives every character, so develop `D` with `ℚ/ℤ` (stdlib `QArith`-based quotient) as the dualizing group, with a header note that the book's `ℝ/ℤ` restricts to this on `Ab_f`.
- Contravariance `D f = (− ∘ f)`; the covariant `DD`; the evaluation family `τ_G` with its naturality square (`maclane:I.4:construction3`).
- `τ_G` iso for finite `G` — via a pairing/counting argument or the cyclic-decomposition route; this is the substantial half.
- The non-naturality remark (`maclane:I.4:remark1`): the iso-only category `Ab_f,i` (donor: `Construction/Groupoid.v` core), the covariant `D'` with `D' f = D (f⁻¹)`, and a proof that no choice of isos `σ_G : G ≅ D G` is natural (a concrete two-object violation suffices).

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`; the ℚ/ℤ-for-ℝ/ℤ restriction disclosed)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `τ` naturality, the finite-iso theorem, and the non-naturality theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Ab/Character.v
# Print Assumptions tau_natural tau_iso_finite sigma_not_natural
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 17 (PDF p. 27) — including the precise `D'`/iso-only formulation of the negative half.

## Dependencies
Depends on: maclane:I.7:construction1

<!-- catalog: {"ids":["maclane:I.4:construction3","maclane:I.4:remark1"],"deps":["maclane:I.7:construction1"]} -->
---8<---
```yaml
title: "MacLane I.4: The double-dual natural isomorphism for finite-dimensional vector spaces"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.4:remark2]
deps_item_ids: [maclane:I.4:ex6]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 17 (PDF p. 27)
- Items: `maclane:I.4:remark2`

## Background
A finite-dimensional vector space is naturally isomorphic to its double dual via evaluation, whereas any isomorphism with the single dual requires a choice of basis and is not natural — the paradigm example distinguishing natural from accidental isomorphisms. See https://en.wikipedia.org/wiki/Dual_space.

## Current state in the library
Verified PARTIAL. The abstract shape exists: `double_dual` is genuinely constructed and functorial (`Structure/Monoidal/StarAutonomous.v:252`), with the iso and naturality square as *class fields* `star_double_dual`/`star_natural` (:269/:273) — assumed data, never proven for any concrete category; `StarAutonomous` has no instance anywhere (docs/INHABITATION.md), and no category of vector spaces exists (all `Vect`/"vector space" hits are essay prose, e.g. `Theory/Functor.v:68`; the header of StarAutonomous.v names FdVect as a motivating, unformalized example).

## Work to be done
Once `FdVect` lands (from the `maclane:I.4:ex6` issue):
- The dual functor `V ↦ V*` (contravariant) on FdVect; the double-dual endofunctor; the evaluation family `V → V**`.
- Naturality of evaluation and the isomorphism theorem for finite-dimensional `V` (dimension bookkeeping from the FdVect infrastructure).
- Connect to the abstract apparatus: note (or prove, as a stretch) that this yields the first concrete inhabitant pattern for the `star_double_dual`/`star_natural` fields, updating docs/INHABITATION.md accordingly.

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; instance-layer stdlib axioms enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed (or documented) for the naturality and isomorphism theorems
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/FdVect/DoubleDual.v
# Print Assumptions double_dual_natural double_dual_iso
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 17 (PDF p. 27).

## Dependencies
Depends on: maclane:I.4:ex6

<!-- catalog: {"ids":["maclane:I.4:remark2"],"deps":["maclane:I.4:ex6"]} -->
---8<---
```yaml
title: "MacLane I.4: The skeleton equivalence between finite sets and finite ordinals"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.4:construction4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed pp. 17–18 (PDF pp. 27–28)
- Items: `maclane:I.4:construction4`

## Background
The inclusion of finite ordinals into all finite sets, together with a cardinal functor built from chosen bijections `θ_X : X ≅ #X`, exhibits the two categories as equivalent — Mac Lane's motivating example for the notion of equivalence of categories (a category and its skeleton). See https://ncatlab.org/nlab/show/skeleton+of+a+category.

## Current state in the library
Verified PARTIAL. Only one side of the comparison exists: the skeletal `FinSet` (`Instance/FinSet.v:116`, objects `nat`, morphisms all functions `Fin.t m → Fin.t n`); the general notion the example motivates exists (`EquivalenceOfCategories`, `Theory/Equivalence.v:151`). Missing: a non-skeletal category of all finite sets (Set_f), the inclusion functor, the choice-of-bijections cardinal functor `#`, and the equivalence theorems `# ∘ S ≈ Id` and `Id ≅ S ∘ #` (no skeleton construction or category-equivalent-to-its-skeleton theorem exists in any generality; `Instance/Ens.v` was checked and rejected as a Set_f candidate).

## Work to be done
- In `Instance/FinSet/Skeleton.v` (new): a category `Set_f` of finite setoids/types — carriers with a finiteness witness (an enumeration or a bijection to some `Fin.t n`), all maps as morphisms (donor: `Construction/Subcategory.v` over `Sets` or `Coq`).
- The inclusion `S : FinSet ⟶ Set_f` (each `n` to the canonical `Fin.t n`).
- The cardinal functor `# : Set_f ⟶ FinSet` using the chosen bijections carried by the finiteness witnesses, with `# f = θ_Y ∘ f ∘ θ_X⁻¹`.
- The equivalence: `# ∘ S ≈ Id` (choosing identity bijections on the canonical objects) and `θ : Id ≅ S ∘ #` — assembled as an `EquivalenceOfCategories` witness.
- Optional stretch: a general `Skeleton` vocabulary (skeletal predicate + every category equivalent to a skeleton needs choice — keep to the finite concrete case here).

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/FinSet/Skeleton.v
# Print Assumptions FinSet_Setf_Equivalence
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed pp. 17–18 (PDF 27–28) — including `# ∘ S` strictly identity-like on the canonical objects.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.4:construction4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.4: The currying adjunction and naturality of evaluation"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 18 (PDF p. 28)
- Items: `maclane:I.4:ex1`

## Background
For fixed `S`, the assignment `X ↦ X^S` is a functor and evaluation `e_X : X^S × S → X`, `e(h, s) = h(s)`, is natural in `X` — the counit of the currying adjunction `(− × S) ⊣ (−)^S`. See https://ncatlab.org/nlab/show/exponential+object.

## Current state in the library
Verified PARTIAL (verifier overturned an initial PRESENT). Part (a) is present and stronger: the internal hom is a bifunctor for every CCC (`InternalHomFunctor`, `Functor/Hom/Internal.v:40`) with `Sets` an instance where `eval` is literally application (`Instance/Sets/Cartesian/Closed.v:38`). Part (b) is a genuine gap: `eval := uncurry id` (`Structure/Cartesian/Closed.v:75`) carries the UMP, and the naturality square is a two-rewrite consequence of `uncurry_comp_r` (:185) + `eval_first` (:141), but it is *nowhere stated*: no named lemma `f ∘ eval ≈ eval ∘ first (fmap f)`, no bundled `Transform`, the single-variable endofunctor `X ↦ X^S` exists only as an unnamed partial application (the `PartialApply_*` machinery is commented out, `Theory/Naturality.v:63–115`), and the currying adjunction is cited in prose three times but never packaged as an `Adjunction` record.

## Work to be done
- Materialize the endofunctor `(−)^S : C ⟶ C` for a CCC `C` (revive or reimplement the partial-application functors of `Theory/Naturality.v`).
- A named lemma for eval's naturality in the target variable, and the bundled `Transform` from `(−)^S × S` to `Id`.
- Package the adjunction `(− × S) ⊣ (−)^S` as an `Adjunction` (donor: `Theory/Adjunction.v`), with `eval` as counit and `curry` as transpose; instantiate at `Sets`, where the counit computes to `e(h, s) = h s`.
- Suggested module: `Structure/Cartesian/Closed/Adjunction.v`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the endofunctor, the naturality lemma, and the adjunction
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Structure/Cartesian/Closed/Adjunction.v
# Print Assumptions exp_functor eval_natural curry_adjunction
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 18 (PDF p. 28) — naturality in `X` with `S` fixed.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.4:ex1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.4: The fixed-factor product functor and its induced transformation"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex2]
deps_item_ids: [maclane:I.6:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 18 (PDF p. 28)
- Items: `maclane:I.4:ex2`

## Background
For a fixed group `H`, `G ↦ H × G` is a functor `Grp ⟶ Grp`, and each morphism `f : H → K` induces a natural transformation `H × − ⟹ K × −` with components `f × id`. See https://ncatlab.org/nlab/show/natural+transformation.

## Current state in the library
Verified PARTIAL. The categorical content is fully proven for an arbitrary cartesian category: the product bifunctor (`InternalProductFunctor`, `Functor/Product/Internal.v:34`), functoriality of the fixed-factor action (`second_id`/`second_comp`, `Structure/Cartesian.v:340/346`), and the naturality square of `f × id` (`first_second`, `Structure/Cartesian.v:386`); the one-variable tensoring functors exist in the binoidal vocabulary (`inj_left`/`inj_right`, `Structure/Binoidal.v:49`). Gaps: the induced family is not packaged as a named `Transform` between the two partial-application functors, and no category `Grp` exists to instantiate the exercise's actual setting.

## Work to be done
- Package, for any cartesian `C` and `f : H ~> K`, the `Transform` `H × − ⟹ K × −` with components `first f` and naturality by `first_second` (suggested: `Functor/Product/Fixed.v`).
- Once `Grp` lands: binary products in `Grp` (direct products — deliver here if the Grp issue has not), and the instantiation of both the functor `H × −` and the induced transformation at `Grp`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the packaged functor and transformation
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Functor/Product/Fixed.v
# Print Assumptions fixed_product_functor fixed_product_transform
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 18 (PDF p. 28) — naturality in the moving factor, component `f × id`.

## Dependencies
Depends on: maclane:I.6:construction2

<!-- catalog: {"ids":["maclane:I.4:ex2"],"deps":["maclane:I.6:construction2"]} -->
---8<---
```yaml
title: "MacLane I.4: Natural transformations between group homomorphisms are conjugations"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex3]
deps_item_ids: [maclane:I.2:construction4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 18 (PDF p. 28)
- Items: `maclane:I.4:ex3`

## Background
For groups `B`, `C` as one-object categories and homomorphisms `S, T : B → C` as functors, a natural transformation `S ⟹ T` exists exactly when `S` and `T` are conjugate: some `h ∈ C` has `T g = h (S g) h⁻¹` for all `g` — natural transformations as intertwiners. See https://ncatlab.org/nlab/show/natural+transformation.

## Current state in the library
Verified ABSENT. No general group delooping exists (the blocking ingredient; `Construction/Funny/Comparison.v:81`'s `ListMon` is a single ad hoc monoid delooping with no transformation-level statements); `conjuga*` hits are all false positives (hom_cast conjugation, braid conjugation, unitor conjugation).

## Work to be done
Once the delooping (`maclane:I.2:construction4`) lands:
- The characterization theorem: `Transform (B S) (B T)` is inhabited iff there exists `h` with `T g ≈ h · S g · h⁻¹` for all `g`; both directions (a transformation's single component is such an `h`; conversely any such `h` is a natural transformation).
- Setoid-level care: the collection of transformations `B S ⟹ B T` corresponds to the set of conjugating elements.
- Suggested module: `Construction/Deloop/Transform.v`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both directions of the characterization
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Construction/Deloop/Transform.v
# Print Assumptions transform_iff_conjugate
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 18 (PDF p. 28) — the iff, not just one direction.

## Dependencies
Depends on: maclane:I.2:construction4

<!-- catalog: {"ids":["maclane:I.4:ex3"],"deps":["maclane:I.2:construction4"]} -->
---8<---
```yaml
title: "MacLane I.4: Natural transformations into a preorder"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 19 (PDF p. 29)
- Items: `maclane:I.4:ex4`

## Background
For functors `S, T : C ⟶ P` with `P` a preorder viewed as a category, a natural transformation `S ⟹ T` exists iff `S c ≤ T c` for every object `c`, and is then unique — functor categories into thin categories are thin. See https://ncatlab.org/nlab/show/preorder.

## Current state in the library
Verified ABSENT. The setting exists — `Proset` (`Instance/Proset.v:33`, with proof-irrelevant homs `equiv := True`) and functor categories (`Instance/Fun.v`) — and the 2-enriched development stops at the functor level (`Construction/Enriched/Two.v:165/183`, no transformation-level result); but the existence-iff-pointwise-≤ characterization and the uniqueness claim are nowhere stated.

## Work to be done
- In `Instance/Proset.v` (extend) or `Instance/Proset/Transform.v` (new): for `S T : C ⟶ Proset P`, a `Transform S T` exists iff `∀ c, S c ≤ T c` (components are exactly the order witnesses; naturality is automatic by thinness).
- Uniqueness: any two such transformations are `≈` (immediate from the trivial hom-setoid — state it anyway, as the book does).
- Optional: restate over the `Thin` predicate if the `maclane:I.2:construction7` issue has landed (soft cross-reference; not a dependency).

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for existence-iff and uniqueness
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Proset/Transform.v
# Print Assumptions transform_into_proset_iff transform_into_proset_unique
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 19 (PDF p. 29).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.4:ex4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.4: The arrows-only presentation of natural transformations"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex5]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 19 (PDF p. 29)
- Items: `maclane:I.4:ex5`

## Background
A natural transformation `τ : S ⟹ T` determines a function on *arrows*, `f : c → c'` to `τ f : S c → T c'`, satisfying `T g ∘ τ f = τ (g ∘ f) = τ g ∘ S f`; conversely any such arrow-indexed family arises from a unique natural transformation with components `τ (1_c)` — an object-free presentation of naturality. See https://ncatlab.org/nlab/show/natural+transformation.

## Current state in the library
Verified ABSENT. The arrows-only development covers categories only (`Theory/Metacategory/ArrowsOnly.v`, zero `Transform` hits in its 612 lines); `Theory/Natural/Transformation.v` carries only the componentwise `Transform` class; no arrow-indexed presentation with the two-sided splice law, and no round-trip theorem, exists anywhere (the funny-tensor "unnatural transformations" are lawless component families — the opposite of this item).

## Work to be done
- In `Theory/Natural/Transformation/Arrows.v` (new): the record of an arrow-indexed family `τ_arr {c c'} (f : c ~> c') : S c ~> T c'` with the law `fmap[T] g ∘ τ_arr f ≈ τ_arr (g ∘ f)` and `τ_arr (g ∘ f) ≈ τ_arr g ∘ fmap[S] f` for composable `g, f`.
- The round trip: from a `Transform` build the family (`τ_arr f := transform ∘ fmap[S] f`, equivalently `fmap[T] f ∘ transform`); from a family recover the `Transform` with components `τ_arr id`; both composites the identity up to `≈`, and the correspondence respects the transformation setoid.

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the round-trip theorems
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Natural/Transformation/Arrows.v
# Print Assumptions on the two round-trip theorems
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 19 (PDF p. 29) — both splice equations and uniqueness.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.4:ex5"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.4: Finite-dimensional vector spaces and the matrix-category equivalence"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.4:ex6]
deps_item_ids: [maclane:I.2:construction5, maclane:I.7:construction3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.4 ("Natural Transformations"), printed p. 19 (PDF p. 29)
- Items: `maclane:I.4:ex6`

## Background
The category of all finite-dimensional vector spaces over a field `F` with linear maps is equivalent to the matrix category `Matr_F` — the classical example of an equivalence between a large category and its small skeleton-like model. See https://ncatlab.org/nlab/show/Vect and https://en.wikipedia.org/wiki/Category_of_matrices.

## Current state in the library
Verified ABSENT. No category of vector spaces over a field exists (all `Vect`/`Matr`/linear-map hits are prose: ZX-calculus motivation in `Instance/ZX.v:108–169`, the star-autonomous example naming FdVect as non-formalized at `Structure/Monoidal/StarAutonomous.v:52`, the equivalence example prose at `Theory/Equivalence.v:87`); neither category in the exercise exists, and no skeleton-equivalence witness of any kind exists in-tree.

## Work to be done
Once `Matr` and the module-category infrastructure land:
- Fields as a class over `CRng` (nonzero, inverses for nonzero elements); `Vct_F := F-Mod` restricted to *finite-dimensional* objects — carriers with a chosen finite basis/enumeration (dimension data), the pragmatic reading that avoids classical basis-existence.
- The functor `Matr_F ⟶ FdVect_F` (`n ↦ F^n`, matrix ↦ linear map) and the comparison back via the chosen bases.
- The equivalence (`EquivalenceOfCategories`, donor `Theory/Equivalence.v:151`), with the natural isos built from basis expansions.
- This delivers the reusable `FdVect` substrate for the double-dual issue (`maclane:I.4:remark2`).

## Definition of Done
- [ ] Statement matches Mac Lane §I.4 in substance (setoid discipline: `≈` on morphisms, never `=`; chosen-basis reading disclosed)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; instance-layer stdlib axioms enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed (or documented) for the equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/FdVect.v
# Print Assumptions FdVect_Matr_Equivalence
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.4, printed p. 19 (PDF p. 29) — equivalence (not isomorphism) of categories.

## Dependencies
Depends on: maclane:I.2:construction5
Depends on: maclane:I.7:construction3

<!-- catalog: {"ids":["maclane:I.4:ex6"],"deps":["maclane:I.2:construction5","maclane:I.7:construction3"]} -->
---8<---
```yaml
title: "MacLane I.5: Epis in Sets are exactly the surjections"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.5:def4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 19 (PDF p. 29)
- Items: `maclane:I.5:def4`

## Background
An arrow is epi when it is right-cancellable; in the category of sets the epis are precisely the surjections. See https://ncatlab.org/nlab/show/epimorphism.

## Current state in the library
Verified PARTIAL. The definition is exact (`Epic`, `Theory/Morphisms.v:104`). The Set characterization is stated as `surjectivity_is_epic` (`Instance/Sets.v:429`) but the proof is abandoned with `Abort` at line 476 — *neither* direction enters the environment; the file's own comment (lines 412–428) documents the size obstruction for the reverse direction (the truth-value setoid lives one universe up) and points to `Instance/Sets/Classifier.v`. No FinSet epi characterization exists either (FinSet has only the monic one, `Instance/FinSet/Classifier.v:334`).

## Work to be done
- Salvage the easy half as a standalone lemma: surjective (`∀ b, ∃ a, h a ≈ b`) implies `Epic` in `Sets` — no size obstruction.
- The converse via the cross-universe classifier route (donors: `PropSetoid`, `Setoid_Lift`, `sets_char_*` in `Instance/Sets/Classifier.v`): state at the honest universe placement (the `Epic` hypothesis quantified at the level that includes the lifted truth-value object), with a header note mirroring `Instance/Sets.v:412–428`.
- `finset_epic_iff_surjective` for `FinSet` (decidable, both directions, no obstruction; donor: `Instance/FinSet/Classifier.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`; universe placement documented)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each direction and the FinSet iff
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Sets.v && coqc -R . Category Instance/FinSet/Classifier.v
# Print Assumptions surjective_implies_epic epic_implies_surjective finset_epic_iff_surjective
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 19 (PDF p. 29); confirm no `Abort`ed statements remain claimed as coverage.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.5:def4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.5: Split morphisms, idempotent composites, and regular arrows"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.5:def5, maclane:I.5:ex7]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed pp. 19–21 (PDF pp. 29–31)
- Items: `maclane:I.5:def5`, `maclane:I.5:ex7`

## Background
One-sided inverses give sections and retractions: an arrow with a right inverse is epi, one with a left inverse is monic, and a split pair `g ∘ h = 1` makes `h ∘ g` idempotent. Exercise 7 introduces (von Neumann) regular arrows — those with `f g f = f` — and asks that split arrows are regular, and that in Set every map with nonempty domain is regular. See https://ncatlab.org/nlab/show/split+epimorphism and https://en.wikipedia.org/wiki/Regular_semigroup.

## Current state in the library
Verified PARTIAL / ABSENT respectively. The one-sided-inverse core is complete: `Section`/`Retraction`/`SplitEpi`/`SplitMono` (`Theory/Morphisms.v:56/70/126`), both implications (`retractions_are_epic`:162, `sections_are_monic`:179), and the flips (:230/:241). Gaps: (i) no lemma that a split pair's composite is idempotent — `SplitIdempotent` (`Theory/Morphisms.v:85`) asserts it only in header prose, and `Idempotent (` matches only `id_idem` and Karoubi internals; (ii) the aside that the converse of split-epi ⇒ epi holds in Set (by choice) but fails elsewhere has no counterpart; (iii) regular arrows are entirely absent (`von Neumann`/`f ∘ g ∘ f` patterns: zero hits; `Structure/Regular*.v` is regular *categories*, a different concept).

## Work to be done
- In `Theory/Morphisms.v` (extend): `split_pair_idempotent : g ∘ h ≈ id → Idempotent (h ∘ g)`.
- Define `RegularMorphism f := ∃ g, f ∘ g ∘ f ≈ f`; prove an arrow with a left or right inverse is regular.
- The Set statement constructively: prove the decidable witness — in `FinSet`, every arrow with inhabited domain is regular (choice-free by finite search); document that the classical "every epi in Set splits"/"every Set map with nonempty domain is regular" requires choice and is deliberately not assumed (header disclosure; no `Axiom`).

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`; choice-dependent halves disclosed, not axiomatized)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the new lemmas
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Morphisms.v
# Print Assumptions split_pair_idempotent regular_of_section regular_of_retraction finset_regular
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed pp. 19–21 (PDF 29–31).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.5:def5","maclane:I.5:ex7"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.5: Uniqueness of terminal, initial, and zero objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.5:def7, maclane:I.5:def8]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 20 (PDF p. 30)
- Items: `maclane:I.5:def7`, `maclane:I.5:def8`

## Background
Terminal and initial objects admit exactly one arrow from/to every object; any two terminal (resp. initial) objects are isomorphic, the only endo-arrow of a terminal object is the identity, and a null (zero) object — both initial and terminal — is likewise unique up to isomorphism, with zero arrows factoring through it. See https://ncatlab.org/nlab/show/terminal+object and https://ncatlab.org/nlab/show/zero+object.

## Current state in the library
The definitions, duality, and Set examples are exact: `Terminal` (`Structure/Terminal.v:107`), `Initial := Terminal (C^op)` (`Structure/Initial.v:96`, with `zero`/`zero_unique` at :109/:112), `Sets_Terminal`/`Sets_Initial` (`Instance/Sets.v:248/265`), `Coq` counterparts, and `Terminal_Limit` (`Structure/Limit/Terminal.v:33`); the zero-object package with all zero-arrow absorption laws is proven (`Structure/ZeroObject.v:35/53/61/73/85`, concrete witness `CMon_Zero` at `Instance/CMon/Biproduct.v:160`). Verified gap (both items): the uniqueness-up-to-isomorphism statements are nowhere formalized — no lemma relates two `Terminal C` (or `Initial C`, or `ZeroObject C`) structures by an iso; the generic machinery exists (`univ_property_unique_up_to_unique_iso`, `Structure/UniversalProperty.v:175`; `Terminal_Limit`; `LimitIsUniversalProperty`) but the composition is never performed, and `Structure/ZeroObject.v:20–22` asserts the fact only as header prose.

## Work to be done
- In `Structure/Terminal.v` (extend): `terminal_unique : ∀ (T1 T2 : @Terminal C), terminal_obj T1 ≅ terminal_obj T2`, with the refinement that the iso is unique (any two parallel arrows into a terminal object are `≈`).
- The dual `initial_unique` by op-duality, and `zero_object_unique` for `ZeroObject` (using `zero_coincide`).
- Either prove directly (a few lines each) or route through the UniversalProperty machinery — if the latter, write the missing glue between bundled `Limit` and the `IsALimit` predicate noted in the coverage record.
- Replace the `ZeroObject.v` header's rhetorical reliance ("no loss of generality") with a reference to the new lemma.

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the three uniqueness lemmas
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Structure/Terminal.v && coqc -R . Category Structure/ZeroObject.v
# Print Assumptions terminal_unique initial_unique zero_object_unique
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 20 (PDF p. 30) — including uniqueness of the connecting iso.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.5:def7","maclane:I.5:def8"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.5: Groupoids and the structure of connected groupoids"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.5:def9, maclane:I.5:remark1]
deps_item_ids: [maclane:I.2:construction4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 20 (PDF p. 30)
- Items: `maclane:I.5:def9`, `maclane:I.5:remark1`

## Background
A groupoid is a category in which every arrow is invertible. Each object then carries a vertex group `hom(x, x)`, any arrow `f : x → x'` conjugates one vertex group onto another, and a *connected* groupoid is determined up to isomorphism by a single vertex group together with its set of objects. See https://ncatlab.org/nlab/show/groupoid.

## Current state in the library
Verified PARTIAL / ABSENT respectively. The abstract notion is missing: no class or predicate says "every arrow of `C` is invertible" — `Construction/Groupoid.v:103` builds only the CORE of a category (homs = isomorphisms), a canonical example family, and its header states "no standalone category of groupoids exists in-tree"; even the core is never proven to satisfy a groupoid property (there is no property to instantiate). The structure theory of `maclane:I.5:remark1` is entirely absent: no vertex-group construction, no conjugation isos, no connectedness predicate (blind sweeps confirmed).

## Work to be done
- In `Structure/Groupoid.v` (new): `IsGroupoid C := ∀ x y (f : x ~> y), IsIsomorphism f` (donor: `Theory/Isomorphism.v:133`); prove the core `Groupoid C` of `Construction/Groupoid.v` satisfies it.
- Vertex structure: `hom(x, x)` is a group (monoid under composition, inverses from `IsGroupoid`); conjugation by `f : x ~> x'` is a group isomorphism `hom(x,x) ≅ hom(x',x')`.
- `Connected` predicate (any two objects joined by an arrow); the structure theorem: a connected groupoid is equivalent to the delooping `B (hom(x,x))` of any one vertex group (donor: the `maclane:I.2:construction4` delooping) — the precise form of "determined by one group and its set of objects".

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `IsGroupoid`, the vertex-group and conjugation lemmas, and the connectedness theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Structure/Groupoid.v
# Print Assumptions IsGroupoid core_is_groupoid vertex_group conjugation_iso connected_deloop_equiv
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 20 (PDF p. 30).

## Dependencies
Depends on: maclane:I.2:construction4

<!-- catalog: {"ids":["maclane:I.5:def9","maclane:I.5:remark1"],"deps":["maclane:I.2:construction4"]} -->
---8<---
```yaml
title: "MacLane I.5: The fundamental groupoid of a topological space"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.5:construction1]
deps_item_ids: [maclane:I.5:def9, maclane:I.7:construction4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 20 (PDF p. 30)
- Items: `maclane:I.5:construction1`

## Background
The fundamental groupoid `π(X)` of a space has points as objects and endpoint-fixing homotopy classes of paths as arrows; concatenation (well defined on classes) composes them and reversal inverts them. See https://ncatlab.org/nlab/show/fundamental+groupoid.

## Current state in the library
Verified ABSENT. No topology, no paths, no homotopy exist anywhere in-tree ("fundamental group"/π₁ appear only in the background essay of `Construction/Groupoid.v:58–64`; `Instance/` has no Top; `Test/Issue138.v`'s loop is a one-node quiver, unrelated).

## Work to be done
Once `Top` (`maclane:I.7:construction4`) and the groupoid predicate (`maclane:I.5:def9`) land:
- Paths as continuous maps from the unit interval; endpoint-fixing homotopies; the setoid of paths up to homotopy rel endpoints.
- `π(X)` as a category (objects: points; homs: homotopy classes; composition: the standard reparametrized concatenation, well defined on classes) and the proof `IsGroupoid (π X)` (reversal).
- Interval infrastructure: this needs a workable `[0,1]` — stdlib `Reals` (instance layer; any new stdlib axioms must be enumerated in docs/AXIOMS.md) or a documented synthetic/constructive substitute; the file header must state the choice and its cost.

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted` or `admit`; any stdlib axioms confined to the instance layer and enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` run on `π(X)` and the groupoid proof; output matches the AXIOMS.md enumeration
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Top/FundamentalGroupoid.v
# Print Assumptions fundamental_groupoid fundamental_groupoid_is_groupoid
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 20 (PDF p. 30) — concatenation well defined on homotopy classes, all arrows invertible.

## Dependencies
Depends on: maclane:I.5:def9
Depends on: maclane:I.7:construction4

<!-- catalog: {"ids":["maclane:I.5:construction1"],"deps":["maclane:I.5:def9","maclane:I.7:construction4"]} -->
---8<---
```yaml
title: "MacLane I.5: Monic/epi cancellation and a non-invertible bimorphism"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.5:ex1, maclane:I.5:ex3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 21 (PDF p. 31)
- Items: `maclane:I.5:ex1`, `maclane:I.5:ex3`

## Background
Two elementary exercises on the monic/epi calculus: if a composite `g ∘ f` is monic then so is `f` (but not necessarily `g`); and there are categories with arrows that are both epi and monic yet not invertible — non-balanced categories. See https://ncatlab.org/nlab/show/monomorphism and https://ncatlab.org/nlab/show/balanced+category.

## Current state in the library
Verified ABSENT (both). Only the closure direction exists (`monic_compose`/`epi_compose`, `Theory/Morphisms.v:212/201`); an exhaustive enumeration found no `Monic (g ∘ f) → Monic f` (the strong-epi analogue `strong_epi_cancel`, `Structure/Factorization/StrongEpi.v:62`, shows the library knows the pattern). `Bimorphic` is defined (`Theory/Morphisms.v:125`) and never instantiated — no witness of a bimorphic arrow exists at all, let alone a non-invertible one; the positive complements (`Monic_Retraction_Iso`:392, `Epic_Section_Iso`:412, with "the converse fails in general" prose at `Theory/Isomorphism.v:261`) have no exhibited failure.

## Work to be done
- In `Theory/Morphisms.v` (extend): `monic_cancel : Monic (g ∘ f) → Monic f` and the dual `epic_cancel : Epic (g ∘ f) → Epic g` (two-line proofs); a counterexample or remark for the non-cancelling factor.
- A concrete non-invertible bimorphism: e.g. the unique non-identity arrow of the interval category `_2` (`Instance/Two.v:134`) is vacuously monic and epi but has no inverse — prove `Bimorphic` + not `IsIsomorphism`; note the book's suggested dense-subspace example as prose (it needs Top).
- Suggested location for the example: `Instance/Two.v` or a small `Test/Bimorphic.v`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the cancellation lemmas and the counterexample
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Morphisms.v && coqc -R . Category Instance/Two.v
# Print Assumptions monic_cancel epic_cancel two_bimorphic_not_iso
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 21 (PDF p. 31) — exercise 3 asks about both factors; the answer for the second factor must be addressed.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.5:ex1","maclane:I.5:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.5: Epimorphisms of groups are surjective"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.5:ex5]
deps_item_ids: [maclane:I.6:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 21 (PDF p. 31)
- Items: `maclane:I.5:ex5`

## Background
In the category of groups every epimorphism is surjective — unlike in Rng, where `ℤ → ℚ` is epi without being onto. The classical proof embeds the codomain into a permutation group of cosets and produces two maps agreeing on the image. See https://ncatlab.org/nlab/show/epimorphisms+of+groups+are+surjective.

## Current state in the library
Verified ABSENT. No category of groups exists (`Structure/Group.v` is internal group objects; `Instance/Comp.v:382` has a `Group` type but no category and no epi theorem); the only epi/surjective characterization attempt in-tree is the Sets lemma `surjectivity_is_epic`, which is `Abort`ed (`Instance/Sets.v:429–476`); no permutation-group construction of the kind the hint uses exists.

## Work to be done
Once `Grp` lands:
- Subgroup and coset infrastructure (left cosets of the image; a symmetric group on a setoid — permutations as invertible setoid maps).
- The classical argument: given non-surjective `φ : G → H` with image `M`, build two distinct homomorphisms `H → Perm(H/M ⊔ pt)` (or use the index-2 quotient shortcut when applicable) agreeing after `φ` — contradicting `Epic φ`.
- Conclude `Epic φ ↔ surjective φ` in `Grp` (the easy direction from the quotient/coset machinery).
- Suggested module: `Instance/Grp/Epi.v`. This is one of the substantial group-theory exercises; the coset machinery should be shared with the abelianization issue where possible.

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the epi ⟺ surjective theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Grp/Epi.v
# Print Assumptions grp_epic_iff_surjective
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 21 (PDF p. 31).

## Dependencies
Depends on: maclane:I.6:construction2

<!-- catalog: {"ids":["maclane:I.5:ex5"],"deps":["maclane:I.6:construction2"]} -->
---8<---
```yaml
title: "MacLane I.5: The natural numbers as an initial algebra"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.5:ex8]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.5 ("Monics, Epis, and Zeros"), printed p. 21 (PDF p. 31)
- Items: `maclane:I.5:ex8`

## Background
In the category of triples `⟨X, e, t⟩` (a set with a point and an endomap, arrows the maps commuting with both), the triple `(ℕ, 0, successor)` is initial — the natural-numbers-object universal property, i.e. initiality for the endofunctor `X ↦ 1 + X`. See https://ncatlab.org/nlab/show/natural+numbers+object.

## Current state in the library
Verified PARTIAL. The ambient framework is complete — `FAlg` with commuting-square homs, `Initial` — and the endofunctor is formalized (`NatF := option`, `Theory/Adamek/Corollaries.v:87`), with the exactly analogous theorem fully proven one parameter up (`list_initial : @Initial (FAlg (ListF A))`, `Instance/Coq/Lists.v:111`). But the nat case itself is explicitly disclosed as NOT stated: "the initial-algebra theorem [nat ≅ μ NatF] is not stated in the tree" (`Theory/Adamek/Corollaries.v:77–80`).

## Work to be done
- In `Instance/Coq/Nat.v` (new, mirroring `Instance/Coq/Lists.v`): the algebra `(nat, [0, S])` and the theorem `nat_initial : @Initial (FAlg NatF)` — existence of the fold (primitive recursion) and its uniqueness as an algebra map.
- Corollaries: Lambek's iso `nat ≅ option nat` via `Theory/Lambek.v`; update the `Theory/Adamek/Corollaries.v` disclosure to point at the new theorem.
- Optional: the direct triple-category reading (algebras of `NatF` ARE Mac Lane's triples) recorded as a remark or a definitional bridge.

## Definition of Done
- [ ] Statement matches Mac Lane §I.5 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; axiom-free like `Instance/Coq/Lists.v`)
- [ ] `Print Assumptions` closed under the global context for `nat_initial`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Coq/Nat.v
# Print Assumptions nat_initial   — expect: Closed under the global context
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.5, printed p. 21 (PDF p. 31) — initiality (existence AND uniqueness of the mediating map).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.5:ex8"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.6: Size and foundations vocabulary"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.6:def1, maclane:I.6:def2, maclane:I.6:def4, maclane:I.6:def5, maclane:I.6:def6, maclane:I.6:remark1, maclane:I.6:remark2, maclane:I.6:remark3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.6 ("Foundations"), printed pp. 22–24 (PDF pp. 32–34)
- Items: `maclane:I.6:def1`, `maclane:I.6:def2`, `maclane:I.6:def4`, `maclane:I.6:def5`, `maclane:I.6:def6`, `maclane:I.6:remark1`, `maclane:I.6:remark2`, `maclane:I.6:remark3`

## Background
Mac Lane's foundations section fixes ZFC plus one universe `U`, defines small sets/functions/categories as those within `U`, classes as subsets of `U`, and large categories over classes, observing that Set is not small; he closes by pointing to set-free first-order alternatives (category axioms on undefined terms; elementary topos axioms for Set). See https://ncatlab.org/nlab/show/Grothendieck+universe.

## Current state in the library
All eight items verified PARTIAL with one shared shape: the *role* of the universe/smallness/class apparatus is fully played by Coq's cumulative universe hierarchy with universe polymorphism — `Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)}` (`Theory/Category.v:111`, header :22), the size essays (`Instance/Cat.v:22–27, 108–114`; `Theory/Metacategory.v:116–118`; `Structure/Complete.v:30`), `Sets@{o so}` stratification (`Instance/Sets.v:188`), and the audited zero-axiom regime (docs/AXIOMS.md) — but no in-tree *vocabulary* reifies it: no universe object with closure conditions, no smallness predicate, no class/proper-class terms, no "large category" definition, and the non-smallness facts are typing-enforced prose, not theorems. The remark-3 pointers are the exception: both first-order alternatives are actually formalized (`Theory/Metacategory.v` arrows-only axioms; `ElementaryTopos`, `Structure/Topos.v:112`, inhabited by `FinSet_Topos`).

## Work to be done
This issue proposes the honest, bounded reification — documentation-first, no membership-based set theory:
- A `docs/SIZE.md` mapping Mac Lane's I.6 vocabulary (universe, small set/function/category, class, proper class, large category, one-universe limits, Grothendieck's axiom) onto the library's universe-polymorphism discipline, with pointers to the size essays and to docs/AXIOMS.md (the remark-2 content), and to `Theory/Metacategory.v`/`Structure/Topos.v` for the remark-3 alternatives.
- A small `Test/Size.v` of machine-checked demonstrations: `Fail Check` witnesses that self-application (`Sets` as an object of itself, `Cat` as an object of itself) is a universe inconsistency — the formal counterpart of remark 1 — plus positive checks that `Sets`/`Cat` at one level are objects of the next level's instances (the Cls/Cat′ pattern already exercised by `Instance/Sets/Classifier.v`).
- Where a light predicate is genuinely useful (e.g. a bundled "category with objects and homs below a given level" record for stating smallness hypotheses), add it; otherwise document why reification stops there.

## Definition of Done
- [ ] The mapping covers every I.6 item listed above, faithfully paraphrased (no book text)
- [ ] `Test/Size.v` compiles with the `Fail` demonstrations passing; no `Admitted`, `admit`, or new `Axiom`
- [ ] `Print Assumptions` closed for any new formal artifacts
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Test/Size.v
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.6, printed pp. 22–24 (PDF 32–34) — every item mapped or explicitly noted as replaced by the type-theoretic foundation.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.6:def1","maclane:I.6:def2","maclane:I.6:def4","maclane:I.6:def5","maclane:I.6:def6","maclane:I.6:remark1","maclane:I.6:remark2","maclane:I.6:remark3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.6: Small completeness of Sets (indexed products and coproducts)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:I.6:ex1, maclane:I.6:ex2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.6 ("Foundations"), printed p. 24 (PDF p. 34)
- Items: `maclane:I.6:ex1`, `maclane:I.6:ex2`

## Background
The two exercises show a universe is closed under small cartesian products and small unions — the set-theoretic facts behind "Set is small-complete and small-cocomplete". Their faithful categorical transposition in this library: `Sets` at level `o` has products and coproducts of families indexed by any type at level `o`. See https://ncatlab.org/nlab/show/complete+category.

## Current state in the library
Verified ABSENT (both). `HasIndexedProducts` is vocabulary-only (`Structure/Limit/Product.v:128`; zero instances tree-wide, with the deliberate-refusal note at `Theory/WeaklyInitial.v:44`); `HasIndexedCoproducts` does not even exist as vocabulary (zero hits); `Complete`/`Cocomplete` (`Structure/Complete.v:115/121`) are only ever consumed as hypotheses (GAFT, SAFT, Adámek) and never instantiated at any concrete category; `Instance/Sets.v:109` confirms Sets' completeness exists only "piecewise" (binary products/exponentials/pushouts).

## Work to be done
- `HasIndexedProducts Sets`: dependent-function setoids `∀ i, F i` with pointwise `≈` (funext-free by the setoid discipline), projections and the tupling UMP (`iprod`/`iprod_proj`/`iprod_ump` fields).
- Define `HasIndexedCoproducts` (dualize `Structure/Limit/Product.v` over discrete diagrams) and instantiate at `Sets`: sigma setoids with the injection/copairing UMP.
- Mind the universe discipline: the index type lives at the object level `o` of `Sets@{o so}` — this is exactly the "small family" side condition; document it in the header.
- Stretch (record if deferred): `Complete Sets` via indexed products + equalizers, feeding the GAFT/SAFT hypotheses with their first concrete witness.

## Definition of Done
- [ ] Statement matches Mac Lane §I.6 in substance (the categorical transposition documented; setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both instances
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Sets/Products.v
# Print Assumptions Sets_HasIndexedProducts Sets_HasIndexedCoproducts
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.6, printed p. 24 (PDF p. 34) — the smallness side condition must be the index type's universe level.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.6:ex1","maclane:I.6:ex2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.6: Grp, the category of groups"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.6:construction2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.6 ("Foundations"), printed p. 22 (PDF p. 32)
- Items: `maclane:I.6:construction2`

## Background
All small groups with all homomorphisms form the category Grp — the archetype of the "category of all small structures of a given type" process that also yields Cat, Mon, Top, and the rest of Mac Lane's roster. See https://ncatlab.org/nlab/show/Grp and https://en.wikipedia.org/wiki/Category_of_groups.

## Current state in the library
Verified PARTIAL. The "same process" is repeatedly witnessed — `CMon` (`Instance/CMon.v:140`, commutative monoids over `Sets` with `CMon_Forget` at :169) and `Cat` (`Instance/Cat.v:142`) — but Grp itself does not exist: `Structure/Group.v:109` (`GroupObject`) is never assembled into a category; `Instance/Comp.v` has the elementwise `Group := Algebra GroupOp GroupEq` (:382) and even a category `Algs` (:151), but `Algs` is over algebras *without* equations, so the category of groups is still never formed (verifier-confirmed). This is the single most-depended-on gap in Chapter I: the center, abelianization, conjugacy, product-functor, and epi exercises all need it.

## Work to be done
- In `Instance/Grp.v` (new, mirroring `Instance/CMon.v`): group objects over `Sets` — setoid carrier, unit, multiplication, inverse, laws up to `≈`; homomorphisms preserving unit and multiplication (inverse preservation derived); the hom-setoid; the category `Grp`.
- The faithful forgetful functor `Grp ⟶ Sets` (faithful by construction, as with `CMon_Forget`).
- Basic API for downstream issues: the one-element group as zero object (both initial and terminal — the book's I.5 example), binary direct products (Cartesian structure), monic ⟺ injective.
- Reconcile with `Structure/Group.v`: show a `Grp` object is a `GroupObject` in `Sets` (or refactor to instantiate it), so the internal and concrete presentations agree.

## Definition of Done
- [ ] Statement matches Mac Lane §I.6 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Grp`, the forgetful functor, and the zero object
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level instance)

## Verification
```
coqc -R . Category Instance/Grp.v
# Print Assumptions Grp Grp_Forget Grp_Zero
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.6, printed p. 22 (PDF p. 32) — all groups at the universe level, ALL homomorphisms.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.6:construction2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.7: Ab, the category of abelian groups"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction1, maclane:I.7:prop1]
deps_item_ids: [maclane:I.6:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed pp. 24–25 (PDF pp. 34–35)
- Items: `maclane:I.7:construction1`, `maclane:I.7:prop1`

## Background
Ab is the category of small additive abelian groups and homomorphisms; the zero group is a null object, and — the section's proposition — monics in Ab are exactly the injections and epis exactly the surjections, the latter proved by the quotient `B/fA`. See https://ncatlab.org/nlab/show/Ab and https://en.wikipedia.org/wiki/Category_of_abelian_groups.

## Current state in the library
Verified PARTIAL / ABSENT respectively. The inverse-free shadow is fully built: `CMon` (`Instance/CMon.v:140`) with the trivial monoid as `ZeroObject` (`CMon_Zero`, `Instance/CMon/Biproduct.v:160`) and the whole semiadditive/biproduct development; but no category of abelian groups exists (zero hits for an `Ab` category; `Structure/Abelian.v` is abelian *categories*), additive inverses are nowhere in the concrete layer, and the monic/epi proposition has no counterpart — the near-misses (`injectivity_is_monic`, `Instance/Sets.v:369`; the `Abort`ed `surjectivity_is_epic`) are Sets facts, and no quotient-group machinery exists (`Structure/Kernel.v` is abstract).

## Work to be done
- In `Instance/Ab.v` (new): abelian group objects over `Sets` (CMon structure + inverse), homomorphisms, the category `Ab`; the zero group as `ZeroObject` (mirroring `CMon_Zero`).
- The proposition (`maclane:I.7:prop1`): monic ⟺ injective (both directions; probe on a suitable one-generator object), and epi ⟺ surjective — the substantive direction by the book's own argument: the setoid quotient `B/fA` (cosets of the image; no choice needed over setoids) with the projection and the zero map as the two distinguishing arrows.
- Wire-up for later chapters: `Ab` as a `Preadditive` instance (hom-groups; donor `Structure/Preadditive.v`), the forgetful `Ab ⟶ Grp` and `Ab ⟶ Sets`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Ab`, `Ab_Zero`, and both characterizations
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level instance)

## Verification
```
coqc -R . Category Instance/Ab.v
# Print Assumptions Ab Ab_Zero ab_monic_iff_injective ab_epic_iff_surjective
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed pp. 24–25 (PDF 34–35) — the epi proof must go through the quotient `B/fA`, or an equivalent honest argument.

## Dependencies
Depends on: maclane:I.6:construction2

<!-- catalog: {"ids":["maclane:I.7:construction1","maclane:I.7:prop1"],"deps":["maclane:I.6:construction2"]} -->
---8<---
```yaml
title: "MacLane I.7: Rng, the category of rings"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:def1, maclane:I.7:construction2, maclane:I.5:ex4]
deps_item_ids: [maclane:I.7:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Sections: I.7 ("Large Categories"), printed p. 25 (PDF p. 35); I.5 ("Monics, Epis, and Zeros") exercise 4, printed p. 21 (PDF p. 31)
- Items: `maclane:I.7:def1`, `maclane:I.7:construction2`, `maclane:I.5:ex4`

## Background
Rng has all small unital rings as objects and unit-preserving ring homomorphisms as arrows; the zero ring is terminal, ℤ is initial, monics are the injections, every surjection is epi — and the inclusion ℤ → ℚ is epi without being surjective, the standard witness that epis need not be onto. See https://ncatlab.org/nlab/show/Ring and https://en.wikipedia.org/wiki/Category_of_rings.

## Current state in the library
Verified ABSENT (all three items). Ring/Rng/CRng/RingObject/semiring: prose-only hits (`Structure/Abelian.v:111`, `Theory/Algebra.v:25–26` on categorified rigs, `Construction/Localization.v:59–66` historical motivation); the internal-algebra layer stops at monoid/comonoid/group/Frobenius objects — no two-operation structure exists in-tree, internal or concrete; consequently none of the sub-claims (ℤ initial, zero ring terminal, ℤ → ℚ epi) is statable.

## Work to be done
- In `Instance/Rng.v` (new): rings over setoid carriers — an additive abelian group (donor: the `Ab` layer from `maclane:I.7:construction1`) plus a multiplicative monoid with two-sided distributivity; unit-preserving homomorphisms; the category `Rng`; the full subcategory `CRng` of commutative rings (needed downstream by `Matr`/GL_n).
- Initial/terminal: the zero ring terminal; `ℤ` (stdlib `BinInt` under setoid equality) initial — the unique arrow determined by the unit.
- Monics are exactly the injections; every surjective hom is epi.
- `maclane:I.5:ex4`: `ℤ → ℚ` (stdlib `QArith`) is epi in `Rng` although not surjective — via the standard argument that a ring map out of ℚ is determined by its values on ℤ.
- The forgetful functors `Rng ⟶ Ab` (additive part) and `Rng ⟶ Sets`.

## Definition of Done
- [ ] Statement matches Mac Lane §§I.5, I.7 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; any stdlib axioms enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed (or documented) for `Rng`, `CRng`, the initial/terminal witnesses, and the ℤ → ℚ theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level instance)

## Verification
```
coqc -R . Category Instance/Rng.v
# Print Assumptions Rng CRng Rng_Initial_Z Rng_Terminal_zero ZtoQ_epi_not_surjective
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 25 (PDF p. 35) — homs must preserve the multiplicative unit; the ℤ → ℚ epi claim proven, not asserted.

## Dependencies
Depends on: maclane:I.7:construction1

<!-- catalog: {"ids":["maclane:I.7:def1","maclane:I.7:construction2","maclane:I.5:ex4"],"deps":["maclane:I.7:construction1"]} -->
---8<---
```yaml
title: "MacLane I.7: Module categories R-Mod and friends"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction3]
deps_item_ids: [maclane:I.7:construction1, maclane:I.7:construction2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed p. 25 (PDF p. 35)
- Items: `maclane:I.7:construction3`

## Background
For a ring `R`, R-Mod has all small left R-modules and R-linear maps, with monics the injections, epis the surjections, and the zero module a null object; Mod-R gives right modules, R-Mod-S bimodules, and for a field `F`, F-Mod = Vct_F is the category of vector spaces. See https://ncatlab.org/nlab/show/Mod.

## Current state in the library
Verified ABSENT. Module/vector-space/linear-map hits are background essays only (`Structure/Abelian.v:68–111` names Ab/R-Mod as motivation; `Theory/DoubleCategory.v:104`, `Theory/Profunctor.v` bimodule analogies); no ring exists to index modules over (see the Rng issue); `Instance/CMon.v` was inspected and rejected as not-this-item; `Structure/Abelian.v` axiomatizes abelian categories parametrically but constructs no module-category instance.

## Work to be done
Once `Ab` and `Rng` land:
- In `Instance/Mod.v` (new): left `R`-modules over setoid carriers (abelian group + `R`-action, laws up to `≈`), `R`-linear maps, the category `R-Mod`; zero module as `ZeroObject`.
- Monic ⟺ injective and epi ⟺ surjective (reuse the quotient technique from the `Ab` issue).
- Variants: `Mod-R` as `R^op`-modules (opposite ring), bimodules `R-Mod-S`, and the notation `Vct_F` for `F-Mod` (fields as a class over `CRng` — deliver the class here or in the FdVect issue, coordinated).
- Preadditive structure on hom-sets (pointwise addition), wiring into `Structure/Preadditive.v`.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `R-Mod`, its zero object, and the monic/epi characterizations
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level instance)

## Verification
```
coqc -R . Category Instance/Mod.v
# Print Assumptions RMod RMod_Zero rmod_monic_iff rmod_epic_iff
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 25 (PDF p. 35) — bimodule compatibility law `r(as) = (ra)s` included.

## Dependencies
Depends on: maclane:I.7:construction1
Depends on: maclane:I.7:construction2

<!-- catalog: {"ids":["maclane:I.7:construction3"],"deps":["maclane:I.7:construction1","maclane:I.7:construction2"]} -->
---8<---
```yaml
title: "MacLane I.7: Top, the category of topological spaces"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed p. 25 (PDF p. 35)
- Items: `maclane:I.7:construction4`

## Background
Top has all small topological spaces and continuous maps; its monics are the injections and epis the surjections, the one-point space is terminal and the empty space initial; Hausdorff and compact Hausdorff variants restrict the objects. See https://ncatlab.org/nlab/show/Top and https://en.wikipedia.org/wiki/Category_of_topological_spaces.

## Current state in the library
Verified ABSENT. Nothing in-tree defines topological spaces, continuity, or open sets; every "continuous" hit is the limit-preservation sense (`Adjunction/Continuity.v:24`, `Structure/Limit/Preservation.v:15`), and Top is named only in comments (`Structure/Complete.v:55`, `Structure/Group.v:46`).

## Work to be done
- In `Instance/Top.v` (new): topological spaces — a carrier type/setoid with an open-set predicate family closed under arbitrary unions and finite intersections (predicate-lattice presentation, funext-free under the setoid discipline); continuous maps (preimages of opens are open); the category `Top`.
- Terminal (one-point) and initial (empty) spaces; monic ⟺ injective; epi ⟺ surjective (the epi direction via the two-point indiscrete-space probe — check its constructive status and document).
- Full subcategories of Hausdorff and compact Hausdorff spaces as `Subcategory` instances (definitions only; their deeper theory is out of scope here).
- Universe placement: the opens live one level up from points, mirroring the powerset-functor discipline; document.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping; any stdlib axioms enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed (or documented) for `Top`, its terminal/initial objects, and the monic/epi characterizations
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level instance)

## Verification
```
coqc -R . Category Instance/Top.v
# Print Assumptions Top Top_Terminal Top_Initial top_monic_iff top_epic_iff
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 25 (PDF p. 35).

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.7:construction4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.7: Homotopy categories and pointed spaces"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction5, maclane:I.7:construction7]
deps_item_ids: [maclane:I.7:construction4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed pp. 25–26 (PDF pp. 35–36)
- Items: `maclane:I.7:construction5`, `maclane:I.7:construction7`

## Background
Toph keeps the spaces but takes homotopy classes of maps as arrows — a category whose arrows are not functions (the homotopy class of an injection need not be monic); Top* and Toph* are the pointed variants, with basepoint-preserving maps and based homotopies, the home of fundamental and higher homotopy groups. See https://ncatlab.org/nlab/show/homotopy+category and https://en.wikipedia.org/wiki/Pointed_space.

## Current state in the library
Verified ABSENT (both items). "Homotopy" appears only in prose (`Instance/Cat.v:31` and `Instance/StrictCat.v:36` call the weak `Cat` "Ho(Cat)" by analogy; `Structure/Factorization.v:102–104` cites Quillen); no category with homotopy-class hom-sets is constructed; Top itself is absent (blocking); pointed sets occur only via the `Par` realization, pointed *spaces* nowhere ("wedge sum" is one prose hit, `Structure/Cocartesian.v:69`).

## Work to be done
Once `Top` lands:
- Homotopy of continuous maps (via an interval object — coordinate with the fundamental-groupoid issue's `[0,1]` infrastructure choice); homotopy is a congruence for composition; `Toph` as the quotient category (hom-setoids: maps under the homotopy equivalence — the setoid discipline makes this a re-equipping of homs, no quotient types needed).
- `Top_*`: pointed spaces and basepoint-preserving continuous maps; `Toph_*`: same objects with based-homotopy classes.
- The "arrows are not functions" moral stands definitionally in `Toph`; the book's specific non-monic example (the bounding circle of a disc) requires genuine algebraic topology — record it as a disclosed stretch goal, not part of this issue's Definition of Done.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`; the circle example explicitly disclosed as deferred)
- [ ] No `Admitted`, `admit`, or new `Axiom` (any stdlib axioms confined to the instance layer and enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` run on `Toph`, `Top_*`, `Toph_*`; output matches the AXIOMS.md enumeration
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Top/Homotopy.v
# Print Assumptions Toph Top_pointed Toph_pointed
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed pp. 25–26 (PDF 35–36) — based homotopies must themselves preserve the basepoint.

## Dependencies
Depends on: maclane:I.7:construction4

<!-- catalog: {"ids":["maclane:I.7:construction5","maclane:I.7:construction7"],"deps":["maclane:I.7:construction4"]} -->
---8<---
```yaml
title: "MacLane I.7: Set_*, the category of pointed sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction6, maclane:I.7:prop2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed p. 26 (PDF p. 36)
- Items: `maclane:I.7:construction6`, `maclane:I.7:prop2`

## Background
Set_* has pointed sets and basepoint-preserving functions, with the one-point set a null object; in it, monic ⟺ has a left inverse, epi ⟺ has a right inverse, and invertible ⟺ monic and epi. See https://ncatlab.org/nlab/show/pointed+set.

## Current state in the library
Verified PARTIAL / ABSENT respectively. The equivalent partial-map presentation exists: `Par` (`Instance/Coq/Par.v:53`, `hom A B := A → option B`), whose header states it is "equivalent (not isomorphic) to the category of pointed sets" (lines 34–36) — but that equivalence is documentation, not a theorem, since no pointed-set category exists to compare against; `False` is proven both terminal (:213) and initial (:229) in `Par` (the transported null object); setoid variant `Part` (`Instance/Sets/Par.v:27`). The characterization proposition has no counterpart anywhere: no Monic/Epic lemmas in any partial-map file, and the generic easy halves (`sections_are_monic`, `retractions_are_epic`) are I.5 content, not the Set_*-specific converses.

## Work to be done
- In `Instance/Sets/Pointed.v` (new): the literal category `Set_*` — pointed setoids (carrier + basepoint) and point-preserving setoid maps; the one-point set as `ZeroObject`.
- The equivalence `Set_* ≃ Par` (or `Part`), upgrading the header claim to a theorem (`EquivalenceOfCategories`).
- The proposition (`maclane:I.7:prop2`): monic ⟺ split monic, epi ⟺ split epi, invertible ⟺ monic ∧ epi. Constructive care: the converse directions build retractions/sections by case analysis on membership in the image — develop over a decidability assumption where unavoidable (documented), with the unconditional decidable witness (finite pointed sets) provided; the classical statement disclosed in the header.
- Cross-link the roster issue and the I.5 zero-object example.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`; any decidability hypotheses disclosed)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the category, the zero object, the equivalence, and the characterizations
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Sets/Pointed.v
# Print Assumptions PointedSets PointedSets_Zero pointed_par_equivalence pointed_monic_iff_split
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 26 (PDF p. 36) — all three iffs of the proposition.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.7:construction6","maclane:I.7:prop2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.7: Rel, converse relations, and the graph embedding"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:construction8]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed p. 26 (PDF p. 36)
- Items: `maclane:I.7:construction8`

## Background
Rel has sets as objects and binary relations as arrows, composed by the relative product with diagonal identities; Set embeds into it by taking graphs of functions, and Rel carries the extra involutive structure of the converse relation `R†`. See https://ncatlab.org/nlab/show/Rel and https://ncatlab.org/nlab/show/dagger+category.

## Current state in the library
Verified PARTIAL. The bare category is built axiom-free (`Rel`, `Instance/Rel.v:45` — relative-product composition, `Singleton` identities) with the graph embedding `Relation_Functor : Coq ⟶ Rel` (:167). Gaps, per the file's own header (lines 36–43, "None of that extra structure is built here"): the converse/dagger operation `R†` is not formalized anywhere in-tree (dagger/converse: prose-only hits), and the faithfulness of the graph embedding — the substance of "Set is a (wide) subcategory of Rel" — is asserted only in the comment at lines 163–165, with no `Faithful` instance; the cartesian/closed instances in the file are inside a comment block, and only the initial half of the zero object is recorded (lines 84–88).

## Work to be done
- In `Instance/Rel.v` (extend) or `Instance/Rel/Dagger.v` (new): the converse `R†` with the involution laws `(R†)† ≈ R` and `(S ∘ R)† ≈ R† ∘ S†`, and identity preservation — packaged either ad hoc or as the first instance of a light `DaggerCategory` class (design choice documented; a general class serves ZX/CompactClosed prose already citing daggers).
- `Faithful Relation_Functor` (functions with equal graphs are equal pointwise).
- Optionally complete the zero-object story (the empty set as terminal in `Rel` via the empty relation) noted missing in the header.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the dagger laws and the faithfulness instance
- [ ] New files registered in `_CoqProject` (if any)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Instance/Rel.v
# Print Assumptions rel_converse_involution rel_converse_compose Relation_Functor_Faithful
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 26 (PDF p. 36) — the converse must be an anti-homomorphism for composition.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.7:construction8"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.7: Concrete categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.7:def2, maclane:I.7:remark1]
deps_item_ids: [maclane:I.7:construction5]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.7 ("Large Categories"), printed p. 26 (PDF p. 36)
- Items: `maclane:I.7:def2`, `maclane:I.7:remark1`

## Background
A concrete category is a pair `⟨C, U⟩` with `U : C → Set` faithful — every object has an underlying set and every arrow is an actual function. Mac Lane remarks that most of the section's categories are concrete relative to their evident forgetful functor, but Toph and Rel are not (for Toph this is Freyd's celebrated theorem "homotopy is not concrete"). See https://ncatlab.org/nlab/show/concrete+category and https://en.wikipedia.org/wiki/Concrete_category.

## Current state in the library
Verified PARTIAL / ABSENT respectively. Every ingredient exists unbundled — `Faithful` (`Theory/Functor.v:342`), the base `Sets` (`Instance/Sets.v:188`), and worked faithful functors (`Mon_Forget_Faithful`, `Theory/Algebra/Monoid/Hom.v:101`; `ev1_Faithful` into `Sets`, `Theory/Lawvere/Sets.v:105`; `CMon_Forget`) — but no `ConcreteCategory` definition bundles a category with a chosen faithful functor to `Sets` ("concrete" in-tree is only the ordinary English word in ~30 comments), and nothing about (non-)concretizability exists.

## Work to be done
- In `Theory/Concrete.v` (new): `Class Concrete (C : Category) := { underlying : C ⟶ Sets; underlying_faithful : Faithful underlying }`, with the "arrows are actual functions" reading recorded as the definitional unfolding.
- Positive instances for the in-tree roster: `Sets` (identity), `Coq` (via its Sets embedding or directly), `CMon` (via `CMon_Forget`), and the algebraic categories as they land (soft cross-references, not dependencies).
- The negative half of `maclane:I.7:remark1`: state precisely what fails for `Rel` relative to its evident candidate functors; the Toph non-concreteness (Freyd 1970) is research-scale and is explicitly OUT of this issue's Definition of Done — record both negative claims in the file header as disclosed deferrals, with the Toph statement becoming stateable once `maclane:I.7:construction5` lands.

## Definition of Done
- [ ] Statement matches Mac Lane §I.7 in substance (setoid discipline: `≈` on morphisms, never `=`; the deferred negative halves disclosed in the header)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Concrete` and each instance
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Theory/Concrete.v
# Print Assumptions Concrete Sets_Concrete CMon_Concrete
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.7, printed p. 26 (PDF p. 36); confirm the Freyd deferral is honestly disclosed rather than silently dropped.

## Dependencies
Depends on: maclane:I.7:construction5

<!-- catalog: {"ids":["maclane:I.7:def2","maclane:I.7:remark1"],"deps":["maclane:I.7:construction5"]} -->
---8<---
```yaml
title: "MacLane I.8: Ab-categories and additive functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.8:def4, maclane:I.8:def6, maclane:I.8:construction1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.8 ("Hom-Sets"), printed pp. 28–29 (PDF pp. 38–39)
- Items: `maclane:I.8:def4`, `maclane:I.8:def6`, `maclane:I.8:construction1`

## Background
An Ab-category (preadditive category) has abelian-group hom-sets with bilinear composition; a functor between Ab-categories is additive when its hom-actions are group homomorphisms, additive functors compose, and small Ab-categories with additive functors form the category Ab-cat. See https://ncatlab.org/nlab/show/Ab-enriched+category and https://ncatlab.org/nlab/show/additive+functor.

## Current state in the library
Verified PARTIAL / PARTIAL / ABSENT. Neither existing class matches Mac Lane's notion exactly: `Preadditive` (`Structure/Preadditive.v:34`) is deliberately commutative-MONOID enrichment ("Additive inverses are deliberately not demanded", header :20), while `Additive` (`Structure/Additive.v:34`) has the group homs but *bundles* a zero object and chosen biproducts, which an Ab-category need not have; the exact intermediate (Preadditive + negation, nothing more) is absent. Additive functors do not exist in any form: zero hits for the notion, for `fmap`-`padd` preservation, and `padd` appears in no functor file. No category of Ab-categories exists (`Ab-cat`/`AbCat`: zero hits; `Construction/Enriched/Fun.v` is only the functor category between two *fixed* enriched categories).

## Work to be done
- In `Structure/Preadditive.v` (extend) or `Structure/AbCategory.v` (new): the exact class — `AbEnriched := Preadditive + pneg + padd_pneg` with bilinearity for negation derived; instances: every `Additive` category, and `CMon`-style witnesses as available.
- `AdditiveFunctor`: a `Functor` whose hom-actions preserve `padd` (and hence `pzero`, `pneg`); closure under composition; identity functor additive.
- `AbCat`: the category of small Ab-categories with additive functors (universe-polymorphic, mirroring `Cat`'s size discipline; functor setoid inherited from `Cat`/`StrictCat`, choice documented).
- Cross-link: the Enriched-at-Ab reading is the `maclane:I.8:def5` issue; keep this one self-contained over the direct classes.

## Definition of Done
- [ ] Statement matches Mac Lane §I.8 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the class, additive functors, composition closure, and `AbCat`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```
coqc -R . Category Structure/AbCategory.v
# Print Assumptions AbEnriched AdditiveFunctor AdditiveFunctor_Compose AbCat
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.8, printed pp. 28–29 (PDF 38–39) — the class must NOT require a zero object or biproducts; bilinearity exactly as stated.

## Dependencies
None

<!-- catalog: {"ids":["maclane:I.8:def4","maclane:I.8:def6","maclane:I.8:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane I.8: The tensor product of abelian groups and Ab-enrichment"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:I.8:def5]
deps_item_ids: [maclane:I.7:construction1, maclane:I.8:def4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: I.8 ("Hom-Sets"), printed pp. 28–29 (PDF pp. 38–39)
- Items: `maclane:I.8:def5`

## Background
Because composition in an Ab-category is bilinear, it factors through the tensor product of abelian groups, so an Ab-category can be presented purely by tensor data: hom-groups, composition morphisms `A(b,c) ⊗ A(a,b) → A(a,c)`, and units `ℤ → A(a,a)` — the template that Kelly's enriched category theory generalizes to any monoidal base. See https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups.

## Current state in the library
Verified PARTIAL. The parametric shape is fully present: `Class Enriched (K) \`{@Monoidal K}` (`Construction/Enriched.v:111`) has exactly the fields (i)–(iv) of Mac Lane's tensor-data definition over an arbitrary monoidal base, and the header (:28) notes that K = Ab gives preadditive categories. But the item's specific content — the base `(Ab, ⊗_ℤ, ℤ)` — cannot even be instantiated: no category of abelian groups exists, and no tensor-product monoidal structure on abelian groups (or commutative monoids) is constructed anywhere; the correspondence between Enriched-at-Ab and the direct Preadditive/Additive classes is prose only.

## Work to be done
Once `Ab` and the Ab-category class land:
- In `Instance/Ab/Tensor.v` (new): the tensor product `G ⊗ H` as a setoid quotient of formal sums over `G × H` by bilinearity (free-abelian-group-on-a-setoid machinery, kept reusable); the universal bilinear map and the UMP.
- The monoidal structure `(Ab, ⊗, ℤ)`: bifunctoriality, unitors, associator, coherence (donor: `Structure/Monoidal.v`).
- Instantiate `Enriched Ab` and prove the correspondence with the direct `AbEnriched` class of the `maclane:I.8:def4` issue (both directions — the precise content of Mac Lane's "can be described completely in these terms").

## Definition of Done
- [ ] Statement matches Mac Lane §I.8 in substance (setoid discipline: `≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `⊗`, the monoidal instance, and the correspondence theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship-level structure)

## Verification
```
coqc -R . Category Instance/Ab/Tensor.v
# Print Assumptions AbTensor Ab_Monoidal Enriched_Ab_iff_AbEnriched
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
Reviewer: statement fidelity against Mac Lane §I.8, printed pp. 28–29 (PDF 38–39) — tensor over ℤ, unit picked out by `ℤ → A(a,a)`.

## Dependencies
Depends on: maclane:I.7:construction1
Depends on: maclane:I.8:def4

<!-- catalog: {"ids":["maclane:I.8:def5"],"deps":["maclane:I.7:construction1","maclane:I.8:def4"]} -->

title: "Awodey 5.1: The subobject preorder Sub_C(X) as a category, and its poset quotient"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.1:def1, awodey:5.1:remark4]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.1 "Subobjects", Definition 5.1 and Remark 5.4, printed pages 94–96 (PDF pages 103–105). Items covered: `awodey:5.1:def1`, `awodey:5.1:remark4`.

## Background

A subobject of an object is a monomorphism into it; morphisms of subobjects are the arrows of the slice category over that object, and because the target mono cancels there is at most one such arrow, so the subobjects of a fixed object form a *preordered* category whose quotient by mutual inclusion is a poset. See [nLab: subobject](https://ncatlab.org/nlab/show/subobject) and [Wikipedia: Subobject](https://en.wikipedia.org/wiki/Subobject).

## Current state in the library

Every ingredient of the definition is in-tree; what is missing is that the preorder is never assembled as a categorical object.

- `Theory/Subobject.v:15` — `SubObj x`, the record bundling `sub_dom`, `sub_mono : sub_dom ~> x` and `sub_is_monic : Monic sub_mono`.
- `Theory/Subobject.v:59` — `sub_le u v := { k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈ sub_mono u }`, the inclusion relation, with `sub_le_refl` (`:62`) and `sub_le_trans` (`:67`).
- `Theory/Subobject.v:78` — `sub_le_unique`: any two mediators are `≈` (the thinness fact, stated as a lemma about arrows, never as "the hom-type is a subsingleton").
- `Theory/Subobject.v:33` — `SubObj_Setoid`, whose `≈` is exactly mutual factorization (`sub_equiv_iff_mutual`, `:93`), so the *quotient* reading of Remark 5.4 is the library default.

The gaps: there is no `Category` (nor `Instance/Proset.v:33` `Proset`) instance whose homs are `sub_le`, so "Sub_C(X) is a preorder category" is a collection of lemmas rather than a construction; `sub_le` is `Type`-valued (a sigma carrying the mediator) and so cannot be fed to `Proset`, whose `R : relation A` is `Prop`-valued; the identification of subobject morphisms with arrows of `Construction/Slice.v:123` (`Slice C x`) is absent — there is no `Monic`-cut full subcategory of the slice anywhere (`rg -c -i 'monic|mono' Construction/Slice.v` → 0 hits); and no order structure is put on the quotient (`sub_le` is never descended to `SubObj_Setoid`-classes, and no antisymmetry-up-to-`≈` statement is made). `Theory/Subobject/Functor.v:180`'s `Sub : C^op ⟶ Sets` lands in setoids, so the order is discarded at the functor level.

Remark 5.4's second half — `Sub_Sets(X) ≅ P(X)` — is out of reach for the library's `Sets`: `Instance/Sets/Classifier.v:29-45` documents the universe obstruction (the truth-value setoid provably lives one level up), there is no `SubobjectClassifier Sets` and no powerset object of a setoid; the concrete witness in-tree is skeletal `FinSet` (`Instance/FinSet/Topos.v`). The `Sets`-side statement is the subject of the already-filed #402 (and the powerset carrier of #382); this issue delivers the general poset-quotient half only.

## Work to be done

Suggested module: `Theory/Subobject/Category.v`.

1. Build `SubCat x : Category` with objects `SubObj x` and homs the factorization witnesses, and prove thinness in the categorical form: any two parallel arrows are `≈` (upgrading `sub_le_unique` from a lemma about mediators to a property of the hom-setoid). Disclose in the header whether the hom-setoid is the `Type`-valued sigma with the trivial setoid, or a truncated `Prop`-valued shadow usable with `Instance/Proset.v` — the second makes `Proset`/`Poset` reuse possible, the first keeps the mediator accessible.
2. Prove the slice identification: a functor `SubCat x ⟶ Slice C x` that is fully faithful and injective on objects, exhibiting `Sub_C(X)` as the full subcategory of the slice cut out by `Monic` — the presentation Awodey takes as the definition.
3. Deliver the poset quotient of Remark 5.4: `sub_le` respects `SubObj_Setoid` in both arguments, and antisymmetry up to `≈` (`sub_le u v → sub_le v u → u ≈ v`, immediate from `sub_equiv_iff_mutual`), so the classes carry a genuine partial order. Package it so downstream order-theoretic work (the subobject lattice, intersections/unions) has a carrier.
4. Record in the header that the `Sets`-specific identification with the powerset is not delivered here and why (the cross-universe obstruction), pointing at the filed classifier issue.

In-tree donors: `Theory/Subobject.v`, `Construction/Slice.v`, `Instance/Proset.v`, `Instance/Poset.v`, `Theory/Subobject/Functor.v`, `Theory/Morphisms.v` (`monic_compose`, and the `monic_cancel` lemma filed as #250, which is what justifies calling a subobject morphism itself monic).

## Definition of Done

- [ ] Statement fidelity to the book (§5.1, printed pp. 94–96 (PDF pp. 103–105)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `Sub_C(X)` is a `Category` whose homs are the inclusion witnesses, with thinness proved as a property of the hom-setoid (not merely `sub_le_unique` restated)
- [ ] The `Monic`-cut full-subcategory-of-the-slice identification is proved (fully faithful functor into `Slice C x`)
- [ ] The poset quotient is delivered: `sub_le` descends to `SubObj_Setoid`-classes and is antisymmetric up to `≈`
- [ ] LIBRARY DEFECT: `Theory/Subobject.v:56` asserts in prose that the mediating arrow between subobjects is itself monic, and nothing in-tree proves it — either prove it here (it is the `Monic (g ∘ f) → Monic f` cancellation filed as #250) or rewrite the comment to cite the proof once it lands
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Theory/Subobject/Category.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions SubCat.
Print Assumptions SubCat_thin.
Print Assumptions SubCat_to_Slice.
Print Assumptions sub_le_antisymmetric.
```
Reviewer: statement matches Awodey §5.1 Definition 5.1 and Remark 5.4 — the category must have the *inclusion witnesses* as homs (not a bare relation), thinness must be a fact about that hom-setoid, and the slice identification must be full and faithful.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:5.1:def1","awodey:5.1:remark4"],"deps":[]} -->

---8<---

title: "Awodey 5.1: Functoriality of subobjects — direct image along a mono, and monotonicity of reindexing"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.1:construction-subobject-pushforward, awodey:5.3:cor13]
deps_item_ids: [awodey:5.1:def1]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.1, printed page 95 (PDF page 104) — the direct-image functor along a mono; and §5.3 "Properties of pullbacks", Corollary 5.13, printed page 103 (PDF page 112) — inverse image as the restriction of the slice base change, hence monotone and defined on equivalence classes. Items covered: `awodey:5.1:construction-subobject-pushforward`, `awodey:5.3:cor13`.

## Background

Post-composition with a monomorphism carries subobjects of its domain to subobjects of the codomain (composites of monos are monic), and pulling back along an arbitrary arrow carries subobjects backwards; both operations are monotone for inclusion, and the backward one is exactly the restriction of the base-change functor between slice categories. See [nLab: subobject](https://ncatlab.org/nlab/show/subobject) and [nLab: base change](https://ncatlab.org/nlab/show/base+change).

## Current state in the library

The forward operation does not exist; the backward one exists but only after the order has been forgotten.

- `Theory/Morphisms.v:212` — `monic_compose : Monic f → Monic g → Monic (f ∘ g)`, exactly the well-definedness ingredient Awodey cites, but nothing in the tree maps `SubObj (sub_dom i)` to `SubObj x`: there is no direct-image operation on subobjects at all, hence no monotonicity, no `Proper (equiv ==> equiv)` instance, and no functoriality.
- `Construction/Slice/Pullback.v:50` — `Bang_Functor f : Slice C a ⟶ Slice C b`, post-composition at the *slice* level, defined for every slice object with no `Monic` hypothesis and carrying no mono-preservation lemma.
- `Theory/Subobject/Functor.v:35`, `:60`, `:152`, `:180` — `sub_reindex`, `sub_reindex_respects`, `sub_reindex_comp` and the contravariant `Sub : C^op ⟶ Sets`. The descent clause of Corollary 5.13 is in-tree in a *stronger* form than the book states: the library never forms the un-quotiented collection, since `SubObj_Setoid` already is the quotient, and full functoriality in the arrow is proved.
- Missing from Corollary 5.13: monotonicity, `sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v)`, is nowhere proved — `sub_le` (`Theory/Subobject.v:59`) and `sub_reindex` live in different files that never meet; and no lemma relates `sub_reindex` to `Construction/Slice/Pullback.v:67` (`Star_Functor`), so the commuting square of Corollary 5.13 has no in-tree form.

## Work to be done

Suggested module: `Theory/Subobject/Pushforward.v` (with the reindexing half extending `Theory/Subobject/Functor.v`).

1. Define `sub_pushforward` (Awodey's `i_*`) for a monic `i : m' ~> x`: post-composition, monic by `monic_compose`; prove it `Proper` for `SubObj_Setoid` and monotone for `sub_le`, and package it as a functor between the subobject categories of the §5.1 subobject-category issue.
2. Prove functoriality of `i_*` in `i` (identity and composition), so the direct image composes along composable monos.
3. Prove monotonicity of reindexing: `sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v)`, and assemble `f^{-1}` as a functor between the subobject categories — the statement "f^{-1} is a functor" that the in-tree `Sub : C^op ⟶ Sets` does *not* make.
4. Prove Corollary 5.13's comparison square: through the inclusion of subobjects into the slice (delivered by the §5.1 subobject-category issue), `f^{-1}` is the restriction of `Star_Functor f`, i.e. the square of categories and functors commutes up to the canonical isomorphism; note in the header that the chosen pullbacks make this an equality only up to that comparison.

In-tree donors: `Theory/Subobject.v`, `Theory/Subobject/Functor.v` (`sub_reindex`, `sub_reindex_transport` at `:46`), `Theory/Morphisms.v`, `Theory/Morphisms/Stability.v` (`monic_pullback_stable`, `:226`), `Construction/Slice/Pullback.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.1 printed p. 95 (PDF p. 104); §5.3 Corollary 5.13, printed p. 103 (PDF p. 112)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `i_*` defined, proved `Proper`, monotone, and functorial, as a functor between subobject categories
- [ ] Monotonicity of reindexing proved, and `f^{-1}` assembled as a functor between subobject categories (not merely the existing `Sub : C^op ⟶ Sets`)
- [ ] The Corollary 5.13 comparison square with the slice base change `Star_Functor` is proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Theory/Subobject/Pushforward.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions sub_pushforward.
Print Assumptions sub_pushforward_monotone.
Print Assumptions sub_reindex_monotone.
Print Assumptions sub_reindex_is_star_restriction.
```
Reviewer: statement matches Awodey §5.1 (direct image along a mono) and §5.3 Corollary 5.13 — monotonicity must be proved for the inclusion order, not merely respect for the quotient equivalence, and the comparison with the slice base change must be an actual statement relating the two functors.

## Dependencies

Depends on: awodey:5.1:def1

<!-- catalog: {"ids":["awodey:5.1:construction-subobject-pushforward","awodey:5.3:cor13"],"deps":["awodey:5.1:def1"]} -->

---8<---

title: "Awodey 5.1: Local membership of generalized elements, and the equalizer as a comprehension subobject"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.1:def-local-membership, awodey:5.1:example3]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.1 "Subobjects", the local-membership definition and Example 5.3, printed page 95 (PDF page 104). Items covered: `awodey:5.1:def-local-membership`, `awodey:5.1:example3`.

## Background

A generalized element of an object is said to belong to a subobject when it factors through the subobject's mono; monicity makes the factorization unique, so membership is a relation rather than extra structure, and the equalizer of a parallel pair is then the subobject of exactly those generalized elements on which the two arrows agree — the internalized comprehension of an equation. See [nLab: generalized element](https://ncatlab.org/nlab/show/generalized+element) and [nLab: equalizer](https://ncatlab.org/nlab/show/equalizer).

## Current state in the library

The defining formula exists only in the special case where the element is itself a subobject, and the equalizer is never packaged as a subobject.

- `Theory/Subobject.v:59` — `sub_le u v := { k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈ sub_mono u }` is precisely "factors through the mono", but both arguments must be `SubObj x`, so the element's arrow is forced to be monic; `Theory/Subobject.v:78` (`sub_le_unique`) is the proof-irrelevance clause the book highlights, again stated only for subobject domains although its proof uses only monicity of the target.
- There is no membership relation for a general generalized element `z : Z ~> x`, no notation for it, and no lemma that such a relation is `Proper` in the element up to `≈` or invariant under `SubObj_Setoid` in the subobject. "Generalized element" occurs in-tree only as header prose (`Structure/Constant.v:15`, `Structure/Terminal.v:61`).
- For Example 5.3: `Structure/Equalizer/Fork.v:83` (`equalizer_monic : IsEqualizer f g q e → Monic e`) supplies the subobject half, and the two `IsEqualizer` fields (`Structure/Equalizer/Fork.v:52`) — `fork_eq` and `eq_desc` — supply the two halves of the characterizing biconditional. But no `SubObj` is ever built from `equalizer_monic` (the only in-tree producers of `SubObj` are `truth_subobject`, `sub_reindex`, and the image subobject of `Instance/Sets/Classifier.v`), and the biconditional itself is unstatable while the membership relation is missing; the forward direction (an element factoring through the equalizer is equalized) is not recorded even as a lemma.

## Work to be done

Suggested module: `Theory/Subobject/Membership.v`.

1. Define local membership for a generalized element: for `m : SubObj x` and `z : Z ~> x`, `z ∈ m := { f : Z ~> sub_dom m & sub_mono m ∘ f ≈ z }`, with a scoped notation. Prove the uniqueness clause (any two witnesses are `≈`, from monicity of `sub_mono m` alone) — the proof-irrelevance Awodey emphasises.
2. Prove the invariance lemmas: membership is `Proper` in the element for `≈`, and invariant under `SubObj_Setoid` equivalence of the subobject; and that `sub_le u v` is the special case where the element is `sub_mono u`, so the new relation genuinely generalizes `Theory/Subobject.v:59`.
3. Package an equalizer as a subobject: `equalizer_subobject : IsEqualizer f g q e → SubObj q_dom` (feeding `equalizer_monic` to the `SubObj` constructor), so that "an equalizer is a subobject" is an inhabitant rather than header prose.
4. Prove Example 5.3's characterization: `z ∈ equalizer_subobject H ↔ f ∘ z ≈ g ∘ z` — the ⇐ direction from `eq_desc`, the ⇒ direction a one-rewrite consequence of `fork_eq`.

In-tree donors: `Theory/Subobject.v`, `Structure/Equalizer/Fork.v`, `Structure/Equalizer.v` (whose header already claims the equalizer/subobject connection in prose), `Theory/Morphisms.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.1, printed p. 95 (PDF p. 104)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Membership defined for an arbitrary generalized element, with the uniqueness (proof-irrelevance) clause proved from monicity of the target only
- [ ] Invariance proved on both sides (`≈` in the element, `SubObj_Setoid` in the subobject), and `sub_le` exhibited as the special case
- [ ] An equalizer is packaged as an inhabitant of `SubObj`, and the characterizing biconditional is proved in both directions
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Theory/Subobject/Membership.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions sub_elem.
Print Assumptions sub_elem_unique.
Print Assumptions equalizer_subobject.
Print Assumptions equalizer_membership.
```
Reviewer: statement matches Awodey §5.1 (the membership relation and Example 5.3) — membership must be defined for an arbitrary `z : Z ~> x`, not only for monic `z`, and the equalizer characterization must be the biconditional the example states.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:5.1:def-local-membership","awodey:5.1:example3"],"deps":[]} -->

---8<---

title: "Awodey 5.3/5.7 Ex 1: Pullback calculus — the prism lemma, and monos as pullback squares"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.3:cor11, awodey:5:ex1]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.3 "Properties of pullbacks", Corollary 5.11, printed page 102 (PDF page 111); and §5.7 Exercise 1, printed page 124 (PDF page 133). Items covered: `awodey:5.3:cor11`, `awodey:5:ex1`.

## Background

Two elementary consequences of the two-pullbacks (pasting) lemma: pulling a commutative triangle back along an arrow yields a unique comparison arrow making the resulting prism commute, with the induced upper square again a pullback; and an arrow is monic exactly when the square with two identity legs on it is a pullback, whence any functor preserving pullbacks — in particular a representable — preserves monomorphisms. See [nLab: pullback](https://ncatlab.org/nlab/show/pullback) and [nLab: monomorphism](https://ncatlab.org/nlab/show/monomorphism).

## Current state in the library

The pasting toolkit is in-tree but neither consequence is stated.

- The two-pullbacks lemma itself is present: `Theory/Morphisms/Stability.v` provides pasting and `:160` (`pullback_unpaste`) the cancellation direction; `Structure/Pullback.v:171` (`ump_pullbacks`) is the universal property.
- Corollary 5.11's comparison arrow exists only *inside* the anonymous `fmap` field of `Construction/Slice/Pullback.v:67` (`Star_Functor`, lines 72–83): its `unique_property` gives both prism commutations and `uniqueness` the uniqueness clause, but there is no standalone lemma, and no consumer or companion result (`rg 'Star_Functor|Bang_Functor'` outside that file finds only prose in `Construction/Slice.v:43,89`).
- The distinctive extra clause — that the induced upper square is itself a pullback — is nowhere proved; `pullback_unpaste` supplies it in one step.
- For Exercise 1: an enumeration of the in-tree mono inventory (`Theory/Morphisms.v` `id_monic`/`sections_are_monic`/`monic_compose`, `Theory/Isomorphism.v` `iso_to_monic`/`iso_from_monic`/`Monic_Retraction_Iso`, `Theory/Morphisms/Stability.v:226` `monic_pullback_stable`, `Structure/Equalizer/Fork.v:83` `equalizer_monic`, `Instance/Sets.v:370` `injectivity_is_monic`, `finset_monic_iff_injective`) contains no square-is-a-pullback characterization; and `rg 'Monic|Epic' Functor/` returns nothing at all, so no functor — representable or otherwise — is shown to preserve monos.

## Work to be done

Suggested module: extend `Theory/Morphisms/Stability.v`, or a new `Structure/Pullback/Calculus.v` re-exported from it.

1. State and prove Corollary 5.11 as a standalone lemma: given a commutative triangle over an object and an arrow into that object, with the two pullbacks chosen, the unique comparison arrow with both prism commutations, plus uniqueness; then the extra clause that the induced upper square is a pullback (via `pullback_unpaste`).
2. Refactor `Construction/Slice/Pullback.v:67` (`Star_Functor`) to consume the new lemma instead of re-deriving the comparison inline, so the functor's `fmap` and its laws read off the corollary.
3. Prove Exercise 1: `Monic m ↔ IsPullback` of the square whose two parallel legs are identities and whose other two are `m`.
4. Conclude that a representable preserves monomorphisms: `Monic f → Monic (fmap[Curried_Hom C a] f)` in `Sets` (in this library `Monic` unfolds to injectivity of postcomposition, so the conclusion is close to definitional — state it anyway, since nothing in `Functor/` records it), and note the general form: any functor preserving pullbacks preserves monos.

In-tree donors: `Theory/Morphisms/Stability.v`, `Structure/Pullback.v`, `Construction/Slice/Pullback.v`, `Functor/Hom.v`, `Theory/Morphisms.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.3 Corollary 5.11, printed p. 102 (PDF p. 111); §5.7 Exercise 1, printed p. 124 (PDF p. 133)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The prism lemma is standalone, with BOTH commutations, the uniqueness clause, and the "upper square is a pullback" conclusion
- [ ] `Star_Functor` is refactored to consume it (no duplicated inline derivation)
- [ ] The monic ⟺ identity-square-is-a-pullback biconditional is proved, and the representable-preserves-monos corollary drawn
- [ ] LIBRARY DEFECT: `Structure/Pullback.v`'s comments around `pullback_unique` (`:182-211`) claim more than the lemma proves — it gives only an isomorphism of the two pullback objects, with compatibility with the projections living separately in `Theory/Morphisms/Stability.v:313` (`PullbackTransport`) / `:329` (`pullback_transport`); correct the comment (or strengthen the lemma) while touching this file
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Structure/Pullback/Calculus.v
coqc -R . Category Construction/Slice/Pullback.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions pullback_prism.
Print Assumptions pullback_prism_upper_is_pullback.
Print Assumptions monic_iff_identity_pullback.
Print Assumptions representable_preserves_monic.
```
Reviewer: statement matches Awodey §5.3 Corollary 5.11 (the upper-square-is-a-pullback clause is the point of calling it a corollary of the two-pullbacks lemma) and §5.7 Exercise 1 (both directions of the biconditional).

## Dependencies

None.

<!-- catalog: {"ids":["awodey:5.3:cor11","awodey:5:ex1"],"deps":[]} -->

---8<---

title: "Awodey 5.3/5.5: Slices of Sets as indexed families — reindexing as pullback, and its preservation of coproducts"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.3:example15, awodey:5.5:example-reindexing-preserves-coproducts]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.3 Example 5.15, printed page 106 (PDF page 115); and §5.5 "Preservation of limits", the reindexing example, printed page 114 (PDF pages 123–124). Items covered: `awodey:5.3:example15`, `awodey:5.5:example-reindexing-preserves-coproducts`.

## Background

A slice of sets over an index set is the same thing as an indexed family of sets, the equivalence sending a map to its fibres; under this reading, reindexing a family along a function is pullback along that function, and the pullback (reindexing) functor between slices preserves coproducts, since coproducts of families are computed fibrewise. See [nLab: over category](https://ncatlab.org/nlab/show/over+category), [nLab: family](https://ncatlab.org/nlab/show/family) and [nLab: base change](https://ncatlab.org/nlab/show/base+change).

## Current state in the library

Neither example is formalized, and the second is not even typeable today.

- `Construction/Slice.v:73-77` records the equivalence between a slice of sets and an indexed family as header prose (citing Leinster); nothing formalizes it.
- There is no `HasPullbacks Sets` instance anywhere — the tree's only `HasPullbacks` instance is `FinSet_Pullbacks` (`Instance/FinSet/Classifier.v:264`) — so `Construction/Slice/Pullback.v:67` (`Star_Functor`), which is defined under a section hypothesis of pullbacks, cannot be instantiated at `Sets`, which is where both examples live. Supplying `Sets` pullbacks is the already-filed #333.
- Slices carry no coproducts: `rg 'Slice.*Cocartesian|Cocartesian.*Slice'` returns 0 hits, so "reindexing preserves coproducts" cannot be stated. The base does have them (`Instance/Sets/Cocartesian.v:28`, `Sets_Cocartesian`).
- The indexed-coproduct vocabulary is missing entirely (`icoprod`/`HasIndexedCoproducts` → 0 hits), although the dual `iprod` exists (`Structure/Limit/Product.v:93`) over `Instance/Discrete.v:37` (`DiscreteCat`).
- What exists is only the abstract subject of the claims (`Star_Functor`, `Bang_Functor`), not any fragment of them; `Construction/Slice/Pullback.v:121` shows the base-change adjunction itself is a commented-out stub (filed as #387).

## Work to be done

Suggested modules: `Construction/Slice/Cocartesian.v` (generic) and `Instance/Sets/Family.v` (the `Sets` story).

1. Coproducts in a slice: for a base with binary (and indexed) coproducts, build `Cocartesian (Slice C c)` — the coproduct of two slice objects is the copairing out of the base coproduct — and the indexed version, introducing `HasIndexedCoproducts` as the dual of `HasIndexedProducts` if that is the cheapest route (it is missing tree-wide, and the dual half of the §5.4 colimit issue wants it too).
2. The family equivalence: `Sets/I ≃ [DiscreteCat I, Sets]`, both functors and the two natural isomorphisms, replacing the `Construction/Slice.v:73-77` prose with a theorem.
3. Reindexing as pullback (Example 5.15): under that equivalence, `Star_Functor α` corresponds to precomposition with `α`, and concretely `J ×_I (∐_i A_i) ≅ ∐_j A_{α j}` as objects of the slice over the reindexing set.
4. Preservation (the §5.5 example): `Star_Functor α : Sets/I ⟶ Sets/J` preserves coproducts — either by transporting the pointwise coproducts across the equivalence, or directly from the pullback universal property; state it with the cone-level preservation vocabulary if the §5.5 preservation issue (#427) has landed, otherwise as an explicit isomorphism of the two constructed objects, and disclose the choice in the header.

In-tree donors: `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Instance/Sets/Cocartesian.v`, `Instance/Discrete.v`, `Structure/Limit/Product.v`, `Theory/Equivalence.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.3 Example 5.15, printed p. 106 (PDF p. 115); §5.5, printed p. 114 (PDF pp. 123–124)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Slice coproducts delivered (binary and indexed), with `HasIndexedCoproducts` introduced if used
- [ ] The equivalence between a slice of `Sets` and the corresponding functor category over a discrete index is proved, and `Construction/Slice.v:73-77`'s prose updated to cite it
- [ ] Reindexing is identified with pullback, with the concrete family formula proved
- [ ] Preservation of coproducts by the reindexing functor is proved (not merely asserted)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` closed (or reported, for the instance layer) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Construction/Slice/Cocartesian.v
coqc -R . Category Instance/Sets/Family.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Slice_Cocartesian.
Print Assumptions Sets_Slice_Family_Equivalence.
Print Assumptions reindex_is_pullback.
Print Assumptions reindex_preserves_coproducts.
```
Reviewer: statement matches Awodey §5.3 Example 5.15 and the §5.5 reindexing example — the preservation statement must be about the pullback functor between slices, and the family formula must be the fibrewise one the book computes.

## Dependencies

Depends on: #333

<!-- catalog: {"ids":["awodey:5.3:example15","awodey:5.5:example-reindexing-preserves-coproducts"],"deps":["#333"]} -->

---8<---

title: "Awodey 5.6: The cumulative hierarchy as an ω-colimit, and the functoriality of V_ω"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.6:example33]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.6 "Colimits", Example 5.33, printed pages 119–120 (PDF pages 128–130). Item covered: `awodey:5.6:example33`.

## Background

The set-theoretic cumulative hierarchy is an ω-colimit: iterating the powerset (relativized: atoms plus powerset) along the natural numbers gives an ascending chain whose colimit is the rank-ω stage, and a function between atom sets induces a map of the whole chain, making the construction a functor. See [nLab: cumulative hierarchy](https://ncatlab.org/nlab/show/cumulative+hierarchy) and [Wikipedia: Von Neumann universe](https://en.wikipedia.org/wiki/Von_Neumann_universe).

## Current state in the library

Nothing of the example is formalized, and one of its ingredients does not exist.

- No cumulative-hierarchy vocabulary of any kind is in-tree; the only `Pow` is the internal power object of a topos (`Structure/Topos.v:129`, `Pow a := Ω ^ a`), an object-level definition with no action on morphisms.
- The covariant (direct-image) powerset functor the example uses does not exist (a whole-tree search for direct-image/powerset functors finds only the topos power object and the *contravariant* reindexing `Sub : C^op ⟶ Sets`, `Theory/Subobject/Functor.v:180`). Supplying it is the already-filed #227.
- The chain machinery is adjacent but not usable as-is: `Instance/Omega.v:72` (`Omega`) is the ω index category, and `Construction/Chain.v:64` (`Chain F : Omega ⟶ C`) builds the iterated-endofunctor chain, but it starts at the *initial* object (`chain_obj O := initial_obj`, lines 28–43), whereas Awodey's relativized chain starts at the atom set; and its colimit is never constructed in `Sets` (it is assumed as data by `Theory/Adamek.v`).

## Work to be done

Suggested module: `Instance/Sets/Cumulative.v`.

1. Generalize the chain construction to an arbitrary start object: `Chain_from F a : Omega ⟶ C` with `X_0 = a`, `X_{n+1} = F X_n`, and the induced steps — either by extending `Construction/Chain.v` or by a local definition, disclosing which in the header.
2. Instantiate with the endofunctor `X ↦ A + P_!(X)` on `Sets` (using the covariant powerset functor of #227 and `Instance/Sets/Cocartesian.v`), with the first step the left coproduct injection, matching the book's chain.
3. Construct the colimit `V_ω(A)` of this chain in `Sets` (a quotient of the disjoint sum by the generated relation, in the style of the existing `Sets` pushout/coend quotients), or state precisely which cocompleteness input is assumed if the general `Sets` ω-colimit is taken as a dependency.
4. Functoriality: a function of atom sets induces a map of chains whose squares commute, hence a cocone and a unique mediator `V_ω(f)`; prove the functor laws, so `V_ω` is a functor on `Sets`. Recover the basic hierarchy as the instance at the empty atom set.

In-tree donors: `Instance/Omega.v`, `Construction/Chain.v`, `Instance/Sets/Cocartesian.v`, `Instance/Sets/Coend.v` and `Instance/Sets/Pushout.v` (setoid quotient patterns), `Structure/Limit.v` (`Colimit`).

## Definition of Done

- [ ] Statement fidelity to the book (§5.6 Example 5.33, printed pp. 119–120 (PDF pp. 128–130)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The relativized chain starting at the atom set is constructed (not the initial-object chain of `Construction/Chain.v`)
- [ ] The ω-colimit is constructed in `Sets`, or its cocompleteness input is declared explicitly in the statement
- [ ] Functoriality of `V_ω` is proved by mediation out of the induced cocone, with both functor laws
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` closed (or reported, for the instance layer) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Sets/Cumulative.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions V_chain.
Print Assumptions V_omega.
Print Assumptions V_omega_functor.
```
Reviewer: statement matches Awodey §5.6 Example 5.33 — the chain must start at the atoms with the coproduct step (not at an initial object), and functoriality must be obtained through the universal property of the colimit.

## Dependencies

Depends on: #227

<!-- catalog: {"ids":["awodey:5.6:example33"],"deps":["#227"]} -->

---8<---

title: "Awodey 5.6: ω-CPOs and continuous monotone maps"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.6:example34]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.6 "Colimits", Example 5.34, printed page 121 (PDF page 130). Item covered: `awodey:5.6:example34`.

## Background

An ω-CPO is a poset in which every ascending chain has a least upper bound — equivalently, in which every ω-shaped diagram has a colimit in the thin category of the poset — and a monotone map is continuous when it preserves those colimits; these form the standard category of domain theory. See [nLab: dcpo](https://ncatlab.org/nlab/show/dcpo) and [Wikipedia: Complete partial order](https://en.wikipedia.org/wiki/Complete_partial_order).

## Current state in the library

Absent, with the strongest possible negative evidence: `rg -i '\bCPO\b|dcpo|directed complete|least upper bound|\blub\b|supremum|ascending chain'` returns zero hits tree-wide.

- `Instance/Poset.v:116` (`Poset`) is the thin category *of* a single poset and carries no completeness layer; `Instance/Proset.v:33` (`Proset`) likewise. There is no category of posets in-tree — that is the already-filed #641.
- The shape and the preservation vocabulary exist (`Instance/Omega.v:72` `Omega` with `omega_step` at `:85`; `Structure/Limit/Preservation.v`), but the order-theoretic characterization of a colimit as a least upper bound is never made, so "the chain has a colimit" and "the chain has a lub" are not connected anywhere.
- `Instance/Poset.v:93` cites Knaster–Tarski least fixed points in its background essay, with no formalization attached.

## Work to be done

Suggested module: `Instance/CPO.v`.

1. Define an ω-CPO: a poset together with, for every ascending chain, a least upper bound given as *data* (an operation plus the two clauses — an upper bound, and below every upper bound), so no choice principle is needed. Add a bottom-element variant (pointed ω-CPO) since the fixed-point theorem needs it.
2. Prove the bridge to the categorical reading: an element is a least upper bound of a chain exactly when it is a colimit of the corresponding `Omega`-diagram in the thin category `Instance/Poset.v:116` — this is what makes Awodey's "ω-cocompleteness in posets" reading a theorem rather than a slogan.
3. Define continuous monotone maps (preserving chain lubs), prove identities and composites continuous, and assemble the category `ωCPO`; give the forgetful functor to `Pos` (#641) and note that it is faithful.
4. Sanity witnesses: a finite poset (every ascending chain is eventually constant) and the ordinal ω extended by a top element, both of which the ambient-dependence example of §5.6 needs.

In-tree donors: `Instance/Poset.v`, `Instance/Proset.v`, `Instance/Omega.v`, `Structure/Limit.v`, `Structure/Cone.v`, the `Pos` category of #641.

## Definition of Done

- [ ] Statement fidelity to the book (§5.6 Example 5.34, printed p. 121 (PDF p. 130)); setoid discipline — `≈` on morphisms, never `=`
- [ ] ω-CPO defined with the lub as data (no choice), and the pointed variant available
- [ ] The lub ⟺ ω-colimit bridge is proved against the in-tree thin category of a poset
- [ ] Continuity defined, closed under identity and composition, and the category `ωCPO` assembled with its forgetful functor to `Pos`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` closed (or reported, for the instance layer) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/CPO.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions omegaCPO.
Print Assumptions lub_iff_colimit.
Print Assumptions omegaCPO_Category.
```
Reviewer: statement matches Awodey §5.6 Example 5.34 — the two lub clauses must be exactly the book's, and continuity must be preservation of chain colimits, not mere monotonicity.

## Dependencies

Depends on: #641

<!-- catalog: {"ids":["awodey:5.6:example34"],"deps":["#641"]} -->

---8<---

title: "Awodey 5.6: Least fixed points of continuous maps on an ω-CPO (Kleene iteration)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.6:prop35]
deps_item_ids: [awodey:5.6:example34]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.6 "Colimits", Proposition 5.35, printed page 121 (PDF pages 130–131). Item covered: `awodey:5.6:prop35`.

## Background

On a pointed ω-CPO, a continuous endomap has a fixed point obtained by iterating it from the bottom element and taking the lub of the resulting chain, and that fixed point is the least one — the Kleene fixed-point theorem, the order-theoretic shadow of the initial-algebra construction. See [Wikipedia: Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem) and [nLab: dcpo](https://ncatlab.org/nlab/show/dcpo).

## Current state in the library

The categorical generalization is in-tree, stronger in generality but strictly conditional and never inhabited; the order-theoretic statement is absent.

- `Construction/Chain.v:64` (`Chain F : Omega ⟶ C`) is exactly Kleene's iteration in categorical dress — bottom becomes the initial object, iteration becomes the endofunctor chain.
- `Theory/Adamek.v:107` (`AdamekData`) is the honest hypothesis (the colimit together with leg agreement for the shifted cocone), `:285` (`adamek`) makes the colimit an initial `F`-algebra, and `Theory/Lambek.v:40` (`lambek`) gives the fixed-point isomorphism; initiality is the leastness clause (in a thin category an `F`-algebra is a prefixed point and a unique map into it is the inequality).
- But: the `PreservesColimit → AdamekData` bridge is deliberately withheld (the apex-only preservation class is documented as insufficient), and docs/INHABITATION.md records that no concrete `AdamekData` is constructed anywhere in-tree, so no actual fixed point of an actual continuous map is exhibited.
- On the order side there is nothing at all: no ω-CPO, no bottom-as-least, no least upper bound, no "least fixed point" statement (`Instance/Poset.v:93` cites Knaster–Tarski only in its background essay).

## Work to be done

Suggested module: `Instance/CPO/FixedPoint.v`.

1. Prove Proposition 5.35 directly in the order-theoretic form: for a pointed ω-CPO and a continuous endomap, the iteration chain from the bottom element is ascending; its lub is a fixed point; and it is below every fixed point (by induction from the bottom).
2. Build the bridge to the in-tree categorical machinery: exhibit the ω-CPO data as an `AdamekData` for the endofunctor induced by the map on the thin category of the poset, and derive Proposition 5.35 a second time as an instance of `adamek` + `lambek`. This would be the **first concrete `AdamekData` witness in the tree** — docs/INHABITATION.md currently records that the theorem is proven parametrically with no in-tree model — so the header should say so and the doc should be updated.
3. Record the comparison in the header: which hypothesis the order-theoretic proof uses (continuity = preservation of chain lubs) versus what `adamek` consumes (leg agreement), and why the bridge is available here even though the general `PreservesColimit → AdamekData` implication is not.

In-tree donors: the ω-CPO development of the §5.6 ω-CPO issue, `Construction/Chain.v`, `Theory/Adamek.v`, `Theory/Lambek.v`, `Theory/Recursion.v`, `Instance/Omega.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.6 Proposition 5.35, printed p. 121 (PDF pp. 130–131)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Both clauses proved: the lub of the iteration chain is a fixed point, and it is the least fixed point
- [ ] The `AdamekData` instantiation is delivered and `adamek`/`lambek` are shown to reproduce the same conclusion
- [ ] docs/INHABITATION.md updated to record the first concrete `AdamekData` witness
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` closed (or reported, for the instance layer) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/CPO/FixedPoint.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions kleene_lfp.
Print Assumptions kleene_lfp_least.
Print Assumptions cpo_AdamekData.
```
Reviewer: statement matches Awodey §5.6 Proposition 5.35 — leastness among *all* fixed points must be proved, and the `AdamekData` bridge must actually be inhabited (not assumed).

## Dependencies

Depends on: awodey:5.6:example34

<!-- catalog: {"ids":["awodey:5.6:prop35"],"deps":["awodey:5.6:example34"]} -->

---8<---

title: "Awodey 5.6: Colimits depend on the ambient category — the chain of finite ω-CPOs in Pos and in ωCPO"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:5.6:example-colimit-ambient-dependence]
deps_item_ids: [awodey:5.6:example34]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.6 "Colimits", the unnumbered worked example closing the section, printed page 122 (PDF pages 131–132). Item covered: `awodey:5.6:example-colimit-ambient-dependence`.

## Background

A colimit is computed relative to an ambient category: the chain of finite initial segments of the natural numbers has the naturals as its colimit among posets, but the naturals are not ω-complete, so in the category of ω-CPOs the same chain has a strictly larger colimit obtained by adjoining a top element. See [nLab: colimit](https://ncatlab.org/nlab/show/colimit) and [nLab: dcpo](https://ncatlab.org/nlab/show/dcpo).

## Current state in the library

No counterpart. Both ambient categories the example needs are missing — there is no category of posets (the already-filed #641; `Instance/Poset.v:116` is the thin category *of* one poset) and no ω-CPOs at all (`rg -i '\bCPO\b|dcpo|directed complete|ascending chain'` → 0 hits). More broadly, no in-tree statement anywhere compares a colimit computed in a subcategory with the one computed in the ambient category: `Construction/Subcategory.v`, `Construction/Reflective.v` and `Construction/Reflective/Idempotent.v` contain no such comparison, and the preservation vocabulary (`Structure/Limit/Preservation.v`) is never instantiated at an inclusion functor.

## Work to be done

Suggested module: `Instance/CPO/AmbientColimit.v`.

1. Construct the chain of finite initial segments as a diagram `Omega ⟶ ωCPO` (each finite segment is trivially an ω-CPO; the inclusions are continuous).
2. Compute its colimit in `Pos` and show the vertex is the naturals with their usual order.
3. Show the naturals are *not* an ω-CPO (the identity chain has no lub), so the `Pos` colimit does not lie in the image of the inclusion.
4. Compute the colimit in `ωCPO` and show its vertex is the naturals with a top element adjoined, verifying the universal property against every ω-CPO cocone.
5. Conclude the intended moral as a theorem about the inclusion functor: the inclusion `ωCPO ↪ Pos` does not preserve this ω-colimit — the first in-tree witness that a (co)limit is ambient-dependent. State it with the preservation vocabulary of `Structure/Limit/Preservation.v` (or the cone-level notion of #427 if it has landed) so it reads as a negative preservation result.

In-tree donors: the ω-CPO development of the §5.6 ω-CPO issue, `Pos` (#641), `Instance/Omega.v`, `Structure/Limit.v`, `Structure/Limit/Preservation.v`, `Construction/Subcategory.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§5.6, printed p. 122 (PDF pp. 131–132)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Both colimits are computed with their universal properties proved, not merely exhibited
- [ ] The negative fact (the naturals are not ω-complete) is proved, not assumed
- [ ] The conclusion is stated as a failure of preservation for the inclusion functor
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` closed (or reported, for the instance layer) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/CPO/AmbientColimit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions finite_segment_chain.
Print Assumptions omega_not_omega_complete.
Print Assumptions segment_colimit_in_CPO.
Print Assumptions inclusion_does_not_preserve.
```
Reviewer: statement matches Awodey §5.6's closing example — the two colimits must be genuinely different objects with both universal properties verified, and the non-completeness of the naturals must be proved.

## Dependencies

Depends on: awodey:5.6:example34
Depends on: #641

<!-- catalog: {"ids":["awodey:5.6:example-colimit-ambient-dependence"],"deps":["awodey:5.6:example34","#641"]} -->

---8<---

title: "Awodey 5.7 Ex 4: The category of partial maps Par(C) over a category with pullbacks"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:5:ex4]
deps_item_ids: [awodey:5.1:def1]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §5.7 Exercise 4 (starred), printed page 125 (PDF page 134). Item covered: `awodey:5:ex4`.

## Background

Over any category with pullbacks one builds the category of partial maps: an arrow is a subobject of the source (its domain of definition) together with a map out of that subobject, taken up to the evident equivalence, and composition restricts the domain of definition by pulling the second map's domain back along the first. See [nLab: restriction category](https://ncatlab.org/nlab/show/restriction+category) and [Wikipedia: Partial function](https://en.wikipedia.org/wiki/Partial_function).

## Current state in the library

Two concrete partial-map categories exist, both by the option/maybe encoding rather than by subobjects and pullbacks.

- `Instance/Sets/Par.v:27` (`Part`) — setoids and partial maps, with all category laws discharged and the classical product at `:115` (`Part_Cartesian`); the file header (`:13-19`) states outright that this is the Kleisli category of the maybe monad and that the identification with partial functions holds because the base is a Boolean topos.
- `Instance/Coq/Par.v:53` (`Par`) — the same construction over Coq types.

Neither construction mentions a subobject or a pullback: the domain of definition is recovered only as a preimage of the `Some` constructor, so the associativity and identity verifications the exercise asks for (the ones that *use* pullback pasting) are not the ones performed in-tree. There is no general `Par(C)` for an arbitrary category with pullbacks, no equivalence relation on domain-plus-map pairs, no composition by pullback, and no restriction-category or partial-map-classifier layer to mediate between the general construction and the two concrete models.

## Work to be done

Suggested module: `Construction/Par.v`.

1. Define the hom-setoid: for objects `a`, `b` of a category with pullbacks, a partial map is a pair of a subobject `U ↣ a` and an arrow `sub_dom U ~> b`; two pairs are equivalent when the subobjects are equivalent (`SubObj_Setoid`) and the maps agree along the mediating isomorphism. Prove it is a setoid.
2. Define identities (the maximal subobject, with the identity map) and composition by pullback: pull the second map's domain back along the first (`sub_reindex`, `Theory/Subobject/Functor.v:35`), then compose.
3. Prove composition is `Proper` for the hom-setoid, and prove the category laws — associativity via pullback pasting (`Theory/Morphisms/Stability.v`) and the unit laws — assembling `Par C : Category`. This is the verification the exercise asks for.
4. Record the identity-on-objects embedding `C ⟶ Par C` (a total map is a partial map with maximal domain), and, if it is in reach in the same PR, the comparison with the existing concrete models — `Part ≅ Par Sets` once `Sets` has pullbacks (#333); otherwise state the comparison as a disclosed follow-up in the header rather than leaving the two developments unrelated.

In-tree donors: `Theory/Subobject.v`, `Theory/Subobject/Functor.v`, `Theory/Morphisms/Stability.v`, `Structure/Pullback.v`, `Instance/Sets/Par.v` and `Instance/Coq/Par.v` (the concrete models to compare against).

## Definition of Done

- [ ] Statement fidelity to the book (§5.7 Exercise 4, printed p. 125 (PDF p. 134)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The hom-setoid is the pair-up-to-equivalence the exercise describes (subobject + map), not an option/maybe encoding
- [ ] Composition is by pullback of the domain of definition, and is proved `Proper`
- [ ] The category laws are proved — associativity through pullback pasting, and both unit laws
- [ ] The embedding of total maps is delivered, and the relation to `Instance/Sets/Par.v` is either proved or explicitly disclosed as deferred in the header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Construction/Par.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Par.
Print Assumptions Par_comp_Proper.
Print Assumptions Par_Total_Embedding.
```
Reviewer: statement matches Awodey §5.7 Exercise 4 — arrows must be subobject-plus-map pairs up to equivalence and composition must be by pullback; a maybe-monad Kleisli category is not an answer to this exercise.

## Dependencies

Depends on: awodey:5.1:def1

<!-- catalog: {"ids":["awodey:5:ex4"],"deps":["awodey:5.1:def1"]} -->

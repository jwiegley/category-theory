```yaml
title: "MacLane III.1: Couniversal arrows (universal arrows from a functor to an object)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:def3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book p. 58 (PDF p. 67). Items: `maclane:III.1:def3`.

## Background
The dual of the universal arrow: for S : D ⟶ C and c ∈ C, a couniversal arrow is a pair ⟨r, v : S r → c⟩ through which every arrow S d → c factors uniquely as v ∘ S f′. It is the counit-side building block of adjunctions, dual to the unit-side universal arrow. See [nLab: universal construction](https://ncatlab.org/nlab/show/universal+construction) and [Wikipedia: Universal property](https://en.wikipedia.org/wiki/Universal_property).

## Current state in the library
Only the primal direction is formalized: `Theory/Universal/Arrow.v:127` defines `Class UniversalArrow (c : C) (F : D ⟶ C)` as an initial object of the comma category `=(c) ↓ F` (with `AUniversalArrow` at line 240 as the direct-UMP form, and the left-adjoint assembly `AdjunctionFromUniversalArrows`). The dual exists only as a header comment (`Theory/Universal/Arrow.v:23`: a universal arrow from F to c is a terminal object of `F ↓ =(c)`) plus the unexploited op-comma route `Cocomma` (`Construction/Comma.v:254`). Searches for `couniversal`, `CouniversalArrow`, and `RightAdjointFunctorFrom*` return zero hits; no in-tree development names, instantiates, or provides API for the dual.

## Work to be done
- Define `CouniversalArrow c F` (terminal object of `F ↓ =(c)`) and the direct-UMP class `ACouniversalArrow`, ideally as definitional instantiations of the primal classes at `C^op`/`D^op` (the library's `C^op^op = C` duality makes this cheap), but with covariant accessors so consumers never see `op`.
- Prove the dual of `ump_universal_arrows` and the converse `couniversal_arrow_from_UMP`.
- Assemble `RightAdjointFunctorFromCouniversalArrows` / `AdjunctionFromCouniversalArrows`, the counit-side mirror of the existing left-adjoint assembly.
- Suggested path: extend `Theory/Universal/Arrow.v` or add `Theory/Universal/Arrow/Dual.v`. Donors: `Theory/Universal/Arrow.v`, `Construction/Comma.v` (`Cocomma`), `Theory/Adjunction.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`CouniversalArrow`, `AdjunctionFromCouniversalArrows`)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Theory/Universal/Arrow.v` (or the new file) compiles standalone after its dependencies
- `Print Assumptions AdjunctionFromCouniversalArrows.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 58

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.1:def3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Universal elements as first-class structures"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:def2, maclane:III.1:remark3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book pp. 57–58 (PDF pp. 66–67). Items: `maclane:III.1:def2`, `maclane:III.1:remark3`.

## Background
A universal element of H : D ⟶ Set is a pair ⟨r, e ∈ H r⟩ through which every element of every H d is reached by a unique arrow's action; Mac Lane shows universal elements and universal arrows subsume one another (an element is an arrow from a one-point set, and a universal arrow is a universal element of the hom-composite functor). See [nLab: universal element](https://ncatlab.org/nlab/show/universal+element) and [Wikipedia: Universal property](https://en.wikipedia.org/wiki/Universal_property).

## Current state in the library
The concept exists only through the Yoneda/representability surrogate: `Structure/UniversalProperty.v:72` (`representability_by_yoneda`) works with the anonymous sigma setoid `{ x : F c & IsIsomorphism (from (Yoneda_Lemma C F c) x) }` — an element whose Yoneda mate is a natural iso — inside a single proposition; no named `UniversalElement` class exists (identifier search: 0 hits), and the elementary unique-factorization definition is never stated. For the subsumption remark: `Structure/UniversalProperty/Universal/Arrow.v:61` (`UniversalArrowIsUniversalProperty`) and `representability_by_yoneda` provide the two halves through representations, but their composite (universal arrow ⟺ universal element of the functor d ↦ Hom(c, U d)) is not stated as a single theorem, and the one-point-set half is entirely absent (`Instance/One.v` is the terminal category, not a one-point-setoid bridge).

## Work to be done
- Define a first-class `UniversalElement (H : D ⟶ Sets)` (carrier object + element + unique-factorization property, elementary form), with a setoid of such structures.
- Prove the equivalence with the existing Yoneda-mate-is-iso encoding (`representability_by_yoneda`), giving reusable accessors both ways.
- Prove the two-way subsumption: (a) universal elements of H are universal arrows from the one-point setoid to H (mediated by a global-elements lemma for `Sets`); (b) `⟨r, u⟩` is a universal arrow from c to S iff `⟨r, u⟩` is a universal element of `d ↦ Hom(c, S d)` — the composite of the two existing propositions, stated directly.
- Suggested path: `Theory/Universal/Element.v`. Donors: `Structure/UniversalProperty.v`, `Structure/UniversalProperty/Universal/Arrow.v`, `Functor/Hom/Yoneda.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`UniversalElement`, both subsumption theorems)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Theory/Universal/Element.v` compiles standalone after its dependencies
- `Print Assumptions` on the equivalence and both subsumption theorems prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, pp. 57–58

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.1:def2","maclane:III.1:remark3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Kernels as universals for a contravariant functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:remark4]
deps_item_ids: [maclane:III.1:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book p. 59 (PDF p. 68). Items: `maclane:III.1:remark4`.

## Background
Mac Lane remarks that the kernel of a homomorphism is itself a universal — precisely, a universal for a suitable contravariant set-valued functor (the functor of arrows killed by f), a packaging that also covers categories like Rng where zero morphisms are unavailable. See [nLab: kernel](https://ncatlab.org/nlab/show/kernel).

## Current state in the library
Only the zero-object equalizer form exists: `Structure/Kernel.v:53` (`IsKernel f i := IsEqualizer f zero_mor k i`) with the universal property `kernel_desc` (line 118) and `kernel_monic` (line 98), all under a `ZeroObject` context. The contravariant-functor packaging — the kernel as a universal element of the presheaf d ↦ {h : d → a | f ∘ h ≈ 0} — is not formalized, and none of the remark's concrete algebraic categories (Ab, Grp, Rng, R-Mod) exists in-tree to instantiate it.

## Work to be done
- Define the "kill-f" presheaf `d ↦ {h : d ~> a | f ∘ h ≈ zero_mor}` as a functor `C^op ⟶ Sets` (zero-object setting) and prove that `IsKernel f i` is equivalent to `⟨k, i⟩` being a universal element of it (representability of the kill-f presheaf by the kernel object).
- State the packaging so it survives in categories without a zero object when a suitable pointed-hom structure is supplied (a parametric "distinguished morphism to kill" version), documenting the Rng-shaped motivation in the header.
- Suggested path: extend `Structure/Kernel.v` or add `Structure/Kernel/Universal.v`. Donors: `Structure/Kernel.v`, `Structure/UniversalProperty.v`, the universal-element API (see dependency).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Kernel/Universal.v` (or the extended file) compiles standalone
- `Print Assumptions` on the kernel-representability theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 59

## Dependencies
Depends on: maclane:III.1:def2

<!-- catalog: {"ids":["maclane:III.1:remark4"],"deps":["maclane:III.1:def2"]} -->
---8<---
```yaml
title: "MacLane III.1: The free vector space on a set as a universal arrow"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book p. 56 (PDF p. 65). Items: `maclane:III.1:construction1`.

## Background
The vector space of formal K-linear combinations on a set X, with its insertion-of-basis map, is the paradigm universal arrow to the forgetful functor Vect_K ⟶ Set: every function from X into a vector space extends to a unique linear map. See [nLab: free module](https://ncatlab.org/nlab/show/free+module) and [Wikipedia: Free module](https://en.wikipedia.org/wiki/Free_module).

## Current state in the library
Absent. No category of vector spaces or modules exists anywhere in-tree (`rg 'vector space|Vect|linear map|K-linear'` finds only background-essay prose, e.g. `Theory/Functor.v:68`, `Structure/Monoidal.v:78`); the `Instance/` listing has no linear-algebra instance, and no formal-linear-combination construction exists. `Theory/Universal/Arrow.v` supplies the universal-arrow vocabulary the statement needs.

## Work to be done
- Over the module-category infrastructure of #258 (K-Mod at a field K, i.e. Vect_K), construct the free vector space `V_X` of finitely supported K-valued functions on a setoid X, with the basis insertion `j : X → U(V_X)`.
- Prove `⟨V_X, j⟩` is a universal arrow from X to the forgetful functor (unique linear extension of any function into U(W)), and package the resulting free ⊣ forgetful adjunction via `AdjunctionFromUniversalArrows`.
- Suggested path: `Instance/Vect/Free.v` (or wherever #258 places the module categories). Donors: `Theory/Universal/Arrow.v`, `Construction/Free/Quiver.v` (the existing free-object pattern), `Instance/CMon.v` (algebraic-object-over-setoids style). The finite-dimensional fragment of #244 may also serve as a stepping stone.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the universal arrow and the adjunction)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Vect/Free.v` compiles standalone after its dependencies
- `Print Assumptions` on the universal-arrow witness prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 56

## Dependencies
Depends on: #258

<!-- catalog: {"ids":["maclane:III.1:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: The tensor product as a universal element of the bilinear-maps functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction6]
deps_item_ids: [maclane:III.1:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book p. 58 (PDF p. 67). Items: `maclane:III.1:construction6`.

## Background
The tensor product V ⊗ V′ with its canonical bilinear map is the universal element of the functor W ↦ Bilin(V, V′; W): every bilinear map out of V × V′ factors through it by a unique linear map. See [Wikipedia: Tensor product](https://en.wikipedia.org/wiki/Tensor_product).

## Current state in the library
Absent. `rg 'bilinear|Bilin'` finds only prose (Ab-enrichment essays in `Structure/Preadditive.v:16`, `Construction/Enriched.v:28`, Frobenius pairings in `Theory/Algebra/Frobenius.v:56`); there is no category of vector spaces or modules (see `maclane:III.1:construction1`), no bilinear-map type, and no tensor-product-by-universal-property construction — the library's abstract monoidal `⨂` is structure data on a category, never constructed from bilinear maps. No tensor product of commutative monoids exists in `Instance/CMon*` either.

## Work to be done
- Over the module categories of #258, define bilinear maps and the functor `Bilin(V, V′; −) : Vect_K ⟶ Sets`.
- Construct V ⊗ V′ (e.g. free vector space on the product carrier modulo the bilinearity relations, using the library's setoid-quotient idiom of `Instance/Sets/Coend.v`/`Instance/Sets/Pushout.v`) and prove ⟨V ⊗ V′, ⊗⟩ is a universal element of `Bilin(V, V′; −)`.
- Note the commutative-ring/module generality in the header; formalize at whatever generality #258 provides.
- Suggested path: `Instance/Vect/Tensor.v`. Donors: `Theory/Universal/Arrow.v`, the universal-element API (dependency below), `Instance/Sets/Coend.v` (inductive setoid quotient pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Vect/Tensor.v` compiles standalone after its dependencies
- `Print Assumptions` on the universal-element theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 58

## Dependencies
Depends on: #258
Depends on: maclane:III.1:def2

<!-- catalog: {"ids":["maclane:III.1:construction6"],"deps":["maclane:III.1:def2"]} -->
---8<---
```yaml
title: "MacLane III.1: The field of quotients as a universal arrow"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction2]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book p. 56 (PDF p. 65). Items: `maclane:III.1:construction2`.

## Background
The field of fractions Q(D) of an integral domain, with its embedding, is a universal arrow from D to the forgetful functor from fields to domains-with-monomorphisms; Mac Lane pairs this with a cautionary non-example — over the category of domains with all homomorphisms, no universal arrow from ℤ to the forgetful functor exists, since the maps ℤ → ℤ/p cannot factor through one field. See [nLab: field of fractions](https://ncatlab.org/nlab/show/field+of+fractions) and [Wikipedia: Field of fractions](https://en.wikipedia.org/wiki/Field_of_fractions).

## Current state in the library
Absent. `rg 'field of quotient|fraction|integral domain'` hits only the historical essay in `Theory/Universal/Arrow.v:44-45` and the ring-localization analogy prose of `Construction/Localization.v:61-74` (categorical orthogonal-subcategory localization — name-adjacent, a different object). No category of fields or integral domains exists, and no ℤ-as-initial-ring machinery for the non-existence example.

## Work to be done
- Over the ring infrastructure of #232 (which files the field-of-quotients *functor* from MacLane I.3), define the categories Fld and Dom_m (domains, monomorphisms only) if not already present, and prove ⟨Q(D), j⟩ is a universal arrow from D to the forgetful Fld ⟶ Dom_m.
- Formalize the non-existence half: over Dom (all homomorphisms), no universal arrow from ℤ to the forgetful functor exists — via the characteristic obstruction with the quotient maps to ℤ/p.
- Suggested path: alongside #232's module (e.g. `Instance/Dom/Fractions.v`). Donors: `Theory/Universal/Arrow.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (universal arrow + non-existence theorem)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new file>` compiles standalone after its dependencies
- `Print Assumptions` on both principal theorems prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 56

## Dependencies
Depends on: #232

<!-- catalog: {"ids":["maclane:III.1:construction2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Metric-space completion as a universal arrow"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book pp. 56–57 (PDF pp. 65–66). Items: `maclane:III.1:construction3`.

## Background
The completion of a metric space, with its isometric embedding, is a universal arrow from the space to the inclusion of complete metric spaces into Met (metric spaces with metric-preserving maps); uniqueness of universal arrows then gives uniqueness of the completion up to unique isomorphism. See [Wikipedia: Complete metric space](https://en.wikipedia.org/wiki/Complete_metric_space).

## Current state in the library
Absent. `rg '\bmetric\b|cauchy sequence'` finds only Lawvere generalized-metric-space prose in background essays (`Theory/Profunctor.v:46,100`, `Construction/Enriched.v:40-75`, `Instance/Poset.v:39,75`); no Met category or metric structure is formalized. `Construction/Karoubi/Universal.v:416` defines `CauchyComplete := IdempotentsSplit` — the categorical Cauchy completeness, a same-name trap, not this construction.

## Work to be done
- Define the category `Met` of metric spaces (setoid carriers with a rational- or real-valued distance; choose a constructively workable metric codomain and document the choice) and the full subcategory of complete spaces.
- Construct the completion (e.g. Cauchy sequences modulo the null-distance relation, the standard setoid quotient) and prove the embedding is a universal arrow to the inclusion functor; derive uniqueness up to unique iso from the universal-arrow machinery.
- Suggested path: `Instance/Met.v` + `Instance/Met/Completion.v`. Donors: `Theory/Universal/Arrow.v`, `Structure/UniversalProperty.v`, `Instance/Sets` quotient idioms.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping; if classical reals are unavoidable the file lives in the instance layer and the axiom use is recorded in docs/AXIOMS.md)
- [ ] `Print Assumptions` reported for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Met/Completion.v` compiles standalone after its dependencies
- `Print Assumptions` on the universal-arrow witness (expected closed, or with the documented stdlib-real axioms only)
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, pp. 56–57

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.1:construction3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Free modules and polynomial rings as universal arrows"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:remark2, maclane:III.1:ex7]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book pp. 56 and 59 (PDF pp. 65, 68). Items: `maclane:III.1:remark2`, `maclane:III.1:ex7`.

## Background
Mac Lane's roster of free constructions as universal arrows to forgetful functors: free category on a graph, free monoid, free group, free R-module, and the polynomial algebra K[x] over a commutative ring (Exercise 7 asks for the last as a universal construction — K[x] with the insertion of x is universal among rings-under-K with a chosen element). See [nLab: free functor](https://ncatlab.org/nlab/show/free+functor) and [Wikipedia: Polynomial ring](https://en.wikipedia.org/wiki/Polynomial_ring).

## Current state in the library
Of the five examples only the free category on a graph is formalized, at full strength: `Construction/Free/Quiver.v:518` (`UniversalArrowQuiverCat`) with `FreeForgetfulAdjunction` (lines 547–551). The free monoid and free group are the subject of the filed issues #296 and #298 respectively. The free R-module and the polynomial algebra have no in-tree counterpart and no host categories: `Theory/Algebra/Monoid/Hom.v:83` gives internal monoids `Mon(C)` with a forgetful functor but no free objects, `Instance/CMon.v` has `CMon_Forget` without a free-object universal arrow, and the free monoid appears only in prose comments (`Theory/Coq/List/Proofs.v:16-21`).

## Work to be done
This issue covers the increment not already filed: the free R-module and the polynomial ring.
- Over #258's module categories, construct the free R-module on a setoid and prove its insertion of generators a universal arrow to the forgetful functor (the K-a-field case coincides with the free vector space issue; keep the general-R statement here).
- Over #257's ring infrastructure, construct K[x] for a commutative ring K and prove universality: for any commutative K-algebra (or ring under K) with a chosen element, there is a unique map from K[x] sending x to it.
- Record in the file header that the free-category (in-tree), free-monoid (#296), and free-group (#298) instances complete Mac Lane's roster.
- Suggested paths: `Instance/Mod/Free.v`, `Instance/Rng/Polynomial.v` (aligned with #257/#258's layout). Donors: `Theory/Universal/Arrow.v`, `Construction/Free/Quiver.v` (pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on both universal-arrow witnesses prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, pp. 56 and 59

## Dependencies
Depends on: #257
Depends on: #258
Related (cover the other roster entries, no code dependency): #296, #298

<!-- catalog: {"ids":["maclane:III.1:remark2","maclane:III.1:ex7"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Group rings, tensor algebras, and exterior algebras as universal arrows"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.1:ex1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, Exercise 1, book p. 59 (PDF p. 68). Items: `maclane:III.1:ex1`.

## Background
The exercise asks for three classical constructions to be exhibited as universal arrows: the integral group ring (better, monoid ring) as left adjoint data to the unit-group/monoid functor, the tensor algebra as the free algebra on a vector space, and the exterior algebra as the universal target of an alternating construction. See [Wikipedia: Tensor algebra](https://en.wikipedia.org/wiki/Tensor_algebra) and [Wikipedia: Group ring](https://en.wikipedia.org/wiki/Group_ring).

## Current state in the library
Absent. `rg -i 'group ring|monoid ring|group algebra|tensor algebra|exterior algebra'` finds only a background-essay mention of group algebras in `Theory/Algebra/Frobenius.v:57`; the `free algebra` hits are F-algebra/monad-algebra material (`Monad/Eilenberg/Moore/Adjunction.v`, `Instance/Comp.v`), not associative algebras over a ring. No categories of rings, K-algebras, or vector spaces exist in `Instance/` to host the constructions.

## Work to be done
- Over #257 (rings) and #258 (modules): define the monoid ring Z[M] (or R[M]) and prove its insertion of the monoid a universal arrow to the units/underlying-monoid forgetful functor; `Theory/Algebra/Monoid/Hom.v`'s `Mon` may serve as the domain category.
- Define the tensor algebra T(V) with its insertion V → T(V) universal among linear maps into associative K-algebras, and the exterior algebra Λ(V) universal among alternating such maps (the tensor-product machinery of `maclane:III.1:construction6` is the natural stepping stone).
- Scope note: one PR bundling the three is acceptable only if the algebra-category substrate from the dependencies is already in place; otherwise split at the maintainer's discretion.
- Suggested paths: `Instance/Rng/MonoidRing.v`, `Instance/Vect/TensorAlgebra.v`. Donors: `Theory/Universal/Arrow.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on each universal-arrow witness prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, p. 59, Exercise 1

## Dependencies
Depends on: #257
Depends on: #258

<!-- catalog: {"ids":["maclane:III.1:ex1"],"deps":[]} -->

---8<---
```yaml
title: "MacLane III.1: A universal element for the contravariant power-set functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.1:ex2]
deps_item_ids: [maclane:III.1:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, Exercise 2, book p. 59 (PDF p. 68). Items: `maclane:III.1:ex2`.

## Background
The exercise asks for a universal element of the contravariant power-set functor — classically the pair ⟨2, {1}⟩: every subset is the preimage of the distinguished value under a unique characteristic map, the germ of the subobject classifier. See [nLab: subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier).

## Current state in the library
The classification content is well developed abstractly: `Structure/SubobjectClassifier.v:44` (class with Ω, `truth`, `char`, classifying pullback + uniqueness) and `classifier_classifies : SubObj x ≅ (x ~> Ω)` per object (line 187); `Theory/Subobject/Functor.v:180` gives the contravariant `Sub : C^op ⟶ Sets` presheaf; `Instance/FinSet/Classifier.v:353` realizes Ω = 2 decidably on finite sets; `Instance/Sets/Classifier.v` proves the Sets story as cross-universe theorems (truth values one level up, a disclosed size obstruction). Missing relative to the exercise as posed: (1) no power-set functor on a set-like category with a III.1-style universal-element statement; (2) representability is per-object, not the natural isomorphism `Sub ≅ Hom(−, Ω)` of functors.

## Work to be done
- Define the contravariant power-set functor in the concrete setting where it exists at one universe level (FinSet: subsets as decidable predicates/monos; Ω = 2), and state its universal element ⟨2, distinguished value⟩ in the elementary III.1 form, connecting it to `FinSet_Classifier`.
- Upgrade the per-object `classifier_classifies` to a natural isomorphism `Sub ≅ Hom(−, Ω)` in `[C^op, Sets]` for any `SubobjectClassifier`, and note in the header why Sets itself only supports the cross-universe reading (per `Instance/Sets/Classifier.v`).
- Suggested paths: `Instance/FinSet/PowerSet.v`; extend `Structure/SubobjectClassifier.v` for the natural-iso upgrade. Donors: `Theory/Subobject/Functor.v`, `Functor/Hom/Yoneda.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/FinSet/PowerSet.v` compiles standalone after its dependencies
- `Print Assumptions` on the universal-element witness and the natural-iso upgrade prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.1, p. 59, Exercise 2

## Dependencies
Depends on: #227
Depends on: maclane:III.1:def2

<!-- catalog: {"ids":["maclane:III.1:ex2"],"deps":["maclane:III.1:def2"]} -->
---8<---
```yaml
title: "MacLane III.1: Universal arrows to the standard forgetful functors"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.1:ex3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, Exercise 3, book p. 59 (PDF p. 68). Items: `maclane:III.1:ex3`.

## Background
The exercise asks, from any object of the codomain, for a universal arrow to each of four forgetful functors: Ab ⟶ Grp (abelianization), Rng ⟶ Ab (forgetting multiplication; free ring), Top ⟶ Set (discrete topology), and Set∗ ⟶ Set (adjoining a basepoint). See [Wikipedia: Forgetful functor](https://en.wikipedia.org/wiki/Forgetful_functor) and [nLab: free functor](https://ncatlab.org/nlab/show/free+functor).

## Current state in the library
Absent. No Grp/Ab/Rng/Top/Set∗ categories exist in `Instance/` (listing checked; `Structure/Group.v` is internal group objects, a same-name trap); `abelianization` appears only in a background comment (`Construction/Localization.v:106`); `Instance/Coq/Par.v` notes an equivalence with pointed sets in a comment but carries no forgetful functor or universal arrow (verified: no adjunction hits in `Instance/Coq/Par.v`, `Instance/Sets/Par.v`).

## Work to be done
- For each pair, construct the universal arrow once the host categories exist: abelianization unit G → U(G/[G,G]) (functor filed as #229); the free-ring-on-an-abelian-group unit (tensor-algebra style over ℤ); the discrete-space unit X → U(X_disc); and the basepoint-adjunction unit X → U(X ⊔ {∗}) — the last is achievable now against `Instance/Sets/Par.v`/`Instance/Coq/Par.v` if pointed sets are realized as partial maps per #261.
- Package each as `UniversalArrow`/`AdjunctionFromUniversalArrows` instances.
- Suggested paths: alongside the respective instance categories (`Instance/Grp/Abelianize.v`, `Instance/Rng/Free.v`, `Instance/Top/Discrete.v`, `Instance/Sets/Pointed.v`). Donors: `Theory/Universal/Arrow.v`, `Construction/Free/Quiver.v` (pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on each universal-arrow witness prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, p. 59, Exercise 3

## Dependencies
Depends on: #229
Depends on: #255
Depends on: #256
Depends on: #257
Depends on: #259
Depends on: #261

<!-- catalog: {"ids":["maclane:III.1:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Quotient groups and the isomorphism theorems by universality"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction5, maclane:III.1:ex4]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, book pp. 57–59 (PDF pp. 66–68). Items: `maclane:III.1:construction5`, `maclane:III.1:ex4`.

## Background
For N normal in G, the projection G → G/N is a universal element of the functor of homomorphisms killing N; Mac Lane stresses that all further properties of quotient groups — in particular the second and third isomorphism theorems (Exercise 4) — follow from this universality alone, without mentioning cosets again. See [Wikipedia: Quotient group](https://en.wikipedia.org/wiki/Quotient_group) and [Wikipedia: Isomorphism theorems](https://en.wikipedia.org/wiki/Isomorphism_theorems).

## Current state in the library
Absent. `rg 'quotient group|normal subgroup|coset|isomorphism theorem'` returns zero formal hits; `Structure/Group.v` defines internal group objects with no quotient machinery; no category Grp exists (`Instance/` listing checked). `Construction/Quotient.v` quotients a category's hom-setoids by a congruence — a different notion.

## Work to be done
- Over #255's Grp: define normal subgroups and the quotient G/N (setoid-quotient style), prove ⟨G/N, p⟩ a universal element of the kills-N homomorphism functor Grp ⟶ Sets.
- Derive, using only that universality: (a) (G/M)/(N/M) ≅ G/N for M ⊆ N both normal in G; (b) SN/N ≅ S/(S ∩ N) for S a subgroup and N normal — i.e. the third and second isomorphism theorems, proved by universal-property chases rather than coset manipulation.
- Suggested path: `Instance/Grp/Quotient.v`. Donors: `Theory/Universal/Arrow.v`, `Structure/UniversalProperty.v`, the Sets quotient idioms (`Instance/Sets/Pushout.v`).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (quotient universality + both isomorphism theorems)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Grp/Quotient.v` compiles standalone after its dependencies
- `Print Assumptions` on the universality witness and both isomorphism theorems prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, pp. 57 and 59

## Dependencies
Depends on: #255

<!-- catalog: {"ids":["maclane:III.1:construction5","maclane:III.1:ex4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Quotient modules and quotient rings by universality"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.1:ex5, maclane:III.1:ex6]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1, Exercises 5–6, book p. 59 (PDF p. 68). Items: `maclane:III.1:ex5`, `maclane:III.1:ex6`.

## Background
The quotient module A/S and the quotient of a ring by a two-sided ideal both admit descriptions by universality (maps killing the submodule/ideal factor uniquely through the projection), from which the module isomorphism theorems follow. See [Wikipedia: Quotient ring](https://en.wikipedia.org/wiki/Quotient_ring) and [Wikipedia: Universal property](https://en.wikipedia.org/wiki/Universal_property).

## Current state in the library
Absent. `rg -i 'submodule|quotient module|quotient ring|\bideal\b'` finds only background-essay comments (`Structure/Abelian.v:69,111`); no module or ring categories exist in-tree, and no isomorphism-theorem statements anywhere.

## Work to be done
- Over #258's R-Mod: define submodules and quotients A/S, prove the projection a universal element of the kills-S functor, derive the module isomorphism theorems by universality (mirroring the group case).
- Over #257's Rng: define two-sided ideals and quotient rings R/I with the analogous universal description.
- Suggested paths: `Instance/Mod/Quotient.v`, `Instance/Rng/Quotient.v`. Donors: the quotient-groups development (`maclane:III.1:construction5`, same pattern), `Theory/Universal/Arrow.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.1 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on each universality witness prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1, p. 59, Exercises 5–6

## Dependencies
Depends on: #257
Depends on: #258

<!-- catalog: {"ids":["maclane:III.1:ex5","maclane:III.1:ex6"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.1: Quotient setoids and coequalizers in Sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.1:construction4, maclane:III.3:remark2, maclane:III.3:ex5]
deps_item_ids: [maclane:III.1:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.1 p. 57 (PDF p. 66), §III.3 pp. 65 and 68 (PDF pp. 74, 77). Items: `maclane:III.1:construction4`, `maclane:III.3:remark2`, `maclane:III.3:ex5`.

## Background
The quotient of a set by an equivalence relation is universal among E-respecting functions (§III.1); in Set the coequalizer of a parallel pair is the quotient by the generated equivalence relation, and the quotient X/E itself is the coequalizer of the two projections E ⇉ X (§III.3, Exercise 5). See [nLab: coequalizer](https://ncatlab.org/nlab/show/coequalizer) and [Wikipedia: Equivalence class](https://en.wikipedia.org/wiki/Equivalence_class).

## Current state in the library
The technique exists only in cognate special cases: `Instance/Sets/Pushout.v:185` (`Sets_HasPushouts`) quotients a coproduct by an inductively generated equivalence closure with a proven unique-factorization UMP, and `Instance/Sets/Coend.v` quotients by the dinaturality relation. But there is no general quotient-setoid construction S/E with the E-respecting-functions universal property, no coequalizers in Sets at all (`rg 'Coequalizer' Instance/Sets/` — 0 hits; `Structure/Equalizer.v:95` carries the Set description as header prose only), and no identification of X/E with the coequalizer of the projection pair.

## Work to be done
- Define the quotient setoid S/E for an arbitrary (setoid-respecting) equivalence relation E, with projection p, and prove ⟨S/E, p⟩ a universal element of the functor sending X to the setoid of E-respecting morphisms S → X.
- Construct `Sets_HasCoequalizers : HasCoequalizers Sets` — the coequalizer of f, g as the quotient of the codomain by the equivalence closure of {f x ~ g x} (the `pushout_eq` idiom of `Instance/Sets/Pushout.v`, transposed).
- Prove X/E is the coequalizer of the two projections from the relation setoid E ⇉ X.
- Suggested paths: `Instance/Sets/Quotient.v`, `Instance/Sets/Coequalizer.v`. Donors: `Instance/Sets/Pushout.v`, `Instance/Sets/Coend.v`, `Structure/Coequalizer.v` (the `IsCoequalizer` API).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §§III.1, III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`Sets_HasCoequalizers`, the quotient universality, the X/E identification)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Sets/Coequalizer.v` compiles standalone after its dependencies
- `Print Assumptions Sets_HasCoequalizers.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.1 p. 57 and §III.3 pp. 65, 68 (the Ab and Top clauses of §III.3's remark are host-category-gated and out of this issue's scope; see #256/#259)

## Dependencies
Depends on: maclane:III.1:def2

<!-- catalog: {"ids":["maclane:III.1:construction4","maclane:III.3:remark2","maclane:III.3:ex5"],"deps":["maclane:III.1:def2"]} -->
---8<---
```yaml
title: "MacLane III.2: Naturality of the Yoneda isomorphism in both variables"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.2:lem2]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.2, book p. 61 (PDF p. 70). Items: `maclane:III.2:lem2`.

## Background
Mac Lane's addendum to the Yoneda lemma: the bijection Nat(D(r,−), K) ≅ K r is natural in both K and r, i.e. it is a natural isomorphism between the evaluation bifunctor E⟨K, r⟩ = K r and the Nat-bifunctor N⟨K, r⟩ = Nat(D(r,−), K), both on Set^D × D. See [nLab: Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma).

## Current state in the library
Only the component isomorphisms exist: `Functor/Hom/Yoneda.v:133` (`Yoneda_Lemma`) and `:182` (`Covariant_Yoneda_Lemma`) give the Sets-iso at every pair (F, A), but no bifunctor `N : [C, Sets] ∏ C ⟶ Sets` is constructed, no evaluation bifunctor is packaged for this purpose (evaluation exists only implicitly as the counit of `Cat_Closed`, `Instance/Cat/Cartesian/Closed.v:47`), and no naturality square of the Yoneda family in either variable is stated (the file's header claims binaturality in prose only, line 22).

## Work to be done
- Construct the evaluation bifunctor `E : [C, Sets] ∏ C ⟶ Sets` and the Nat-bifunctor `N : [C, Sets] ∏ C ⟶ Sets`, ⟨F, A⟩ ↦ the hom-setoid `[C, Sets]([Hom A,─], F)`, with the action on arrows ⟨τ, f⟩ by whiskering/precomposition.
- Prove the Yoneda family assembles into a natural isomorphism `N ≅ E` in `[[C, Sets] ∏ C, Sets]`; state the contravariant twin over `Presheaves`.
- Suggested path: `Functor/Hom/Yoneda/Natural.v`. Donors: `Functor/Hom/Yoneda.v`, `Functor/Bifunctor.v`, `Instance/Fun.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.2 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both bifunctors, the natural iso)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Functor/Hom/Yoneda/Natural.v` compiles standalone after its dependencies
- `Print Assumptions` on the natural isomorphism prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.2, p. 61

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.2:lem2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.2: Representations are functorial in natural transformations"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.2:ex1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.2, Exercise 1, book p. 62 (PDF p. 71). Items: `maclane:III.2:ex1`.

## Background
Given representations ⟨r, ψ⟩ of K and ⟨r′, ψ′⟩ of K′, every natural transformation τ : K ⟹ K′ is induced by a unique arrow h : r′ → r between the representing objects, compatibly with both representations. See [nLab: representable functor](https://ncatlab.org/nlab/show/representable+functor).

## Current state in the library
Only the τ = id case exists: `Structure/UniversalProperty.v:112` (`univ_property_unique`) and `:175` (`univ_property_unique_up_to_unique_iso`) give the unique compatible isomorphism between two objects representing the same functor. The general statement is an immediate corollary of `Yoneda_Embedding'` (`Functor/Hom.v:109`, transport τ to ψ′⁻¹ ∘ τ ∘ ψ and apply the hom-bijection) but is nowhere stated; no functoriality-of-representations lemma exists (verified by usage sweep of `Representable`).

## Work to be done
- State and prove: for `Representable` instances of K and K′ and any τ : K ⟹ K′, there is a unique `h : repr_obj K' ~> repr_obj K` with `τ ∘ represented ≈ represented' ∘ fmap[Curried_Hom] h` (up to the library's variance conventions).
- Derive the τ = id case as a corollary, cross-linking `univ_property_unique_up_to_unique_iso`, and (optionally) package "take the representing object" as a functor from a category of represented functors.
- Suggested path: extend `Functor/Representable.v`. Donors: `Functor/Hom.v` (`Yoneda_Full`/`Yoneda_Faithful`/`Yoneda_Embedding'`), `Structure/UniversalProperty.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.2 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] File(s) registered in `_CoqProject` (if new)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Functor/Representable.v` compiles standalone after its dependencies
- `Print Assumptions` on the induced-arrow theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.2, p. 62, Exercise 1

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.2:ex1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.2: Naturality is unchanged by enlarging the codomain"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.2:ex4, maclane:III.2:remark1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.2, Exercise 4 and the large-categories remark, book p. 62 (PDF p. 71). Items: `maclane:III.2:ex4`, `maclane:III.2:remark1`.

## Background
For a full subcategory inclusion J : E ↪ E′ and functors K, L : D ⟶ E, the natural transformations K ⟹ L computed in E and those J∘K ⟹ J∘L computed in E′ coincide — the reason enlarging the ambient category of sets does not change what "natural" means, which underwrites the Yoneda lemma for large categories. See [nLab: full subcategory](https://ncatlab.org/nlab/show/full+subcategory).

## Current state in the library
Absent as a statement. `Construction/Subcategory.v`'s `Full`/`Full_Implies_Full_Functor` concern hom-level fullness of the inclusion, not Nat-setoids of functor categories; no postcomposition functor `[D, E] ⟶ [D, E′]` along a functor J is defined anywhere, hence no full/faithfulness result for it (whisker lemmas in `Instance/Fun.v` are internal to one functor category). The large-categories remark itself is realized foundationally by universe polymorphism (`Lib/Setoid.v:10`), with exactly this invariance clause as its unformalized residue.

## Work to be done
- Define the postcomposition functor `J ∘ − : [D, E] ⟶ [D, E′]` for any J : E ⟶ E′.
- Prove it faithful when J is, and full when J is full and faithful — yielding the Nat-setoid isomorphism `Nat(K, L) ≅ Nat(J∘K, J∘L)` for a fully faithful (e.g. full-subcategory) J.
- Add a short header note connecting this to the universe-polymorphic Yoneda story (the remark's enlargement-invariance clause).
- Suggested path: `Functor/Construction/Postcompose.v` (or extend `Instance/Fun.v`). Donors: `Construction/Subcategory.v`, `Instance/Fun.v`, `Theory/Functor.v` (`Full`/`Faithful`).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.2 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Functor/Construction/Postcompose.v` compiles standalone after its dependencies
- `Print Assumptions` on the Nat-setoid isomorphism prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.2, p. 62

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.2:ex4","maclane:III.2:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.2: Kan's coyoneda lemma over the category of elements"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.2:ex3]
deps_item_ids: [maclane:III.7:construction1]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.2, Exercise 3, book p. 62 (PDF p. 71). Items: `maclane:III.2:ex3`.

## Background
Kan's form of the coyoneda lemma: for K : D ⟶ Set with category of elements (∗ ↓ K), projection Q to D, and a the constant functor at an object a, there is a natural isomorphism Nat(K, D(a,−)) ≅ Nat(Δa, Q) — maps out of K into a representable correspond to cones from the constant functor to the elements projection. See [nLab: co-Yoneda lemma](https://ncatlab.org/nlab/show/co-Yoneda+lemma) and [nLab: category of elements](https://ncatlab.org/nlab/show/category+of+elements).

## Current state in the library
Absent. No category-of-elements construction exists (`Construction/Grothendieck.v:108` mentions el(F) in prose only; no (∗ ↓ K) comma instance for Sets-valued K is built); `Theory/Coend/Yoneda.v`'s `coyoneda_reduction` (∫^x C(x,c) × F x ≅ F c) is a different theorem sharing the name — checked and rejected as a same-name trap in verification.

## Work to be done
- Over the category-of-elements construction (dependency below), state and prove the natural isomorphism `Nat(K, [Hom a,─]) ≅ Nat(Δa, Q)` where Q is the elements projection and Δa the constant functor.
- Establish naturality in a (the two sides as functors of a), matching the exercise's "natural isomorphism" reading.
- Suggested path: `Construction/Elements/Kan.v`. Donors: `Functor/Hom/Yoneda.v`, `Functor/Diagonal.v`, `Construction/Comma.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.2 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Construction/Elements/Kan.v` compiles standalone after its dependencies
- `Print Assumptions` on the isomorphism prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.2, p. 62, Exercise 3

## Dependencies
Depends on: maclane:III.7:construction1

<!-- catalog: {"ids":["maclane:III.2:ex3"],"deps":["maclane:III.7:construction1"]} -->

---8<---
```yaml
title: "MacLane III.3: Indexed coproducts"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:def2]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, book p. 64 (PDF p. 73). Items: `maclane:III.3:def2`.

## Background
For a set X as a discrete category, the X-fold coproduct of a family {a_x} is an object with injections through which every family of arrows out factors uniquely — equivalently, a bijection C(⊔ₓ aₓ, c) ≅ ∏ₓ C(aₓ, c) natural in c. See [nLab: coproduct](https://ncatlab.org/nlab/show/coproduct).

## Current state in the library
The product side is fully developed — `Structure/Limit/Product.v` (`IsIndexedProduct`:51, `iprod`:93, `iprod_proj`:98, `iprod_ump`:105, `HasIndexedProducts`:128 over `Instance/Discrete.v`) — but the coproduct dual is only expressible, not developed: `Colimit (DiscreteCat_Functor f)` states it (`Structure/Limit.v:158`), yet there is no `icoprod`/injection/UMP accessor pack, no `HasIndexedCoproducts` class, and the natural bijection C(⊔ₓ aₓ, c) ≅ ∏ₓ C(aₓ, c) is nowhere stated (searches: `IndexedCoproduct|icoprod|HasIndexedCoproducts` — 0 hits). Only the binary case is complete via `Structure/Cocartesian.v`.

## Work to be done
- Build the exact dual of `Structure/Limit/Product.v`: `IsIndexedCoproduct`, `icoprod`/`icoprod_inj`/`icoprod_ump` reading a `Colimit (DiscreteCat_Functor f)`, the bridge `colimit_is_indexed_coproduct`, and `HasIndexedCoproducts`.
- State the hom-setoid bijection `C(⊔ₓ aₓ, c) ≅ ∏ₓ C(aₓ, c)` natural in c (the ∏ as the dependent-function setoid, the library's Sets idiom).
- The Sets witness (X-fold disjoint union) is the scope of the filed issue #254 and is not duplicated here; cross-link it in the header.
- Suggested path: `Structure/Limit/Coproduct.v`. Donors: `Structure/Limit/Product.v`, `Instance/Discrete.v`, `Structure/Limit/Preservation.v` (covariant colimit accessors).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`icoprod_ump`, the hom bijection)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Limit/Coproduct.v` compiles standalone after its dependencies
- `Print Assumptions icoprod_ump.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, p. 64

## Dependencies
Related: #254 (indexed products and coproducts in Sets — supplies the concrete witness; no code dependency in either direction).

<!-- catalog: {"ids":["maclane:III.3:def2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Powers and copowers of an object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.4:def4, maclane:III.3:def3]
deps_item_ids: [maclane:III.3:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3 p. 64 (PDF p. 73) and §III.4 p. 70 (PDF p. 79). Items: `maclane:III.4:def4`, `maclane:III.3:def3`.

## Background
The power b^J is the product of a constant J-indexed family, characterized by C(c, b)^J ≅ C(c, b^J); dually the copower J · b is the constant-family coproduct with C(J · b, c) ≅ C(b, c)^J (in Set, J · Y is the cartesian product J × Y). See [nLab: copower](https://ncatlab.org/nlab/show/copower) and [nLab: powering](https://ncatlab.org/nlab/show/power).

## Current state in the library
No named power or copower exists. `rg 'copower|copow'` — 0 hits; the `power` hits are all different concepts (cartesian-closed exponentials `Structure/Cartesian/Closed.v`, topos power objects `Pow a := Ω^a` in `Structure/Topos.v:75`, Lawvere `law_pow`). Powers occur only as anonymous instantiations of `iprod` at constant families — one is load-bearing in the GAFT spine (`Theory/WeaklyInitial.v:89`, the endomorphism-indexed power). The characterizing isomorphisms are nowhere stated. Near-miss recorded in verification: `WeightedColimit` at the one-object shape (`Structure/Limit/Weighted.v:370`) would be the copower but is never instantiated.

## Work to be done
- Define `power (J : Type) (b : C)` as `iprod (fun _ : J => b)` with notation, and prove `C(c, b^J) ≅ (J → C(c, b))` (the Sets-power of the hom-setoid), natural in c.
- Define the dual `copower` over the indexed-coproduct API (dependency below) with `C(J · b, c) ≅ (J → C(b, c))`; prove the Set example `J · Y ≅ J × Y` in Sets once #254's coproducts land.
- Refactor opportunity (optional checklist item): re-express `Theory/WeaklyInitial.v`'s anonymous endomorphism power and `Adjunction/SAFT.v`'s `cogen_power` through the named API.
- Suggested path: `Structure/Limit/Power.v`. Donors: `Structure/Limit/Product.v`, `Structure/Limit/Weighted.v` (header cross-reference).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §§III.3–III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both characterizing isomorphisms)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Limit/Power.v` compiles standalone after its dependencies
- `Print Assumptions` on both characterizing isomorphisms prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.3 p. 64 and §III.4 p. 70

## Dependencies
Depends on: maclane:III.3:def2

<!-- catalog: {"ids":["maclane:III.4:def4","maclane:III.3:def3"],"deps":["maclane:III.3:def2"]} -->
---8<---
```yaml
title: "MacLane III.3: Wide equalizers and wide coequalizers"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:construction2]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, book pp. 64–65 (PDF pp. 73–74). Items: `maclane:III.3:construction2`.

## Background
After presenting the coequalizer as a universal arrow over the walking parallel pair, Mac Lane notes that coequalizers of an arbitrary set of parallel maps a → b are defined the same way; these wide (co)equalizers appear later in the Freyd initial-object argument. See [nLab: wide pullback](https://ncatlab.org/nlab/show/wide+pullback) and [nLab: coequalizer](https://ncatlab.org/nlab/show/coequalizer).

## Current state in the library
The binary correspondence is complete in both directions (`Instance/Parallel.v`, `Coequalizer (APair f g) := Colimit`, `coequalizer_is_coequalizer` / `is_coequalizer_colimit` in `Structure/Coequalizer.v:226/275`). The arbitrary-arity generalization is absent: there is no wide-parallel shape category (only the two-arrow `Parallel`) and no wide-(co)equalizer definition; `rg 'wide (co)?equal|WideParallel'` finds only a prose mention of a wide-equalizer device in `Theory/WeaklyInitial.v:39`.

## Work to be done
- Define the wide parallel-pair shape `Parallel I` (two objects, an I-indexed family of arrows) generalizing `Instance/Parallel.v`, and the elementary records `IsWideEqualizer` / `IsWideCoequalizer` for a family {f_i : a → b}.
- Prove the round trips with `Limit`/`Colimit` over the wide shape, mirroring `Structure/Equalizer/Fork.v` and `Structure/Coequalizer.v`.
- Optional stretch (checklist item, may be split off): restate `Theory/WeaklyInitial.v`'s equalize-all-endomorphisms step through the wide-equalizer API.
- Suggested paths: `Instance/Parallel/Wide.v`, `Structure/Equalizer/Wide.v`, `Structure/Coequalizer/Wide.v`. Donors: `Instance/Parallel.v`, `Structure/Equalizer/Fork.v`, `Structure/Coequalizer.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both wide records and both round trips)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Coequalizer/Wide.v` compiles standalone after its dependencies
- `Print Assumptions` on the round-trip conversions prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, pp. 64–65

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.3:construction2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.3: Cokernel pairs and the pushout characterization of epimorphisms"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:def7, maclane:III.4:ex4]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3 p. 66 (PDF p. 75) and §III.4 Exercise 4, p. 72 (PDF p. 81). Items: `maclane:III.3:def7`, `maclane:III.4:ex4`.

## Background
The cokernel pair of f is the pushout of f with itself — a parallel pair u, v out of the codomain, universal among pairs coequalizing f; and f is an epimorphism exactly when the square on f with two identity legs is a pushout (its cokernel pair is trivial). See [nLab: kernel pair](https://ncatlab.org/nlab/show/kernel+pair) (dual notion) and [Wikipedia: Epimorphism](https://en.wikipedia.org/wiki/Epimorphism).

## Current state in the library
The general pushout is complete (`Structure/Pushout.v:47` `IsPushout := Pullback in C^op`, with `pushout_ump`, mediator kit, `HasPushouts`), and the exactly dual `kernel_pair := Pullback f f` is named and load-bearing (`Structure/Regular.v:46`). But `rg 'cokernel.?pair|CokernelPair'` returns 0 hits — the specialization `IsPushout f f` is never named or given API. For the epi characterization: no lemma relates `Epic` to any pushout square (`pullback_paste`/`monic_pullback_stable` exist in `Theory/Morphisms/Stability.v`; the dual mono-iff-identity-pullback is also absent).

## Work to be done
- Name `cokernel_pair f : IsPushout f f` (chosen form under `HasPushouts`, plus the one-off record form), with accessors for the parallel pair u, v, the equation u ∘ f ≈ v ∘ f, and the UMP stated on parallel pairs coequalizing f.
- Prove: f is `Epic` iff the square with both cotriangle legs the identity on the codomain is a pushout of f with f; derive the dual (`Monic` iff identity pullback square) for free via `C^op`.
- Suggested path: extend `Structure/Pushout.v` (a CokernelPair section) with the epi lemma in `Theory/Morphisms/Stability.v` or a sibling. Donors: `Structure/Regular.v` (`kernel_pair` pattern), `Structure/Pushout.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §§III.3–III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (cokernel-pair API, the epi iff theorem)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Pushout.v` (or the new file) compiles standalone
- `Print Assumptions` on the epi characterization prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.3 p. 66 and §III.4 p. 72, Exercise 4

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.3:def7","maclane:III.4:ex4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.3: Coproducts in the familiar algebraic and topological categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:remark1, maclane:III.3:ex1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, book pp. 63 and 68 (PDF pp. 72, 77). Items: `maclane:III.3:remark1`, `maclane:III.3:ex1`.

## Background
Mac Lane's roster of concrete coproducts: disjoint unions (Set, Top), wedge sums (Top∗), direct sums (Ab, R-Mod), free products (Grp), and — Exercise 1 — the tensor product R ⊗ S as the coproduct in commutative rings; in a preorder, coproducts are joins. See [Wikipedia: Coproduct](https://en.wikipedia.org/wiki/Coproduct) and [Wikipedia: Free product](https://en.wikipedia.org/wiki/Free_product).

## Current state in the library
The Set-style and preorder examples are witnessed: `Sets_Cocartesian` (`Instance/Sets/Cocartesian.v:28`), `Coq_Cocartesian` (`Instance/Coq.v:199`), `FinSet_Cocartesian` (`Instance/FinSet.v:250`), `Props_Cocartesian` (`Instance/Props.v:80`, the join example), `Cat_Cocartesian` (`Instance/Cat/Cocartesian.v:40`). The algebraic and topological examples are absent for want of host categories (no Ab, R-Mod, Grp, CRng, Top, Top∗ in-tree); the nearest relative is `Instance/CMon/Biproduct.v` (direct sums of commutative monoids).

## Work to be done
Once the host categories land (dependencies below), witness the remaining roster:
- Direct sum as coproduct in Ab and R-Mod (biproduct route, following `Instance/CMon/Biproduct.v`).
- Free product as coproduct in Grp.
- Tensor product R ⊗ S with r ↦ r⊗1, s ↦ 1⊗s as the coproduct diagram in commutative rings (Exercise 1; needs a CRng full subcategory of #257's rings).
- Disjoint union in Top and wedge sum in Top∗.
- Scope note: this is example-material spanning several substrates; split into per-category PRs at filing-follow-up time if any single piece (notably Grp free products) grows to PR size on its own.
- Suggested paths: alongside the respective instances (`Instance/Ab/Coproduct.v`, `Instance/Grp/FreeProduct.v`, `Instance/Rng/Tensor.v`, `Instance/Top/Coproduct.v`). Donors: `Structure/Cocartesian.v`, `Instance/CMon/Biproduct.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on each Cocartesian instance prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.3, pp. 63 and 68

## Dependencies
Depends on: #255
Depends on: #256
Depends on: #257
Depends on: #258
Depends on: #259
Depends on: #260

<!-- catalog: {"ids":["maclane:III.3:remark1","maclane:III.3:ex1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.3: Pushouts in Grp and Top; amalgamated products"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:remark3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, book p. 66 (PDF p. 75). Items: `maclane:III.3:remark3`.

## Background
Pushouts in Set glue a disjoint union along the span; the same construction with quotient topology gives pushouts in Top (adjunction spaces), and pushouts exist in Grp — with the classical refinement that when both legs are monic the pushout injections are monic and the vertex is the amalgamated product. See [nLab: pushout](https://ncatlab.org/nlab/show/pushout) and [Wikipedia: Free product](https://en.wikipedia.org/wiki/Free_product) (amalgamation).

## Current state in the library
The Set clause is fully present and constructively sharpened: `Sets_HasPushouts` (`Instance/Sets/Pushout.v:185`, quotient by the inductive glue closure, funext-free) and computable `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v:513`). The Top clause and the entire Grp clause are absent — no Top or Grp category in-tree, and `amalgam` has no formal hits (one prose mention in `Construction/Groupoid.v:62`).

## Work to be done
- Over #255's Grp: construct pushouts (free product with amalgamation, via generators-and-relations or a normal-form development), and prove the monic-legs refinement: f, g monic ⇒ the pushout injections are monic, identifying the vertex as the amalgamated product.
- Over #259's Top: pushouts by the quotient-topology construction (adjunction spaces as the motivating case).
- Suggested paths: `Instance/Grp/Pushout.v`, `Instance/Top/Pushout.v`. Donors: `Instance/Sets/Pushout.v` (glue-quotient pattern), `Structure/Pushout.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both HasPushouts instances, the monic-legs theorem)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Grp/Pushout.v` compiles standalone after its dependencies
- `Print Assumptions` on the amalgamated-product theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, p. 66

## Dependencies
Depends on: #255
Depends on: #259

<!-- catalog: {"ids":["maclane:III.3:remark3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Interdefinability of the finite (co)limit constructions"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.3:ex2, maclane:III.4:ex7, maclane:III.4:ex9, maclane:III.4:ex10]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3 Exercise 2, p. 68 (PDF p. 77); §III.4 Exercises 7, 9, 10, p. 72 (PDF p. 81). Items: `maclane:III.3:ex2`, `maclane:III.4:ex7`, `maclane:III.4:ex9`, `maclane:III.4:ex10`.

## Background
The classical reductions among finite (co)limit generators: binary coproducts + coequalizers yield pushouts (dually, products + equalizers yield pullbacks, giving kernel pairs as equalizers of the two composite projections); equalizers arise as pullbacks of the two pairings ⟨id, f⟩, ⟨id, g⟩; and pullbacks + a terminal object yield all finite products and equalizers. See [nLab: pullback](https://ncatlab.org/nlab/show/pullback) and [Wikipedia: Pullback (category theory)](https://en.wikipedia.org/wiki/Pullback_(category_theory)).

## Current state in the library
A disclosed in-tree gap: `Structure/Topos.v:22-24` states outright that the reduction of pullbacks to products and equalizers (and conversely) is not formalized, which is why `ElementaryTopos` carries terminal + products + pullbacks explicitly; `Structure/Pullback.v:254-274` carries the constructions only inside "jww TODO" comments; `Structure/Regular.v:26-30` and `Structure/Complete.v:49-51` state the facts as header prose. No lemma builds `IsPushout` from `Cocartesian` + coequalizers, kernel pairs from products + equalizers, equalizers from pullbacks of pairings, or `Cartesian`/`HasEqualizers` from `HasPullbacks` + `Terminal`.

## Work to be done
One coherent PR establishing the reduction toolkit:
- `Cartesian` + `HasEqualizers` ⇒ `HasPullbacks` (pullback as equalizer of the two composites out of the product), with the kernel-pair corollary (Exercise 7: kernel pair of f as equalizer of f∘p₁, f∘p₂), and the dual `Cocartesian` + `HasCoequalizers` ⇒ `HasPushouts` (Exercise III.3.2) by the library's `C^op` duality.
- `HasPullbacks` ⇒ equalizers via the pullback of ⟨id, f⟩ and ⟨id, g⟩ (Exercise 9; needs binary products for the pairings).
- `HasPullbacks` + `Terminal` ⇒ `Cartesian` and `HasEqualizers` (Exercise 10; products as pullbacks over the terminal object).
- Retire the corresponding TODO comments in `Structure/Pullback.v` and update the `Structure/Topos.v` disclosure.
- Suggested path: `Structure/Pullback/Reduction.v` (with the dual re-exports). Donors: `Structure/Pullback.v`, `Structure/Equalizer/Fork.v`, `Structure/Cartesian.v`, `Theory/Morphisms/Stability.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §§III.3–III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (all four reductions)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits (the retired `jww` TODOs should reduce the count)
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Pullback/Reduction.v` compiles standalone after its dependencies
- `Print Assumptions` on each reduction prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.3 p. 68 Ex. 2 and §III.4 p. 72 Ex. 7/9/10; confirm the `Structure/Topos.v` header disclosure is updated

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.3:ex2","maclane:III.4:ex7","maclane:III.4:ex9","maclane:III.4:ex10"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.3: Coequalizers in the matrix category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.3:ex3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, Exercise 3, book p. 68 (PDF p. 77). Items: `maclane:III.3:ex3`.

## Background
In the category of matrices over a field (objects natural numbers, arrows m×n matrices), the coequalizer of two parallel matrices A, B : n → m is computed from the cokernel of their difference — concretely, a matrix presenting a complement of the column space of A − B. See [Wikipedia: Category of matrices](https://en.wikipedia.org/wiki/Category_of_matrices) and [nLab: coequalizer](https://ncatlab.org/nlab/show/coequalizer).

## Current state in the library
Absent. No matrix category exists (`rg '\bMatr\b|matrices over'` — 0 hits; `Instance/ZX.v` is the qubit ZX-calculus PROP, not Matr_K), and no coequalizer computation exists in any linear category. The Matr_K category itself is the filed issue #221.

## Work to be done
- Over #221's Matr_K: describe the coequalizer of parallel matrices A, B : n → m — a surjection q : m → k with q(A − B) = 0, universal among such; prove `IsCoequalizer A B k q` and package `HasCoequalizers Matr_K` (requires a rank/complement computation over the field, e.g. Gaussian elimination).
- Suggested path: `Instance/Matr/Coequalizer.v` (aligned with #221's layout). Donors: `Structure/Coequalizer.v` (`IsCoequalizer` API), `Structure/Kernel.v` (difference-cokernel framing).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Matr/Coequalizer.v` compiles standalone after its dependencies
- `Print Assumptions` on the HasCoequalizers instance prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, p. 68, Exercise 3

## Dependencies
Depends on: #221

<!-- catalog: {"ids":["maclane:III.3:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.3: Coproducts in Mon and Grph"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.3:ex4]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, Exercise 4, book p. 68 (PDF p. 77). Items: `maclane:III.3:ex4`.

## Background
The exercise asks for explicit coproducts in Cat, Mon, and Grph: disjoint unions of categories, the free product of monoids (interleaved words modulo unit laws), and componentwise disjoint unions of graphs. See [nLab: quiver](https://ncatlab.org/nlab/show/quiver) and [Wikipedia: Free product](https://en.wikipedia.org/wiki/Free_product).

## Current state in the library
One third is complete: `Cat_Cocartesian` (`Instance/Cat/Cocartesian.v:40` over `Construction/Coproduct.v:35`). For Mon: the category `Mon(C)` of internal monoids exists (`Theory/Algebra/Monoid/Hom.v:83`) but carries no coproduct structure, and the free product of monoids appears only in prose (`Structure/Cocartesian.v:44-74`; `Construction/Funny.v:113` even observes, unproven, that the funny tensor of one-object categories is the free product in Mon). For Grph: no coproduct development on the in-tree `QuiverCategory` (`Construction/Free/Quiver.v`); the verified negative-search found no graph-coproduct statement anywhere.

## Work to be done
- Free product of monoids: construct M ∗ N (alternating words with normalization, or the quotient of interleaved words by unit/multiplication relations) and prove it the coproduct in the category of set-level monoids (`Mon(Sets)` via `Theory/Algebra/Monoid/Hom.v` instantiated at Sets, or a dedicated Instance).
- Graph coproducts: componentwise disjoint union on `QuiverCategory`, with the copairing UMP.
- Cross-link the Cat case as already done; optionally prove the `Construction/Funny.v` prose claim as a corollary.
- Suggested paths: `Theory/Algebra/Monoid/Coproduct.v` (or `Instance/Mon/Coproduct.v`), `Construction/Free/Quiver/Coproduct.v`. Donors: `Instance/Cat/Cocartesian.v`, `Construction/Coproduct.v`, `Instance/Sets/Cocartesian.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both coproduct constructions)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category <new files>` compile standalone after their dependencies
- `Print Assumptions` on both coproduct UMPs prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, p. 68, Exercise 4

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.3:ex4"],"deps":[]} -->

---8<---
```yaml
title: "MacLane III.3: Chain unions as colimits and the cocompleteness of Sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.3:remark4]
deps_item_ids: [maclane:III.3:ex5]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, book pp. 67–68 (PDF pp. 76–77). Items: `maclane:III.3:remark4`.

## Background
For an ω-indexed nested sequence of sets with inclusion maps, the union with its inclusion cone is the colimit; Mac Lane reads unions-as-colimits into the familiar algebraic categories and forward-points to the fact that Set has all small colimits. See [Wikipedia: Direct limit](https://en.wikipedia.org/wiki/Direct_limit) and [nLab: cocomplete category](https://ncatlab.org/nlab/show/cocomplete+category).

## Current state in the library
The shape and vocabulary exist — `Omega` (`Instance/Omega.v:72`), ω-chains as functors (`Construction/Chain.v:64`), `Cocomplete` (`Structure/Complete.v:119`) — but no colimit over Omega is ever computed in Sets, `Cocomplete` has no concrete witness anywhere (`rg 'Sets_Cocomplete|Coq_Cocomplete'` — 0 hits; it appears only as a hypothesis in `Theory/Adamek/Corollaries.v:61`), and no union-as-colimit statement exists (CLAUDE.md itself records that no concrete `AdamekData` is constructed and the in-tree initial algebras are proved directly).

## Work to be done
- Compute the colimit of an arbitrary functor `Omega ⟶ Sets` (the union/sum-quotient construction), and specialize: when every connecting map is a section-like inclusion, the colimit is the union with inclusion cone (state in the setoid idiom).
- Prove `Sets_Cocomplete : @Cocomplete Sets` — the general small colimit as the quotient of the indexed sum by the zig-zag relation, building on Sets coproducts (#254) and the new Sets coequalizers (dependency below). This discharges the remark's forward pointer (Mac Lane's Exercise V.1.8) and unblocks the Adámek corollary chain.
- Suggested paths: `Instance/Sets/Cocomplete.v` (general), `Instance/Sets/Chain.v` (ω-chain reading). Donors: `Instance/Sets/Coend.v` (inductive quotient), `Instance/Omega.v`, `Construction/Chain.v`, `Structure/Limit/Preservation.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions Sets_Cocomplete.` closed
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (a cocompleteness witness for Sets likely qualifies)

## Verification
- `coqc -R . Category Instance/Sets/Cocomplete.v` compiles standalone after its dependencies
- `Print Assumptions Sets_Cocomplete.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, pp. 67–68 (including the forward pointer to V.1.8)

## Dependencies
Depends on: #254
Depends on: maclane:III.3:ex5

<!-- catalog: {"ids":["maclane:III.3:remark4"],"deps":["maclane:III.3:ex5"]} -->
---8<---
```yaml
title: "MacLane III.3: An abelian group is the colimit of its finitely generated subgroups"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.3:ex7]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.3, Exercise 7, book p. 68 (PDF p. 77). Items: `maclane:III.3:ex7`.

## Background
With the finitely generated subgroups of an abelian group A ordered by inclusion as the index preorder, A is the colimit of the evident inclusion diagram — the archetype of a directed colimit of subobjects, with an invitation to generalize. See [Wikipedia: Direct limit](https://en.wikipedia.org/wiki/Direct_limit) and [nLab: filtered colimit](https://ncatlab.org/nlab/show/filtered+colimit).

## Current state in the library
Absent. No category of (abelian) groups exists (`Structure/Abelian.v` is abstract abelian categories; `Instance/` has no Ab/Grp); no finitely-generated-subobject machinery; no filtered/directed colimit theory (`rg 'filtered|directed colimit'` finds only an unrelated stream comment). `Instance/Poset.v` supplies preorders-as-categories for the index.

## Work to be done
- Over #256's Ab: define finitely generated subgroups and the inclusion preorder J_A (as a thin category via the `Instance/Poset.v`/`Instance/Proset.v` machinery), the inclusion diagram J_A ⟶ Ab, and prove A with the subgroup-inclusion cocone is its colimit.
- Generalize per the exercise's closing instruction where cheap: state the directed-union principle for any concrete algebraic category available at that time (at minimum, note the CMon analogue).
- Suggested path: `Instance/Ab/DirectedColimit.v`. Donors: `Instance/Poset.v`, `Structure/Limit.v`, `Structure/Limit/Preservation.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.3 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Ab/DirectedColimit.v` compiles standalone after its dependencies
- `Print Assumptions` on the colimit theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.3, p. 68, Exercise 7

## Dependencies
Depends on: #256

<!-- catalog: {"ids":["maclane:III.3:ex7"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Hom-functors preserve products and limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.4:remark3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.4, book p. 70 (PDF p. 79). Items: `maclane:III.4:remark3`.

## Background
The covariant hom-functor C(c, −) carries products existing in C to products in Set — the first appearance of the continuity of representables, which Mac Lane proves in general later (§V.4). See [nLab: hom-functor](https://ncatlab.org/nlab/show/hom-functor) and [nLab: continuous functor](https://ncatlab.org/nlab/show/continuous+functor).

## Current state in the library
Only the surrounding vocabulary exists: `PreservesLimit` (`Structure/Limit/Preservation.v:48`) defines preservation, and `Sets_Cartesian` (`Instance/Sets/Cartesian.v:32`) gives binary products in Sets — but no preservation statement mentions `Hom`, `Curried_Hom`, or representables (the RAPL machinery of `Adjunction/Continuity.v` covers right adjoints only, and no `PreservesLimit` instance exists for hom-functors), and Sets has no indexed-product witness (that is #254's scope).

## Work to be done
- Prove `C(c, −) : C ⟶ Sets` preserves limits: a `PreservesLimit G [Hom c,─]` instance for every diagram G (the limit of hom-setoids computed pointwise/as compatible families, per `Instance/Sets/End.v` style), with the binary- and indexed-product corollaries stated explicitly (the remark's form).
- State the contravariant twin (C(−, c) turns colimits into limits) by the library's duality.
- This also strengthens the cone-level preservation story: derive `PreservesImageLimit` for hom-functors where applicable (cf. `Structure/Limit/Preservation.v`'s honest cone-level class).
- Suggested path: `Functor/Hom/Limit.v`. Donors: `Functor/Hom.v`, `Structure/Limit/Preservation.v`, `Instance/Sets/End.v`, `Adjunction/Continuity.v` (proof pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Functor/Hom/Limit.v` compiles standalone after its dependencies
- `Print Assumptions` on the preservation instance prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.4, p. 70 (products case; general limits anticipate §V.4)

## Dependencies
Depends on: #254

<!-- catalog: {"ids":["maclane:III.4:remark3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Graph-shaped diagrams and their limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.4:def8, maclane:III.4:remark6]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.4, book p. 71 (PDF p. 80). Items: `maclane:III.4:def8`, `maclane:III.4:remark6`.

## Background
A diagram of graph shape is a graph morphism into the underlying graph of C; cones and limits over such diagrams need no functoriality of the diagram, and they reduce to functor limits: diagrams factor uniquely through the free category on the graph, with limits corresponding exactly. See [nLab: quiver](https://ncatlab.org/nlab/show/quiver) and [Wikipedia: Limit (category theory)](https://en.wikipedia.org/wiki/Limit_(category_theory)).

## Current state in the library
The diagram notion is first-class — `Quiver` (`Construction/Free/Quiver.v:54`), `QuiverHomomorphism` (:205), `QuiverOfCat` (:398), and the factorization half of the reduction is complete as `UniversalArrowQuiverCat` (:518) with `InducedFunctor` (:464) and `FreeForgetfulAdjunction` (:550). But `Cone`/`Limit` are defined only over functors from a Category; no cone-over-a-quiver-homomorphism exists (0 hits for cone/limit in `Construction/Free/Quiver.v`), so the limit-correspondence half of the remark cannot even be stated.

## Work to be done
- Define cones over a graph diagram D : G ⇨ U C (a node-indexed family of legs with one triangle per edge) and the limit of such a diagram as the universal cone.
- Prove the correspondence: cones (and limits) of D biject with cones (and limits) of `InducedFunctor D : FreeOnQuiver G ⟶ C`, in both directions.
- Suggested path: `Construction/Free/Quiver/Limit.v`. Donors: `Construction/Free/Quiver.v`, `Structure/Cone.v`, `Structure/Limit.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the cone definition's UMP and both directions of the correspondence)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Construction/Free/Quiver/Limit.v` compiles standalone after its dependencies
- `Print Assumptions` on the correspondence theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.4, p. 71

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.4:def8","maclane:III.4:remark6"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Pullbacks and kernel pairs in Sets"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.4:ex1, maclane:III.4:ex6]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.4, Exercises 1 and 6, book p. 72 (PDF p. 81). Items: `maclane:III.4:ex1`, `maclane:III.4:ex6`.

## Background
In Set the pullback of f and g is the set of pairs on which they agree, with the evident projections; the kernel pair of f is the induced equivalence relation {(x, x′) | f x = f x′} with its two projections. See [nLab: pullback](https://ncatlab.org/nlab/show/pullback) and [Wikipedia: Pullback (category theory)](https://en.wikipedia.org/wiki/Pullback_(category_theory)).

## Current state in the library
The agreement-subset pullback is witnessed only in skeletal FinSet (`FinSet_Pullbacks`, `Instance/FinSet/Classifier.v:264`); Sets has NO general `HasPullbacks` instance — only the one-off classifier square `sets_char_pullback` (`Instance/Sets/Classifier.v:224`) and the dual `Sets_HasPushouts`. The generic `kernel_pair := pullback f f` exists (`Structure/Regular.v:46`), and in FinSet it computes definitionally to the agreement subset, but no lemma anywhere identifies the kernel pair with the induced equivalence relation, and Sets has no kernel pairs at all.

## Work to be done
- Construct `Sets_HasPullbacks : HasPullbacks Sets` — the sub-setoid of the product carrier on which the two legs agree, with the projections and ∃!-mediator.
- Prove the kernel-pair identification: `kernel_pair f` in Sets is the relation setoid {(x, x′) | f x ≈ f x′} with its projections, and record its equivalence-relation reading (reflexivity/symmetry/transitivity as arrows).
- The Top half of Exercise 1 is host-category-gated: record it as an extension over #259.
- Suggested path: `Instance/Sets/Pullback.v`. Donors: `Instance/Sets/Cartesian.v`, `Structure/Pullback.v`, `Instance/FinSet/Classifier.v` (predicate pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions Sets_HasPullbacks.` closed
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Sets/Pullback.v` compiles standalone after its dependencies
- `Print Assumptions Sets_HasPullbacks.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.4, p. 72, Exercises 1 and 6

## Dependencies
Depends on: #259 (the Top clause of Exercise 1 only)

<!-- catalog: {"ids":["maclane:III.4:ex1","maclane:III.4:ex6"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.4: Limits along an index category with an initial object"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.4:ex3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.4, Exercise 3, book p. 72 (PDF p. 81). Items: `maclane:III.4:ex3`.

## Background
If the index category J has an initial object s, every functor F : J ⟶ C has a limit, computed by evaluation: F(s) with the legs F(unique arrow) is the limiting cone; dually, a terminal index object computes colimits by evaluation. See [nLab: initial object](https://ncatlab.org/nlab/show/initial+object) and [Wikipedia: Limit (category theory)](https://en.wikipedia.org/wiki/Limit_(category_theory)).

## Current state in the library
Absent. Extensive verified negative search: no lemma computes a limit by evaluation at an initial index object; the `initial × limit` hits are all different theorems (colimit-as-initial-cocone, `initial_from_weakly_initial` in `Theory/WeaklyInitial.v`, empty-diagram limits in `Structure/Limit/Terminal.v`); no final/initial-functor (cofinality) machinery exists that would subsume it.

## Work to be done
- Prove: given `I : @Initial J` and `F : J ⟶ C`, `IsALimit F (F (initial_obj))` with legs `fmap[F] zero` — existence and uniqueness of the mediator from any cone via initiality.
- State the dual (terminal index object ⇒ colimit by evaluation) through the library's `C^op` duality, with covariant accessors.
- Suggested path: `Structure/Limit/Initial.v`. Donors: `Structure/Limit.v`, `Structure/Initial.v`, `Structure/Limit/Terminal.v` (file pattern).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.4 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both directions)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Limit/Initial.v` compiles standalone after its dependencies
- `Print Assumptions` on the evaluation-limit theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.4, p. 72, Exercise 3 (both halves)

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.4:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.5: All finite products from a terminal object and binary products"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.5:prop1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.5, Proposition 1, book p. 73 (PDF p. 82). Items: `maclane:III.5:prop1`.

## Background
A terminal object plus a chosen binary product for every pair yield product diagrams for every finite list of objects, make × a bifunctor, and produce the canonical natural isomorphisms α, λ, ρ by uniqueness of universals; dually for finite coproducts. See [Wikipedia: Product (category theory)](https://en.wikipedia.org/wiki/Product_(category_theory)) and [nLab: cartesian monoidal category](https://ncatlab.org/nlab/show/cartesian+monoidal+category).

## Current state in the library
The bifunctor and the coherence components are complete: `InternalProductFunctor` (`Functor/Product/Internal.v:34`), `CC_Monoidal` (`Structure/Monoidal/Internal/Product.v:54`, canonical α/λ/ρ with all naturality obligations), `prod_assoc`/`prod_one_l`/`prod_one_r` (`Structure/Cartesian.v:485/451/465`), and the coproduct dual via `Cocartesian := Cartesian (C^op)`. The headline quantifier is missing: no theorem produces an n-ary product diagram for an arbitrary finite list from `Cartesian` + `Terminal` (nearest neighbors are `law_pow`, powers of a single object, and `Multicategory`'s `pow` — verified, no list-indexed iteration lemma exists).

## Work to be done
- Prove the iteration theorem: for any `l : list C` (or `f : Fin n → C`), a product diagram exists — e.g. `Limit (DiscreteCat_Functor f)` or an `IsIndexedProduct` witness built by folding binary products against the terminal object.
- Package as a `HasFiniteProducts`-style corollary of `Cartesian` + `Terminal` (and the dual for `Cocartesian` + `Initial` by op).
- Suggested path: `Structure/Limit/Product/Finite.v`. Donors: `Structure/Limit/Product.v`, `Structure/Cartesian.v`, `Instance/Discrete.v`, `Structure/Monoidal/Internal/Product.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.5 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the n-ary existence theorem, both dual forms)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Limit/Product/Finite.v` compiles standalone after its dependencies
- `Print Assumptions` on the n-ary product theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.5, Proposition 1, p. 73

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.5:prop1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.5: The matrix calculus from finite coproducts to finite products"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.5:remark1, maclane:III.5:remark2]
deps_item_ids: [maclane:III.5:prop1]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.5, book pp. 73–74 (PDF pp. 82–83). Items: `maclane:III.5:remark1`, `maclane:III.5:remark2`.

## Background
Arrows from an m-fold coproduct to an n-fold product are uniquely determined by their m×n matrix of components; with a null object, the identity matrix defines the canonical comparison arrow from finite coproducts to finite products, which may be an isomorphism (Ab, R-Mod), a proper monic (pointed sets/spaces), or a proper epi (Grp). See [nLab: biproduct](https://ncatlab.org/nlab/show/biproduct) and [Wikipedia: Biproduct](https://en.wikipedia.org/wiki/Biproduct).

## Current state in the library
Only the binary (2×2) case exists: `fork_merge` (`Structure/Bicartesian.v:39`, with the in-file 2×2 gloss), `merge_ext`/`fork_ext` (`Structure/Semiadditive.v:274/260`), and the binary canonical comparison `can_comparison` with its four entry lemmas and the semiadditivity development (`Structure/Semiadditive.v:288-321`, `bicartesian_preadditive`:573; concrete iso witness `CMon_Biproduct`, `Instance/CMon/Biproduct.v:442`). Missing: the general m×n matrix-determination lemma, the n-ary identity-matrix comparison, and the non-iso example classifications (no FdVect/Matr instance for the classical-matrix reading; no pointed-sets proper-monic or Grp proper-epi witness).

## Work to be done
- Over the n-ary products/coproducts of `maclane:III.5:prop1`: prove the m×n matrix determination — two arrows from an m-fold coproduct to an n-fold product agree iff all m·n components p_k ∘ f ∘ i_j agree.
- Define the n-ary canonical comparison (identity matrix: diagonal identities, zero arrows elsewhere, under a `ZeroObject`), generalizing `can_comparison`.
- Example classifications as follow-ups gated on host categories: proper-monic witness in pointed sets (#261), proper-epi witness in Grp (#255), classical-matrix reading in FdVect (#244); record these as optional checklist items.
- Suggested path: `Structure/Bicartesian/Matrix.v`. Donors: `Structure/Bicartesian.v`, `Structure/Semiadditive.v`, `Structure/ZeroObject.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.5 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (matrix determination, n-ary comparison)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Bicartesian/Matrix.v` compiles standalone after its dependencies
- `Print Assumptions` on the matrix-determination lemma prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.5, pp. 73–74

## Dependencies
Depends on: maclane:III.5:prop1
Related (example witnesses only): #244, #255, #261

<!-- catalog: {"ids":["maclane:III.5:remark1","maclane:III.5:remark2"],"deps":["maclane:III.5:prop1"]} -->
---8<---
```yaml
title: "MacLane III.5: Cat has pullbacks and comma categories are pullbacks in Cat"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.5:ex3]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.5, Exercise 3, book p. 74 (PDF p. 83). Items: `maclane:III.5:ex3`.

## Background
Cat has pullbacks (fiber products of categories, objectwise and arrowwise), and the slice-style comma categories (b ↓ C), (C ↓ a) arise as pullbacks in Cat against projections from the arrow category — the 2-categorical construction of comma objects from products, pullbacks, and the walking arrow. See [nLab: Cat](https://ncatlab.org/nlab/show/Cat) and [Wikipedia: Pullback (category theory)](https://en.wikipedia.org/wiki/Pullback_(category_theory)).

## Current state in the library
Absent. The only `HasPullbacks` instance in-tree is `FinSet_Pullbacks`; `Instance/Cat/` contains only Bicategory/Cartesian/Cocartesian; comma-as-pullback appears solely as prose in `Construction/Comma.v:108`; the closest neighbor `Comma_Product` (`Construction/Product/Comma.v:57`, (F ↓ G) ≅ C ∏ D over the terminal category) involves no pullback. No completeness result for Cat could supply pullbacks indirectly.

## Work to be done
- Construct `Cat_Pullbacks : HasPullbacks Cat`: the fiber-product category of F : A ⟶ C ⟵ B : G (pairs of objects/arrows agreeing under the legs — note the strictness caveat: state the equality of images at the level Cat's setoid of functors supports, and document the design choice in the header).
- Prove the comma categories (b ↓ C) and (C ↓ a) are pullbacks in Cat of the appropriate arrow-category projections (`Construction/Comma.v`, the II.6 arrow-category machinery of #290).
- Suggested path: `Instance/Cat/Pullback.v`. Donors: `Construction/Comma.v`, `Instance/Cat.v`, `Instance/Cat/Cartesian.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.5 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Cat/Pullback.v` compiles standalone after its dependencies
- `Print Assumptions Cat_Pullbacks.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.5, p. 74, Exercise 3 (both parts)

## Dependencies
Depends on: #290

<!-- catalog: {"ids":["maclane:III.5:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.5: Cat has small coproducts"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.5:ex4]
deps_item_ids: [maclane:III.3:def2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.5, Exercise 4, book p. 74 (PDF p. 83). Items: `maclane:III.5:ex4`.

## Background
Cat has coproducts over any small index set: the disjoint union of an indexed family of categories, with functors out given by case analysis. See [nLab: Cat](https://ncatlab.org/nlab/show/Cat) and [Wikipedia: Coproduct](https://en.wikipedia.org/wiki/Coproduct).

## Current state in the library
Finite coproducts only: `Cat_Cocartesian` (`Instance/Cat/Cocartesian.v:40`, binary disjoint-union with the case-functor UMP) and `Cat_Initial` (`Instance/Zero.v:44`). No Σ-indexed disjoint-union category, no discrete-diagram `Colimit` instance for Cat, no `Cocomplete Cat` (verified searches: 0 hits).

## Work to be done
- Construct the indexed disjoint-union category `∐ᵢ Cᵢ` for an arbitrary family `C : I → Category` (objects `{i & obj Cᵢ}`, cross-summand homs empty), with injections and the case-functor UMP.
- Package as an indexed-coproduct witness for Cat over the API of `maclane:III.3:def2` (a `Colimit (DiscreteCat_Functor C)` / `HasIndexedCoproducts Cat` instance).
- Suggested path: `Construction/Coproduct/Indexed.v` + `Instance/Cat/Coproduct.v`. Donors: `Construction/Coproduct.v`, `Instance/Cat/Cocartesian.v`, `Instance/Discrete.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.5 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Cat/Coproduct.v` compiles standalone after its dependencies
- `Print Assumptions` on the indexed-coproduct UMP prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.5, p. 74, Exercise 4

## Dependencies
Depends on: maclane:III.3:def2

<!-- catalog: {"ids":["maclane:III.5:ex4"],"deps":["maclane:III.3:def2"]} -->

---8<---
```yaml
title: "MacLane III.5: Pointwise finite products in functor categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.5:ex5]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.5, Exercise 5, book p. 74 (PDF p. 83). Items: `maclane:III.5:ex5`.

## Background
If B has (finite) products, so does any functor category B^C, computed pointwise — the ambient fact behind pointwise algebraic structure on functors and the finite products of presheaf categories. See [nLab: functor category](https://ncatlab.org/nlab/show/functor+category) and [Wikipedia: Functor category](https://en.wikipedia.org/wiki/Functor_category).

## Current state in the library
Binary pointwise products exist: `Functor_Category_Cartesian` (`Instance/Fun/Cartesian.v:111`). The nullary case is missing — no `@Terminal (Fun C D)` instance (the constant functor at D's terminal object) exists anywhere in-tree (verified against the full Terminal-instance listing), so "finite products" is covered only in its binary part; general indexed/small pointwise products in functor categories are also absent.

## Work to be done
- Construct `Functor_Category_Terminal : @Terminal ([C, D])` when D has a terminal object (constant functor at 1, unique natural transformation into it).
- Extend to indexed pointwise products: `HasIndexedProducts D → HasIndexedProducts [C, D]` (and note the general pointwise-limits theorem as V-chapter material).
- Suggested path: `Instance/Fun/Terminal.v` (+ extension of `Instance/Fun/Cartesian.v`). Donors: `Instance/Fun/Cartesian.v`, `Structure/Terminal.v`, `Structure/Limit/Product.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.5 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Fun/Terminal.v` compiles standalone after its dependencies
- `Print Assumptions Functor_Category_Terminal.` prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.5, p. 74, Exercise 5

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.5:ex5"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.6: Ring and lattice objects by internalization"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.6:remark1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.6, book p. 75 (PDF p. 84). Items: `maclane:III.6:remark1`.

## Background
Commutative diagrams like those for monoid and group objects internalize any algebraic system given by finitary operations and equational laws — Mac Lane names rings in C and lattices in C as the next examples. See [nLab: ring object](https://ncatlab.org/nlab/show/ring+object) and [nLab: internalization](https://ncatlab.org/nlab/show/internalization).

## Current state in the library
The general scheme exists in modern form — models of a Lawvere theory as finite-product-preserving functors (`Theory/Lawvere/Model.v:50`, with the category `Models`:77) — and the hand-rolled instances `MonoidObject` (`Structure/Monoid.v:124`) and `GroupObject` (`Structure/Group.v:109`). Missing: no ring object or lattice object is defined; no machinery derives a Lawvere theory from a raw signature-plus-equations presentation (presentations exist for PROPs only, `Construction/PROP/Presentation.v`); and no bridge identifies the hand-rolled classes with Lawvere models.

## Work to be done
- Define `RingObject` (semiring first if that stages better: additive commutative-monoid object + multiplicative monoid object + distributivity + annihilation) and `LatticeObject` (two commutative idempotent monoid structures + absorption) over a cartesian category, in the `Structure/Monoid.v`/`Structure/Group.v` style.
- Prove basic sanity (e.g. the Sets instances recover ordinary (semi)rings/lattices on setoids), and add a header note connecting the pattern to `Theory/Lawvere/Model.v` (the bridge theorem MonoidObject ≅ Models(Th_Mon) may be recorded as an optional stretch item, not required for closure).
- Suggested paths: `Structure/Ring.v`, `Structure/Lattice.v`. Donors: `Structure/Monoid.v`, `Structure/Group.v`, `Structure/Monoidal/Internal/Product.v` (CC_Monoidal).

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.6 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both classes, the Sets sanity instances)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Ring.v` and `Structure/Lattice.v` compile standalone after their dependencies
- `Print Assumptions` on the Sets instances prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.6, p. 75

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.6:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.6: Group objects through their representable functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.6:prop1, maclane:III.6:remark2]
deps_item_ids: [maclane:III.5:ex5]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.6, Proposition 1 and the following remark, book pp. 75–76 (PDF pp. 84–85). Items: `maclane:III.6:prop1`, `maclane:III.6:remark2`.

## Background
The functor-of-points criterion: an object c of a finite-products category is a group (monoid) object iff the presheaf C(−, c) is a group (monoid) in Set^(C^op) — multiplication transferred through C(−,c) × C(−,c) ≅ C(−, c×c) and the Yoneda lemma; the remark notes this even *defines* group-like objects over a base without finite products. See [nLab: group object](https://ncatlab.org/nlab/show/group+object) and [Wikipedia: Group object](https://en.wikipedia.org/wiki/Group_object).

## Current state in the library
Absent. The only trace is a header comment (`Structure/Group.v:28`) asserting the equivalence; no formal statement exists (verified sweeps over `MonoidObject`/`GroupObject` consumers, `representable × (monoid|group)`, and functor-category group objects — all 0 relevant hits). The ambient pointwise cartesian structure on functor categories exists in part (`Instance/Fun/Cartesian.v`), lacking the terminal object (see dependency).

## Work to be done
- Prove the transfer both ways: `GroupObject c` (resp. `MonoidObject` at CC_Monoidal) iff `[Hom ─,c]` carries a group (monoid) object structure in `[C^op, Sets]` with its pointwise cartesian structure — via the product-comparison iso `C(−,c) × C(−,c) ≅ C(−, c×c)` and `Yoneda_Lemma`, including the associativity/unit/inverse transfer chases.
- State the remark's generalization: for C without finite products, define representably-group objects (a group structure on the presheaf) and show it agrees with `GroupObject` when finite products exist.
- Suggested path: `Structure/Group/Representable.v`. Donors: `Structure/Group.v`, `Functor/Hom/Yoneda.v`, `Instance/Fun/Cartesian.v`, `Structure/Monoidal/Internal/Product.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.6 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both directions of the criterion)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Structure/Group/Representable.v` compiles standalone after its dependencies
- `Print Assumptions` on the criterion prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.6, Proposition 1, pp. 75–76

## Dependencies
Depends on: maclane:III.5:ex5

<!-- catalog: {"ids":["maclane:III.6:prop1","maclane:III.6:remark2"],"deps":["maclane:III.5:ex5"]} -->
---8<---
```yaml
title: "MacLane III.6: Pointwise group objects in functor categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.6:ex3]
deps_item_ids: [maclane:III.5:ex5]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.6, Exercise 3, book p. 76 (PDF p. 85). Items: `maclane:III.6:ex3`.

## Background
A functor T : B ⟶ Set is a group object in Set^B exactly when every value T b is an ordinary group and every T f is a group homomorphism — group objects in functor categories are pointwise groups with homomorphic action. See [nLab: group object](https://ncatlab.org/nlab/show/group+object) and [nLab: functor category](https://ncatlab.org/nlab/show/functor+category).

## Current state in the library
Absent. The pointwise cartesian structure on functor categories exists (`Instance/Fun/Cartesian.v`), so the ambient is partly available, but no monoid/group object is ever instantiated at a functor category and no pointwise characterization is stated (verified; `Monad/Monoid.v` is the composition tensor on [C,C], a different monoidal structure).

## Work to be done
- Prove the characterization both ways: `GroupObject T` in `[B, Sets]` (pointwise cartesian structure) iff each `T b` carries a group-object structure in Sets varying homomorphically along every `T f` (and the monoid analogue, which is nearly free).
- Requires the functor-category terminal object (dependency below) so the internal-structure classes can even be instantiated there.
- Suggested path: `Instance/Fun/Group.v`. Donors: `Instance/Fun/Cartesian.v`, `Structure/Group.v`, `Instance/Sets/Cartesian.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.6 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both directions)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Fun/Group.v` compiles standalone after its dependencies
- `Print Assumptions` on the characterization prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.6, p. 76, Exercise 3

## Dependencies
Depends on: maclane:III.5:ex5

<!-- catalog: {"ids":["maclane:III.6:ex3"],"deps":["maclane:III.5:ex5"]} -->
---8<---
```yaml
title: "MacLane III.6: The categories of internal monoids and groups have finite products"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.6:ex1, maclane:III.6:ex2]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.6, Exercises 1–2, book p. 76 (PDF p. 85). Items: `maclane:III.6:ex1`, `maclane:III.6:ex2`.

## Background
Over a category with finite products, the monoids in C (arrows commuting with multiplication and unit) form a category with finite products, and likewise the groups in C — products computed on product carriers with componentwise structure. See [nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category) and [nLab: group object](https://ncatlab.org/nlab/show/group+object).

## Current state in the library
Half of Exercise 1: the category `Mon(C)` is fully built (`Theory/Algebra/Monoid/Hom.v`: `MonoidHom`:34, `Mon`:83, faithful `Mon_Forget`:101) at monoidal generality, but no Terminal/Cartesian instance on it exists; `Product_Monoid` (`Structure/Monoid.v:179`) supplies the componentwise candidate carrier but lives on the sibling `MonoidObject` class and is never wired into `Mon`. Exercise 2 is entirely absent: no category of group objects `Grp(C)` exists at all (no `GroupHom`, no `Theory/Algebra/Group/Hom.v` analogue — verified).

## Work to be done
- Give `Mon(C)` (at the cartesian instantiation) its finite products: terminal object (terminal carrier with trivial structure) and binary products (componentwise structure on x × y), resolving the `Monoid`-vs-`MonoidObject` sibling-class wiring so `Product_Monoid` becomes usable.
- Define `GroupHom` and the category `Grp(C)` of group objects, with the faithful forgetful functor, and prove it has finite products the same way.
- Suggested paths: `Theory/Algebra/Monoid/Product.v`, `Theory/Algebra/Group/Hom.v` (or `Structure/Group/Category.v`). Donors: `Theory/Algebra/Monoid/Hom.v`, `Structure/Monoid.v` (`Product_Monoid`), `Structure/Group.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.6 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both Cartesian/Terminal instances)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Theory/Algebra/Group/Hom.v` compiles standalone after its dependencies
- `Print Assumptions` on both finite-product structures prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statements match Mac Lane §III.6, p. 76, Exercises 1–2

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.6:ex1","maclane:III.6:ex2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.6: Groups in Grp are abelian groups"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:III.6:ex4]
deps_item_ids: [maclane:III.6:ex2]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.6, Exercise 4, book p. 76 (PDF p. 85). Items: `maclane:III.6:ex4`.

## Background
An abelian group's multiplication, unit, and inverse are themselves group homomorphisms, making it a group object in Grp; conversely every group object in Grp arises this way — the Eckmann–Hilton phenomenon: two compatible unital multiplications coincide and are commutative. See [nLab: Eckmann-Hilton argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argument) and [Wikipedia: Eckmann–Hilton argument](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument).

## Current state in the library
Absent (verifier overturned an initial PARTIAL): no category Grp and no category of group objects exists, so neither direction has a carrier. The Eckmann–Hilton *engine* does exist in a different context — `Structure/Semiadditive.v`'s `conv_interchange`/`conv_conv_pr`/`conv_comm`/`conv_assoc` (lines 503–534) formalize the interchange argument for hom-set convolutions — and the abstract two-operations argument is the scope of the filed issue #285.

## Work to be done
- Over #255's Grp and the group-object category of `maclane:III.6:ex2`: (a) show an abelian group's structure maps are homomorphisms, assembling a group object in Grp; (b) prove every group object in Grp is of this form — the second multiplication agrees with the first and forces commutativity, by the interchange argument (reuse #285's abstract lemma where possible).
- Suggested path: `Instance/Grp/EckmannHilton.v`. Donors: `Structure/Group.v`, `Structure/Semiadditive.v` (interchange pattern), #285's artifact.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.6 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both directions)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Instance/Grp/EckmannHilton.v` compiles standalone after its dependencies
- `Print Assumptions` on both directions prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.6, p. 76, Exercise 4

## Dependencies
Depends on: #255
Depends on: #285
Depends on: maclane:III.6:ex2

<!-- catalog: {"ids":["maclane:III.6:ex4"],"deps":["maclane:III.6:ex2"]} -->
---8<---
```yaml
title: "MacLane III.7: The category of elements of a set-valued functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.7:construction1]
deps_item_ids: []
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.7, book p. 76 (PDF p. 85). Items: `maclane:III.7:construction1`.

## Background
For K : D ⟶ Set, the category of elements pairs each object with an element of its image; arrows are the arrows of D carrying one element to the other — Mac Lane presents it as the comma category of a point over K, and it indexes the canonical diagram of representables. See [nLab: category of elements](https://ncatlab.org/nlab/show/category+of+elements) and [Wikipedia: Category of elements](https://en.wikipedia.org/wiki/Category_of_elements).

## Current state in the library
Absent as an instantiation: the two generic machines that subsume it exist — the fully general comma category (`Construction/Comma.v:127`) and the Grothendieck construction (`Construction/Grothendieck.v`, whose header at line 107 names el(F) as the discrete-fibre special case in prose) — but el(K) itself is never assembled: no (∗ ↓ K) comma instance for Sets-valued K, no discrete-fibre Grothendieck specialization, no projection functor. The verifier notes the missing one-point-select functor is a trivial instantiation of `Functor/Diagonal.v`'s constant functor.

## Work to be done
- Define `Elements (K : D ⟶ Sets)` — directly (objects `{d & K d}`, arrows the underlying arrows with the transport equation) or as the comma of the one-point-setoid select functor over K; provide the projection `Elements K ⟶ D` and the comma-category comparison.
- Prove the basic API consumers need: faithfulness of the projection, and the discrete-opfibration reading as a remark or lemma (cross-linking `Construction/Grothendieck/Fibration.v`).
- This construction is the diagram shape for the density theorem (`maclane:III.7:thm1`) and Kan's coyoneda exercise (`maclane:III.2:ex3`), which depend on it.
- Suggested path: `Construction/Elements.v`. Donors: `Construction/Comma.v`, `Construction/Grothendieck.v`, `Functor/Diagonal.v`, `Instance/One.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.7 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`Elements`, the projection, the comma comparison)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
- `coqc -R . Category Construction/Elements.v` compiles standalone after its dependencies
- `Print Assumptions` on the construction and the comma comparison prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.7, p. 76

## Dependencies
None.

<!-- catalog: {"ids":["maclane:III.7:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane III.7: The density theorem: set-valued functors as colimits of representables"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:III.7:thm1, maclane:III.7:remark1]
deps_item_ids: [maclane:III.7:construction1]
```

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §III.7, Theorem 1 and the dual remark, book pp. 76–77 (PDF pp. 85–86). Items: `maclane:III.7:thm1`, `maclane:III.7:remark1`.

## Background
Every set-valued functor K on a small category is canonically a colimit of representables: index by the category of elements, send each element to its representable, and the Yoneda-derived cocone is colimiting in the functor category; dually for presheaves — the density of the Yoneda embedding. See [nLab: co-Yoneda lemma](https://ncatlab.org/nlab/show/co-Yoneda+lemma) and [nLab: dense functor](https://ncatlab.org/nlab/show/dense+functor).

## Current state in the library
Only the pointwise coend form exists: `coyoneda_reduction` (`Theory/Coend/Yoneda.v:174`, ∫^x C(x,c) × F x ≅ F c, funext-free over the concrete Sets coend), with `coyoneda_iso` (:146); the `Structure/Coend.v` header (:102) advertises exactly this. Missing: the functor-level statement — no category-of-elements index, no diagram of representables `M : (el K)^op ⟶ [D, Sets]`, no colimiting-cocone theorem in the functor category, and no naturality in c of the pointwise iso (the Section context at `Theory/Coend/Yoneda.v:69-71` fixes c, so naturality is not even stateable there). The dual presheaf instantiation is a zero-content specialization but is never written down.

## Work to be done
- Over `maclane:III.7:construction1`: build the diagram of representables indexed by (a suitable orientation of) the category of elements of K, assemble the Yoneda-derived cocone to K, and prove it colimiting in `[D, Sets]` (the mediating transformation from any cocone via Yoneda, with its uniqueness).
- Derive the presheaf dual as a named artifact (instantiation at D^op), and connect to the existing coend form (`coyoneda_reduction`) with a naturality-in-c upgrade.
- Suggested path: `Theory/Density.v` (or `Functor/Hom/Density.v`). Donors: `Functor/Hom/Yoneda.v`, `Theory/Coend/Yoneda.v`, `Structure/Limit.v`, `Instance/Fun.v`.

## Definition of Done
- [ ] Statements are faithful to Mac Lane §III.7 up to setoid presentation (`≈` on morphisms, never `=`)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the colimit theorem, the dual, the naturality upgrade)
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a density theorem is flagship-level)

## Verification
- `coqc -R . Category Theory/Density.v` compiles standalone after its dependencies
- `Print Assumptions` on the colimit theorem prints "Closed under the global context"
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed
- Review item: statement matches Mac Lane §III.7, Theorem 1, pp. 76–77, and the dual remark on p. 77

## Dependencies
Depends on: maclane:III.7:construction1

<!-- catalog: {"ids":["maclane:III.7:thm1","maclane:III.7:remark1"],"deps":["maclane:III.7:construction1"]} -->

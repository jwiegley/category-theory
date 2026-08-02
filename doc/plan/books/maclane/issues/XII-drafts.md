---
title: "MacLane XII.1: Internal categories (category objects in a finitely complete category)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.1:def1, maclane:XII.1:remark1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.1 (book pp. 267–268, PDF pp. 274–275). Items `maclane:XII.1:def1` (the category object / internal category in a finitely complete ambient category) and `maclane:XII.1:remark1` (a category object in Set is an ordinary small category).

## Background

In an ambient category `E` with finite limits, an internal category packages a "category" whose objects and arrows are themselves `E`-objects: an object-of-objects `C₀`, an object-of-arrows `C₁`, identity `i : C₀ → C₁`, source/target `d₀, d₁ : C₁ → C₀`, and a composition `γ : C₁ ×_{C₀} C₁ → C₁` on the pullback of composable arrows, subject to the source/target, unit, and associativity laws expressed diagrammatically. Taking `E = Set` recovers ordinary small categories. See the nLab, [internal category](https://ncatlab.org/nlab/show/internal+category), and [internalization](https://ncatlab.org/nlab/show/internalization).

## Current state in the library

Absent. There is no category-object record anywhere: no object-of-objects/object-of-arrows pair with source/target/identity structure maps and a pullback composition (verified by whole-tree search for `InternalCat`/`CatObject`/`CategoryObject` and for source/target/pullback-composition records — zero definitional hits). The only cousins are strictly different structures: `Structure/Monoid.v:124` (`MonoidObject`) is the one-object special case (`C₀` terminal, so no object-of-objects, no source/target, and the composition domain degenerates to a plain product), `Structure/Group.v:112` (`GroupObject`) is the internal-group notion, and `Theory/Metacategory.v` is the arrows-only (single-sorted) axiomatization over a fixed numeric `FMap` base, not a category internal to a general `E`. `Theory/DoubleCategory.v` axiomatizes the `E = Cat` case directly and, moreover, as a *pseudo* (weak) double category — it is not even the strict `E = Cat` internal category, and its header (`:115–116`) mentions "a category internal to Cat" only in prose. No statement identifies a category object in `Set` with a small category.

## Work to be done

- Define an `InternalCategory` class over an ambient `Category E` equipped with the finite limits it needs (a terminal object plus pullbacks, or an assumed `HasPullbacks`/binary-products interface): the data `C₀`, `C₁`, `i`, `d₀`, `d₁`, and `γ` on the chosen pullback `C₁ ×_{C₀} C₁`, with the source/target laws (`d₀ ∘ i ≈ id ≈ d₁ ∘ i`, `d₀ ∘ γ`, `d₁ ∘ γ`), the left/right unit laws, and associativity across the triple pullback — all as setoid equalities of `E`-morphisms.
- Prove the validation theorem (§XII.1 remark): instantiated at `Sets`, an `InternalCategory` is equivalent to an ordinary small `Category` (build the `Category` from the internal data with objects the "global elements"/underlying setoid of `C₀`, and conversely package a small category as a category object in `Sets`), exhibiting the correspondence up to the appropriate notion of sameness.
- Suggested modules: `Structure/InternalCategory.v` (the class, reusable), `Instance/Sets/InternalCategory.v` (the `Set`-case correspondence). In-tree donors: `Structure/Pullback.v` and `Structure/Cartesian.v` (the finite-limit apparatus and chosen pullbacks), `Structure/Span.v` (composable-pair shapes), `Theory/DoubleCategory.v` (the `E = Cat` analogue for cross-checking the laws), and `Structure/Monoid.v`/`Structure/Group.v` as the degenerate one-object precedents.

## Definition of Done

- [ ] `InternalCategory` over a finitely complete `E` is defined with `C₀`, `C₁`, `i`, `d₀`, `d₁`, `γ` and the source/target, unit, and associativity laws (pullback composition).
- [ ] Instantiated at `Sets`, the equivalence with ordinary small categories is proved in both directions.
- [ ] All structure-map equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the class and the `Sets` correspondence.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (this is a reusable, flagship-level foundation).

## Verification

- `coqc -R . Category Structure/InternalCategory.v Instance/Sets/InternalCategory.v` compiles cleanly.
- `Print Assumptions` on the `InternalCategory` class and on the `Sets`-case correspondence show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the data and the four axioms match Mac Lane §XII.1, and the `Set` case yields an ordinary small category (§XII.1 remark).

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XII.1:def1","maclane:XII.1:remark1"],"deps":[]} -->

---8<---

---
title: "MacLane XII.1: Internal functors and internal natural transformations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.1:def2, maclane:XII.1:def3]
deps_item_ids: [maclane:XII.1:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.1 (book p. 269, PDF p. 276). Items `maclane:XII.1:def2` (internal functor) and `maclane:XII.1:def3` (internal natural transformation, which Mac Lane only sketches).

## Background

An internal functor between category objects `C, D` in `E` is a pair of `E`-maps `f₀ : C₀ → D₀`, `f₁ : C₁ → D₁` commuting with source, target, identities, and composition; an internal natural transformation is the internal analogue of a natural transformation (a component map `C₀ → D₁` compatible with source/target and the actions). Together with internal categories these assemble the 2-category `Cat(E)` of categories internal to `E`. See the nLab, [internal category](https://ncatlab.org/nlab/show/internal+category) (which develops internal functors and transformations).

## Current state in the library

Absent. There is no internal functor — no pair `(f₀ : C₀ → D₀, f₁ : C₁ → D₁)` of `E`-maps commuting with `i`, `d₀`, `d₁`, `γ` (whole-tree search for `InternalFunctor` / "internal functor" as a definition returns zero hits; the sole textual matches are unrelated hypergraph-functor names and prose). The ordinary `Functor` class (`Theory/Functor.v`) and monoid-object homomorphisms (`Theory/Algebra/Monoid/Hom.v`) exist but are not the internal-pair notion. The internal natural transformation is doubly absent — Mac Lane himself only asserts it — and there is no component-map-over-source/target construction in-tree.

## Work to be done

- Define an `InternalFunctor` between two internal categories (of §XII.1) as a pair of `E`-morphisms on objects and arrows with the four commutation laws (with `i`, `d₀`, `d₁`, and `γ` — the last through the induced map on pullbacks), as setoid equalities.
- Define an `InternalTransformation` between two internal functors `C → D`: a component `E`-map `θ : C₀ → D₁` with `d₀ ∘ θ ≈ f₀`, `d₁ ∘ θ ≈ g₀`, and the internal naturality square relating `θ`, `f₁`, `g₁` through the composition `γ_D`.
- Establish identity and composite internal functors (and vertical composition of internal transformations) so that internal categories, functors, and internal transformations form a category (the underlying 1-category of `Cat(E)`).
- Suggested module: `Structure/InternalCategory/Functor.v`. In-tree donors: the internal-category class of §XII.1, `Theory/Functor.v` and `Theory/Natural/Transformation.v` as the `E = Set` templates, and `Structure/Pullback.v` for the induced-map-on-pullbacks bookkeeping.

## Definition of Done

- [ ] `InternalFunctor` defined with the four commutation laws; identity and composite internal functors given.
- [ ] `InternalTransformation` defined with the source/target and internal-naturality laws; vertical composition and identities given.
- [ ] Internal categories/functors/transformations assemble into a category.
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the two classes and the assembled category.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the internal-categories development rises to flagship level.

## Verification

- `coqc -R . Category Structure/InternalCategory/Functor.v` compiles cleanly.
- `Print Assumptions` on `InternalFunctor`, `InternalTransformation`, and the assembled category are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the internal functor's commutation laws and the internal transformation's naturality match Mac Lane §XII.1 (paraphrased; Mac Lane sketches the transformation, so the diagrams are filled in per the standard internal notion).

## Dependencies

Depends on: maclane:XII.1:def1

<!-- catalog: {"ids":["maclane:XII.1:def2","maclane:XII.1:def3"],"deps":["maclane:XII.1:def1"]} -->

---8<---

---
title: "MacLane XII.1: Internal diagrams (left C-objects) and their morphisms"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.1:def4, maclane:XII.1:def5]
deps_item_ids: [maclane:XII.1:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.1 (book pp. 269–270, PDF pp. 276–277). Items `maclane:XII.1:def4` (left `C`-object, i.e. internal diagram / internal base-valued functor) and `maclane:XII.1:def5` (morphism of left `C`-objects).

## Background

For an internal category `C` in `E`, a left `C`-object (internal diagram, internal presheaf) is an object `π : H → C₀` over `C₀` together with an action `μ : C₁ ×_{C₀} H → H` (pullback along `d₀`) that is unital and associative, exactly as a monoid acts on a set; when `E = Set` this is precisely a `Set`-valued functor on `C`. A morphism of left `C`-objects is a map over `C₀` compatible with the two action maps — a natural transformation of internal diagrams. See the nLab, [internal diagram](https://ncatlab.org/nlab/show/internal+diagram).

## Current state in the library

Absent. There is no left-`C`-object structure — no object `π : H → C₀` with an action `μ : C₁ ×_{C₀} H → H` over `d₀` satisfying unit and associativity (search for `InternalDiagram`/internal-presheaf/base-valued-functor definitions returns zero hits; the `Theory/Profunctor.v` "left action" occurrence is profunctor composition, unrelated). When `E = Set` the intended object is an ordinary copresheaf `C ⟶ Sets`, and such functors are present in full (`Theory/Functor.v` into `Instance/Sets.v`), but they are not presented as internal diagrams, and the general internal action is absent for want of the internal-category notion. The morphism notion (a map over `C₀` compatible with the two actions) is likewise absent.

## Work to be done

- Define a `LeftCObject` (internal diagram) over an internal category `C` (of §XII.1): an `E`-object `H` with `π : H → C₀` and an action `μ : C₁ ×_{C₀} H → H` over `C₀`, satisfying the unit law (action by identities is trivial) and the associativity law (action respects `γ`), as setoid equalities.
- Define a `LeftCObjectMorphism`: an `E`-map `φ : H → K` over `C₀` (`π_K ∘ φ ≈ π_H`) commuting with the two action maps, and assemble left `C`-objects and their morphisms into a category.
- Optionally record the `E = Sets` reading: a left `C`-object is a copresheaf `C ⟶ Sets` and a morphism is a natural transformation, connecting to the existing functor/`Sets` machinery.
- Suggested module: `Structure/InternalCategory/Diagram.v`. In-tree donors: the internal-category class of §XII.1, `Structure/Pullback.v` (the action domain `C₁ ×_{C₀} H`), and `Theory/Functor.v`/`Theory/Natural/Transformation.v` for the `Sets` reading.

## Definition of Done

- [ ] `LeftCObject` defined with `π`, the action `μ`, and the unit/associativity laws.
- [ ] `LeftCObjectMorphism` defined (over `C₀`, compatible with the actions); left `C`-objects assemble into a category.
- [ ] The `E = Sets` reading (internal diagram ↔ copresheaf; morphism ↔ natural transformation) recorded, at least for `Sets`.
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the two structures and their category.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the internal-categories development rises to flagship level.

## Verification

- `coqc -R . Category Structure/InternalCategory/Diagram.v` compiles cleanly.
- `Print Assumptions` on `LeftCObject`, its morphism structure, and the assembled category are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the action `μ` with unit/associativity and the morphism's action-compatibility match Mac Lane §XII.1, and the `Set` case recovers copresheaves and their natural transformations.

## Dependencies

Depends on: maclane:XII.1:def1

<!-- catalog: {"ids":["maclane:XII.1:def4","maclane:XII.1:def5"],"deps":["maclane:XII.1:def1"]} -->

---8<---

---
title: "MacLane XII.1: Category objects in Grp are group objects in Cat, and the interchange of internalizations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.1:remark2]
deps_item_ids: [maclane:XII.1:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.1 (book p. 268, PDF pp. 275–276). Item `maclane:XII.1:remark2` (a category object in `Grp` is the same as a group object in `Cat`, and the general interchange-of-structures principle).

## Background

Internalizing two algebraic doctrines commutes: a category object in `Grp` — a category whose object- and arrow-sets are groups with group-homomorphism structure maps — is the same as a group object in `Cat`, and more generally the category of `X`-objects among `Y`-objects coincides with the category of `Y`-objects among `X`-objects (an Eckmann–Hilton-style interchange of commuting structures). See the nLab, [internalization](https://ncatlab.org/nlab/show/internalization), and [group object](https://ncatlab.org/nlab/show/group+object).

## Current state in the library

Absent. The two ingredients partly exist — `Structure/Group.v:112` (`GroupObject`, a group object in a cartesian monoidal category) and `Instance/Cat/Cartesian.v:39` (`Cat_Cartesian`) — so the *type* "group object in `Cat`" is expressible, but it is never instantiated (zero `GroupObject` hits in `Instance/`), and the substantive content (its identification with a category object in `Grp`, and the general interchange principle) is unformalizable without the internal-category notion of §XII.1. `Structure/Group.v:72` notes in prose only the different Eckmann–Hilton fact that a group object in `Grp` is abelian.

## Work to be done

- Instantiate a group object in `Cat` using the in-tree `GroupObject` at `Cat_Cartesian`, and define (or specialize the §XII.1 internal-category notion to) a category object in `Grp` — a category internal to the category of groups (#255).
- Prove the identification: category objects in `Grp` and group objects in `Cat` are the same, exhibiting the correspondence on objects and morphisms.
- State and prove the interchange principle at the level generality the library supports (at least the `Grp`/`Cat` case, ideally an abstract "commuting internalizations" lemma over two cartesian doctrines).
- Suggested modules: `Structure/InternalCategory/Grp.v` (the two presentations and their identification) and/or `Instance/Cat/GroupObject.v`. In-tree donors: the internal-category class of §XII.1, `Structure/Group.v` (`GroupObject`), `Instance/Cat/Cartesian.v` (`Cat_Cartesian`), and the category of groups (#255).

## Definition of Done

- [ ] Group object in `Cat` instantiated; category object in `Grp` defined (as a specialization of the §XII.1 internal category to groups).
- [ ] The identification "category object in `Grp` = group object in `Cat`" proved in both directions.
- [ ] The interchange-of-internalizations principle stated and proved for the `Grp`/`Cat` case (and abstractly where feasible).
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the identification.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Structure/InternalCategory/Grp.v` compiles cleanly.
- `Print Assumptions` on the `Grp`/`Cat` identification is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the identification and interchange statement match Mac Lane §XII.1 (paraphrased).

## Dependencies

Depends on: maclane:XII.1:def1
Depends on: #255

<!-- catalog: {"ids":["maclane:XII.1:remark2"],"deps":["maclane:XII.1:def1","#255"]} -->

---8<---

---
title: "MacLane XII.2: The nerve of a category as a simplicial set"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.2:construction1, maclane:XII.2:ex1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.2 (book pp. 270–272, PDF pp. 277–279). Items `maclane:XII.2:construction1` (the nerve of a small category as a simplicial set) and `maclane:XII.2:ex1` (verify the simplicial identities for the nerve).

## Background

The nerve of a small category `C` is the simplicial set whose `n`-simplices are strings of `n` composable arrows: `C₀`, `C₁`, `C₂ = C₁ ×_{C₀} C₁`, …, `Cₙ` the iterated pullback; the face maps `dᵢ` drop an end arrow (`i = 0, n`) or compose an adjacent pair (`0 < i < n`) and the degeneracies `sⱼ` insert an identity, satisfying the simplicial identities. See the nLab, [nerve](https://ncatlab.org/nlab/show/nerve), and Wikipedia, [Nerve (category theory)](https://en.wikipedia.org/wiki/Nerve_(category_theory)).

## Current state in the library

Absent. There is no nerve construction and no simplicial-set target for it: whole-tree search for `Nerve`/`Simplic`/face/degeneracy definitions returns zero hits, and every `delta` identifier in-tree is a (co)monoid comultiplication, not a simplex-category face/degeneracy. The topic appears only in background essays (`Theory/Kan/Extension.v:36,91` names "nerve and realization" as motivation; `Instance/FinSet.v:86–89` states that presheaves on FinSet are augmented *symmetric* simplicial sets and that the simplex category embeds into FinSet, without constructing it; `Structure/Coend.v:113` mentions geometric realization). The pieces to build over exist — pullbacks (`Structure/Pullback.v`) and small index shapes (`Instance/Omega.v`, `Instance/Two.v`, `Instance/Parallel.v`) — but the simplicial-set machinery itself is being introduced separately (#515, over the simplex category #225).

## Work to be done

- Build the nerve functor `N : Cat ⟶ sSet` (into the simplicial-set category of #515): define `(N C)ₙ` via the iterated pullback of `n` composable arrows (equivalently as functors out of the ordinal `[n]`), the face maps `dᵢ` (drop-end / compose-adjacent) and degeneracies `sⱼ` (insert-identity).
- Discharge Exercise 1: prove the face/degeneracy (simplicial) identities, so that `N C` is a genuine object of the simplicial-set category, and prove functoriality of `N` in `C`.
- Suggested module: `Instance/Simplicial/Nerve.v` (or `Construction/Nerve.v`). In-tree donors: the simplicial sets/objects of #515, the simplex category of #225, `Structure/Pullback.v` (the iterated pullback `Cₙ`), and `Theory/Category.v`/`Instance/Cat.v` for the source functoriality.

## Definition of Done

- [ ] `N C` defined levelwise (`Cₙ` via iterated pullback) with faces `dᵢ` and degeneracies `sⱼ`.
- [ ] The simplicial identities proved (Exercise 1), so `N C` is an object of the simplicial-set category.
- [ ] `N : Cat ⟶ sSet` shown functorial in `C`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `N` and the simplicial-identity lemmas.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Instance/Simplicial/Nerve.v` compiles cleanly.
- `Print Assumptions` on `N` (the nerve functor) and the simplicial-identity lemmas show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the levelwise pullbacks, faces, degeneracies, and simplicial identities match Mac Lane §XII.2 (construction and Exercise 1).

## Dependencies

Depends on: #515
Depends on: #225

<!-- catalog: {"ids":["maclane:XII.2:construction1","maclane:XII.2:ex1"],"deps":["#515","#225"]} -->

---8<---

---
title: "MacLane XII.2: The nerve of an internal category as a simplicial object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.2:remark1]
deps_item_ids: [maclane:XII.2:construction1, maclane:XII.1:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.2 (book p. 271, PDF p. 278). Item `maclane:XII.2:remark1` (the nerve of an internal category in `E` is a simplicial object in `E`).

## Background

The same iterated-pullback nerve construction, applied to a category object in an ambient finitely complete `E`, produces a simplicial object in `E` (a functor `Δᵒᵖ → E`) rather than a simplicial set. See the nLab, [simplicial object](https://ncatlab.org/nlab/show/simplicial+object), and [nerve](https://ncatlab.org/nlab/show/nerve).

## Current state in the library

Absent. No simplicial object in a general `E` is built (search for a `Simplicial`-in-`E` object returns zero hits; the only "simplicial" mentions are the bar-resolution essays in `Comonad/*`). This item sits on two prerequisites that are themselves being introduced elsewhere: the nerve construction of §XII.2 and the internal-category notion of §XII.1. Once those exist, the internal nerve is the evident generalization, landing in the simplicial-objects target of #515.

## Work to be done

- Generalize the nerve (of §XII.2) to a category object in a finitely complete `E` (of §XII.1): form `Cₙ` as the iterated pullback in `E`, with the `E`-morphism faces and degeneracies, yielding a simplicial object in `E` (a functor `Δᵒᵖ ⟶ E`, using the simplicial-object target of #515).
- Prove the simplicial identities hold at the level of `E`-morphisms, and that the ordinary nerve of §XII.2 is the `E = Sets` case.
- Suggested module: `Construction/Nerve/Internal.v` (or a section of the nerve module). In-tree donors: the nerve of §XII.2, the internal-category class of §XII.1, the simplicial-objects target of #515, and `Structure/Pullback.v`.

## Definition of Done

- [ ] The internal nerve of a category object in `E` defined as a simplicial object in `E` (functor `Δᵒᵖ ⟶ E`).
- [ ] The simplicial identities proved at the `E`-morphism level; the `E = Sets` case recovers the ordinary nerve.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the internal-nerve construction.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Construction/Nerve/Internal.v` compiles cleanly.
- `Print Assumptions` on the internal-nerve construction is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the internal nerve is a simplicial object in `E` and specializes to the ordinary nerve, matching Mac Lane §XII.2.

## Dependencies

Depends on: maclane:XII.2:construction1
Depends on: maclane:XII.1:def1
Depends on: #515

<!-- catalog: {"ids":["maclane:XII.2:remark1"],"deps":["maclane:XII.2:construction1","maclane:XII.1:def1","#515"]} -->

---8<---

---
title: "MacLane XII.3: The hom-category (Cat-enriched) formulation of a 2-category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.3:def2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.3 (book pp. 275–276, PDF pp. 282–283). Item `maclane:XII.3:def2` (the equivalent hom-category / `Cat`-enriched formulation of a 2-category, and its equivalence with the elementary definition).

## Background

Parallel to the hom-set definition of a category, a 2-category can be given by hom-*categories*: objects `a, b, …`; for each pair a category `T(a,b)` (arrows = 2-cells under vertical composition); for each triple a composition functor `K : T(b,c) × T(a,b) → T(a,c)`; and identity-picking functors `Uₐ : 1 → T(a,a)`; with strict associativity and units. This exhibits a 2-category as a category enriched in `Cat`. See the nLab, [2-category](https://ncatlab.org/nlab/show/2-category), and [enriched category](https://ncatlab.org/nlab/show/enriched+category).

## Current state in the library

Partial. The general enriched-category notion is present as `Construction/Enriched.v:111` (`Class Enriched (K : Category) {@Monoidal K}`), whose header (`:69`) explicitly names `K = Cat` as giving strict 2-categories — but that specialization is not realized: there is no `Monoidal` instance on `Cat` (`Instance/Cat/Cartesian.v:39` provides `Cat_Cartesian` but it is not wired to `Monoidal`, and `Enriched` is instantiated only at `Sets` and `Two`). The hom-category *shape* also appears weakly in `Theory/Bicategory.v:241` (`bicat x y : Category` as `T(a,b)`, `hcompose` as the composition bifunctor `K`, `bi1id` for `Uₐ`), but that is the *weak* (bicategory) packaging, not the strict `Cat`-enriched category, and the equivalence with the elementary strict 2-category (built via #283's double-category route) is not proved.

## Work to be done

- Construct a monoidal structure on `Cat` from the existing `Cat_Cartesian` (cartesian monoidal), i.e. a `Monoidal Cat` instance — a reusable construction.
- Instantiate `Enriched` at `K = Cat` and show the resulting `Cat`-enriched category is exactly the hom-category formulation of §XII.3 (`T(a,b)` a category, `K` a composition functor, `Uₐ` the identity-picker), with strict associativity/units.
- Prove the equivalence of the two axiomatizations: the strict 2-category built via the double-category route (#283) and the `Cat`-enriched category agree.
- Suggested modules: `Instance/Cat/Monoidal.v` (the `Monoidal Cat` instance), `Instance/Cat/Enriched.v` (the `Cat`-enriched-category = 2-category realization and the equivalence). In-tree donors: `Construction/Enriched.v` (the `Enriched` class), `Instance/Cat/Cartesian.v` (`Cat_Cartesian`), `Theory/Bicategory.v` (the hom-category shape), and the strict 2-category of #283.

## Definition of Done

- [ ] `Monoidal Cat` (cartesian monoidal) constructed and registered.
- [ ] `Enriched` instantiated at `K = Cat`, yielding the hom-category formulation of a 2-category (`T(a,b)`, `K`, `Uₐ`) with strict associativity/units.
- [ ] The equivalence with the elementary strict 2-category (#283) proved.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `Monoidal Cat`, the `Cat`-enriched realization, and the equivalence.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (a `Monoidal Cat` instance is a reusable, flagship-level addition).

## Verification

- `coqc -R . Category Instance/Cat/Monoidal.v Instance/Cat/Enriched.v` compiles cleanly.
- `Print Assumptions` on `Monoidal Cat`, the `Cat`-enriched 2-category, and the equivalence show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the hom-category data `(T(a,b), K, Uₐ)` and its equivalence with the elementary definition match Mac Lane §XII.3.

## Dependencies

Depends on: #283

<!-- catalog: {"ids":["maclane:XII.3:def2"],"deps":["#283"]} -->

---8<---

---
title: "MacLane XII.3: The homotopy 2-category of topological spaces"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.3:construction2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.3 (book pp. 272–273, PDF pp. 279–280). Item `maclane:XII.3:construction2` (topological spaces, continuous maps, and homotopy classes of homotopies as a 2-category).

## Background

Topological spaces form a 2-category with continuous maps as 1-cells and homotopy *classes* of homotopies as 2-cells; classes are needed because the naive concatenation of homotopies is associative only up to reparametrization. There is a vertical composite (concatenation of homotopy classes) and a horizontal composite, and horizontal composition commutes with vertical. See the nLab, [homotopy 2-category](https://ncatlab.org/nlab/show/homotopy+2-category), and [2-category](https://ncatlab.org/nlab/show/2-category).

## Current state in the library

Absent. There is no category of topological spaces, no continuous maps, and no homotopies: a search for topological-space datatypes, `Top`, open sets, or continuous maps finds only prose (`Theory/Universal/Arrow.v:38` mentions "topology"), and the `homotopy` hits are the contracting homotopies of bar resolutions (`Comonad/Coalgebra.v`), unrelated to homotopies of continuous maps. Consequently the homotopy 2-category of §XII.3 has no in-tree counterpart. Its prerequisites — the category `Top` (#259) and the homotopy relation on maps (#260) — are being introduced separately, and the target "2-category" needs the strict 2-category vocabulary of #283.

## Work to be done

- Over `Top` (#259) and the homotopy notion (#260): define homotopies between continuous maps, take homotopy classes (quotient by reparametrization/end-fixing homotopy of homotopies), and give vertical and horizontal composition of classes.
- Assemble spaces / continuous maps / homotopy-classes-of-homotopies as a strict 2-category (using the strict 2-category interface of #283), verifying the interchange law and the identity conditions.
- Suggested module: `Instance/Top/TwoCategory.v`. In-tree donors: the category `Top` (#259), the homotopy relation (#260), the strict 2-category interface of #283, and `Construction/Quotient.v` for the homotopy-class quotient.

## Definition of Done

- [ ] Homotopy of continuous maps and homotopy classes of homotopies defined (with the reparametrization quotient).
- [ ] Vertical and horizontal composition of 2-cells defined; the interchange law and identity conditions proved.
- [ ] `Top` with these 2-cells assembled as a strict 2-category (per #283).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the 2-category instance.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Instance/Top/TwoCategory.v` compiles cleanly.
- `Print Assumptions` on the homotopy-2-category instance is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: 2-cells are homotopy classes of homotopies with interchange holding, matching Mac Lane §XII.3.

## Dependencies

Depends on: #259
Depends on: #260
Depends on: #283

<!-- catalog: {"ids":["maclane:XII.3:construction2"],"deps":["#259","#260","#283"]} -->

---8<---

---
title: "MacLane XII.4: Right Kan extensions in a 2-category (formal Kan extensions)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.4:def2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.4 (book pp. 277–278, PDF pp. 284–285). Item `maclane:XII.4:def2` (right Kan extension in an arbitrary 2-category).

## Background

Right Kan extensions are a 2-categorical notion: given 1-cells `k : m → c` and `t : m → a`, a right Kan extension of `t` along `k` is a 1-cell `r : c → a` with a universal 2-cell `ε : r∘k ⇒ t` — for every `α : s∘k ⇒ t` there is a unique `σ : s ⇒ r` factoring `α` through `ε` whiskered by `k`. This is the formal (2-categorical) lifting of the ordinary right Kan extension. See the nLab, [Kan extension](https://ncatlab.org/nlab/show/Kan+extension).

## Current state in the library

Partial. The exact universal-property shape is formalized, but only in the 2-category `Cat`: `Theory/Kan/Extension.v:154` (`LocalRightKan`, with the extending 1-cell `LocalRan`, the counit `ran_transform : LocalRan ◯ F ⟹ X`, and the unique mediating `δ`) and `:140` (`RightKan` as the right adjoint to precomposition). No Kan-extension notion appears internal to a bicategory or general 2-category — a search for `kan` in `Theory/Bicategory/` returns zero hits — so the abstract 2-categorical definition is available only in its `Cat` instance (1-cells = functors, 2-cells = natural transformations). This is asymmetric with the adjunction case, where `Theory/Bicategory/Adjunction.v` already gives `BicatAdjunction` internal to an arbitrary bicategory.

## Work to be done

- Define a right Kan extension internal to a bicategory (which the library already has as `Theory/Bicategory.v`; a bicategory subsumes Mac Lane's strict 2-category): 1-cells `k`, `t`, an extending 1-cell `r`, a 2-cell `ε : r∘k ⇒ t` (up to the coherence isos), and the universal property producing a unique mediating 2-cell.
- Show it specializes, in the bicategory `Cat`, to the existing `LocalRightKan`; optionally state the dual (left Kan extension) by the built-in bicategory duality once available.
- Suggested module: `Theory/Bicategory/Kan.v`. In-tree donors: `Theory/Bicategory.v` (the bicategory interface and coherence isos), `Theory/Bicategory/Adjunction.v` (`BicatAdjunction`, the sibling internal universal notion), and `Theory/Kan/Extension.v` (the `Cat` specialization to recover).

## Definition of Done

- [ ] Right Kan extension defined internal to a bicategory (extending 1-cell, universal 2-cell, unique mediator), coherence-iso-conjugated as needed.
- [ ] Specialization to `Cat` recovers the in-tree `LocalRightKan`.
- [ ] All 2-cell equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the bicategorical Kan extension and the `Cat` specialization.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/Bicategory/Kan.v` compiles cleanly.
- `Print Assumptions` on the bicategorical right Kan extension and its `Cat` specialization show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the universal 2-cell and unique-mediator property match Mac Lane §XII.4, and the `Cat` case agrees with the existing Kan extension.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XII.4:def2"],"deps":[]} -->

---8<---

---
title: "MacLane XII.4: 2-functors and 2-natural transformations (strict)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.4:def3, maclane:XII.4:def4]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.4 (book p. 278, PDF p. 285). Items `maclane:XII.4:def3` (2-functor) and `maclane:XII.4:def4` (2-natural transformation).

## Background

A (strict) 2-functor between 2-categories preserves all 0-, 1-, and 2-cell structure on the nose — identities and both composites in every dimension — with no compositor/unitor isomorphisms. A (strict) 2-natural transformation assigns a 1-cell to each object so that every naturality square commutes strictly. See the nLab, [2-functor](https://ncatlab.org/nlab/show/2-functor), and [2-natural transformation](https://ncatlab.org/nlab/show/2-natural+transformation).

## Current state in the library

Partial. Only the *weak* versions exist. `Theory/Bicategory/Pseudofunctor.v:147` (`Pseudofunctor`) carries genuine invertible-2-cell data `pf_id : pf1(bi1id) ≅ bi1id` and `pf_comp : pf1(g∘f) ≅ pf1 g ∘ pf1 f`, preserving identities and horizontal composition only up to iso — whereas a 2-functor preserves them strictly. `Theory/Bicategory/Lax.v:56` (`LaxTransformation`) carries a naturator 2-cell `lt1` as data, and `:152` (`Pseudonatural`) only forces it invertible, not identity; the strict 2-natural transformation (identity naturator, strictly commuting squares) is not carved out. The `Cat`-enriched route (`EnrichedFunctor` at `Construction/Enriched.v:145`, `EnrichedTransform` at `Construction/Enriched/Natural.v:28`) is blocked by the absence of a `Monoidal Cat` instance.

## Work to be done

- Over the strict 2-category interface (#283), define a strict `TwoFunctor`: maps on 0-/1-/2-cells preserving identities and both composites as setoid equalities (either directly, or by carving out the `Pseudofunctor` special case with identity compositor/unitor and proving the coherence trivial).
- Define a strict `TwoNaturalTransformation`: a family of 1-cells with strictly commuting naturality squares (the `LaxTransformation` special case with identity naturator), with vertical composition and identities.
- Provide `Cat` (or another concrete strict 2-category) as a witness where the strict notions are inhabited.
- Suggested modules: `Theory/TwoCategory/Functor.v`, `Theory/TwoCategory/Transformation.v` (building on #283's `Theory/TwoCategory.v`). In-tree donors: the strict 2-category of #283, `Theory/Bicategory/Pseudofunctor.v` and `Theory/Bicategory/Lax.v` (the weak versions to strictify), and `Construction/Enriched.v` for the enriched reading.

## Definition of Done

- [ ] Strict `TwoFunctor` defined (on-the-nose preservation of identities and both composites).
- [ ] Strict `TwoNaturalTransformation` defined (strictly commuting squares) with vertical composition and identities.
- [ ] A concrete witness (e.g. `Cat`) inhabits both notions.
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the two classes and the witness.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/TwoCategory/Functor.v Theory/TwoCategory/Transformation.v` compiles cleanly.
- `Print Assumptions` on `TwoFunctor`, `TwoNaturalTransformation`, and the witness show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: strict (on-the-nose) preservation and strictly commuting naturality squares match Mac Lane §XII.4.

## Dependencies

Depends on: #283

<!-- catalog: {"ids":["maclane:XII.4:def3","maclane:XII.4:def4"],"deps":["#283"]} -->

---8<---

---
title: "MacLane XII.4: The 2-category 2-Cat"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.4:construction1]
deps_item_ids: [maclane:XII.4:def3, maclane:XII.4:def4]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.4 (book p. 278, PDF p. 285). Item `maclane:XII.4:construction1` (2-categories, 2-functors, and 2-natural transformations form a 2-category, `2-Cat`).

## Background

2-categories (0-cells), 2-functors (1-cells), and 2-natural transformations (2-cells) themselves assemble into a 2-category, denoted `2-Cat`; the modifications supply the fillers between 2-natural transformations. See the nLab, [2-category](https://ncatlab.org/nlab/show/2-category).

## Current state in the library

Partial. The constituents exist but only in weak form, and the global object is not assembled. `Theory/Bicategory/Pseudofunctor.v:227,463` give identity and composite pseudofunctors, `Theory/Bicategory/Lax.v` the lax/pseudonatural transformations, `Theory/Bicategory/Modification.v:57` the modifications, and `Theory/Bicategory/Modification.v:162` (`LaxTransformation_Category`) assembles a *single* hom-category of lax transformations (with modifications as morphisms) between two fixed pseudofunctors. But there is no `2-Cat` object: `Instance/Cat/Bicategory.v:22` explicitly disclaims a "bicategory of bicategories", and the only `Bicategory`-valued definitions in-tree are `Cat_Bicategory`, `Monoidal_OneObject_Bicategory`, and `Trivial_Bicategory`.

## Work to be done

- Using the strict 2-functors and 2-natural transformations of §XII.4 (and modifications, present as `Theory/Bicategory/Modification.v`), assemble `2-Cat`: 0-cells strict 2-categories, 1-cells strict 2-functors, hom-2-cells 2-natural transformations, with the hom-categories `T(a,b)` (2-natural transformations and modifications), horizontal composition of 2-functors, and the coherence (here strict) making it a 2-category.
- Address the universe placement (as with `Cat`, `2-Cat` sits one level up); a registration-free `Definition` is acceptable, mirroring `Cat_Bicategory`.
- Suggested module: `Instance/TwoCat.v`. In-tree donors: the strict 2-functors/2-natural transformations of §XII.4, `Theory/Bicategory/Modification.v` (`LaxTransformation_Category` as the hom-category template), the strict 2-category interface of #283, and `Instance/Cat/Bicategory.v` for the universe/packaging pattern.

## Definition of Done

- [ ] `2-Cat` assembled with strict 2-categories / 2-functors / 2-natural transformations (and modifications as the top cells), and its 2-category laws verified.
- [ ] Universe placement handled consistently with `Cat` (registration-free `Definition` acceptable).
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `2-Cat`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Instance/TwoCat.v` compiles cleanly.
- `Print Assumptions` on `2-Cat` is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `2-Cat` has 2-categories as 0-cells, 2-functors as 1-cells, and 2-natural transformations as 2-cells, matching Mac Lane §XII.4.

## Dependencies

Depends on: maclane:XII.4:def3
Depends on: maclane:XII.4:def4
Depends on: #283

<!-- catalog: {"ids":["maclane:XII.4:construction1"],"deps":["maclane:XII.4:def3","maclane:XII.4:def4","#283"]} -->

---8<---

---
title: "MacLane XII.4: 3-categories via enrichment in 2-Cat"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.4:remark1]
deps_item_ids: [maclane:XII.4:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.4 (book p. 279, PDF p. 286). Item `maclane:XII.4:remark1` (a modification is a 3-cell; iterating enrichment, a 2-category is a `Cat`-enriched category and a 3-category is a `2-Cat`-enriched category).

## Background

Iterating the enriched-hom viewpoint climbs the dimension ladder: a category with hom-sets enriched in `Cat` is a 2-category, and a category with hom-sets enriched in `2-Cat` is a 3-category; a modification then plays the role of a 3-cell. See the nLab, [3-category](https://ncatlab.org/nlab/show/3-category), and [n-category](https://ncatlab.org/nlab/show/n-category).

## Current state in the library

Partial. The "3-cell" is realized — `Theory/Bicategory/Modification.v:57` (`Modification`) is exactly a top-dimensional modification — and the enrichment device the remark invokes exists abstractly as `Construction/Enriched.v:111` (`Enriched (K : Category) {@Monoidal K}`). But the substantive content is uninstantiated: there is no `2-Cat` (see §XII.4 construction), no monoidal structure on `2-Cat`, and consequently no "category enriched in `2-Cat`" and no 3-category (search for `3-categor`/`tricategor` returns zero hits; the enrichment class is instantiated only at `Sets` and `Two`).

## Work to be done

- Equip `2-Cat` (of §XII.4) with the monoidal structure needed to enrich over it (cartesian monoidal from its finite products, mirroring the `Monoidal Cat` step).
- Instantiate `Enriched` at `K = 2-Cat` and define a 3-category as a `2-Cat`-enriched category; identify the modification as the resulting 3-cell.
- Optionally record the tower relationship (`Cat`-enrichment ⟹ 2-categories at the level below).
- Suggested module: `Theory/ThreeCategory.v`. In-tree donors: `2-Cat` (of §XII.4), `Construction/Enriched.v` (the enrichment class), and `Theory/Bicategory/Modification.v` (the modification as 3-cell).

## Definition of Done

- [ ] A monoidal structure on `2-Cat` constructed (for the enrichment).
- [ ] A 3-category defined as a `2-Cat`-enriched category; the modification identified as its 3-cell.
- [ ] All equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the 3-category notion.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/ThreeCategory.v` compiles cleanly.
- `Print Assumptions` on the 3-category notion is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: a 3-category is a `2-Cat`-enriched category with modifications as 3-cells, matching Mac Lane §XII.4.

## Dependencies

Depends on: maclane:XII.4:construction1

<!-- catalog: {"ids":["maclane:XII.4:remark1"],"deps":["maclane:XII.4:construction1"]} -->

---8<---

---
title: "MacLane XII.5: Single-set (arrows-only) categories and functors via source/target operators"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.5:def1, maclane:XII.5:def2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.5 (book p. 279, PDF p. 286). Items `maclane:XII.5:def1` (a single-set / arrows-only category via source and target operators) and `maclane:XII.5:def2` (functor between single-set categories).

## Background

Mac Lane's §XII.5 presentation of a category uses one set `C` of arrows with source/target endofunctions `s, t : C → C` and a partial composition `x # y` defined exactly when `s x = t y`, subject to `s(x#y) = s y`, `t(x#y) = t x`, the unit laws `x#(s x) = x` and `(t x)#x = x`, associativity, and the idempotence laws `ssx = sx = tsx`, `ttx = tx = stx`; an element is an identity iff `x = s x = t x`. A functor is an arrow-function commuting with `s`, `t` and preserving `#`. This source/target formulation is the substrate for the single-set `n`- and `ω`-categories of the same section. See the nLab, [single-sorted definition of a category](https://ncatlab.org/nlab/show/single-sorted+definition+of+a+category).

## Current state in the library

Partial (object), absent (functor). The arrows-only category is captured — `Theory/Metacategory/ArrowsOnly.v:37` (`Record Metacategory`, with `Category_from_Metacategory:212`) and `Theory/Metacategory.v:133` (with `FromArrows:261`) — but in the Mac Lane I.1 composable-pairs form, over a *fixed* arrow sort `N`/`nat` with a finite-map composition table, not the §XII.5 source/target-operator form; the general-carrier version with corrected identity axioms is the subject of #217. The single-set *functor* (an arrow-function commuting with `s`, `t` and preserving partial composition) is entirely absent: the only functors in the arrows-only files (`Two_to_Two`, `Two_from_Two`) are ordinary functors between the *derived* categories, not single-set arrow-maps. Separately, the existing `identity_law` field is documented (in-file `jww` TODO) as vacuous as written — a latent defect this rework should repair.

## Work to be done

- Define a single-set category in the §XII.5 source/target form: an arrow `Type` with `s, t : C → C`, a partial composition (relation or partial function) defined when `s x = t y`, and the `s`/`t`, unit, associativity, and idempotence laws stated *correctly* (not vacuously); characterize identities as the `s`/`t` fixed points.
- Define a single-set functor: an arrow-function commuting with `s`, `t` and preserving partial composition, with identity and composite functors.
- Relate the source/target form to the composable-pairs arrows-only record built under #217 (they present the same categories), so this issue is the source/target increment on top of #217 rather than a re-derivation.
- Suggested modules: `Theory/Metacategory/SourceTarget.v` (the `s`/`t` single-set category and functor). In-tree donors: the general-carrier arrows-only record of #217, `Theory/Metacategory/ArrowsOnly.v` and `Theory/Metacategory.v` (the composable-pairs presentation to bridge), and `Theory/Category.v` for the derived two-sorted category.

## Definition of Done

- [ ] Single-set category defined in the `s`/`t` operator form over an arbitrary arrow `Type`, with all §XII.5 laws stated non-vacuously (the vacuous `identity_law` issue does not recur).
- [ ] Single-set functor defined (commutes with `s`, `t`, preserves `#`) with identities and composites.
- [ ] The source/target form related to the composable-pairs arrows-only record of #217.
- [ ] All equations use setoid `≈` where morphisms are involved; the partial-composition equalities are stated with the correct definedness guards.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the single-set category and functor.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/Metacategory/SourceTarget.v` compiles cleanly.
- `Print Assumptions` on the single-set category and functor are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the `s`/`t`, unit, associativity, idempotence laws and the functor conditions match Mac Lane §XII.5, and the identity axioms are non-vacuous.

## Dependencies

Depends on: #217

<!-- catalog: {"ids":["maclane:XII.5:def1","maclane:XII.5:def2"],"deps":["#217"]} -->

---8<---

---
title: "MacLane XII.5: Single-set n-categories and ω-categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.5:def3, maclane:XII.5:def4, maclane:XII.5:def5]
deps_item_ids: [maclane:XII.5:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.5 (book p. 280, PDF p. 287). Items `maclane:XII.5:def3` (single-set 2-category), `maclane:XII.5:def4` (single-set `n`-category), and `maclane:XII.5:def5` (`ω`-category).

## Background

Iterating the single-set presentation: a single-set 2-category is one set carrying two single-set category structures — a "horizontal" `(#₀, s₀, t₀)` and a "vertical" `(#₁, s₁, t₁)` — that commute (their source/target operators commute) and satisfy the interchange law, with every identity of the first structure an identity of the second. A single-set `n`-category has `n` pairwise-commuting such structures, and an `ω`-category has infinitely many. See the nLab, [strict omega-category](https://ncatlab.org/nlab/show/strict+omega-category), and [n-category](https://ncatlab.org/nlab/show/n-category).

## Current state in the library

Absent. There is no single-set 2-category (two commuting single-set structures on one 2-cell set with the interchange law), no single-set `n`-category, and no `ω`-category: search for single-set two-structure interchange and for `omega-categor`/`n-categor`/`globular` returns zero relevant hits (the interchange occurrences are the bifunctor middle-four in `Functor/Bifunctor.v` and `Comonad/Strong.v`, not a single-set two-structure law). The in-tree 2-dimensional development is the weak, hom-category-based `Theory/Bicategory.v`, a different presentation, and `Instance/Omega.v` is the ordinal-`ω` *shape* category for Adámek's chain, not an `ω`-category.

## Work to be done

- Over the single-set category of §XII.5: define a single-set 2-category as one arrow set with two single-set category structures `(#₀, s₀, t₀)`, `(#₁, s₁, t₁)`, the four source/target commutation equations, the interchange law `(x #₀ u) #₁ (y #₀ v) = (x #₁ y) #₀ (u #₁ v)`, and the identity-inclusion condition.
- Generalize to a single-set `n`-category (`n` pairwise-commuting structures with the higher-identity-inclusion condition) and to an `ω`-category (an indexed family over all `i`), likely via a `nat`-indexed family of single-set structures with the pairwise interchange/inclusion laws.
- Suggested module: `Theory/Metacategory/NCategory.v`. In-tree donor: the single-set category and functor of §XII.5.

## Definition of Done

- [ ] Single-set 2-category defined (two commuting single-set structures, interchange, identity inclusion).
- [ ] Single-set `n`-category and `ω`-category defined (indexed families with pairwise interchange/inclusion).
- [ ] All equations use setoid `≈` where morphisms are involved, with correct definedness guards on the partial compositions.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the 2-/`n`-/`ω`-category definitions.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/Metacategory/NCategory.v` compiles cleanly.
- `Print Assumptions` on the single-set 2-/`n`-/`ω`-category definitions are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the two commuting structures, interchange law, and iteration to `n` and `ω` match Mac Lane §XII.5.

## Dependencies

Depends on: maclane:XII.5:def1

<!-- catalog: {"ids":["maclane:XII.5:def3","maclane:XII.5:def4","maclane:XII.5:def5"],"deps":["maclane:XII.5:def1"]} -->

---8<---

---
title: "MacLane XII.6: The two duals of a bicategory"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.6:remark1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.6 (book p. 282, PDF pp. 289–290). Item `maclane:XII.6:remark1` (a bicategory, or 2-category, has two distinct duals).

## Background

A bicategory admits two independent opposites: `Bᵒᵖ`, obtained by reversing the 1-cells (`a → b` becomes `b → a`, with horizontal composition reversed), and `Bᶜᵒ`, obtained by reversing the 2-cells (each hom-category `B(a,b)` is replaced by its opposite). Combining both gives a third, `Bᶜᵒᵒᵖ`. See the nLab, [bicategory](https://ncatlab.org/nlab/show/bicategory), and [opposite category](https://ncatlab.org/nlab/show/opposite+category).

## Current state in the library

Absent. There is no bicategory-valued opposite construction — neither the 1-cell reversal `Bᵒᵖ` nor the 2-cell reversal `Bᶜᵒ` (a search for `op.?bicat`/`co.?bicat`/reverse-1-cell/reverse-2-cell returns zero hits). The only `Bicategory`-valued definitions in-tree are `Cat_Bicategory`, `Monoidal_OneObject_Bicategory` (`Theory/Bicategory/OneObject.v:57`), and `Trivial_Bicategory` (`Theory/Bicategory/Lax.v:176`), none a dual of a given bicategory. `Natural/Transformation/Opposite.v:15` is the `Cat`-specific natural-transformation opposite, not a `Bicategory → Bicategory` construction, and although the library has built-in duality for 1-categories (`Construction/Opposite.v`, `C^op^op = C` by reflexivity), that machinery is not lifted to the `Bicategory` class.

## Work to be done

- Define `Bᵒᵖ` for a bicategory `B`: same 0-cells, hom-categories `Bᵒᵖ(a,b) := B(b,a)`, horizontal composition reversed, with the associator/unitors transported; aim to keep `Bᵒᵖᵒᵖ = B` (up to the coherence the setoid setting allows, ideally definitionally as with `Construction/Opposite.v`).
- Define `Bᶜᵒ`: same 0- and 1-cells, hom-categories replaced by their opposites (`Bᶜᵒ(a,b) := B(a,b)ᵒᵖ`), horizontal composition kept, coherence 2-cells inverted; check `Bᶜᵒᶜᵒ = B`.
- Optionally record that the two operations commute, yielding `Bᶜᵒᵒᵖ`.
- Suggested module: `Theory/Bicategory/Opposite.v`. In-tree donors: `Theory/Bicategory.v` (the class and coherence isos), `Construction/Opposite.v` (the 1-category opposite to reuse on the hom-categories for `Bᶜᵒ`), and `Instance/Cat/Bicategory.v` for the packaging/universe pattern.

## Definition of Done

- [ ] `Bᵒᵖ` (1-cell reversal) defined as a `Bicategory`, with the coherence laws transported and involutivity recorded.
- [ ] `Bᶜᵒ` (2-cell reversal) defined as a `Bicategory`, with involutivity recorded.
- [ ] All 2-cell equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for both duals.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/Bicategory/Opposite.v` compiles cleanly.
- `Print Assumptions` on `Bᵒᵖ` and `Bᶜᵒ` are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `Bᵒᵖ` reverses 1-cells and `Bᶜᵒ` reverses 2-cells, matching Mac Lane §XII.6.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XII.6:remark1"],"deps":[]} -->

---8<---

---
title: "MacLane XII.7: Every one-object bicategory is a monoidal category (and bicategorical coherence)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.7:construction1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.7 (book p. 283, PDF p. 290). Item `maclane:XII.7:construction1` (a monoidal category is the same as a one-0-cell bicategory, and monoidal coherence yields bicategorical coherence for `α`, `λ`, `ρ`).

## Background

Delooping identifies monoidal categories with one-object bicategories: the single hom-category is the monoidal category, horizontal composition is the tensor, and the associativity/unit isomorphisms are `α`, `λ`, `ρ`. The correspondence is a biconditional, and it transports the monoidal coherence theorem to a coherence result for bicategorical `α`, `λ`, `ρ`. See the nLab, [delooping](https://ncatlab.org/nlab/show/delooping), and [monoidal category](https://ncatlab.org/nlab/show/monoidal+category).

## Current state in the library

Partial. The forward delooping is fully built: `Theory/Bicategory/OneObject.v:56` (`Monoidal_OneObject_Bicategory`) turns any `Monoidal C` into a one-object `Bicategory` with every coherence law, and `:90` (`Monoidal_OneObject_unit_coincidence`) transports Kelly's `λ_I ≈ ρ_I`. Missing are the other two halves of the book item: (1) the converse, that every one-0-cell bicategory is a monoidal category — no `Bicategory → Monoidal` construction exists in-tree (the only `Bicategory`-valued definitions are `Cat_Bicategory`, `Monoidal_OneObject_Bicategory`, and `Trivial_Bicategory`); and (2) the stated consequence that monoidal coherence yields `α`/`λ`/`ρ` coherence for bicategories — Mac Lane–Paré coherence is cited only in the essay at `Theory/Bicategory.v:113`, with only the single unit-coincidence instance transported.

## Work to be done

- Construct the converse `Bicategory → Monoidal`: from a bicategory with a single 0-cell, extract the monoidal category on its unique hom-category (tensor = horizontal composition, unit = the identity 1-cell, associator/unitors from `hassoc`/`hunit_left`/`hunit_right`), and prove the round-trip with the forward delooping.
- Record the coherence payoff: derive bicategorical coherence for `α`, `λ`, `ρ` (at least the one-object case) from monoidal coherence, upgrading the prose citation to a theorem to the extent the in-tree monoidal coherence supports.
- Suggested module: extend `Theory/Bicategory/OneObject.v` (add the converse and the round-trip). In-tree donors: `Theory/Bicategory/OneObject.v` (the forward delooping and unit-coincidence), `Structure/Monoidal.v` (the monoidal class and coherence), and `Theory/Bicategory.v`.

## Definition of Done

- [ ] The converse `Bicategory` (one 0-cell) `→ Monoidal` constructed, with the round-trip against the forward delooping.
- [ ] The bicategorical coherence consequence for `α`/`λ`/`ρ` recorded (at least the one-object case) from monoidal coherence.
- [ ] All morphism/2-cell equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the converse and the round-trip.
- [ ] Edited file remains registered in `_CoqProject`; downstream users of `Monoidal_OneObject_Bicategory` still build.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Theory/Bicategory/OneObject.v` (and dependents) compiles cleanly.
- `Print Assumptions` on the converse construction and the round-trip show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the biconditional monoidal ⇔ one-object bicategory and the coherence transport match Mac Lane §XII.7.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XII.7:construction1"],"deps":[]} -->

---8<---

---
title: "MacLane XII.7: The bicategory of rings and bimodules"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.7:construction2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.7 (book p. 283, PDF p. 290). Item `maclane:XII.7:construction2` (the bicategory of rings, bimodules, and bimodule homomorphisms).

## Background

Rings, `(S,R)`-bimodules as 1-cells `R → S`, and bimodule homomorphisms as 2-cells form a bicategory; horizontal composition is the tensor product of bimodules over the middle ring, with associativity from the bimodule tensor isomorphism, and vertical composition is ordinary composition of homomorphisms. See the nLab, [bimodule](https://ncatlab.org/nlab/show/bimodule).

## Current state in the library

Absent. There are no rings, modules, or bimodules as structures: search finds only background-essay references (`Theory/Bicategory.v`, `Theory/DoubleCategory.v`, `Theory/Profunctor.v` cite bimodules as the motivating weak example) and zero structural definitions of a module, bimodule, or a category of rings. `Structure/Group.v` defines group objects, unrelated. The prerequisites — a category of rings (#257) and modules (#258) — are being introduced separately; the tensor product of bimodules over a ring and the bicategory assembly are entirely new.

## Work to be done

- Over the category of rings (#257) and modules (#258): define `(S,R)`-bimodules and their homomorphisms, and the tensor product `⊗_R` of bimodules over the middle ring with its universal property.
- Assemble the bicategory: 0-cells rings, hom-categories `Bimod(R,S)` of `(S,R)`-bimodules and homomorphisms, horizontal composition `⊗`, identity 1-cells the ring-as-bimodule, and the associator/unitors from the bimodule tensor isomorphisms, verifying pentagon and triangle.
- Suggested module: `Instance/Bimod.v`. In-tree donors: the category of rings (#257) and modules (#258), `Theory/Bicategory.v` (the target class), and `Structure/Coend.v`/`Construction/Day.v` as tensor-of-modules references if a coend presentation is used.

## Definition of Done

- [ ] `(S,R)`-bimodules, bimodule homomorphisms, and the tensor `⊗_R` over the middle ring defined with its universal property.
- [ ] The bicategory of rings and bimodules assembled, with pentagon and triangle verified.
- [ ] All morphism/2-cell equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the bicategory.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Instance/Bimod.v` compiles cleanly.
- `Print Assumptions` on the bimodule bicategory is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: 1-cells are bimodules, horizontal composition is `⊗` over the middle ring, and coherence holds, matching Mac Lane §XII.7.

## Dependencies

Depends on: #257
Depends on: #258

<!-- catalog: {"ids":["maclane:XII.7:construction2"],"deps":["#257","#258"]} -->

---8<---

---
title: "MacLane XII.7: The bicategory Span(C)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.7:construction3]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.7 (book pp. 283–285, PDF pp. 290–292). Item `maclane:XII.7:construction3` (the bicategory `Span(C)` for a category `C` with chosen pullbacks).

## Background

For a category `C` with a chosen pullback per cospan, `Span(C)` is the bicategory whose 0-cells are objects of `C`, 1-cells are spans `a ← v → b`, and 2-cells are arrows of `C` between apices making both triangles commute; vertical composition composes apex arrows, horizontal composition takes the chosen pullback of inner legs, the associator comes from pullback uniqueness (whence the pentagon), and the left unitor from identity spans. See the nLab, [span](https://ncatlab.org/nlab/show/span), and Wikipedia, [Span (category theory)](https://en.wikipedia.org/wiki/Span_(category_theory)).

## Current state in the library

Partial. The in-tree object is an ordinary 1-category, not the bicategory: `Construction/Span/Category.v` builds `SpanCat` (`:522`, needing `HasPullbacks`) from `SpanArrow` (`:49`, apex + two legs) with `span_compose` (`:120`, chosen-pullback horizontal composition), but its hom-setoid equality is `span_equiv` (`:64`) — apex-*isomorphism* respecting the legs — so the 2-cells are collapsed to invertible span morphisms and identified, and associativity is proved as strict equality of iso-classes. The file header itself (`:26–33`) states that `Span(C)` "is in general a bicategory, not a strict 1-category" and that it deliberately quotients to a 1-category. Missing: hom-categories of spans, non-invertible span-morphism 2-cells, associator/unitor 2-cells, and pentagon/triangle at the 2-cell level.

## Work to be done

- Build the genuine `Span(C)` bicategory: hom-categories `Span(C)(a,b)` whose objects are spans and whose morphisms are *arbitrary* apex arrows commuting with the legs (not only isomorphisms), with vertical composition composing apex arrows.
- Horizontal composition by the chosen pullback as a bifunctor on 2-cells; the associator from the universal property of pullbacks (giving the pentagon) and the unitors from identity spans (giving the triangle), as invertible 2-cells.
- Assemble as a `Bicategory` (over a `C` with chosen pullbacks), reusing the pullback bookkeeping already in `Construction/Span/Category.v`.
- Suggested module: `Construction/Span/Bicategory.v`. In-tree donors: `Construction/Span/Category.v` (`SpanArrow`, `span_compose`, the pullback plumbing), `Structure/Span.v` (spans), `Structure/Pullback.v` (chosen pullbacks and their UMP), and `Theory/Bicategory.v` (the target class).

## Definition of Done

- [ ] Hom-categories `Span(C)(a,b)` with spans as objects and general apex arrows (not just isos) as 2-cells.
- [ ] Horizontal composition by chosen pullback as a bifunctor; associator/unitors as invertible 2-cells; pentagon and triangle proved.
- [ ] `Span(C)` assembled as a `Bicategory` over a `C` with chosen pullbacks.
- [ ] All 2-cell equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the `Span(C)` bicategory.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (Span(C) as a bicategory is flagship-level).

## Verification

- `coqc -R . Category Construction/Span/Bicategory.v` compiles cleanly.
- `Print Assumptions` on the `Span(C)` bicategory is closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: 2-cells are arbitrary span morphisms, horizontal composition is chosen pullback, and the associator/unitors satisfy pentagon/triangle, matching Mac Lane §XII.7.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XII.7:construction3"],"deps":[]} -->

---8<---

---
title: "MacLane XII.8: Crossed modules of groups"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.8:def1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.8 (book p. 285, PDF p. 292). Item `maclane:XII.8:def1` (crossed module of groups).

## Background

A crossed module is a group homomorphism `d : H → P` together with an action of `P` on `H` (written `h ↦ hᵖ`) that is a group action by automorphisms (`h¹ = h`, `(hᵖ)^q = h^{pq}`, `(hk)ᵖ = hᵖ kᵖ`) and is equivariant, `d(hᵖ) = p (d h) p⁻¹` (the standard notion additionally imposes the Peiffer identity `h^{d k} = k h k⁻¹`). See the nLab, [crossed module](https://ncatlab.org/nlab/show/crossed+module), and Wikipedia, [Crossed module](https://en.wikipedia.org/wiki/Crossed_module).

## Current state in the library

Absent. A search for `crossed module` returns zero hits (the only `crossed` occurrences are an unrelated unitor-naming note and a braiding remark). There is no `(H, P, d, action)` datum with the action laws and the equivariance/Peiffer conditions. The library does have a concrete notion of group (`Instance/Comp.v:382`, `Group`) and group objects (`Structure/Group.v:112`, `GroupObject`), which supply the group-theoretic base to build over, but nothing organizes them into crossed modules.

## Work to be done

- Define a `CrossedModule`: groups `H`, `P`, a homomorphism `d : H → P`, and a `P`-action on `H` by automorphisms, satisfying the action laws, the equivariance `d(hᵖ) = p (d h) p⁻¹`, and the Peiffer identity `h^{d k} = k h k⁻¹` (per the standard formulation).
- Define morphisms of crossed modules (a pair of group homomorphisms commuting with the `d`'s and the actions) and assemble the category `XMod` of crossed modules — reusable for the equivalence with category objects in `Grp` (§XII.8).
- Suggested module: `Structure/CrossedModule.v`. In-tree donors: `Instance/Comp.v` (the concrete `Group`) and/or `Structure/Group.v` (`GroupObject`) for the group base, and the category of groups (#255) for organizing `XMod` compatibly.

## Definition of Done

- [ ] `CrossedModule` defined with `H`, `P`, `d`, the `P`-action, the action laws, equivariance, and the Peiffer identity.
- [ ] Morphisms of crossed modules and the category `XMod` defined.
- [ ] All group equations use setoid `≈` where the group hom-sets are setoids.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `CrossedModule` and `XMod`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification

- `coqc -R . Category Structure/CrossedModule.v` compiles cleanly.
- `Print Assumptions` on `CrossedModule` and `XMod` are closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the action laws, equivariance, and Peiffer identity match Mac Lane §XII.8 (and the standard crossed-module axioms).

## Dependencies

Depends on: #255

<!-- catalog: {"ids":["maclane:XII.8:def1"],"deps":["#255"]} -->

---8<---

---
title: "MacLane XII.8: Crossed modules are equivalent to category objects in Grp"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XII.8:lem1, maclane:XII.8:thm1]
deps_item_ids: [maclane:XII.1:def1, maclane:XII.8:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XII.8 (book pp. 285–287, PDF pp. 292–294). Items `maclane:XII.8:lem1` (a category object in `Grp` is determined by its underlying reflexive graph with a commutator condition) and `maclane:XII.8:thm1` (crossed modules are equivalent to category objects in `Grp`, after Janelidze).

## Background

An internal category in `Grp` is determined by its reflexive graph `C₁ ⇉ C₀` with section `i` (`d₀ i = 1 = d₁ i`) together with the commutator condition `[ker d₀, ker d₁] = 1`: the middle-four interchange forces composition to `g ∘ f = f · 1_b⁻¹ · g`, and conversely that formula defines a valid internal composition. The category of crossed modules is then equivalent to the category of category objects in `Grp`, sending such a graph to `∂ = d₁|_{ker d₀} : ker d₀ → C₀` via the `i`-split short exact sequence `1 → ker d₀ → C₁ → C₀ → 1`. See the nLab, [crossed module](https://ncatlab.org/nlab/show/crossed+module).

## Current state in the library

Absent. Both sides and the bridge are missing: there is no internal-category notion (§XII.1), no category of groups yet (`Construction/Groupoid.v` even remarks that no category of groupoids exists in-tree), no reflexive graph `C₁ ⇉ C₀` with a section, and no crossed module (§XII.8). The middle-four-forced composition `g ∘ f = f · 1_b⁻¹ · g` and the commutator condition `[ker d₀, ker d₁] = 1` have no counterpart; the lone `Janelidze` occurrence (`Construction/Opposite.v:60`) is an unrelated Goswami–Janelidze duality citation.

## Work to be done

- Prove the lemma (§XII.8): a category object in `Grp` (specializing the internal category of §XII.1 to the category of groups #255) is determined by its reflexive graph `C₁ ⇉ C₀` with section `i` satisfying `d₀ i = 1 = d₁ i` and the commutator condition `[ker d₀, ker d₁] = 1`; derive the forced composition `g ∘ f = f · 1_b⁻¹ · g` from the interchange law and prove the converse (the formula gives a valid internal composition).
- Prove the theorem: the category of crossed modules (§XII.8) is equivalent to the category of category objects in `Grp`, constructing the functor to crossed modules via the `i`-split short exact sequence (`H = ker d₀`, `P = C₀`, `∂ = d₁|_{ker d₀}`, conjugation action) and the inverse via the split extension, and proving the two composites naturally isomorphic to the identities.
- Suggested module: `Structure/CrossedModule/Equivalence.v`. In-tree donors: the internal category of §XII.1 (specialized to groups), the crossed module and `XMod` of §XII.8, the category of groups (#255), and `Structure/Kernel.v` for kernels and the split exact sequence.

## Definition of Done

- [ ] The lemma proved: a category object in `Grp` is determined by the reflexive graph with section and `[ker d₀, ker d₁] = 1`, with composition forced to `g ∘ f = f · 1_b⁻¹ · g` and the converse.
- [ ] The equivalence `XMod ≃ Cat(Grp)` proved in both directions (functors both ways and the natural isomorphisms of the round-trips), via the `i`-split short exact sequence.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the lemma and the equivalence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (the crossed-module / `Cat(Grp)` equivalence is flagship-level).

## Verification

- `coqc -R . Category Structure/CrossedModule/Equivalence.v` compiles cleanly.
- `Print Assumptions` on the lemma and the `XMod ≃ Cat(Grp)` equivalence show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the forced composition, the commutator condition, and the `i`-split equivalence match Mac Lane §XII.8 (Janelidze's proof).

## Dependencies

Depends on: maclane:XII.1:def1
Depends on: maclane:XII.8:def1
Depends on: #255

<!-- catalog: {"ids":["maclane:XII.8:lem1","maclane:XII.8:thm1"],"deps":["maclane:XII.1:def1","maclane:XII.8:def1","#255"]} -->

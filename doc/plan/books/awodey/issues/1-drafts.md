---
title: "Awodey 1.4: Wide subcategories of Sets cut out by a class of functions"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:1.4:construction-sets]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.4: Wide subcategories of Sets cut out by a class of functions

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.4 (Examples of categories), printed p. 6 (PDF p. 15). Item: `awodey:1.4:construction-sets`.

The passage introduces `Sets` and `Sets_fin`, then remarks that one may keep the same objects but *restrict the arrows* to obtain further categories of sets: finite sets with only **injective** functions, and sets with functions whose fibres `f⁻¹(b)` are all of size ≤ 2, all finite, or all infinite.

## Background

A subcategory that keeps every object of the ambient category and restricts only the morphisms is a *wide* (lluf) subcategory; nLab: [wide subcategory](https://ncatlab.org/nlab/show/wide+subcategory) ("a subcategory containing all the objects of C"). The examples here are wide subcategories of `Sets` whose arrows range over a class of functions closed under identity and composition (injections; bounded- or restricted-fibre maps).

## Current state in the library

The two principal categories of the passage are already in-tree: `Sets` (the category of setoids) at `Instance/Sets.v:188`, `FinSet` (the skeleton of finite sets) at `Instance/FinSet.v:116`, with the bare-type variant `Coq` at `Instance/Coq.v:120` and the Ensembles variant `Ens` at `Instance/Ens.v:34`. Monomorphisms of `Sets` are already characterised as the injective maps: `injectivity_is_monic` at `Instance/Sets.v:369`.

What is **absent** is any of the *arrow-restricted* wide subcategories the section describes: no category of sets with only injective functions, and none for the fibre-cardinality restrictions (fibres all ≤ 2 / all finite / all infinite). A whole-tree search for a fibre- or injection-restricted category of sets returned only unrelated pullback/coend fibre material (verified in the coverage record for §1.4).

## Work to be done

- Define the **wide subcategory of `Sets` on injective functions** — the category of sets and injections — as a `Category` whose objects are those of `Sets` and whose morphisms are `SetoidMorphism`s carrying an injectivity proof, with identities and composites shown to preserve injectivity. This is the standard, clearly-valuable case and should be the principal artifact.
- Optionally provide the fibre-restricted variants as instances of a single reusable pattern: a wide subcategory of `Sets` determined by a predicate on morphisms that holds of identities and is closed under composition (fibres all finite; fibres bounded by `n`). The "all infinite" fibre case is closed under composition only degenerately and may be recorded as a remark.
- Suggested module: `Instance/Sets/Sub.v` (a new file), or a parametric constructor `Instance/Sets/WideSub.v`. In-tree donors: `Construction/Subcategory.v` (subcategory infrastructure), the morphism-class vocabulary in `Theory/Morphisms/Classes.v`, and `injectivity_is_monic` (`Instance/Sets.v:369`) to relate the injective class to the monos of `Sets`. Keep the setoid discipline: injectivity is `∀ x y, f x ≈ f y → x ≈ y`, never `=`.

## Definition of Done

- [ ] The category of sets and injective functions is defined with all category laws proven, using `≈` for morphism equality throughout (never `=` on morphisms).
- [ ] Statement matches Awodey §1.4 (same objects as `Sets`; arrows restricted to injections / restricted-fibre maps).
- [ ] At least the injective-function case is complete; fibre-restricted variants either delivered or explicitly scoped out in the file header.
- [ ] No `Admitted`/`admit`/`Axiom`; the development stays within the zero-axiom core scoping of `docs/AXIOMS.md`.
- [ ] `Print Assumptions` is closed for each principal `Category` artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` is green on Rocq 9.1 and the nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Instance/Sets/Sub.v` (adjust to the chosen path).
- `Print Assumptions Sets_Inj.` (or the chosen name) reports no axioms beyond the `Instance/Sets.v` baseline of `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the statement matches Awodey §1.4: same objects as `Sets`, arrows restricted to the named function class, identities/composites closed under the restriction.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:1.4:construction-sets"],"deps":[]} -->

---8<---

---
title: "Awodey 1.4: Pos, the category of posets and monotone maps"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:1.4:construction-pos]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.4: Pos, the category of posets and monotone maps

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.4 (Examples of categories), printed pp. 7–8 (PDF pp. 16–17). Item: `awodey:1.4:construction-pos`.

The text defines a poset and a monotone map, then states that posets and monotone functions form a category **Pos**: identity functions are monotone and composites of monotone functions are monotone.

## Background

nLab: [Pos](https://ncatlab.org/nlab/show/Pos) — "the category whose objects are posets and whose morphisms are monotone (weakly increasing) maps." It is a standard large concrete category of order-structured sets.

## Current state in the library

Every ingredient exists, but the category is never assembled. A poset is realised as a thin category by `Poset` at `Instance/Poset.v:116` (a `PreOrder` with `Antisymmetric`, built as `Proset P`). Monotone maps are realised by `MonotoneMap` at `Construction/Enriched/Two.v:175`, and the identification "a functor between order categories is exactly a monotone map" is `EnrichedFunctor_Two_monotone` at `Construction/Enriched/Two.v:183`. The identity and composite of monotone maps being monotone is exactly the identity/composite functor from `Theory/Functor.v`. The category of categories `Cat` (`Instance/Cat.v:142`) and full-subcategory infrastructure (`Construction/Subcategory.v`) are available.

What is missing is the single bundling into a `Pos : Category` whose **objects are posets** and **arrows are monotone maps**. The names occur only as dangling comment references: `[Pos]` at `Instance/Poset.v:21` and `[Ord]` at `Instance/Proset.v:19`. A whole-tree search found no `Pos`/`Ord`/`Posets` category definition.

## Work to be done

- Define `Pos : Category` with objects a sigma of a carrier together with its partial-order structure (reflexive + transitive + antisymmetric relation) and morphisms the monotone maps between them, with identities and composition inherited from functions/monotone maps. Prove the category laws, keeping `≈` discipline on morphism equality.
- Alternatively realise `Pos` as the full subcategory of `Cat` on the skeletal thin categories `Poset P` via `Construction/Subcategory.v`, then show the two presentations agree; the direct construction is likely simpler and is the recommended principal artifact.
- Resolve the dangling comment pointers `[Pos]` (`Instance/Poset.v:21`) and `[Ord]` (`Instance/Proset.v:19`) so they reference the new object.
- Suggested module: `Instance/Pos.v`. In-tree donors: `Instance/Poset.v` (posets as thin categories), `Construction/Enriched/Two.v` (`MonotoneMap`), `Theory/Functor.v` (`Id`/`Compose` for monotone identity/composition), `Construction/Subcategory.v`, `Instance/Cat.v`.

## Definition of Done

- [ ] `Pos : Category` is defined (objects = posets, arrows = monotone maps) with all category laws proven and `≈` used for morphism equality (never `=`).
- [ ] Statement matches Awodey §1.4 (identities monotone, composites of monotone maps monotone).
- [ ] The dangling `[Pos]`/`[Ord]` comment references (`Instance/Poset.v:21`, `Instance/Proset.v:19`) are updated to point at the new object.
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions Pos` is closed.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Instance/Pos.v`.
- `Print Assumptions Pos.` reports no axioms beyond the `Instance/Poset.v` baseline.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms objects are posets and morphisms are monotone maps, matching Awodey §1.4, and that the `[Pos]`/`[Ord]` comments now resolve.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:1.4:construction-pos"],"deps":[]} -->

---8<---

---
title: "Awodey 1.4: The category of a deductive system (proofs as arrows)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:1.4:construction-deductive]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.4: The category of a deductive system (proofs as arrows)

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.4 (Examples of categories), printed p. 11 (PDF p. 20). Item: `awodey:1.4:construction-deductive`.

The text builds, from a deductive system, a category whose objects are formulas and whose arrows `p : φ → ψ` are deductions/proofs; composition is concatenation of deductions, identities are trivial deductions, and there may be **many** arrows `φ → ψ`.

## Background

This is the syntactic (Curry–Howard–Lambek) reading of a logic as a category: formulas are objects, proofs are morphisms, proof-composition is cut/substitution. nLab: [deductive system](https://ncatlab.org/nlab/show/deductive+system). Wikipedia: [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) (the Curry–Howard–Lambek correspondence, "morphisms as deductions mapping a set of assumptions to a valid consequent").

## Current state in the library

There is no *generic* construction taking an arbitrary deductive system (formulas + proofs + composition of deductions) to a proof-relevant category. Two special/degenerate cases exist:

- `Lambda` at `Instance/Lambda.v:226` — a genuinely proof-relevant category of **one** specific deductive system, the simply-typed λ-calculus (Curry–Howard); its header cites Lambek's *Deductive Systems and Categories*. Its objects are types, its arrows are open terms (proofs), and it is non-thin. However its hom-equivalence identifies proofs *denotationally* (`∀ E, SemExp f E ≈ SemExp g E`), not by deduction-concatenation.
- `Props` at `Instance/Props.v:39` — the **thin**, proof-irrelevant collapse (propositions ordered by implication, `equiv := True`), which discards Awodey's "many arrows `φ → ψ`".

So the deductive-system-as-category idea is realised only for a single logic and only up to denotational equality, or else collapsed to a preorder.

## Work to be done

- Define a general datatype for a deductive system: a type of formulas, a family of *deductions* `deduction φ ψ` (a setoid per pair), an identity deduction, and a composition (cut/concatenation) with a chosen congruence `≈` on deductions.
- Build `DeductiveCategory : Category` from that data (objects = formulas, homs = deductions modulo the chosen congruence, id = trivial deduction, compose = concatenation), proving the category laws. Keep proof-relevance: do not force the hom-setoids to be subsingletons.
- Show the intended examples factor through it: the thin `Props` arises by taking the trivial congruence, and (optionally) exhibit a small many-arrows instance to witness that `φ → ψ` can carry several distinct deductions.
- Suggested module: `Construction/DeductiveSystem.v` (a construction parametric in the deductive-system data), with instances under `Instance/`. In-tree donors: `Instance/Lambda.v` and `Instance/Props.v` as reference points, and `Construction/Quotient.v` for the hom-congruence quotient if deductions are quotiented by a relation.

## Definition of Done

- [ ] A generic `DeductiveCategory` construction is defined from abstract deductive-system data, with all category laws proven and `≈` used for the deduction congruence (never `=` on morphisms).
- [ ] The construction is proof-relevant (hom-setoids are not forced to be subsingletons), faithful to Awodey's "many arrows `φ → ψ`".
- [ ] Statement matches Awodey §1.4 (formulas as objects, deductions as arrows, concatenation as composition, trivial deduction as identity).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for the principal `DeductiveCategory` artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Construction/DeductiveSystem.v`.
- `Print Assumptions DeductiveCategory.` reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the generic construction matches Awodey §1.4 and that at least one instance exhibits multiple distinct arrows between two formulas.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:1.4:construction-deductive"],"deps":[]} -->

---8<---

---
title: "Awodey 1.5: Automorphism groups, permutation groups, and Cayley's theorem"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:1.5:construction-aut, awodey:1.5:thm-cayley]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.5: Automorphism groups, permutation groups, and Cayley's theorem

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.5 (Isomorphisms), printed p. 14 (PDF p. 23). Items: `awodey:1.5:construction-aut`, `awodey:1.5:thm-cayley`.

- `Aut(X)` is the group of automorphisms (permutations) of an object `X` — its isomorphisms in the ambient category; a *group of permutations* is a subgroup `G ⊆ Aut(X)`.
- **Cayley's theorem**: every group `G` is isomorphic to a group of permutations, via the left-regular (Cayley) representation `g ↦ ḡ`, `ḡ(h) = g·h`, with `i(g) = ḡ` and `j(ḡ) = g` mutually inverse group homomorphisms.

## Background

nLab: [automorphism group](https://ncatlab.org/nlab/show/automorphism+group) (the automorphisms of an object "form a group under composition"). Wikipedia: [Cayley's theorem](https://en.wikipedia.org/wiki/Cayley%27s_theorem) ("every group G is isomorphic to a subgroup of a symmetric group"). The categorical reading is the one-object case of the (covariant) Yoneda/Cayley embedding.

## Current state in the library

Only the *data* of `Aut(X)`, and only the *many-object categorical generalisation* of Cayley, are present:

- The core groupoid `Groupoid` at `Construction/Groupoid.v:103` has `hom X Y := Isomorphism X Y`, so its endo-homset `Hom(X,X)` is exactly the isomorphisms `X ≅ X` — the underlying data of `Aut(X)`. The group operations are `iso_id`/`iso_sym`/`iso_compose` (`Theory/Isomorphism.v:149`), packaged as an `Equivalence` at `Theory/Isomorphism.v:187`. But `Aut(X)` is never bundled as a *group* (there is no `Aut` identifier in the tree), there is no `Sym(X)`, and no "group of permutations / subgroup of `Aut(X)`" notion.
- `Construction/Cayley.v:158` (`To_Cayley`/`From_Cayley`) builds the many-object Cayley/Yoneda representation of an arbitrary category and is split-faithful, but the **group-specific** statement — `G` isomorphic to a group of permutations — is never instantiated: there is no concrete category of groups, no `Sym(G)`, no `Aut(G)`, and no derivation of group Cayley from `Construction/Cayley.v`.

## Work to be done

- With the concrete category of groups available (see Dependencies), define the **automorphism group** `Aut(X)` of an object of a category as a group whose carrier is `Isomorphism X X`, unit `iso_id`, multiplication `iso_compose`, inverse `iso_sym`; and, in `Sets`, identify `Aut(X)` with the group of bijections (permutations) of the underlying setoid. Provide the notion of a *permutation group* as a subgroup of `Aut(X)`.
- State and prove **Cayley's theorem** at the group level: every group `G` is isomorphic (in the category of groups) to a subgroup of `Sym(G) = Aut(G_set)`, via the left-translation representation; the two maps `i`, `j` are mutually inverse group homomorphisms. Where possible, derive it as the one-object specialisation of `Construction/Cayley.v` rather than re-proving from scratch.
- Suggested modules: `Instance/Grp/Aut.v` (automorphism/permutation groups) and `Instance/Grp/Cayley.v` (the theorem). In-tree donors: `Construction/Groupoid.v`, `Theory/Isomorphism.v` (`iso_id`/`iso_sym`/`iso_compose`), `Construction/Cayley.v`, and `Instance/Sets.v` (bijections/permutations of a setoid). Use `≈` throughout; the Cayley iso is an isomorphism in the category of groups.

## Definition of Done

- [ ] `Aut(X)` is defined as a group (carrier `Isomorphism X X`, unit/mult/inverse from `iso_id`/`iso_compose`/`iso_sym`), with the group laws proven; in `Sets`, `Aut(X)` is identified with the permutations of the underlying setoid.
- [ ] A permutation group (subgroup of `Aut(X)`) notion is provided.
- [ ] Cayley's theorem is stated and proven: `G ≅ (a subgroup of) Sym(G)` in the category of groups, with the isomorphism witnessed by mutually inverse homomorphisms; `≈` discipline throughout (never `=` on morphisms).
- [ ] Statement matches Awodey §1.5 (left-regular representation; `Aut(X)` = permutations of `X`).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for `Aut` and for the Cayley theorem.
- [ ] New files registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Instance/Grp/Aut.v` then `Instance/Grp/Cayley.v`.
- `Print Assumptions Cayley_theorem.` (chosen name) reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the statement matches Awodey §1.5 (every group isomorphic to a group of permutations via left translation) and that the two levels of isomorphism (permutations are isos in `Sets`; `G ≅ Ḡ` is an iso in the category of groups) are kept distinct, per Warning 1.5.

## Dependencies

Depends on: #255 (the concrete category of groups and group homomorphisms — MacLane I.6: Grp).

<!-- catalog: {"ids":["awodey:1.5:construction-aut","awodey:1.5:thm-cayley"],"deps":["#255"]} -->

---8<---

---
title: "Awodey 1.5: Every category with small hom-collections is concrete (Cayley/Yoneda into Sets)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:1.5:thm6]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.5: Every category with small hom-collections is concrete (Cayley/Yoneda into Sets)

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.5 (Isomorphisms), Theorem 1.6, printed p. 15 (PDF pp. 24–25). Item: `awodey:1.5:thm6`.

Theorem 1.6: every category `C` whose arrows form a set is isomorphic to a category of sets and functions. The proof is the Cayley representation `Č`: each object `C` goes to `Č = { f | cod(f) = C }`, and each arrow `g : C → D` to `ḡ : Č → Ḏ`, `ḡ(f) = g∘f`; the set-of-arrows hypothesis is what makes each `Č` a set.

## Background

nLab: [concrete category](https://ncatlab.org/nlab/show/concrete+category) — a category "equipped with a faithful functor `U : C → Set`." Theorem 1.6 is the classical statement that any (small-hom) category admits such a functor and is thus concrete, via a Cayley/Yoneda representation.

## Current state in the library

The related Yoneda content is present but with a **different target** and a **different conclusion**:

- The Yoneda embedding is full and faithful into the *presheaf* category: `Yoneda_Full` and `Yoneda_Faithful` on `Curried_Hom : C^op ⟶ [C, Sets]` at `Functor/Hom.v:96` (with `Curried_Hom` at `Functor/Hom.v:60`), and the hom-set iso `Covariant_Yoneda_Embedding` at `Functor/Hom/Yoneda.v:253`.
- `Construction/Cayley.v:114` realises the covariant representation concretely with a split-faithful `To_Cayley : C ⟶ Cayley`, but `Cayley` keeps abstract (non-`Set`) objects and the conclusion is split-faithfulness, not an isomorphism onto a concrete subcategory of `Sets`.

So the in-tree embedding lands in `[C, Sets]` (functor-valued), whereas Theorem 1.6 wants a **single `Set`-valued** faithful functor `C → Sets` and the resulting isomorphism of `C` onto a subcategory of `Sets` and functions. The `Č`-style bundled representation (an object to the set of all arrows into it) and the "isomorphic to a concrete category" conclusion are not in-tree; the set-of-arrows smallness hypothesis is handled instead by universe polymorphism.

## Work to be done

- Construct the bundled `Set`-valued representation `Č : C ⟶ Sets` sending each object to (a setoid of) all arrows into it (`∐_D Hom(D, C)`), acting on arrows by post-composition, and prove it **faithful**.
- Package Awodey's conclusion: exhibit `C` as isomorphic to (equivalently, faithfully embedded as) a subcategory of `Sets` and functions — i.e. that `C` is *concrete* in the sense of the concrete-category notion (see Dependencies). Relate this to the existing Yoneda full-faithfulness (`Functor/Hom.v:96`) rather than re-deriving it.
- Suggested module: `Functor/Concrete.v` (or `Construction/Concrete.v`). In-tree donors: `Functor/Hom.v` and `Functor/Hom/Yoneda.v` (the Yoneda machinery), `Construction/Cayley.v` (the categorical Cayley representation), and `Instance/Sets.v` (the target). Keep `≈` discipline; faithfulness is `fmap f ≈ fmap g → f ≈ g`.

## Definition of Done

- [ ] A `Set`-valued functor `Č : C ⟶ Sets` (the bundled arrows-into representation) is defined and proven faithful.
- [ ] `C` is exhibited as concrete (faithful functor to `Sets`), matching Theorem 1.6's "isomorphic to a category of sets and functions", with the relationship to Yoneda full-faithfulness made explicit.
- [ ] Statement matches Awodey Theorem 1.6, including how the smallness hypothesis is discharged (universe polymorphism, documented in the header).
- [ ] `≈` used for morphism equality throughout (never `=`).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for the faithful representation functor.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Functor/Concrete.v`.
- `Print Assumptions Concrete_Representation.` (chosen name) reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the statement matches Awodey Theorem 1.6 (a faithful `Set`-valued representation exhibiting concreteness) and that the target is `Sets` (not merely the presheaf category `[C, Sets]`).

## Dependencies

Depends on: #263 (the concrete-category notion — a category with a faithful functor to `Set` — MacLane I.7: Concrete categories).

<!-- catalog: {"ids":["awodey:1.5:thm6"],"deps":["#263"]} -->

---8<---

---
title: "Awodey 1.9 Ex 3: Isomorphisms versus bijective homomorphisms in Sets, Mon, and Pos"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:1:ex3]
deps_item_ids: [awodey:1.4:construction-pos]
deps_pending: []
---

# Awodey 1.9 Ex 3: Isomorphisms versus bijective homomorphisms in Sets, Mon, and Pos

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.9 (Exercises), Exercise 3, printed p. 29 (PDF p. 38). Item: `awodey:1:ex3`.

Exercise 3: show that (a) in `Sets` the isomorphisms are exactly the bijections; (b) in monoids the isomorphisms are exactly the bijective homomorphisms; (c) in posets the isomorphisms are **not** the same as the bijective monotone maps (exhibit a bijective monotone map that is not an order-isomorphism).

## Background

nLab: [isomorphism](https://ncatlab.org/nlab/show/isomorphism) (an invertible morphism with a two-sided inverse). Wikipedia: [order isomorphism](https://en.wikipedia.org/wiki/Order_isomorphism) — a monotone bijection is an order-isomorphism only when its inverse is also monotone, so bijective monotone maps and order-isomorphisms genuinely differ. This exercise is the standard cautionary contrast between "iso" and "bijective structure-preserving map".

## Current state in the library

Only one direction of part (a) is in-tree:

- `bijective_is_iso` at `Instance/Sets.v:400` proves `injective h → surjective h → IsIsomorphism h` in `Sets` (the *bijection ⇒ iso* direction), supported by `injectivity_is_monic` at `Instance/Sets.v:369`. The converse *iso ⇒ bijection* is not assembled: `iso ⇒ injective` is derivable via `injectivity_is_monic`, but the `iso ⇒ surjective` direction is deliberately unavailable (`surjectivity_is_epic`'s `epic ⇒ surjective` half is abandoned at `Instance/Sets.v:412`), so there is no bundled `iso ↔ bijection` lemma.
- Part (b): the category of monoids `Mon` exists (`Theory/Algebra/Monoid/Hom.v:83`) but carries **no** iso-vs-bijective-homomorphism characterization.
- Part (c): there is no category `Pos` of posets and monotone maps, and no counterexample of a bijective monotone map that fails to be an order-isomorphism.

## Work to be done

- **Part (a):** complete `Sets`: prove `iso ⇒ injective ∧ surjective` and bundle a full `IsIsomorphism h ↔ (injective h ∧ surjective h)` characterization in `Sets`, reusing `bijective_is_iso` and `injectivity_is_monic`.
- **Part (b):** in the category of monoids (`Theory/Algebra/Monoid/Hom.v`), prove that a morphism is an isomorphism iff its underlying function is a bijective monoid homomorphism (a bijective homomorphism has a homomorphic inverse).
- **Part (c):** in the category **Pos** of posets and monotone maps (Awodey §1.4, drafted separately in this batch — see Dependencies), exhibit a concrete bijective monotone map whose inverse is not monotone, hence not an order-isomorphism (the standard witness: two comparable elements re-ordered to be incomparable, or `{0,1}` discrete mapping onto `{0<1}`), and prove it is not an iso.
- Suggested placement: extend `Instance/Sets.v` (the `Sets` iso characterization), `Theory/Algebra/Monoid/Hom.v` (the `Mon` characterization), and add the `Pos` counterexample under `Instance/Pos.v`/`Test/`. In-tree donors: `Instance/Sets.v:400`/`:369`, `Theory/Isomorphism.v`, and the `Pos` object from the dependency. `≈` discipline throughout.

## Definition of Done

- [ ] Part (a): a full `iso ↔ bijection` characterization in `Sets` is proven (both directions), using `≈` (never `=` on morphisms).
- [ ] Part (b): isomorphisms in the category of monoids are characterized as exactly the bijective monoid homomorphisms.
- [ ] Part (c): a concrete bijective monotone map that is not an order-isomorphism is exhibited in `Pos`, with a proof that it is not an iso.
- [ ] Statements match Awodey Exercise 3(a)/(b)/(c).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for each named characterization/counterexample.
- [ ] Any new file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile of each touched/added file (`coqc -R . Category Instance/Sets.v`, `... Theory/Algebra/Monoid/Hom.v`, `... Instance/Pos.v`).
- `Print Assumptions` on the three named results reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the three statements match Awodey Exercise 3, in particular that part (c) is a genuine counterexample (bijective + monotone, but non-monotone inverse).

## Dependencies

Depends on: `awodey:1.4:construction-pos` (the category `Pos` of posets and monotone maps, needed to state and exhibit part (c); drafted separately in this batch).

<!-- catalog: {"ids":["awodey:1:ex3"],"deps":["awodey:1.4:construction-pos"]} -->

---8<---

---
title: "Awodey 1.9 Ex 4: The coslice as the opposite of the slice over the opposite category"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:1:ex4]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.9 Ex 4: The coslice as the opposite of the slice over the opposite category

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.9 (Exercises), Exercise 4, printed p. 29 (PDF p. 38). Item: `awodey:1:ex4`.

Exercise 4: construct the coslice category `C\C` under an object `C` from the slice construction `C/C` together with the opposite operation `(-)^op` — i.e. exhibit the coslice as (essentially) `(C^op / C)^op`.

## Background

nLab: [comma category](https://ncatlab.org/nlab/show/comma+category) — slice and coslice categories are the special cases where one functor is the identity and the other selects an object; the coslice is the dual of the slice, obtained by dualizing. This exercise asks to make that duality precise.

## Current state in the library

All building blocks exist, but the specific duality the exercise asks for is not proven:

- `Coslice` is defined *directly* at `Construction/Slice.v:169` (objects `∃ a, c ~> a`; morphisms commuting triangles `h∘ι = ι'`), not as `(C^op / c)^op`.
- `Comma_Coslice` at `Construction/Slice.v:181` proves the coslice is `≅[Cat]` the comma `(=(c) ↓ Id)` — relating the coslice to a comma, but **not** to the opposite of the slice on `C^op`.
- `Cocomma` at `Construction/Comma.v:254` is literally `@Comma (B^op) (A^op) (C^op) (T^op) (S^op)`, and the comment there asserts it is `(S ↓ T)^op` "up to isomorphism" — but that isomorphism is **not proven** (it is an in-comment remark only).
- The opposite functor `(-)^op` and `op_invol : (C^op)^op = C` are available at `Construction/Opposite.v:106`/`:126`.

## Work to be done

- Prove the general comma-opposite duality `(S ↓ T)^op ≅[Cat] Cocomma S T` (equivalently `(S ↓ T)^op ≅ (T^op ↓ S^op)`), upgrading the existing in-comment remark at `Construction/Comma.v:254` to a theorem.
- Specialise to obtain the exercise's identity: `Coslice C c ≅[Cat] (Slice (C^op) c)^op`, i.e. exhibit the coslice under `c` as the opposite of the slice over `c` taken in `C^op`. Connect it to the existing `Comma_Coslice`/`Comma_Slice` isos so the two coslice presentations agree.
- Suggested placement: `Construction/Comma/Opposite.v` (the general op-duality) plus a lemma in `Construction/Slice.v`. In-tree donors: `Construction/Comma.v:254` (`Cocomma`), `Construction/Slice.v` (`Slice`, `Coslice`, `Comma_Slice`, `Comma_Coslice`), `Construction/Opposite.v` (`op_invol`). Use `≅[Cat]` and `≈` throughout.

## Definition of Done

- [ ] The comma-opposite duality `(S ↓ T)^op ≅[Cat] Cocomma S T` is proven (no longer an in-comment remark).
- [ ] The exercise's identity `Coslice C c ≅[Cat] (Slice (C^op) c)^op` is proven and connected to the existing comma isos.
- [ ] Statement matches Awodey Exercise 4 (coslice built from slice via `(-)^op`).
- [ ] `≈`/`≅[Cat]` discipline throughout (never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for the two named isomorphisms.
- [ ] Any new file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Construction/Comma/Opposite.v` and the touched `Construction/Slice.v`.
- `Print Assumptions` on the comma-opposite duality and the coslice-from-slice iso reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the statement matches Awodey Exercise 4 (coslice `≅` the opposite of the slice over `C^op`).

## Dependencies

None.

<!-- catalog: {"ids":["awodey:1:ex4"],"deps":[]} -->

---8<---

---
title: "Awodey 1.9 Ex 5: Free categories on graphs with exactly six arrows"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:1:ex5]
deps_item_ids: []
deps_pending: []
---

# Awodey 1.9 Ex 5: Free categories on graphs with exactly six arrows

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §1.9 (Exercises), Exercise 5, printed p. 29 (PDF p. 38). Item: `awodey:1:ex5`.

Exercise 5: determine how many free categories on graphs have exactly six arrows, and draw the generating graphs.

## Background

nLab: [free category](https://ncatlab.org/nlab/show/free+category) — the morphisms of the free category on a directed graph are the finite paths ("tuples of composable edges"). A free category has finitely many arrows only when the graph is acyclic (any directed cycle generates infinitely many paths), so this is a finite enumeration of acyclic generating graphs whose total path count (identities included) is six.

## Current state in the library

The free-category machinery is fully present — `FreeOnQuiver` at `Construction/Free/Quiver.v:431` builds the path category of a quiver (objects = nodes, morphisms = `tlist edges`, identity = empty path, composition = concatenation) — so the objects of the exercise are formalizable in principle. But there is **no** in-tree counterpart to the exercise's specific deliverable: no path-count of a free category, and no enumeration of the (finitely many) graphs whose free category has exactly six arrows. A whole-tree search for any arrow-counting/enumeration result over free categories returned nothing.

## Work to be done

- Formalise the number of arrows of the free category on a finite quiver as the total number of finite paths (including the length-0 identity path at each node), for acyclic finite quivers.
- Enumerate (up to graph isomorphism) the finite graphs whose free category has exactly six arrows, and prove the count is exactly that list — e.g. by a decidable characterization of small acyclic quivers by node/edge counts and per-graph path totals. Provide the generating graphs explicitly (the "drawing" rendered as the concrete quiver data).
- Suggested placement: a dedicated file such as `Test/Awodey_Ch1_Ex5.v` (or `Instance/`), building on the existing quiver/path infrastructure. In-tree donors: `Construction/Free/Quiver.v` (`FreeOnQuiver`, `tlist`-paths), and the finite/`FinSet` enumeration idioms in `Instance/FinSet.v`. Keep any computed witnesses axiom-free (`eq_refl`-checkable where possible).

## Definition of Done

- [ ] Path-count of a free category on a finite acyclic quiver is defined and connected to `FreeOnQuiver`.
- [ ] The generating graphs with exactly six arrows are enumerated and the count proven complete (a proven list, not a prose count).
- [ ] Statement matches Awodey Exercise 5 (number of free categories on graphs with exactly six arrows, plus the generating graphs).
- [ ] No `Admitted`/`admit`/`Axiom`; consistent with `docs/AXIOMS.md` scoping.
- [ ] `Print Assumptions` closed for the enumeration result.
- [ ] Any new file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; nix Coq 8.19/8.20 targets build.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile: `coqc -R . Category Test/Awodey_Ch1_Ex5.v` (adjust to the chosen path).
- `Print Assumptions` on the enumeration theorem reports no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20`.
- Reviewer confirms the count and the drawn generating graphs match Awodey Exercise 5, and that acyclicity (finiteness of the free category) is handled explicitly.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:1:ex5"],"deps":[]} -->

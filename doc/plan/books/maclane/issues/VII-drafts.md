---
title: "MacLane VII.1: Cocartesian monoidal structure from finite coproducts"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.1:construction1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1 (book p. 163, PDF p. 171). Item `maclane:VII.1:construction1` (the cartesian half is present; the cocartesian half is the gap).

## Background

Any category with finite products carries a monoidal structure with tensor the binary product and unit the terminal object, and dually any category with finite coproducts is monoidal with tensor the coproduct and unit the initial object; the pentagon and triangle hold automatically from the universal properties. See the nLab, [cartesian monoidal category](https://ncatlab.org/nlab/show/cartesian+monoidal+category).

## Current state in the library

The cartesian direction is fully present and general: `Cartesian_Monoidal := CC_Monoidal` at `Structure/Monoidal/Cartesian.v:49`, with the triangle and pentagon discharged in `Structure/Monoidal/Internal/Product.v`. The dual (cocartesian) direction, however, exists only as loose ingredients: `Structure/Cocartesian.v:94-96` states that `coprod_assoc`, `coprod_comm`, `coprod_zero_l` and `coprod_zero_r` "are the components of a symmetric monoidal structure on `(C, +, 0)`", but no assembled `@Monoidal C` instance with tensor the coproduct is ever defined. The only place a coproduct-tensor monoidal category is actually built is for the single object `Cospan(C)` (`Construction/Cospan/Symmetric.v`), not as a general construction on an arbitrary category with finite coproducts.

## Work to be done

Provide the general cocartesian monoidal structure: a `Cocartesian_Monoidal : @Monoidal C` for any `C` with finite coproducts (`Cocartesian`) and an initial object, with tensor the binary coproduct, unit the initial object, and the unitors/associator assembled from `coprod_zero_l`/`coprod_zero_r`/`coprod_assoc`, discharging triangle and pentagon. Suggested module: `Structure/Monoidal/Cocartesian.v`. In-tree donors: `Structure/Cocartesian.v` (component isos), `Structure/Monoidal/Internal/Product.v` (the cartesian template to dualize), and `Construction/Opposite/Monoidal.v` (`Monoidal_op`, so one option is to define it as `Monoidal_op` applied to `CC_Monoidal` on `C^op`, then re-expose the covariant accessors). Prefer the direct definition so the tensor computes to the coproduct without an `op` indirection.

## Definition of Done

- [ ] `Cocartesian_Monoidal : @Monoidal C` defined for any finitely cocartesian `C`, tensor = binary coproduct, unit = initial object.
- [ ] Triangle and pentagon proved; unitor/associator naturality discharged.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions Cocartesian_Monoidal` is closed under the global context (per docs/AXIOMS.md scoping).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- `coqc -R . Category Structure/Monoidal/Cocartesian.v` compiles cleanly.
- `Print Assumptions Cocartesian_Monoidal.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the assembled tensor is definitionally the binary coproduct and the unit the initial object; statement matches Mac Lane §VII.1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:construction1"],"deps":[]} -->

---8<---

---
title: "MacLane VII.1: Moncat, the category of monoidal categories, and its finite products"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.1:construction2, maclane:VII.1:ex2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1 (book pp. 164-165, PDF pp. 172-173). Items `maclane:VII.1:construction2` (the category Moncat and its terminal object), `maclane:VII.1:ex2` (Exercise 2: the product in Moncat).

## Background

Small monoidal categories and strict monoidal functors form a category Moncat, which has finite products and a terminal object (the one-object monoidal category); it contains the strict monoidal categories as a full subcategory. See the nLab, [monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor) and [monoidal category](https://ncatlab.org/nlab/show/monoidal+category).

## Current state in the library

The arrow-level data of Moncat is present but the category is never assembled. `Functor/Structure/Monoidal/Strict.v` supplies `Id_StrictMonoidalFunctor` (line 151) and `Compose_StrictMonoidalFunctor` (line 160), i.e. identities and composition of strict monoidal functors; "MonCat" occurs only in prose comments (Strict.v:43, Compose.v:55, Product.v:28, Braided.v:43) describing an informal 2-category. No `@Category` whose objects are monoidal categories exists, so there is no proof of finite products on it and no terminal one-object monoidal category. For Exercise 2, `Structure/Monoidal/Product.v:38` builds `Product_Monoidal`, the pointwise monoidal structure on `C ∏ D` (the product *object*), but the projections are not shown to be strict monoidal functors and no universal property in Moncat is stated.

## Work to be done

Assemble `Moncat : Category` with objects bundled small monoidal categories and morphisms bundled strict monoidal functors, reusing `Id_StrictMonoidalFunctor` and `Compose_StrictMonoidalFunctor` for identity and composition and proving the category laws at that level. Then: (a) exhibit the one-object monoidal category as a terminal object of Moncat; (b) show `Product_Monoidal` (with the two projections as strict monoidal functors and the mediating pair) is the categorical product in Moncat, discharging Exercise 2; (c) record the full subcategory on strict monoidal categories. Suggested module: `Instance/MonCat.v` (with the product in `Instance/MonCat/Product.v`). In-tree donors: `Functor/Structure/Monoidal/Strict.v`, `Structure/Monoidal/Product.v`, `Instance/Cat.v` (the category-of-categories template).

## Definition of Done

- [ ] `Moncat : Category` assembled with the strict-monoidal-functor hom and the category laws proved.
- [ ] Terminal object (one-object monoidal category) exhibited.
- [ ] `Product_Monoidal` shown to be the categorical product in Moncat: projections strict monoidal, pairing with uniqueness (Exercise 2).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions Moncat` closed under the global context.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/MonCat.v` (and `Instance/MonCat/Product.v`) compile cleanly.
- `Print Assumptions Moncat.` and `Print Assumptions Moncat_Product.` show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: objects/arrows are monoidal categories / strict monoidal functors; the terminal and product match Mac Lane §VII.1 and Exercise 2.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:construction2","maclane:VII.1:ex2"],"deps":[]} -->

---8<---

---
title: "MacLane VII.1: The pointwise monoidal structure on a functor category and the exponential law"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.1:ex4]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1, Exercise 4 (book p. 165, PDF p. 173). Item `maclane:VII.1:ex4`.

## Background

For a monoidal category `B` and any category `C`, the functor category `[C,B]` is monoidal under the pointwise tensor `(S ⊗ T)c = Sc ⊗ Tc` with unit the constant functor at `I`, and the exponential comparison `B^{C×D} ≅ (B^C)^D` is an isomorphism of monoidal categories. See the nLab, [monoidal category](https://ncatlab.org/nlab/show/monoidal+category).

## Current state in the library

Only the object-level ingredient exists. `Functor/Product.v:34` defines `Product` (notation `F :*: G`), the pointwise tensor of two functors into a monoidal `D`, with `fobj x = F x ⊗ G x`; its header names the constant functor at `I` as the intended unit. There is no assembled `@Monoidal [C,B]` instance (no tensor bifunctor `[C,B] ∏ [C,B] ⟶ [C,B]`, no unitors, associator, triangle or pentagon), and the monoidal exponential law `B^{C×D} ≅ (B^C)^D` is absent. Note that `Structure/Monoidal/Compose.v` builds `@Monoidal [C,C]` under functor *composition* — a different monoidal structure, not this pointwise one.

## Work to be done

Assemble the pointwise monoidal structure `@Monoidal [C,B]` from `Functor/Product.v`'s `F :*: G`: a tensor bifunctor, the constant-at-`I` unit, unitors/associator from those of `B` computed pointwise, and triangle/pentagon inherited pointwise. Then formalize the exponential law `[C×D, B] ≅ [D, [C,B]]` as an isomorphism of monoidal categories (a strict monoidal isomorphism, using `Instance/Fun.v` and the currying of functor categories). Suggested module: `Structure/Monoidal/Pointwise.v` (exponential law in `Structure/Monoidal/Pointwise/Exp.v`). In-tree donors: `Functor/Product.v`, `Structure/Monoidal.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] `@Monoidal [C,B]` (pointwise) assembled: tensor bifunctor, constant unit, unitors, associator, triangle, pentagon.
- [ ] The monoidal exponential iso `[C×D,B] ≅ [D,[C,B]]` formalized (strict monoidal isomorphism).
- [ ] The overstated header of `Functor/Product.v` (which claims a monoidal structure is "transported pointwise to the functor category `[C,D]`", though none was ever assembled) is corrected to point at the new instance. *(LIBRARY-DEFECT: `Functor/Product.v` header, flagged during verification of this item — the file provides only the objectwise tensor, not the assembled `@Monoidal [C,D]` its header implies.)*
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the monoidal instance and the exponential iso.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Monoidal/Pointwise.v` compiles cleanly.
- `Print Assumptions Pointwise_Monoidal.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the tensor is pointwise `Fx ⊗ Gx`, the unit is constant `I`, and the exponential iso is monoidal; statement matches Mac Lane §VII.1 Exercise 4. Confirm the `Functor/Product.v` header no longer overstates.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:ex4"],"deps":[]} -->

---8<---

---
title: "MacLane VII.1: One-object strict monoidal categories and the Eckmann–Hilton interchange"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.1:ex5]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1, Exercise 5 (book p. 165, PDF p. 173). Item `maclane:VII.1:ex5`.

## Background

A strict monoidal category with a single object is exactly a set (its arrows) carrying two binary operations — composition and tensor — that satisfy the interchange law and share a common two-sided unit; this is the categorical face of the Eckmann–Hilton argument. See the nLab, [Eckmann-Hilton argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argument).

## Current state in the library

Both mathematical ingredients exist, but not assembled into this statement. The Eckmann–Hilton argument itself is proved in `Structure/Semiadditive.v` (`conv_interchange`:503, `conv_conv_pr`:515, `conv_comm`:524, `conv_assoc`:533 — two unital operations satisfying interchange coincide, are commutative and associative), but in the biproduct-convolution setting, on `hom(x, y)`, not on `End(e)` of a one-object monoidal category. The `∘`-vs-`⊗` interchange law itself is the bifunctoriality of `tensor : C ∏ C ⟶ C` (`Structure/Monoidal.v:127`). There is no in-tree "one-object strict monoidal category" object, and no theorem unfolding one to a two-operation interchange structure sharing a unit; `Structure/Monoidal/Proofs.v` only remarks in prose that `unit_identity` underlies the commutativity of `End(I)`.

## Work to be done

Define a one-object strict monoidal category (or specialize `StrictMonoidal` to a chosen single object) and prove that its arrow-set, with `∘` and `⊗`, is a set with two interchange-compatible binary operations sharing the common unit `id_e`; deduce (via the existing Eckmann–Hilton chain) that the two operations coincide and are commutative — recovering `End(e)` as a commutative monoid. Suggested module: `Structure/Monoidal/OneObject.v` (or extend `Theory/Bicategory/OneObject.v`, which currently deloops the other way, monoidal category → one-object bicategory). In-tree donors: `Structure/Semiadditive.v` (the Eckmann–Hilton lemmas), `Structure/Monoidal.v` (tensor bifunctoriality = interchange), `Structure/Monoidal/Strict.v`.

## Definition of Done

- [ ] A one-object strict monoidal category defined, and its arrow-set characterized as a two-operation `(∘, ⊗)` interchange structure with a shared unit.
- [ ] Eckmann–Hilton payoff applied at `End(e)`: the two operations coincide and are commutative.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the principal theorem.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Monoidal/OneObject.v` compiles cleanly.
- `Print Assumptions` on the characterization theorem shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: statement matches Mac Lane §VII.1 Exercise 5 (cf. II.5 Exercise 5), with the two operations sharing `id_e`.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:ex5"],"deps":[]} -->

---8<---

---
title: "MacLane VII.1: Independence of the pentagon and triangle axioms"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.1:ex6]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1, Exercise 6 (book p. 165, PDF p. 173). Item `maclane:VII.1:ex6`.

## Background

The pentagon and triangle coherence axioms of a monoidal category are logically independent: neither follows from the other, shown by exhibiting structures satisfying one but not the other. See the nLab, [monoidal category](https://ncatlab.org/nlab/show/monoidal+category).

## Current state in the library

`pentagon_identity` and `triangle_identity` occur only as jointly-assumed fields of `Class Monoidal` (`Structure/Monoidal.v`); the library never constructs a structure satisfying the pentagon while failing the triangle (or vice versa), and there is no in-tree witness of their independence.

## Work to be done

Construct two witness structures — one carrying all the natural-isomorphism data of a monoidal category and satisfying the pentagon but violating the triangle, and one satisfying the triangle but violating the pentagon — thereby establishing the independence of the two axioms. This requires a `PreMonoidal`-style bundle that carries the associator/unitors and their naturality but *not* the two coherence fields, over which the two axioms can be independently asserted or refuted on a small concrete example. Suggested module: `Structure/Monoidal/Independence.v` (small concrete models, e.g. built over `Instance/Two.v` or a two-object category). In-tree donors: `Structure/Monoidal.v` (the axiom statements), `Instance/Two.v`, `Instance/Cat.v`.

## Definition of Done

- [ ] A data bundle isolating the pentagon and triangle as separately-assertable properties.
- [ ] A model satisfying the pentagon but refuting the triangle (with the refutation proved).
- [ ] A model satisfying the triangle but refuting the pentagon (with the refutation proved).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for both witnesses.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Monoidal/Independence.v` compiles cleanly.
- `Print Assumptions` on both witness structures shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the two models genuinely satisfy one axiom and refute the other; statement matches Mac Lane §VII.1 Exercise 6.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:ex6"],"deps":[]} -->

---8<---

---
title: "MacLane VII.1: Isbell's argument against strictifying by identifying isomorphic objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.1:remark2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.1 (book p. 164, PDF p. 172). Item `maclane:VII.1:remark2` (Isbell's impossibility argument).

## Background

A monoidal category cannot be strictified merely by identifying all isomorphic objects: in the skeleton of `(Set, ×)` a countably infinite set `D` satisfies `D ≅ D × D`, and if the associator were the identity compatible with the three projections one would derive, for all endomaps, both `f × g = f` and `f × g = g` — an absurdity. See the nLab, [coherence and strictification for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent. There is no `Isbell` result (`grep -i isbell` → 0 hits), no skeleton construction, and no `D ≅ D × D` object. `Structure/Monoidal.v` mentions in its header prose only that `(Set, ×)` is the standard obstruction to naive strictification; `Structure/Monoidal/Collapse.v` holds *unrelated* no-go results (Frobenius collapse, Abramsky no-cloning), not this identify-isomorphic-objects argument.

## Work to be done

Formalize the impossibility argument: exhibit (over a suitable concrete category, e.g. `Instance/Sets.v` or `Instance/Coq.v`) an object `D` with a chosen isomorphism `D ≅ D × D`, and prove that the hypothesis "the product-associator is the identity and commutes with the three projections after identifying isomorphic objects" forces `f × g ≈ f` and `f × g ≈ g` for endomorphisms of `D`, hence a contradiction — so no such on-the-nose strictification-by-identification exists. Suggested module: `Structure/Monoidal/Strictification.v` (the no-go), possibly with the `D ≅ D×D` witness in `Instance/Sets/Isbell.v`. In-tree donors: `Instance/Sets.v` / `Instance/Coq.v` (a concrete cartesian category with an infinite object), `Structure/Monoidal/Cartesian.v`.

## Definition of Done

- [ ] A concrete object `D` with `D ≅ D × D` constructed.
- [ ] The Isbell contradiction proved: the naive-strictification hypothesis forces `f × g ≈ f` and `f × g ≈ g`, hence `False`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed for the no-go theorem (Instance-layer stdlib axioms per docs/AXIOMS.md are acceptable if the witness lives in `Instance/`, and must be documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Monoidal/Strictification.v` compiles cleanly.
- `Print Assumptions` on the no-go theorem shows closed (or only the documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the argument reproduces Mac Lane §VII.1's Isbell remark (paraphrased).

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.1:remark2"],"deps":[]} -->

---8<---

---
title: "MacLane VII.2: The free monoidal category on one generator"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.2:def1, maclane:VII.2:construction1, maclane:VII.2:thm1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.2 (book pp. 165-168, PDF pp. 173-176). Items `maclane:VII.2:def1` (binary words), `maclane:VII.2:construction1` (the category W), `maclane:VII.2:thm1` (Theorem 1: W is free).

## Background

The free monoidal category `W` on one generator has as objects the binary words (formal parenthesized products of a placeholder, with empty-word slots) and exactly one arrow between any two words of equal length, so every diagram commutes; it is the walking (weak, non-symmetric) monoidal category, universal for a single object. See the nLab, [coherence and strictification for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent. There is no binary-word datatype (`find -iname '*word*.v'` → none; the `Term` types in `Solver/`, `Instance/Comp.v`, `Construction/PROP/Term.v` are unrelated). The nearest object is `FreePROP` (`Construction/PROP/Free.v`), which is the free **symmetric strict** monoidal category on a signature, with objects flattened to `nat` and symmetry built in — a different universal object, proved free only against `StrictMonoidalFunctor` + `SymmetricStrict` (`Construction/PROP/Universal.v`). Mac Lane's `W` is the free **plain** (weak, non-symmetric) monoidal category on **one** generator with a thin hom, and neither it nor its freeness against arbitrary `MonoidalFunctor`s is built.

## Work to be done

Define binary words as an inductive type (empty word, generator, tensor of two words), the category `W` with a unique arrow between equal-length words, its `@Monoidal W` structure (tensor of words, unit the empty word, unitors/associator the unique such arrows), and prove Theorem 1: for any monoidal `B` and object `b : B`, there is a unique monoidal functor `W ⟶ B` sending the generator to `b` (substitution of `b` into all blanks). Suggested module: `Construction/FreeMonoidal.v` (binary words + `W` + freeness). In-tree donors: `Structure/Monoidal.v`, `Functor/Structure/Monoidal.v` (`MonoidalFunctor`), `Construction/PROP/*` (as a design reference for the strict/symmetric analogue). This is the reusable core on which §VII.2's coherence corollary and several §VII.3 results depend.

## Definition of Done

- [ ] Binary words defined inductively; `W : Category` with thin hom (one arrow per equal-length pair) assembled.
- [ ] `@Monoidal W` with tensor of words, empty-word unit, and the unique unitors/associator.
- [ ] Theorem 1: existence and uniqueness of the monoidal functor `W ⟶ B` sending the generator to `b`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `W`, its monoidal structure, and the freeness theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level construction).

## Verification

- `coqc -R . Category Construction/FreeMonoidal.v` compiles cleanly.
- `Print Assumptions FreeMonoidal_universal.` (freeness) shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `W` is the plain (non-symmetric, non-strict) free monoidal category on one generator with thin hom, and the universal property is against arbitrary monoidal functors; statement matches Mac Lane §VII.2 Theorem 1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.2:def1","maclane:VII.2:construction1","maclane:VII.2:thm1"],"deps":[]} -->

---8<---

---
title: "MacLane VII.2: The coherence theorem for monoidal categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.2:cor1]
deps_item_ids: [maclane:VII.2:thm1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.2, Corollary (book p. 169, PDF pp. 177-178). Item `maclane:VII.2:cor1`.

## Background

Mac Lane's coherence theorem: for a monoidal category `B` there is a canonical natural isomorphism `can_B(v,w) : v_B ⇒ w_B` between the word-functors `B^n ⟶ B` of any two equal-length words, with the identity, `α`, `λ`, `ρ` and their inverses canonical and closed under composite and tensor — so every diagram of word-functors built from these commutes. See the nLab, [coherence and strictification for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent as a general theorem, present only as isolated consequences. `Structure/Monoidal.v:44` asserts in prose "By Mac Lane's coherence theorem these two laws force every formal diagram ... to commute", and `Structure/Monoidal/Proofs.v` proves a fixed handful of consequences of pentagon+triangle — `triangle_identity_left` (184), `triangle_identity_right` (299), `inverse_pentagon_identity` (215), `bimap_triangle_left/right` (327/314), `unit_identity` (344) — but there is no `can_B` assignment, no auxiliary category `It(B)`, and no general "all word-functor diagrams commute" statement. A consumer needing a new diagram to commute has no general result to invoke.

## Work to be done

Formalize the coherence theorem over the free monoidal category `W` of §VII.2 (see `maclane:VII.2:thm1`): define the canonical-map assignment `can_B(v,w)` for equal-length words (e.g. via the unique arrow in `W` transported along the substitution functor, or via the auxiliary iterated-tensor category `It(B)`), prove it is closed under composite and tensor with the structural isos canonical, and conclude that any two parallel canonical natural transformations between word-functors are equal (hence every such diagram commutes). Suggested module: `Structure/Monoidal/Coherence.v`. In-tree donors: `Construction/FreeMonoidal.v` (`W` and its freeness), `Structure/Monoidal/Proofs.v` (the base-case consequences), `Structure/Monoidal.v`.

## Definition of Done

- [ ] `can_B(v,w) : v_B ⇒ w_B` defined for equal-length words and shown canonical, closed under composite and tensor.
- [ ] Coherence theorem: any two parallel canonical maps between word-functors are equal (`≈`); every diagram of word-functors commutes.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the coherence theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Structure/Monoidal/Coherence.v` compiles cleanly.
- `Print Assumptions monoidal_coherence.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the theorem is the general "all word-functor diagrams commute", not merely the named base cases; statement matches Mac Lane §VII.2 Corollary.

## Dependencies

Depends on: maclane:VII.2:thm1

<!-- catalog: {"ids":["maclane:VII.2:cor1"],"deps":["maclane:VII.2:thm1"]} -->

---8<---

---
title: "MacLane VII.2: The free monoidal category on a set"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.2:ex3]
deps_item_ids: [maclane:VII.2:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.2, Exercise 3 (book p. 170, PDF p. 178). Item `maclane:VII.2:ex3`.

## Background

The free monoidal category `W_X` on a set `X` has objects the words in which each `x ∈ X` is a length-1 word, a canonical surjection `W_X → M_X` onto the free monoid on `X`, and a unique arrow `v → w` iff `v, w` have equal image in `M_X`; it satisfies the evident universal property. See the nLab, [coherence and strictification for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent for the plain-monoidal case. `Construction/PROP/Free.v` builds `FreePROP S`, the free **symmetric strict** monoidal category on a signature (objects flattened to `nat`), with universal property in `Construction/PROP/Universal.v` — a different universal object. There is no `W_X`, no surjection onto the free monoid, and no thin-hom-by-equal-image object for the weak, non-symmetric case.

## Work to be done

Generalize the free monoidal category `W` of §VII.2 (`maclane:VII.2:construction1`) from one generator to an arbitrary set/type `X`: objects are `X`-words (each `x` a length-1 word), with a surjection to the free monoid `M_X` and a unique arrow between two words iff they have equal image in `M_X`; then prove the universal property (a unique monoidal functor `W_X ⟶ B` extending any function `X → ob B`). Suggested module: `Construction/FreeMonoidal/OnSet.v`. In-tree donors: `Construction/FreeMonoidal.v` (the one-generator case to generalize), `Construction/PROP/Free.v` (the strict/symmetric analogue as reference), a free-monoid `M_X`.

## Definition of Done

- [ ] `W_X : Category` for a set/type `X`, with `X`-words, the surjection to `M_X`, and thin hom by equal image.
- [ ] `@Monoidal W_X` assembled.
- [ ] Universal property: unique monoidal functor `W_X ⟶ B` extending `X → ob B`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the universal property.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Construction/FreeMonoidal/OnSet.v` compiles cleanly.
- `Print Assumptions FreeMonoidalOnSet_universal.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `W_X` is the plain free monoidal category on `X` with thin hom by equal image in `M_X`; statement matches Mac Lane §VII.2 Exercise 3.

## Dependencies

Depends on: maclane:VII.2:construction1

<!-- catalog: {"ids":["maclane:VII.2:ex3"],"deps":["maclane:VII.2:construction1"]} -->

---8<---

---
title: "MacLane VII.2: The associahedron of canonical maps"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.2:ex1, maclane:VII.2:ex2]
deps_item_ids: [maclane:VII.2:cor1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.2, Exercises 1 and 2 (book p. 170, PDF p. 178). Items `maclane:VII.2:ex1` (length-5 diagram) and `maclane:VII.2:ex2` (Stasheff, general case).

## Background

The diagram of all canonical maps between binary words of length `n+3` forms a polyhedral subdivision of the `n`-sphere — the Stasheff associahedron; the length-5 case has 19 regions (16 pentagons realizing `α`, 3 squares realizing naturality). See the nLab, [associahedron](https://ncatlab.org/nlab/show/associahedron).

## Current state in the library

Absent. `grep -i` for `associahedr|stasheff|polyhedr|subdivision|sphere` yields zero hits; there is no cell-complex, polytope, or geometric-realization machinery, and the underlying canonical-maps apparatus (the coherence theorem of §VII.2, item `maclane:VII.2:cor1`) is itself not yet formalized.

## Work to be done

Building on the canonical maps of the coherence theorem (`maclane:VII.2:cor1`): (a) present the finite diagram of all canonical maps between length-5 words as a combinatorial complex with 19 cells (16 pentagons + 3 naturality squares) and verify its face structure; (b) generalize to length `n+3` as the associahedron `K_{n+2}`, exhibited as a polyhedral subdivision of `S^n`. Because this needs polytope/CW combinatorics the library lacks, the tractable in-tree core is the **combinatorial** associahedron (a finite poset/complex of bracketings and their `α`-edges) rather than a metric polytope; the topological realization as a sphere subdivision is the stretch goal. Suggested module: `Instance/Associahedron.v`. In-tree donors: `Structure/Monoidal/Coherence.v` (the canonical maps), `Instance/Roof.v` / small finite categories for the cell poset.

## Definition of Done

- [ ] The finite diagram of canonical maps between length-5 words presented as a combinatorial complex; the 16 pentagons + 3 squares accounted for.
- [ ] The general associahedron `K_{n+2}` of length-`(n+3)` bracketings defined combinatorially, with (at minimum) its cell/face count characterized; sphere-subdivision realization documented as far as the library's machinery allows.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer stdlib axioms per docs/AXIOMS.md acceptable and documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Associahedron.v` compiles cleanly.
- `Print Assumptions` on the length-5 complex shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the length-5 cell count (16 pentagons + 3 squares) and the general `K_{n+2}` match Mac Lane §VII.2 Exercises 1-2 (Stasheff 1963).

## Dependencies

Depends on: maclane:VII.2:cor1

<!-- catalog: {"ids":["maclane:VII.2:ex1","maclane:VII.2:ex2"],"deps":["maclane:VII.2:cor1"]} -->

---8<---

---
title: "MacLane VII.3: Monoids in a monoidal category recover the classical algebraic structures"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.3:remark1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.3 (book p. 171, PDF p. 179). Item `maclane:VII.3:remark1` (the examples table).

## Background

Monoid objects in various monoidal categories specialize to familiar structures: ordinary monoids in `(Set, ×)`, topological monoids in `(Top, ×)`, monads in `([C,C], ∘)`, rings in `(Ab, ⊗, ℤ)`, K-algebras in `(K-Mod, ⊗_K)`, comonoids in `B^op`, strict monoidal categories in `(Cat, ×)`, and categories in `(O-Grph, ×_O)`. See the nLab, [monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

Only part of the table is instantiated. The general mechanism is present (`MonoidObject` over any `Monoidal`). Proven as a genuine equivalence: monad = monoid object in `([C,C], ∘)` — `Monoid_Monad` at `Monad/Monoid.v:40`. Present as a definition: the cartesian specialization to ordinary monoids, `Structure/Monoid.v:173`. Present as a sibling class (identification to monoid-in-`C^op` noted but not proved): `Comonoid` at `Theory/Algebra/Comonoid.v:40`. Missing: rings (monoid in `(Ab, ⊗)`), K-algebras (monoid in `(K-Mod, ⊗)`), topological/graded/DG algebras, K-coalgebras, and the identification "strict monoidal category = monoid in `(Cat, ×)`" (only the funny-tensor premonoidal analogue exists, `Instance/StrictCat/Premonoid.v`).

## Work to be done

Fill in the outstanding entries of the examples table by instantiating `MonoidObject` in the relevant monoidal categories and identifying the monoid objects with the classical structures: (a) rings as monoids in `(Ab, ⊗, ℤ)` and K-algebras as monoids in `(K-Mod, ⊗_K)` — depend on those categories (`Ab` is #256, its tensor product is #265, module categories are #258); (b) the identification "strict monoidal category = monoid object in `(Cat, ×, 1)`", the cartesian counterpart of the existing funny-tensor result; (c) the definitional identification `Comonoid X ≃ Monoid (C^op) X`. Suggested module: `Theory/Algebra/Monoid/Examples.v` (with the `Cat`-monoid identification perhaps in `Instance/StrictCat/Monoid.v`). In-tree donors: `Structure/Monoid.v`, `Monad/Monoid.v`, `Theory/Algebra/Comonoid.v`, `Instance/StrictCat/Premonoid.v`, `Instance/Cat.v`.

## Definition of Done

- [ ] Rings identified as monoid objects in `(Ab, ⊗, ℤ)` (and K-algebras in `(K-Mod, ⊗_K)`), each direction stated.
- [ ] "Strict monoidal category = monoid object in `(Cat, ×, 1)`" proved (cartesian counterpart of the funny-tensor result).
- [ ] `Comonoid X ≃ Monoid (C^op) X` established.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for each identification (Instance-layer axioms per docs/AXIOMS.md documented where the concrete categories are used).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Monoid/Examples.v` compiles cleanly.
- `Print Assumptions` on each identification shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: each entry recovers the classical structure; statement matches Mac Lane §VII.3's table.

## Dependencies

Depends on: #256
Depends on: #258
Depends on: #265

<!-- catalog: {"ids":["maclane:VII.3:remark1"],"deps":["#256","#258","#265"]} -->

---8<---

---
title: "MacLane VII.3: The general associative law and coherence for monoids"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.3:prop1, maclane:VII.3:ex2]
deps_item_ids: [maclane:VII.2:cor1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.3, Proposition 1 and Exercise 2 (book pp. 171-173, PDF pp. 179-181). Items `maclane:VII.3:prop1` (General Associative Law) and `maclane:VII.3:ex2` (coherence for monoids).

## Background

For a monoid object `⟨c, μ, η⟩` in a monoidal category, the iterated products along any two equal-length words agree after the canonical map: `μ_w ∘ can_c(v,w) = μ_v`, so the `n`-fold product `μ^{(n)} : c^n → c` is well defined and satisfies `μ^{(n)}(μ^{(k₁)} ⊗ ⋯ ⊗ μ^{(kₙ)}) = μ^{(k₁+⋯+kₙ)}`. Exercise 2 re-reads this as a coherence theorem for monoids. See the nLab, [monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

Only the ternary (n=3) case exists: `mu_assoc` in `Theory/Algebra/Monoid.v:44` and `mappend_assoc` (with `mappend_assoc_sym`) in `Structure/Monoid.v:135`. There is no `μ^{(n)}`, no canonical assignment `can_c(v,w)` for monoids, no word-indexed iterated product, and no general law. (The "General associativity coherence" cells in `Construction/PROP/Universal.v:254` are the interpretation functor's associator cell, a different object.) The prerequisite — the monoidal coherence canonical maps of §VII.2 (item `maclane:VII.2:cor1`) — is itself not yet formalized.

## Work to be done

Define the word-indexed iterated product `μ_w` and the `n`-fold product `μ^{(n)}` for a monoid object, and prove the General Associative Law `μ_w ∘ can_c(v,w) = μ_v` by induction over canonical maps (the monoid axioms supply the `α`/`λ`/`ρ` base cases), then derive `μ^{(n)}(μ^{(k₁)} ⊗ ⋯) = μ^{(Σkᵢ)}`. For Exercise 2, phrase the result as a coherence theorem (any two paths `w → (−)` in the monoid-arrow graph agree) and note that it fails when the target is `(−) ⊗ (−)` of length 2. Suggested module: `Theory/Algebra/Monoid/Associativity.v`. In-tree donors: `Structure/Monoidal/Coherence.v` (the canonical maps `can_B`, item `maclane:VII.2:cor1`), `Theory/Algebra/Monoid.v`, `Structure/Monoid.v`.

## Definition of Done

- [ ] `μ_w` and `μ^{(n)}` defined; General Associative Law `μ_w ∘ can_c(v,w) ≈ μ_v` proved.
- [ ] `μ^{(n)}(μ^{(k₁)} ⊗ ⋯ ⊗ μ^{(kₙ)}) ≈ μ^{(k₁+⋯+kₙ)}` derived.
- [ ] Exercise 2: the coherence reading for monoids stated (paths to `(−)` agree; the length-2 target failure noted).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the General Associative Law.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Monoid/Associativity.v` compiles cleanly.
- `Print Assumptions monoid_general_associativity.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the law is the full word-indexed statement, not merely the ternary axiom; statement matches Mac Lane §VII.3 Proposition 1 and Exercise 2.

## Dependencies

Depends on: maclane:VII.2:cor1

<!-- catalog: {"ids":["maclane:VII.3:prop1","maclane:VII.3:ex2"],"deps":["maclane:VII.2:cor1"]} -->

---8<---

---
title: "MacLane VII.3: Construction of free monoids as coproducts of tensor powers"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.3:thm2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.3, Theorem 2 (book pp. 172-173, PDF pp. 180-181). Item `maclane:VII.3:thm2`.

## Background

If a monoidal category `B` has countable coproducts preserved by every `a ⊗ −` and `− ⊗ a`, then the forgetful functor `U : Mon(B) → B` has a left adjoint; the free monoid on `a` is `∐ₙ aⁿ` (the coproduct of tensor powers), with juxtaposition multiplication `aᵐ ⊗ aⁿ ≅ aᵐ⁺ⁿ` and unit the injection of `a⁰`. This specializes to the free monoid on a set, the tensor algebra of a module, and free topological monoids. See the nLab, [free monoid](https://ncatlab.org/nlab/show/free+monoid).

## Current state in the library

Absent. `Mon_Forget : Mon ⟶ C` exists (`Theory/Algebra/Monoid/Hom.v:93`) but has no left adjoint. "Free monoid" appears only aspirationally: `Structure/Monoid.v:73` (essay), `Theory/Coq/Foldable.v` (the class "records no laws ... stated in prose rather than enforced"), and `Theory/Coq/List.v` (comment). There is no `∐ₙ aⁿ` construction, no juxtaposition multiplication, and no universal property — even the `Set`/`Type` specialization (lists as the value of a left adjoint) is prose-only.

## Work to be done

Construct the free-monoid functor and the adjunction `Free ⊣ U` under the hypothesis that `B` has countable coproducts preserved by `a ⊗ −` and `− ⊗ a`: define `Free a := ∐ₙ aⁿ` (tensor powers via `a⁰ = I`, `aⁿ⁺¹ = a ⊗ aⁿ`), the multiplication from `aᵐ ⊗ aⁿ ≅ aᵐ⁺ⁿ` and coproduct universality, the unit `a⁰ → ∐ₙ aⁿ`, prove the monoid laws, and establish the universal property / adjunction `Free ⊣ Mon_Forget`. Keep the coproduct-preservation hypotheses explicit inputs. Suggested module: `Theory/Algebra/Monoid/Free.v`. In-tree donors: `Theory/Algebra/Monoid/Hom.v` (`Mon`, `Mon_Forget`), `Structure/Cocartesian.v` / countable-coproduct machinery, `Structure/Monoidal.v`, `Theory/Adjunction.v`.

## Definition of Done

- [ ] `Free a := ∐ₙ aⁿ` with juxtaposition multiplication and unit; the monoid-object laws proved.
- [ ] The universal property / adjunction `Free ⊣ Mon_Forget` under the explicit coproduct-preservation hypotheses.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the adjunction.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Monoid/Free.v` compiles cleanly.
- `Print Assumptions Free_Monoid_Adjunction.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the free monoid is `∐ₙ aⁿ` with juxtaposition and the coproduct-preservation hypotheses are explicit; statement matches Mac Lane §VII.3 Theorem 2.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.3:thm2"],"deps":[]} -->

---8<---

---
title: "MacLane VII.3: Finite products in the category of monoids"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.3:ex1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.3, Exercise 1 (book p. 173, PDF p. 181). Item `maclane:VII.3:ex1`.

## Background

If a monoidal category `B` has finite products, then the category `Mon(B)` of monoid objects again has finite products, computed on underlying objects. See the nLab, [monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

Partial. The category `Mon` of internal monoids exists (`Theory/Algebra/Monoid/Hom.v:83`) with a faithful `Mon_Forget`. The object-level fragment "the product carrier `x × y` is a monoid" is present but only for the cartesian structure: `Product_Monoid : @MonoidObject C CC_Monoidal (x × y)` at `Structure/Monoid.v:179` — and on the *sibling* `MonoidObject` definition, not the `Monoid` on which `Mon` is built. It is never assembled into the categorical product on `Mon`: no proof that the projections/pairing are monoid homomorphisms, no `@Cartesian Mon`, and no terminal monoid.

## Work to be done

Show `Mon(B)` inherits finite products: prove the underlying-object product `x × y` is the categorical product in `Mon` (projections `exl`/`exr` and pairing `⟨f,g⟩` are monoid homomorphisms and satisfy the product universal property), exhibit the terminal monoid (the unit object with its trivial structure), and assemble `@Cartesian Mon` (+ `@Terminal Mon`). Reconcile the two monoid-object definitions (`Theory/Algebra/Monoid.v` vs `Structure/Monoid.v`) so `Product_Monoid` applies to `Mon`. Suggested module: `Theory/Algebra/Monoid/Product.v`. In-tree donors: `Theory/Algebra/Monoid/Hom.v` (`Mon`), `Structure/Monoid.v` (`Product_Monoid`), `Structure/Cartesian.v`.

## Definition of Done

- [ ] `x × y` shown to be the categorical product in `Mon`: projections and pairing are monoid homomorphisms; universal property proved.
- [ ] Terminal monoid exhibited; `@Cartesian Mon` (and `@Terminal Mon`) assembled.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the cartesian structure on `Mon`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Monoid/Product.v` compiles cleanly.
- `Print Assumptions Mon_Cartesian.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the product is computed on underlying objects with equivariant projections; statement matches Mac Lane §VII.3 Exercise 1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.3:ex1"],"deps":[]} -->

---8<---

---
title: "MacLane VII.3: Substitution of words and the generalized associative law"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.3:ex3]
deps_item_ids: [maclane:VII.2:construction1, maclane:VII.3:prop1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.3, Exercise 3 (book p. 173, PDF p. 181). Item `maclane:VII.3:ex3`.

## Background

Each word `u` of length `n` induces a substitution functor `u_W : Wⁿ → W`; for words `v₁,…,vₙ` the word `u_W(v₁,…,vₙ)` has length the sum of the lengths, and the canonical maps satisfy `μ_w = μ_u ∘ (μ_{v₁} ⊗ ⋯ ⊗ μ_{vₙ}) ∘ (canonical)`, generalizing the general associative law. See the nLab, [coherence and strictification for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent. The free monoidal category `W` on which this exercise is stated (item `maclane:VII.2:construction1`) does not exist, and there is no word-substitution functor `u_W : Wⁿ → W`. `Construction/PROP/Monoidal.v` (`FreeMonoidal`) builds the free symmetric strict structure of a PROP, not `W` or its substitution operation. The general associative law it generalizes (§VII.3 Proposition 1) is likewise not yet formalized.

## Work to be done

Define the word-substitution functor `u_W : Wⁿ → W` (substitute the arguments into `u`'s blanks) over the free monoidal category `W` (`maclane:VII.2:construction1`), verify the length additivity, and prove the substitution identity for iterated products `μ_{u_W(v₁,…,vₙ)} ≈ μ_u ∘ (μ_{v₁} ⊗ ⋯ ⊗ μ_{vₙ}) ∘ can`, exhibiting it as a generalization of the general associative law (`maclane:VII.3:prop1`). Suggested module: `Construction/FreeMonoidal/Substitution.v`. In-tree donors: `Construction/FreeMonoidal.v` (`W`), `Theory/Algebra/Monoid/Associativity.v` (the general associative law), `Structure/Monoidal/Coherence.v` (canonical maps).

## Definition of Done

- [ ] `u_W : Wⁿ → W` defined; length additivity proved.
- [ ] The substitution identity `μ_{u_W(v₁,…,vₙ)} ≈ μ_u ∘ (μ_{v₁} ⊗ ⋯ ⊗ μ_{vₙ}) ∘ can` proved.
- [ ] Shown to generalize the general associative law of §VII.3 Proposition 1.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the substitution identity.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Construction/FreeMonoidal/Substitution.v` compiles cleanly.
- `Print Assumptions word_substitution_law.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the substitution functor and identity match Mac Lane §VII.3 Exercise 3.

## Dependencies

Depends on: maclane:VII.2:construction1
Depends on: maclane:VII.3:prop1

<!-- catalog: {"ids":["maclane:VII.3:ex3"],"deps":["maclane:VII.2:construction1","maclane:VII.3:prop1"]} -->

---8<---

---
title: "MacLane VII.4: Modules over a monoid object and the free/forgetful adjunction"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.4:def1, maclane:VII.4:def2, maclane:VII.4:construction1, maclane:VII.4:def3]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4 (book p. 174, PDF p. 182). Items `maclane:VII.4:def1` (left action), `maclane:VII.4:def2` (morphism of actions), `maclane:VII.4:construction1` (the category `cLact` with forgetful and free functors), `maclane:VII.4:def3` (right action and bimodule).

## Background

A left action of a monoid object `⟨c, μ, η⟩` on an object `a` in a monoidal category is an arrow `ν : c ⊗ a → a` satisfying an associativity square and a unit triangle; actions and equivariant maps form a category `cLact`, with forgetful `cLact → B` having a left adjoint `b ↦ c ⊗ b`; there are dually right actions `σ : b ⊗ c → b` and, combining a commuting pair, bimodules. See the nLab, [module over a monoid](https://ncatlab.org/nlab/show/module+over+a+monoid).

## Current state in the library

Absent. There is no class for an internal module/action `ν : c ⊗ a → a` (no `MonoidAction`/`LeftModule`/`RightModule`/`Bimodule`), no morphism-of-modules class, no category `cLact`, and no free functor `c ⊗ −`. The only near-miss is `TAlgebra` (`Monad/Algebra.v:24`), which is an action of a monoid in the endofunctor category `[X,X]` on an object — the special case `B = [X,X]`, not the general internal module with `c` and `a` both objects of one monoidal category. The monoid-object notion itself is present (`Theory/Algebra/Monoid.v:44`, `Structure/Monoid.v:124`), but no object acted on by such a monoid.

## Work to be done

Develop the internal module theory in a fixed monoidal category `B`: (a) `LeftAction c a := { ν : c ⊗ a ~> a | assoc-square ∧ unit-triangle }` with the left-regular action `c` on itself by `μ`; (b) morphisms of left actions; (c) the category `cLact` of left `c`-actions, the forgetful `cLact → B`, and its left adjoint `b ↦ c ⊗ b` (with the induced action via `α` and `μ`); (d) right actions `σ : b ⊗ c → b` and the bimodule combining a commuting left and right action. Suggested module: `Theory/Algebra/Module.v` (with the category/adjunction in `Theory/Algebra/Module/Category.v`). In-tree donors: `Theory/Algebra/Monoid.v` / `Structure/Monoid.v` (monoid objects), `Monad/Algebra.v` (the `[X,X]`-special case as a design reference), `Theory/Adjunction.v`. This is the reusable core for the rest of §VII.4.

## Definition of Done

- [ ] `LeftAction`, morphisms of left actions, and the left-regular action defined with laws proved.
- [ ] `cLact : Category`, the forgetful `cLact → B`, and the left adjoint `b ↦ c ⊗ b` (adjunction proved).
- [ ] Right actions and bimodules defined with their laws.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `cLact` and the free/forgetful adjunction.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (reusable development).

## Verification

- `coqc -R . Category Theory/Algebra/Module.v` (and `Theory/Algebra/Module/Category.v`) compile cleanly.
- `Print Assumptions cLact_Free_Adjunction.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the module `ν : c ⊗ a → a` has both `c` and `a` objects of one monoidal `B` (not the monad special case); statement matches Mac Lane §VII.4.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.4:def1","maclane:VII.4:def2","maclane:VII.4:construction1","maclane:VII.4:def3"],"deps":[]} -->

---8<---

---
title: "MacLane VII.4: Limits and colimits in the category of modules"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex4, maclane:VII.4:ex5]
deps_item_ids: [maclane:VII.4:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercises 4 and 5 (book p. 175, PDF p. 183). Items `maclane:VII.4:ex4` (coproducts) and `maclane:VII.4:ex5` (finite products).

## Background

If the base monoidal category `B` has coproducts preserved by every `a ⊗ −`, the module category `cLact` has coproducts and the forgetful functor preserves them; if `B` has finite products, so does `cLact`, with the product projections becoming morphisms of actions. See the nLab, [module over a monoid](https://ncatlab.org/nlab/show/module+over+a+monoid).

## Current state in the library

Absent, pending the module category. The category `cLact` of left actions (item `maclane:VII.4:construction1`) does not exist, so there is nothing to inherit (co)limits. Coproducts (`Structure/Cocartesian.v`), finite products (`Structure/Cartesian.v`), and the fact that left adjoints preserve colimits are available generically, but not applied to modules.

## Work to be done

Building on the module category `cLact` (`maclane:VII.4:construction1`): (a) under the hypothesis that `B` has coproducts preserved by every `a ⊗ −`, construct coproducts in `cLact` and show the forgetful functor preserves them; (b) under the hypothesis that `B` has finite products, construct finite products in `cLact` with the projections `a × a' → a`, `a × a' → a'` shown equivariant. Suggested module: `Theory/Algebra/Module/Limits.v`. In-tree donors: `Theory/Algebra/Module.v` (`cLact` and forgetful), `Structure/Cocartesian.v`, `Structure/Cartesian.v`.

## Definition of Done

- [ ] Coproducts in `cLact` under the coproduct-preservation hypothesis; forgetful preserves them (Exercise 4).
- [ ] Finite products in `cLact` under a finite-products hypothesis on `B`; projections equivariant (Exercise 5).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the (co)product structures.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Module/Limits.v` compiles cleanly.
- `Print Assumptions` on the (co)product structures shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: statement matches Mac Lane §VII.4 Exercises 4-5, with equivariant projections.

## Dependencies

Depends on: maclane:VII.4:construction1

<!-- catalog: {"ids":["maclane:VII.4:ex4","maclane:VII.4:ex5"],"deps":["maclane:VII.4:construction1"]} -->

---8<---

---
title: "MacLane VII.4: The relative tensor product of a right module by a left module"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex6]
deps_item_ids: [maclane:VII.4:def1, maclane:VII.4:def3]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercise 6 (book p. 175, PDF p. 183). Item `maclane:VII.4:ex6`.

## Background

If `B` has coequalizers, the relative tensor product `b ⊗_c a` of a right `c`-module `b` and a left `c`-module `a` is the coequalizer of the two maps `b ⊗ (c ⊗ a) ⇉ b ⊗ a` given by the two actions; `⊗_c` is a functor `Ract_c × cLact → B`. See the nLab, [bimodule](https://ncatlab.org/nlab/show/bimodule).

## Current state in the library

Absent. There is no relative/balanced tensor `b ⊗_c a`; the module notions it depends on (a left action, item `maclane:VII.4:def1`, and a right action, item `maclane:VII.4:def3`) are not yet formalized. The ambient colimit is available — `Structure/Coequalizer.v` (with `Reflexive.v` and `Split.v`) — but the coequalizer-of-two-actions construction and the functoriality of `⊗_c` are not.

## Work to be done

Given the module notions of §VII.4 (`maclane:VII.4:def1`, `maclane:VII.4:def3`) and coequalizers in `B`, define `b ⊗_c a` as the coequalizer of the right-action-on-the-left-factor and left-action-on-the-right-factor maps `b ⊗ (c ⊗ a) ⇉ b ⊗ a`, and prove `⊗_c : Ract_c × cLact ⟶ B` is a functor. Suggested module: `Theory/Algebra/Module/Tensor.v`. In-tree donors: `Theory/Algebra/Module.v` (left/right actions), `Structure/Coequalizer.v`, `Structure/Monoidal.v`.

## Definition of Done

- [ ] `b ⊗_c a` defined as the stated coequalizer (under a coequalizers hypothesis on `B`).
- [ ] `⊗_c : Ract_c × cLact ⟶ B` proved a functor.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `⊗_c`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Module/Tensor.v` compiles cleanly.
- `Print Assumptions relative_tensor_functor.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `b ⊗_c a` is the coequalizer of the two action maps and `⊗_c` is a bifunctor; statement matches Mac Lane §VII.4 Exercise 6.

## Dependencies

Depends on: maclane:VII.4:def1
Depends on: maclane:VII.4:def3

<!-- catalog: {"ids":["maclane:VII.4:ex6"],"deps":["maclane:VII.4:def1","maclane:VII.4:def3"]} -->

---8<---

---
title: "MacLane VII.4: Comodules over a comonoid object"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex3]
deps_item_ids: [maclane:VII.4:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercise 3 (book p. 175, PDF p. 183). Item `maclane:VII.4:ex3` (actions of a K-coalgebra).

## Background

Dually to a module over a monoid, a comodule over a comonoid (coalgebra) object `c` is a coaction `ρ : a → c ⊗ a` satisfying the coassociativity and counit laws obtained by dualizing the module axioms — the "actions of a K-coalgebra" of the exercise. See the nLab, [comodule](https://ncatlab.org/nlab/show/comodule).

## Current state in the library

Absent. There is no comodule/coaction `ρ : a → c ⊗ a` over a general internal comonoid object. `Comonad/Coalgebra.v` has `w_coaction` — but that is a coalgebra over a *comonad* (a comodule over a comonoid in the endofunctor category), the special case, not the general internal comodule. Internal comonoids and their homomorphisms exist (`Theory/Algebra/Comonoid.v`) but not their comodules; there is no `K-Mod` category either.

## Work to be done

Dualize the internal-module notion of §VII.4 (`maclane:VII.4:def1`): define a comodule `ρ : a → c ⊗ a` over a comonoid object `c` with the coassociativity and counit laws, the morphisms of comodules, and the category of `c`-comodules (with the cofree comodule `c ⊗ −` and the forgetful/cofree adjunction where available). Suggested module: `Theory/Algebra/Comodule.v`. In-tree donors: `Theory/Algebra/Comonoid.v` (comonoid objects), `Theory/Algebra/Module.v` (the module notion to dualize), `Comonad/Coalgebra.v` (the endofunctor special case as reference).

## Definition of Done

- [ ] `Comodule c a := { ρ : a ~> c ⊗ a | coassoc ∧ counit }` with morphisms and the comodule category.
- [ ] Cofree comodule `c ⊗ −` and the forgetful/cofree adjunction (where the dual hypotheses hold).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the comodule category.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Comodule.v` compiles cleanly.
- `Print Assumptions Comodule.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the coaction `ρ : a → c ⊗ a` is over a general comonoid object; statement matches Mac Lane §VII.4 Exercise 3.

## Dependencies

Depends on: maclane:VII.4:def1

<!-- catalog: {"ids":["maclane:VII.4:ex3"],"deps":["maclane:VII.4:def1"]} -->

---8<---

---
title: "MacLane VII.4: Coherence for a module action"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex7]
deps_item_ids: [maclane:VII.4:def1, maclane:VII.2:cor1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercise 7 (book p. 175, PDF p. 183). Item `maclane:VII.4:ex7`.

## Background

Given a left action `ν : c ⊗ a → a`, the canonical maps `ν_w : w_{c,a} → a` (for words `w` of length ≥ 1 whose last argument is the placeholder, with `a` substituted last and `c` elsewhere) satisfy a coherence property extending Mac Lane's monoidal coherence to actions. See the nLab, [module over a monoid](https://ncatlab.org/nlab/show/module+over+a+monoid).

## Current state in the library

Absent. There is no module/action of a monoid object in the first place (item `maclane:VII.4:def1`), and the underlying monoidal coherence apparatus — the word category and canonical maps of §VII.2 (item `maclane:VII.2:cor1`) — is likewise not yet formalized, so no coherence result for the canonical maps `ν_w` of an action exists.

## Work to be done

Building on the left action of §VII.4 (`maclane:VII.4:def1`) and the coherence canonical maps of §VII.2 (`maclane:VII.2:cor1`): define, for words `w` whose last argument is the placeholder, the induced object `w_{c,a}` and the canonical evaluation `ν_w : w_{c,a} → a`, and prove the coherence property (any two canonical evaluations agree), the action analogue of the general associative law. Suggested module: `Theory/Algebra/Module/Coherence.v`. In-tree donors: `Theory/Algebra/Module.v`, `Structure/Monoidal/Coherence.v`, `Construction/FreeMonoidal.v`.

## Definition of Done

- [ ] `w_{c,a}` and `ν_w` defined for admissible words; the coherence property (canonical evaluations agree) proved.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the coherence result.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Theory/Algebra/Module/Coherence.v` compiles cleanly.
- `Print Assumptions action_coherence.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the coherence property for `ν_w` matches Mac Lane §VII.4 Exercise 7.

## Dependencies

Depends on: maclane:VII.4:def1
Depends on: maclane:VII.2:cor1

<!-- catalog: {"ids":["maclane:VII.4:ex7"],"deps":["maclane:VII.4:def1","maclane:VII.2:cor1"]} -->

---8<---

---
title: "MacLane VII.4: Actions of a monad on an endofunctor and liftings to the algebras"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercise 1 (book p. 174, PDF p. 182). Item `maclane:VII.4:ex1` (Dubuc 1970).

## Background

For a monad `⟨T, η, μ⟩` on `X`, an action of `T` on an endofunctor `S : X → X` (a `T`-algebra structure on `S` in `[X,X]`) corresponds bijectively to a lifting `S' : X → X^T` with `Gᵀ S' = S`; liftings and actions are in one-to-one correspondence. See the nLab, [Eilenberg-Moore category](https://ncatlab.org/nlab/show/Eilenberg-Moore+category).

## Current state in the library

Partial. The Eilenberg–Moore category `X^T` and its forgetful `Uᵀ = Gᵀ` are present (`Monad/Eilenberg/Moore.v:44`), as is the object-level monad action `TAlgebra` (`Monad/Algebra.v:24`, the pointwise ingredient). Missing: the notion of a `T`-action on an endofunctor `S` (a natural `α : T S → S` with the algebra laws in `[X,X]`), the construction of a lifting `S' : X → X^T` with `Gᵀ S' = S` from such an action and conversely, and the bijection between the two. Note `Monad/Lifting.v` is a *different* theorem — the Dubuc (1968) adjoint-triangle lifting of left adjoints along a monadic functor — not this action/lifting correspondence.

## Work to be done

Define a `T`-action on an endofunctor `S : X → X` (a `T`-algebra object in `[X,X]` under `T ∘ −`, i.e. natural `α : T S ⇒ S` with unit and associativity), construct from it a lifting `S' : X → X^T` with `Gᵀ S' = S` (fibrewise via `TAlgebra`), construct the inverse, and prove the two are mutually inverse (the Dubuc correspondence). Suggested module: `Monad/Action.v` (or `Monad/Lifting/Endofunctor.v`). In-tree donors: `Monad/Eilenberg/Moore.v`, `Monad/Algebra.v` (`TAlgebra`, `TAlgebraHom`), `Instance/Fun.v`.

## Definition of Done

- [ ] A `T`-action on an endofunctor `S` defined (natural `α : T S ⇒ S` with algebra laws).
- [ ] Lifting `S' : X → X^T` with `Gᵀ S' = S` constructed both ways; the bijection {actions} ↔ {liftings} proved.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the correspondence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Monad/Action.v` compiles cleanly.
- `Print Assumptions monad_action_lifting_bijection.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: this is the Dubuc (1970) action/lifting correspondence (distinct from `Monad/Lifting.v`'s adjoint triangle); statement matches Mac Lane §VII.4 Exercise 1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:VII.4:ex1"],"deps":[]} -->

---8<---

---
title: "MacLane VII.4: A monoidal category acting on a category (actegories)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.4:ex2]
deps_item_ids: [maclane:VII.4:ex1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.4, Exercise 2 (book p. 174, PDF p. 182). Item `maclane:VII.4:ex2`.

## Background

A small strict monoidal category `B` (a monoid in `(Cat, ×, 1)`) can act on a category `C` — an actegory, with an action `⊗ : B × C → C` coherent with the tensor of `B` — and a monoid in `B` then acts on objects of `C`; this extends the monad/lifting correspondence to functors `S : A → X`. See the nLab, [action of a monoidal category](https://ncatlab.org/nlab/show/actegory).

## Current state in the library

Absent. There is no actegory / module-category structure (no "monoidal category acting on a category"), no action of a monoid in `B` on an object of `C`, and no extension of the monad-action correspondence to functors `S : A → X`. `Instance/StrictCat/Premonoid.v` (strict premonoidal = monoid in `(StrictCat, □)`) is a monoid object in a `Cat`-like setting but not an action *on* a category. The monad/Eilenberg–Moore development is the one specific actegory instance (`[X,X]` acting on `X`), not the general framework.

## Work to be done

Define an actegory: a (strict) monoidal category `B` acting on a category `C` via `act : B ∏ C ⟶ C` with unitor/associator coherence relating `act` to the tensor and unit of `B`; then define the action of a monoid object in `B` on an object of `C`, and use it to extend the monad action/lifting correspondence of §VII.4 (`maclane:VII.4:ex1`) to functors `S : A → X`. Suggested module: `Structure/Actegory.v`. In-tree donors: `Structure/Monoidal.v`, `Structure/Monoidal/Strict.v`, `Monad/Action.v` (the endofunctor instance to generalize), `Instance/StrictCat/Premonoid.v`.

## Definition of Done

- [ ] `Actegory` defined (a monoidal `B` acting on `C` with coherence).
- [ ] Action of a monoid object in `B` on an object of `C` defined.
- [ ] The monad action/lifting correspondence extended to functors `S : A → X`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the principal results.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Actegory.v` compiles cleanly.
- `Print Assumptions Actegory.` shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the action `B ∏ C ⟶ C` is coherent with the tensor of `B`; statement matches Mac Lane §VII.4 Exercise 2.

## Dependencies

Depends on: maclane:VII.4:ex1

<!-- catalog: {"ids":["maclane:VII.4:ex2"],"deps":["maclane:VII.4:ex1"]} -->

---8<---

---
title: "MacLane VII.5: The simplicial category Δ as the free strict monoidal category on a monoid"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.5:construction1, maclane:VII.5:remark-protean, maclane:VII.5:prop1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.5 (book pp. 175-176, 180, PDF pp. 183-184, 188). Items `maclane:VII.5:construction1` (Δ with ordinal-sum monoidal structure and the universal monoid), `maclane:VII.5:remark-protean` (the four characterizations of Δ), `maclane:VII.5:prop1` (Proposition 1, the universal property).

## Background

The simplicial category Δ (finite ordinals and monotone maps) is a strict monoidal category under ordinal addition, with unit the ordinal 0; the object 1 with the unique `μ : 2 → 1` and `η : 0 → 1` is the universal monoid, so Δ is the free strict monoidal category containing a monoid: a monoid in any strict monoidal `⟨B, □, e⟩` induces a unique strict monoidal functor `Δ → B`. See the nLab, [simplex category](https://ncatlab.org/nlab/show/simplex+category), and Wikipedia, [Simplex category](https://en.wikipedia.org/wiki/Simplex_category).

## Current state in the library

The category Δ itself is not yet built (tracked as #225): the library has only isolated ordinals-as-categories (`Instance/Omega.v`, `Instance/Two.v`) and categories of all posets/prosets with monotone maps (`Instance/Poset.v`), never the skeletal category of finite ordinals with monotone maps. Consequently the ordinal-sum monoidal structure, the universal monoid `⟨1, μ, η⟩`, the universal property (Proposition 1), and the four structural characterizations (Δ as a full subcategory of `Ord`, as a full subcategory of `Cat` via finite preorders, as the strict monoidal category of iterated multiplications, and as a subcategory of `Top`) are all absent. The target of the universal property — monoid objects in a strict monoidal category — *is* present (`Theory/Algebra/Monoid.v:44`, `Structure/Monoid.v:124`).

## Work to be done

Building on the category Δ of #225: (a) equip Δ with the strict monoidal structure of ordinal addition `+ : Δ ∏ Δ ⟶ Δ`, unit 0; (b) exhibit the universal monoid `⟨1, μ : 2 → 1, η : 0 → 1⟩`; (c) prove Proposition 1 — for a monoid in a strict monoidal `⟨B, □, e⟩` there is a unique strict monoidal functor `F : Δ → B` with `F1 = c`, `Fμ = μ'`, `Fη = η'`, so Δ's objects are the free monoid on 1 under `+`; (d) record the structural characterizations of Δ (full subcategory of `Cat` via finite preorders; the strict monoidal universal-monoid description; the `Ord` embedding). The `Top` characterization is handled by the geometric-realization issue. Suggested module: `Instance/Delta/Monoidal.v` (extending #225's Δ). In-tree donors: #225 (Δ), `Structure/Monoidal/Strict.v`, `Theory/Algebra/Monoid.v`, `Instance/Cat.v`.

## Definition of Done

- [ ] Ordinal-sum strict monoidal structure on Δ (unit 0) assembled.
- [ ] The universal monoid `⟨1, μ, η⟩` in Δ exhibited.
- [ ] Proposition 1: existence and uniqueness of the strict monoidal functor `Δ → B` induced by a monoid.
- [ ] The structural characterizations of Δ recorded (full subcategory of `Cat` via finite preorders; the strict-monoidal / `Ord` descriptions).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the universal property (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level construction).

## Verification

- `coqc -R . Category Instance/Delta/Monoidal.v` compiles cleanly.
- `Print Assumptions Delta_universal_monoid.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: Δ is the free strict monoidal category on a monoid via ordinal addition; statement matches Mac Lane §VII.5 Proposition 1.

## Dependencies

Depends on: #225

<!-- catalog: {"ids":["maclane:VII.5:construction1","maclane:VII.5:remark-protean","maclane:VII.5:prop1"],"deps":["#225"]} -->

---8<---

---
title: "MacLane VII.5: The arrow calculus of Δ — factorization, generators and relations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.5:construction2, maclane:VII.5:lem-normalform, maclane:VII.5:prop2, maclane:VII.5:ex1, maclane:VII.5:ex2, maclane:VII.5:ex3]
deps_item_ids: [maclane:VII.5:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.5 (book pp. 176-180, PDF pp. 184-188). Items `maclane:VII.5:construction2` (coface maps, epi-mono factorization), `maclane:VII.5:lem-normalform` (unique normal form), `maclane:VII.5:prop2` (generators and relations), `maclane:VII.5:ex1` (monic/epi = injective/surjective), `maclane:VII.5:ex2` (the monic subcategory Δ_mon), `maclane:VII.5:ex3` (the epi subcategory Δ_epi and universal semigroup).

## Background

Every monotone map factors uniquely as a surjection followed by an injection; the injective/surjective generators are the coface maps `δᵢ` and codegeneracy maps `σⱼ`, subject exactly to the (co)simplicial identities, giving each arrow of Δ a unique coface-then-codegeneracy normal form; monics are the injections and epis the surjections, presented by the cofaces (Δ_mon) and codegeneracies (Δ_epi, with `2 → 1` a universal semigroup). See the nLab, [simplex category](https://ncatlab.org/nlab/show/simplex+category).

## Current state in the library

Absent. With Δ itself not yet built (#225), there are no coface/codegeneracy operators, no epi-mono factorization of monotone maps, no simplicial identities, no normal form, and no generators-and-relations presentation. The abstract orthogonal factorization machinery (`Structure/Factorization.v`, `Regular/Factorization.v`, `Instance/Sets/Image.v`) factors morphisms in an arbitrary/regular category via an OFS but is not the specific surjective-monotone/injective-monotone factorization and has no Δ to act on. The `monic ⇔ injective` / `epi ⇔ surjective` characterization exists only for `Sets` (`Instance/Sets.v`), a different category. There is no semigroup-object notion (`Structure/Monoid.v` has monoid objects only; `Theory/Category/Semi.v` is `Semigroupoid`, unrelated).

## Work to be done

Over the simplicial category Δ (of #225, with the ordinal-sum structure of `maclane:VII.5:construction1`): (a) the epi-mono factorization of monotone maps and the coface `δᵢ`/codegeneracy `σⱼ` generators; (b) the (co)simplicial identities and the unique coface-then-codegeneracy normal form (the normal-form lemma); (c) the generators-and-relations presentation of Δ (Proposition 2); (d) `monic ⇔ injective`, `epi ⇔ surjective` in Δ; (e) the monic subcategory Δ_mon generated by the cofaces and the epi subcategory Δ_epi generated by the codegeneracies, including a `SemigroupObject` notion (associative `μ` without unit) and `2 → 1` as the universal semigroup in Δ_epi. Suggested module: `Instance/Delta/Arrows.v` (with `SemigroupObject` in `Structure/Semigroup.v`). In-tree donors: #225, `Instance/Delta/Monoidal.v`, `Structure/Factorization.v`, `Theory/Morphisms.v`.

## Definition of Done

- [ ] Epi-mono factorization and the `δᵢ`/`σⱼ` generators defined.
- [ ] (Co)simplicial identities and the unique normal-form representation proved.
- [ ] Generators-and-relations presentation of Δ (Proposition 2).
- [ ] `monic ⇔ injective`, `epi ⇔ surjective` in Δ.
- [ ] Δ_mon (cofaces) and Δ_epi (codegeneracies) presented; `SemigroupObject` and the universal semigroup `2 → 1` in Δ_epi.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the normal-form lemma and Proposition 2 (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Delta/Arrows.v` compiles cleanly.
- `Print Assumptions Delta_normal_form.` and `Print Assumptions Delta_presentation.` show closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the factorization, simplicial identities, normal form, presentation, and mono/epi subcategories match Mac Lane §VII.5 (Proposition 2, Exercises 1-3).

## Dependencies

Depends on: #225
Depends on: maclane:VII.5:construction1

<!-- catalog: {"ids":["maclane:VII.5:construction2","maclane:VII.5:lem-normalform","maclane:VII.5:prop2","maclane:VII.5:ex1","maclane:VII.5:ex2","maclane:VII.5:ex3"],"deps":["#225","maclane:VII.5:construction1"]} -->

---8<---

---
title: "MacLane VII.5: The geometric-realization functor Δ → Top"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.5:construction-geometric]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.5 (book p. 178, PDF p. 186). Item `maclane:VII.5:construction-geometric`.

## Background

There is a functor `Δ → Top` exhibiting Δ as a subcategory of `Top`: the ordinal 0 goes to the empty space and `n+1` to the standard affine `n`-simplex `{(t₀,…,tₙ) : tᵢ ≥ 0, Σtᵢ = 1}`, an arrow going to the affine map `sⱼ = Σ_{f i = j} tᵢ`, so the cofaces realize as the face inclusions. See the nLab, [geometric realization](https://ncatlab.org/nlab/show/geometric+realization).

## Current state in the library

Absent. There is no category `Top` of topological spaces in-tree (tracked as #259; `grep 'topological space|continuous map|open set'` → 0 hits), no affine-simplex functor, and Δ itself is not yet built (#225). `Structure/Coend.v:113` mentions geometric realization only as nLab-cited background prose.

## Work to be done

Once Δ (#225) and the category `Top` (#259) are available, define the geometric-realization functor `Δ → Top` sending `n+1` to the standard affine `n`-simplex (with barycentric coordinates) and each monotone map to the corresponding affine map, verify functoriality, and identify the images of the cofaces as the face inclusions; note Δ becomes a subcategory of `Top`. Suggested module: `Instance/Delta/Realization.v`. In-tree donors: #225 (Δ), #259 (`Top`), `Instance/Delta/Arrows.v` (cofaces).

## Definition of Done

- [ ] The affine-simplex functor `Δ → Top` defined; functoriality proved.
- [ ] Cofaces realized as face inclusions.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Delta/Realization.v` compiles cleanly.
- `Print Assumptions Delta_realization.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the functor sends `n+1` to the affine `n`-simplex and cofaces to face inclusions; statement matches Mac Lane §VII.5.

## Dependencies

Depends on: #225
Depends on: #259

<!-- catalog: {"ids":["maclane:VII.5:construction-geometric"],"deps":["#225","#259"]} -->

---8<---

---
title: "MacLane VII.5: Simplicial sets and simplicial objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.5:def-deltaplus, maclane:VII.5:def-simplicialset, maclane:VII.5:def-simplicialobject, maclane:VII.5:def-augmented, maclane:VII.5:ex4]
deps_item_ids: [maclane:VII.5:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.5 (book pp. 178-180, PDF pp. 186-188). Items `maclane:VII.5:def-deltaplus` (the subcategory Δ⁺), `maclane:VII.5:def-simplicialset` (simplicial set), `maclane:VII.5:def-simplicialobject` (simplicial object and its face/degeneracy description), `maclane:VII.5:def-augmented` (augmented simplicial object), `maclane:VII.5:ex4` (simplicial sets are small-complete).

## Background

A simplicial object in `X` is a functor `(Δ⁺)ᵒᵖ → X` (Δ⁺ the positive ordinals); equivalently a sequence `S₀, S₁, …` with faces `dᵢ` and degeneracies `sᵢ` satisfying the simplicial identities. A simplicial set is the case `X = Set`; an augmented simplicial object is a functor `Δᵒᵖ → X` (over the full Δ). The category of simplicial sets is small-complete. See the nLab, [simplicial set](https://ncatlab.org/nlab/show/simplicial+set).

## Current state in the library

Absent. With Δ not yet built (#225), the subcategory Δ⁺, the functor-category definitions of a simplicial set `(Δ⁺)ᵒᵖ → Set` and a simplicial object `(Δ⁺)ᵒᵖ → X`, the face/degeneracy presentation with the dual simplicial identities, and the augmented variant `Δᵒᵖ → X` are all absent. `Instance/FinSet.v:86` records only in prose that *presheaves on FinSet* are the augmented **symmetric** simplicial sets of Grandis — a different object (FinSet's arrows are arbitrary functions, not monotone). Small-completeness of a `Set`-valued functor category is not proved either (`Instance/Fun.v:101-105` is essay prose; `Structure/Complete.v:115` defines `Complete` but has no instance for `Sets` or any functor category).

## Work to be done

Building on Δ (of #225): (a) define Δ⁺ as the full subcategory of Δ on the positive ordinals; (b) define a simplicial set as `(Δ⁺)ᵒᵖ ⟶ Sets` and a simplicial object as `(Δ⁺)ᵒᵖ ⟶ X`, with morphisms natural transformations; (c) derive the equivalent face `dᵢ`/degeneracy `sᵢ` presentation and the dual simplicial identities; (d) define the augmented simplicial object `Δᵒᵖ ⟶ X` and the augmentation `ε : S₀ → S₋₁` with `ε d₀ = ε d₁`; (e) prove the category of simplicial sets is small-complete (via pointwise limits in a `Set`-valued functor category — this may need a general functor-category completeness lemma as a by-product). Suggested module: `Instance/Simplicial.v` (with the augmented variant and completeness in satellites). In-tree donors: #225, `Instance/Fun.v`, `Instance/Sets.v`, `Construction/Subcategory.v`, `Structure/Complete.v`.

## Definition of Done

- [ ] Δ⁺ defined; `SimplicialSet := (Δ⁺)ᵒᵖ ⟶ Sets` and `SimplicialObject X := (Δ⁺)ᵒᵖ ⟶ X` defined with morphisms.
- [ ] The face/degeneracy presentation and the dual simplicial identities derived.
- [ ] Augmented simplicial object `Δᵒᵖ ⟶ X` and the augmentation `ε` defined.
- [ ] Simplicial sets shown small-complete.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the completeness result (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (reusable development).

## Verification

- `coqc -R . Category Instance/Simplicial.v` compiles cleanly.
- `Print Assumptions SimplicialSet_Complete.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: a simplicial object is `(Δ⁺)ᵒᵖ ⟶ X` with the correct face/degeneracy identities; statement matches Mac Lane §VII.5 (Exercise 4 for completeness).

## Dependencies

Depends on: #225
Depends on: maclane:VII.5:construction1

<!-- catalog: {"ids":["maclane:VII.5:def-deltaplus","maclane:VII.5:def-simplicialset","maclane:VII.5:def-simplicialobject","maclane:VII.5:def-augmented","maclane:VII.5:ex4"],"deps":["#225","maclane:VII.5:construction1"]} -->

---8<---

---
title: "MacLane VII.5: Homology of a simplicial object and singular homology"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.5:construction-homology, maclane:VII.5:construction-singular]
deps_item_ids: [maclane:VII.5:def-simplicialobject, maclane:VII.5:construction-geometric]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.5 (book pp. 179-180, PDF pp. 187-188). Items `maclane:VII.5:construction-homology` (homology of a simplicial object in an abelian category), `maclane:VII.5:construction-singular` (singular chain complex and singular homology of a space).

## Background

For a simplicial object `S` in an abelian category, the alternating sums `d = Σ (−1)ⁱ dᵢ` give a boundary with `dd = 0`, making a chain complex whose homology is `Hₙ(S)`; an augmentation augments the complex. The singular chain complex of a space `X` arises by applying the free-abelian-group functor to the singular simplicial set `hom(Δ_•, X)`, and its homology is the singular homology of `X`. See the nLab, [Moore complex](https://ncatlab.org/nlab/show/Moore+complex), and Wikipedia, [Singular homology](https://en.wikipedia.org/wiki/Singular_homology).

## Current state in the library

Absent. There is no chain-complex object, no boundary differential, and no homology functor: `grep 'ChainComplex|homology|boundary'` finds only background-essay prose (`Structure/Abelian.v:70/75/100`), and `Construction/Chain.v` is the ω-chain `Omega ⟶ C` for initial algebras (unrelated). The abelian-category base *is* present (`Structure/Abelian.v` with kernels, cokernels, images, the (Epi,Mono) factorization) — exactly Mac Lane's setting — but nothing homological is built on it. Simplicial objects (item `maclane:VII.5:def-simplicialobject`) are absent, and singular homology additionally needs `Top` (#259), the singular simplicial set (the geometric-realization functor, item `maclane:VII.5:construction-geometric`), and the free-abelian-group functor to `Ab` (#256).

## Work to be done

(a) Define a chain complex in an abelian category and the homology functor `Hₙ = ker/im`; over a simplicial object `S` (of `maclane:VII.5:def-simplicialobject`) build the alternating-sum boundary `d = Σ(−1)ⁱ dᵢ`, prove `dd = 0` from the simplicial identities, and define `Hₙ(S)`; handle the augmented case. (b) Construct the singular simplicial abelian group `S(X) = ℤ·hom(Δ_•, X)` (using `Top` #259, the singular simplicial set from the geometric-realization functor `maclane:VII.5:construction-geometric`, and the free-abelian-group functor to `Ab` #256), its singular chain complex, and singular homology. Suggested modules: `Structure/Homology.v` (chain complexes and homology of simplicial objects), `Instance/Singular.v` (singular homology). In-tree donors: `Structure/Abelian.v`, `Structure/Kernel.v`, `Instance/Simplicial.v`.

## Definition of Done

- [ ] Chain complex and homology functor in an abelian category defined.
- [ ] Alternating-sum boundary of a simplicial object, `dd ≈ 0`, and `Hₙ(S)` defined; augmented case handled.
- [ ] Singular chain complex `S(X)` and singular homology constructed.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `dd ≈ 0` and `Hₙ` (Instance-layer axioms per docs/AXIOMS.md documented for the singular construction).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level development).

## Verification

- `coqc -R . Category Structure/Homology.v` (and `Instance/Singular.v`) compile cleanly.
- `Print Assumptions simplicial_boundary_squared.` shows closed under the global context; `Print Assumptions singular_homology.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `d = Σ(−1)ⁱ dᵢ`, `dd ≈ 0`, and the singular complex `ℤ·hom(Δ_•,X)` match Mac Lane §VII.5.

## Dependencies

Depends on: maclane:VII.5:def-simplicialobject
Depends on: maclane:VII.5:construction-geometric
Depends on: #256
Depends on: #259

<!-- catalog: {"ids":["maclane:VII.5:construction-homology","maclane:VII.5:construction-singular"],"deps":["maclane:VII.5:def-simplicialobject","maclane:VII.5:construction-geometric","#256","#259"]} -->

---8<---

---
title: "MacLane VII.6: The simplicial bar construction and standard resolution of a comonad"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.6:remark-universal-comonoid, maclane:VII.6:construction-smpl, maclane:VII.6:construction-resolution]
deps_item_ids: [maclane:VII.5:prop1, maclane:VII.5:def-simplicialobject, maclane:VII.5:construction-homology]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.6 (book pp. 181, PDF p. 189). Items `maclane:VII.6:remark-universal-comonoid` (comonads as augmented simplicial objects), `maclane:VII.6:construction-smpl` (`Smp L`, the simplicial object of a comonad), `maclane:VII.6:construction-resolution` (the comonad bar-resolution chain complex).

## Background

By the dual of the universal property of Δ, `Δᵒᵖ` contains the universal comonoid, so a comonad `⟨L, ε, δ⟩` in a strict monoidal category determines a unique strict monoidal functor `Δᵒᵖ → B` — an augmented simplicial object `Smp L` with `n ↦ Lⁿ`, faces `Lⁱ ε Lⁿ⁻ⁱ` and degeneracies `Lⁱ δ Lⁿ⁻ⁱ⁻¹`; in an Ab-category the alternating sums give the standard resolution `L⁎ a`. See the nLab, [bar construction](https://ncatlab.org/nlab/show/bar+construction).

## Current state in the library

Absent. The comonad `⟨L, ε, δ⟩` is present (`Theory/Monad.v:144`, `Comonad/Core.v` with `extract`, `duplicate`, coassociativity), and "comonad = comonoid in the endofunctor category" is available by duality, but there is no universal comonoid, no `Δᵒᵖ`, no `Smp L`, no iterated-power faces/degeneracies, and no resolution chain complex. `Comonad/Coalgebra.v:105-107` honestly disclaims it ("None of this is formalized in this file; the pointers record where the notion earns its keep").

## Work to be done

Building on the universal property of Δ (dualized from `maclane:VII.5:prop1`), simplicial objects (`maclane:VII.5:def-simplicialobject`), and homology (`maclane:VII.5:construction-homology`): (a) exhibit the universal comonoid in `Δᵒᵖ` and, from a comonad in a strict monoidal `B`, the unique strict monoidal functor `Δᵒᵖ → B` (an augmented simplicial object); (b) construct `Smp L : Δᵒᵖ → [A,A]` with `n ↦ Lⁿ`, faces `dᵢ = Lⁱ ε Lⁿ⁻ⁱ`, degeneracies `sᵢ = Lⁱ δ Lⁿ⁻ⁱ⁻¹`; (c) in an Ab-category, form the alternating-sum resolution `L⁎ a : … → L³a → L²a → La` with augmentation `ε_a`. Suggested module: `Comonad/Bar.v`. In-tree donors: `Comonad/Core.v`, `Instance/Delta/Monoidal.v`, `Instance/Simplicial.v`, `Structure/Homology.v`, `Structure/Monoidal/Compose.v` (the endofunctor strict monoidal category).

## Definition of Done

- [ ] The universal comonoid in `Δᵒᵖ` and the induced augmented simplicial object from a comonad.
- [ ] `Smp L` with faces `Lⁱ ε Lⁿ⁻ⁱ` and degeneracies `Lⁱ δ Lⁿ⁻ⁱ⁻¹`; simplicial identities verified.
- [ ] The standard resolution `L⁎ a` in an Ab-category with augmentation.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `Smp L` and the resolution.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level construction).

## Verification

- `coqc -R . Category Comonad/Bar.v` compiles cleanly.
- `Print Assumptions Smp.` and `Print Assumptions comonad_resolution.` show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `Smp L` has `n ↦ Lⁿ` with the stated faces/degeneracies and the resolution is the alternating-sum complex; statement matches Mac Lane §VII.6.

## Dependencies

Depends on: maclane:VII.5:prop1
Depends on: maclane:VII.5:def-simplicialobject
Depends on: maclane:VII.5:construction-homology

<!-- catalog: {"ids":["maclane:VII.6:remark-universal-comonoid","maclane:VII.6:construction-smpl","maclane:VII.6:construction-resolution"],"deps":["maclane:VII.5:prop1","maclane:VII.5:def-simplicialobject","maclane:VII.5:construction-homology"]} -->

---8<---

---
title: "MacLane VII.6: The monoid-ring functor and the group ring"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.6:construction-monoidring]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.6 (book p. 182, PDF p. 190). Item `maclane:VII.6:construction-monoidring`.

## Background

The forgetful functor `U : Rng → Mon` (forget addition) has a left adjoint `ℤ : Mon → Rng` sending a monoid `M` to its monoid ring `ℤM` (additive group the free abelian group on `M`, multiplication the bilinear extension of the product); for a group `Π`, `ℤΠ` is the group ring. See the nLab, [group algebra](https://ncatlab.org/nlab/show/group+algebra), and Wikipedia, [Group ring](https://en.wikipedia.org/wiki/Group_ring).

## Current state in the library

Absent. There is no category of rings (tracked as #257; `grep '\bRng\b|category of rings'` → only comments) and no monoid-ring/group-ring functor. A category of monoids `Mon` (internal monoid objects) *does* exist (`Theory/Algebra/Monoid/Hom.v:83`), so the domain is nameable, but the codomain `Rng` and the adjoint `ℤ` are entirely absent.

## Work to be done

Once the category of rings `Rng` (#257) is available, construct the monoid-ring functor `ℤ : Mon → Rng` and the adjunction `ℤ ⊣ U` (with `U : Rng → Mon` forgetting addition): `ℤM` has additive group the free abelian group on `M` and multiplication the bilinear extension of `M`'s product; unit and counit as in the book; specialize to the group ring `ℤΠ` for a group `Π`. Suggested module: `Instance/GroupRing.v`. In-tree donors: #257 (`Rng`), `Theory/Algebra/Monoid/Hom.v` (`Mon`), the free-abelian-group construction (#256), `Theory/Adjunction.v`.

## Definition of Done

- [ ] `ℤ : Mon → Rng` defined; the adjunction `ℤ ⊣ U` proved.
- [ ] The group ring `ℤΠ` recovered as the specialization to a group.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the adjunction (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/GroupRing.v` compiles cleanly.
- `Print Assumptions MonoidRing_Adjunction.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `ℤ` is left adjoint to the addition-forgetting functor and `ℤΠ` is the group ring; statement matches Mac Lane §VII.6.

## Dependencies

Depends on: #257

<!-- catalog: {"ids":["maclane:VII.6:construction-monoidring"],"deps":["#257"]} -->

---8<---

---
title: "MacLane VII.6: Group (co)homology via the bar resolution"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.6:construction-freemodule, maclane:VII.6:construction-barresolution, maclane:VII.6:construction-groupcohomology, maclane:VII.6:remark-grouphomology]
deps_item_ids: [maclane:VII.6:construction-monoidring, maclane:VII.6:construction-smpl, maclane:VII.5:construction-homology]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.6 (book pp. 182-183, PDF pp. 190-191). Items `maclane:VII.6:construction-freemodule` (free Π-module functor), `maclane:VII.6:construction-barresolution` (bar resolution of the trivial module), `maclane:VII.6:construction-groupcohomology` (group cohomology `Hⁿ(Π,A)`), `maclane:VII.6:remark-grouphomology` (group homology `Hₙ(Π,C)`).

## Background

The forgetful functor `Π-Mod → Ab` has a left adjoint `ℤΠ ⊗ −`, giving a comonad whose bar construction on the trivial module `ℤ` is the standard free resolution `ℤ ← ℤΠ ← ℤΠ⁽²⁾ ← ⋯` (bar symbols `[x₁|⋯|xₙ]`); applying `hom_Π(−,A)` gives group cohomology `Hⁿ(Π,A)` and applying `C ⊗_Π −` gives group homology `Hₙ(Π,C)`, with `H₁(Π,ℤ) = Π/[Π,Π]`. See the nLab, [group cohomology](https://ncatlab.org/nlab/show/group+cohomology), and Wikipedia, [Group cohomology](https://en.wikipedia.org/wiki/Group_cohomology).

## Current state in the library

Absent. There is no module category (tracked as #258; `R-Mod`/`Π-Mod` appear only in Morita essay prose), no free/induced-module functor, and no group (co)homology (`Hⁿ` appears only in `Structure/Group.v:53` prose). The prerequisites — the group ring (item `maclane:VII.6:construction-monoidring`), the comonad bar construction (item `maclane:VII.6:construction-smpl`), and homology of a complex (item `maclane:VII.5:construction-homology`) — are themselves not yet formalized. The abelian-category base (`Structure/Abelian.v`) is available.

## Work to be done

Building on the group ring (`maclane:VII.6:construction-monoidring`), the comonad bar construction (`maclane:VII.6:construction-smpl`), homology (`maclane:VII.5:construction-homology`), and the module category (#258): (a) the free Π-module functor `ℤΠ ⊗ − : Ab → Π-Mod` left adjoint to the forgetful, with unit/counit; (b) the resulting comonad's bar construction on the trivial module `ℤ`, i.e. the standard free resolution `ℤ ← ℤΠ ← ℤΠ⁽²⁾ ← ⋯` with the explicit bar faces/degeneracies; (c) group cohomology `Hⁿ(Π,A) = Hⁿ(hom_Π(bar, A))` with the `H⁰`/`H¹`/`H²` identifications where feasible; (d) group homology `Hₙ(Π,C) = Hₙ(C ⊗_Π bar)` with `H₁(Π,ℤ) = Π/[Π,Π]`. Suggested modules: `Instance/GroupCohomology.v` (with the free module and bar resolution in satellites). In-tree donors: #258, `Comonad/Bar.v`, `Structure/Homology.v`, `Structure/Abelian.v`.

## Definition of Done

- [ ] Free Π-module functor `ℤΠ ⊗ −` and its adjunction to `Ab`.
- [ ] The bar resolution of the trivial module `ℤ` with explicit faces/degeneracies.
- [ ] Group cohomology `Hⁿ(Π,A)` (with `H⁰`/`H¹`/`H²` identifications as feasible) and group homology `Hₙ(Π,C)` (with `H₁(Π,ℤ) = Π/[Π,Π]`).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level development).

## Verification

- `coqc -R . Category Instance/GroupCohomology.v` compiles cleanly.
- `Print Assumptions group_cohomology.` and `Print Assumptions group_homology.` show closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the bar resolution and `Hⁿ(Π,A)`/`Hₙ(Π,C)` (incl. `H₁(Π,ℤ) = Π/[Π,Π]`) match Mac Lane §VII.6.

## Dependencies

Depends on: maclane:VII.6:construction-monoidring
Depends on: maclane:VII.6:construction-smpl
Depends on: maclane:VII.5:construction-homology
Depends on: #258

<!-- catalog: {"ids":["maclane:VII.6:construction-freemodule","maclane:VII.6:construction-barresolution","maclane:VII.6:construction-groupcohomology","maclane:VII.6:remark-grouphomology"],"deps":["maclane:VII.6:construction-monoidring","maclane:VII.6:construction-smpl","maclane:VII.5:construction-homology","#258"]} -->

---8<---

---
title: "MacLane VII.7: Coherence for symmetric monoidal categories, and product/coproduct as symmetric tensor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.7:remark-symmetric]
deps_item_ids: [maclane:VII.1:construction1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.7 (book p. 184, PDF p. 192). Item `maclane:VII.7:remark-symmetric`.

## Background

Two claims: (a) the symmetry axioms suffice to prove a coherence theorem — every diagram built from `α`, `λ`, `ρ`, `γ` commutes provided both sides induce the same permutation of factors; (b) any monoidal category whose tensor is the categorical product or coproduct is automatically symmetric, `γ` the canonical iso over the projections. See the nLab, [symmetric monoidal category](https://ncatlab.org/nlab/show/symmetric+monoidal+category).

## Current state in the library

Partial. Claim (b) is realized for products: `CC_SymmetricMonoidal` at `Structure/Monoidal/Internal/Product.v:314` makes every Cartesian+Terminal category symmetric monoidal via `braid := swap`. But the coproduct case is *not* instantiated (no coproduct-tensor symmetric instance exists — related to the missing cocartesian monoidal structure, item `maclane:VII.1:construction1`). Claim (a) — the symmetric coherence theorem — is absent: only isolated consequences exist (`bimap_braid`, `braid_bimap_braid` in `Structure/Monoidal/Symmetric.v`; `Yang_Baxter_equation` in `Braided.v`), and `Theory/Lawvere/PROP.v:131`'s `Lawvere_Symmetric_monoidal_coherence` is merely an `eq_refl` sanity check.

## Work to be done

(a) Prove the coherence theorem for symmetric monoidal categories: any two parallel canonical maps built from `α`, `λ`, `ρ`, `γ` that realize the same permutation of tensor factors are equal (over the free symmetric monoidal category / a permutation-indexed canonical-map assignment). (b) Instantiate the coproduct case: using the general cocartesian monoidal structure (item `maclane:VII.1:construction1`), assemble the `CocartesianSymmetricMonoidal` instance with `γ` the canonical coproduct iso. Suggested modules: `Structure/Monoidal/Symmetric/Coherence.v` (the theorem), `Structure/Monoidal/Cocartesian.v` (extend with the symmetric instance). In-tree donors: `Structure/Monoidal/Symmetric.v`, `Structure/Monoidal/Braided.v`, `Structure/Monoidal/Internal/Product.v` (`CC_SymmetricMonoidal` as the dual template), the free-monoidal/coherence development of §VII.2.

## Definition of Done

- [ ] The symmetric coherence theorem (same-permutation canonical maps agree) proved.
- [ ] `CocartesianSymmetricMonoidal` assembled with `γ` the canonical coproduct iso.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the coherence theorem and the cocartesian symmetric instance.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Structure/Monoidal/Symmetric/Coherence.v` compiles cleanly.
- `Print Assumptions symmetric_monoidal_coherence.` and `Print Assumptions Cocartesian_SymmetricMonoidal.` show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: coherence is the general same-permutation statement (not the `eq_refl` sanity check), and both product and coproduct tensors are shown symmetric; statement matches Mac Lane §VII.7.

## Dependencies

Depends on: maclane:VII.1:construction1

<!-- catalog: {"ids":["maclane:VII.7:remark-symmetric"],"deps":["maclane:VII.1:construction1"]} -->

---8<---

---
title: "MacLane VII.8: The compact-open function space and the local-compactness exponential law"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.8:construction-compactopen]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.8 (book p. 185, PDF p. 193). Item `maclane:VII.8:construction-compactopen`.

## Background

The function space `Top(Y,Z)` carries the compact-open topology (subbasis `N(C,U) = {h : hC ⊆ U}` for `C` compact, `U` open); the exponential adjunction `Top(X × Y, Z) ≅ Top(X, Cop(Y,Z))` then holds when `Y` is locally compact Hausdorff. See the nLab, [exponential law for spaces](https://ncatlab.org/nlab/show/exponential+law+for+spaces).

## Current state in the library

Absent. There is no category `Top` of topological spaces in-tree (tracked as #259; `grep 'topological space|continuous map|open set'` → 0 hits), hence no compact-open function-space topology and no local-compactness exponential law. The abstract CCC hom-adjunction `Hom(X × Y, Z) ≅ Hom(X, Zʸ)` exists for cartesian closed categories but there is no `Top` to instantiate it.

## Work to be done

Once `Top` (#259) is available, topologize `Top(Y,Z)` with the compact-open topology (subbasis `N(C,U)`) as `Cop(Y,Z)`, and prove the exponential adjunction `Top(X × Y, Z) ≅ Top(X, Cop(Y,Z))` restricts to a homeomorphism when `Y` is locally compact Hausdorff (with the transpose `f ↦ f#`, `(f# x) y = f(x,y)`). Suggested module: `Instance/Top/CompactOpen.v`. In-tree donors: #259 (`Top`), `Structure/Cartesian/Closed.v` (the abstract exponential law as a template).

## Definition of Done

- [ ] The compact-open topology `Cop(Y,Z)` defined.
- [ ] The exponential adjunction `Top(X × Y, Z) ≅ Top(X, Cop(Y,Z))` for locally compact Hausdorff `Y`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Top/CompactOpen.v` compiles cleanly.
- `Print Assumptions compact_open_exponential.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the topology is the compact-open one and the adjunction restricts under local compactness; statement matches Mac Lane §VII.8.

## Dependencies

Depends on: #259

<!-- catalog: {"ids":["maclane:VII.8:construction-compactopen"],"deps":["#259"]} -->

---8<---

---
title: "MacLane VII.8: Compactly generated Hausdorff spaces and the Kelleyfication coreflection"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.8:def-compactlygenerated, maclane:VII.8:construction-kelleyfication, maclane:VII.8:prop1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.8 (book pp. 185-186, PDF pp. 193-194). Items `maclane:VII.8:def-compactlygenerated` (compactly generated space and CGHaus), `maclane:VII.8:construction-kelleyfication` (the Kelleyfication functor `K`), `maclane:VII.8:prop1` (Proposition 1: CGHaus is coreflective in Haus).

## Background

A space is compactly generated when a subset is closed iff it meets each compact subset in a relatively closed set; CGHaus (compactly generated Hausdorff / Kelley spaces) is a full coreflective subcategory of Haus, the coreflection given by the Kelleyfication functor `K` (retopologize with the compact-closure test) whose counit `KY → Y` is universal. See the nLab, [compactly generated topological space](https://ncatlab.org/nlab/show/compactly+generated+topological+space), and Wikipedia, [Compactly generated space](https://en.wikipedia.org/wiki/Compactly_generated_space).

## Current state in the library

Absent. There is no category `Top`/`Haus` (tracked as #259) and no CGHaus (`grep 'CGHaus|kelley|compactly.generated'` → 0 hits), so the compactly generated spaces, the Kelleyfication functor `K`, and the coreflection are all absent. The abstract coreflective-subcategory vocabulary *is* present (`Construction/Reflective.v:85`, `Coreflective S := Reflective (op_subcategory S)`) but is ambient scaffolding only, not applied to any topological category.

## Work to be done

Once `Top`/`Haus` (#259) is available: (a) define a compactly generated space (closed ⇔ relatively closed against every compact subset) and the full subcategory `CGHaus`; (b) construct the Kelleyfication functor `K : Haus → CGHaus` (same points, finer topology by the compact-closure test) with the continuous universal counit `εᵧ : KY → Y`; (c) prove Proposition 1 — `CGHaus` is a full coreflective subcategory of `Haus`, `K` right adjoint to the inclusion — using the existing `Coreflective` vocabulary. Suggested module: `Instance/CGHaus.v`. In-tree donors: #259 (`Top`/`Haus`), `Construction/Reflective.v` (`Coreflective`), `Construction/Subcategory.v`.

## Definition of Done

- [ ] Compactly generated space and the category `CGHaus` defined.
- [ ] The Kelleyfication functor `K : Haus → CGHaus` with universal counit `εᵧ : KY → Y`.
- [ ] Proposition 1: `CGHaus` full coreflective in `Haus`, `K` right adjoint to the inclusion.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the coreflection (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (reusable development).

## Verification

- `coqc -R . Category Instance/CGHaus.v` compiles cleanly.
- `Print Assumptions CGHaus_coreflective.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `K` is right adjoint to the inclusion with the stated counit; statement matches Mac Lane §VII.8 Proposition 1.

## Dependencies

Depends on: #259

<!-- catalog: {"ids":["maclane:VII.8:def-compactlygenerated","maclane:VII.8:construction-kelleyfication","maclane:VII.8:prop1"],"deps":["#259"]} -->

---8<---

---
title: "MacLane VII.8: CGHaus is complete and cocomplete"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.8:prop2]
deps_item_ids: [maclane:VII.8:def-compactlygenerated]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.8, Proposition 2 (book pp. 186-187, PDF pp. 194-195). Item `maclane:VII.8:prop2`.

## Background

CGHaus is small-complete and cocomplete: limits come from Haus via the right adjoint `K` (in particular the product is the Kelleyfied product `X □ Y = K(X × Y)`), and colimits (coproducts, coequalizers) formed in Haus already lie in CGHaus. See the nLab, [compactly generated topological space](https://ncatlab.org/nlab/show/compactly+generated+topological+space).

## Current state in the library

Absent, pending CGHaus. The category CGHaus (item `maclane:VII.8:def-compactlygenerated`) does not exist, so there is no completeness/cocompleteness statement about it. Abstract (co)completeness vocabulary (`Structure/Complete.v`, `Structure/Limit.v`, `Structure/Cocartesian.v`, `Structure/Coequalizer.v`) and the fact that right adjoints preserve limits (`Adjunction/Continuity.v`, RAPL) are available but not applied to any topological category.

## Work to be done

Building on CGHaus and the Kelleyfication `K` (item `maclane:VII.8:def-compactlygenerated`): prove CGHaus is small-complete (limits transported from Haus by the right adjoint `K`; the product `X □ Y = K(X × Y)`) and cocomplete (coproducts and coequalizers formed in Haus already lie in CGHaus, via the counit being monic and iso onto the Haus coequalizer). Suggested module: `Instance/CGHaus/Limits.v`. In-tree donors: `Instance/CGHaus.v`, `Adjunction/Continuity.v` (RAPL), `Structure/Complete.v`, `Structure/Coequalizer.v`.

## Definition of Done

- [ ] CGHaus small-complete, with `X □ Y = K(X × Y)`.
- [ ] CGHaus cocomplete (coproducts and coequalizers in CGHaus).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/CGHaus/Limits.v` compiles cleanly.
- `Print Assumptions CGHaus_Complete.` and `Print Assumptions CGHaus_Cocomplete.` show closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the product is `K(X × Y)` and colimits are formed in Haus; statement matches Mac Lane §VII.8 Proposition 2.

## Dependencies

Depends on: maclane:VII.8:def-compactlygenerated

<!-- catalog: {"ids":["maclane:VII.8:prop2"],"deps":["maclane:VII.8:def-compactlygenerated"]} -->

---8<---

---
title: "MacLane VII.8: CGHaus is cartesian closed"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.8:thm3]
deps_item_ids: [maclane:VII.8:def-compactlygenerated, maclane:VII.8:construction-compactopen, maclane:VII.8:prop2]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.8, Theorem 3 (book pp. 187-188, PDF pp. 195-196). Item `maclane:VII.8:thm3`.

## Background

CGHaus is cartesian closed: for compactly generated Hausdorff `X, Y` the exponential is `X^Y = K(Cop(Y,X))` (the Kelleyfied compact-open space), with evaluation `e : X^Y □ Y → X` universal, giving `CGHaus(Z □ Y, X) ≅ CGHaus(Z, X^Y)` and the exponential law `X^{Z □ Y} ≅ (X^Y)^Z` — Steenrod's convenient category. See the nLab, [convenient category of topological spaces](https://ncatlab.org/nlab/show/convenient+category+of+topological+spaces).

## Current state in the library

Absent. CGHaus (item `maclane:VII.8:def-compactlygenerated`), the compact-open function space (item `maclane:VII.8:construction-compactopen`), and its product structure (item `maclane:VII.8:prop2`) are not yet formalized. The abstract cartesian-closed notion (`Structure/Cartesian/Closed.v`) with concrete CCC instances Sets, Cat, FinSet exists, but the topological instance — CGHaus as a CCC — is not built.

## Work to be done

Building on CGHaus and its products (items `maclane:VII.8:def-compactlygenerated`, `maclane:VII.8:prop2`) and the compact-open function space (item `maclane:VII.8:construction-compactopen`): define the exponential `X^Y = K(Cop(Y,X))`, prove the evaluation `e : X^Y □ Y → X` is continuous and universal, establish `CGHaus(Z □ Y, X) ≅ CGHaus(Z, X^Y)`, and derive the exponential law `X^{Z □ Y} ≅ (X^Y)^Z`; assemble `@Closed CGHaus` (over `@Cartesian CGHaus`). Suggested module: `Instance/CGHaus/Closed.v`. In-tree donors: `Instance/CGHaus.v`, `Instance/CGHaus/Limits.v`, `Instance/Top/CompactOpen.v`, `Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] Exponential `X^Y = K(Cop(Y,X))` and continuous universal evaluation.
- [ ] `CGHaus(Z □ Y, X) ≅ CGHaus(Z, X^Y)` and the exponential law `X^{Z □ Y} ≅ (X^Y)^Z`.
- [ ] `@Closed CGHaus` assembled.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Instance/CGHaus/Closed.v` compiles cleanly.
- `Print Assumptions CGHaus_Closed.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `X^Y = K(Cop(Y,X))` with the stated adjunction and exponential law; statement matches Mac Lane §VII.8 Theorem 3.

## Dependencies

Depends on: maclane:VII.8:def-compactlygenerated
Depends on: maclane:VII.8:construction-compactopen
Depends on: maclane:VII.8:prop2

<!-- catalog: {"ids":["maclane:VII.8:thm3"],"deps":["maclane:VII.8:def-compactlygenerated","maclane:VII.8:construction-compactopen","maclane:VII.8:prop2"]} -->

---8<---

---
title: "MacLane VII.8: Further properties of compactly generated spaces (exercises)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.8:ex1, maclane:VII.8:ex2, maclane:VII.8:ex3, maclane:VII.8:ex4, maclane:VII.8:ex5]
deps_item_ids: [maclane:VII.8:def-compactlygenerated, maclane:VII.8:thm3]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.8, Exercises 1-5 (book p. 188, PDF p. 196). Items `maclane:VII.8:ex1` (KY as a colimit of compacta), `maclane:VII.8:ex2` (closed/open subsets are compactly generated), `maclane:VII.8:ex3` (the inclusion creates colimits), `maclane:VII.8:ex4` (box-product agrees with × for a locally compact factor), `maclane:VII.8:ex5` (alternative description of CGHaus).

## Background

Basic properties of compactly generated Hausdorff spaces: `KY` is the colimit in Haus of the compact subspaces ordered by inclusion; closed/open subspaces of a CG space are CG; the inclusion `CGHaus → Haus` creates colimits; `Z □ X = Z × X` when `Z` is locally compact Hausdorff; and CGHaus is equivalent to Hausdorff spaces with continuous-on-compacts maps. See the nLab, [compactly generated topological space](https://ncatlab.org/nlab/show/compactly+generated+topological+space).

## Current state in the library

Absent, pending CGHaus. These are point-set statements about CGHaus (item `maclane:VII.8:def-compactlygenerated`) and its closed structure (item `maclane:VII.8:thm3`), neither of which exists in-tree. Abstract colimits and creation-of-colimits vocabulary (`Structure/Limit.v`, `Theory/Equivalence/Limit.v`) and equivalence of categories (`Theory/Equivalence.v`) are available but have no topological instance.

## Work to be done

Building on CGHaus (item `maclane:VII.8:def-compactlygenerated`) and its cartesian closed structure (item `maclane:VII.8:thm3`): prove (1) `KY` is the colimit in Haus of the poset of compact subspaces; (2) closed and open subspaces of a CG space are CG; (3) the inclusion `CGHaus → Haus` creates colimits; (4) `Z □ X = Z × X` for locally compact Hausdorff `Z`; (5) CGHaus is equivalent to the category of Hausdorff spaces and continuous-on-compacts maps. Suggested module: `Instance/CGHaus/Properties.v`. In-tree donors: `Instance/CGHaus.v`, `Instance/CGHaus/Limits.v`, `Theory/Equivalence.v`, `Structure/Limit.v`.

## Definition of Done

- [ ] Exercises 1-5 each proved (colimit of compacta; subspace CG; inclusion creates colimits; box-product = product for locally compact; equivalence description).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/CGHaus/Properties.v` compiles cleanly.
- `Print Assumptions` on each exercise result shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the five properties match Mac Lane §VII.8 Exercises 1-5.

## Dependencies

Depends on: maclane:VII.8:def-compactlygenerated
Depends on: maclane:VII.8:thm3

<!-- catalog: {"ids":["maclane:VII.8:ex1","maclane:VII.8:ex2","maclane:VII.8:ex3","maclane:VII.8:ex4","maclane:VII.8:ex5"],"deps":["maclane:VII.8:def-compactlygenerated","maclane:VII.8:thm3"]} -->

---8<---

---
title: "MacLane VII.9: The category of pointed objects and the pointed function space"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.9:def-pointed]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.9 (book pp. 188-189, PDF pp. 196-197). Item `maclane:VII.9:def-pointed`.

## Background

`CGHaus_*` is the category of pointed compactly generated Hausdorff spaces (chosen basepoint, basepoint-preserving maps); the pointed function space `X^{(*)Y}` is the closed subspace of basepoint-preserving maps, itself compactly generated, and the exponential adjunction restricts to basepoint-preserving transposes. See the nLab, [pointed object](https://ncatlab.org/nlab/show/pointed+object).

## Current state in the library

Partial. The general category-of-pointed-objects construction is present: `Coslice` at `Construction/Slice.v:169`, documented (Slice.v:82) as capturing pointed sets = coslice under the terminal, and `Instance/Coq/Par.v` is a concrete category equivalent to `Set_*` with basepoint-preserving maps. Missing: (i) a topological base — no `Top`/`CGHaus` (tracked as #259), so pointed compactly generated *spaces* cannot be formed; (ii) the pointed function space / pointed internal hom `X^{(*)Y}`, not developed even at the `Set` level.

## Work to be done

(a) Package the general category of pointed objects `C_*` as the coslice under the terminal (using `Construction/Slice.v`'s `Coslice`), with the pointed function space / pointed internal hom `X^{(*)Y}` (basepoint-preserving maps, basepoint the constant map) defined at the level of a closed/pointed base; (b) once `Top`/`CGHaus` (#259) is available, instantiate `CGHaus_*` (pointed CG Hausdorff spaces) and its pointed function space, and show the exponential adjunction restricts to basepoint-preserving transposes. Suggested module: `Construction/Pointed.v` (with the CGHaus instance in `Instance/CGHaus/Pointed.v`). In-tree donors: `Construction/Slice.v` (`Coslice`), `Instance/Coq/Par.v` (`≅ Set_*`), #259 (`Top`/`CGHaus`).

## Definition of Done

- [ ] The general category of pointed objects `C_*` packaged (coslice under the terminal) with the pointed function space `X^{(*)Y}`.
- [ ] `CGHaus_*` instantiated (contingent on #259) with its pointed function space and the restricted exponential adjunction.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Construction/Pointed.v` compiles cleanly.
- `Print Assumptions Pointed.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: pointed objects are the coslice under the terminal and `X^{(*)Y}` is the basepoint-preserving function space; statement matches Mac Lane §VII.9.

## Dependencies

Depends on: #259

<!-- catalog: {"ids":["maclane:VII.9:def-pointed"],"deps":["#259"]} -->

---8<---

---
title: "MacLane VII.9: The smash product and the smash–hom adjunction on pointed spaces"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.9:def-smash, maclane:VII.9:ex2, maclane:VII.9:ex3]
deps_item_ids: [maclane:VII.9:def-pointed]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.9 (book pp. 189-190, PDF pp. 197-198). Items `maclane:VII.9:def-smash` (wedge, smash product, smash–hom adjunction), `maclane:VII.9:ex2` (smash makes CGHaus_* symmetric monoidal), `maclane:VII.9:ex3` (a functor in Top_* with no right adjoint).

## Background

In pointed spaces the wedge is `Z ∨ Y = (Z □ *) ∪ (* □ Y)` and the smash product `Z ∧ Y = (Z □ Y)/(Z ∨ Y)`; base-point-preserving maps out of `Z □ Y` are exactly those collapsing the wedge, giving `CGHaus_*(Z ∧ Y, X) ≅ CGHaus_*(Z, X^{(*)Y})`, so `− ∧ Y` is left adjoint to `(−)^{(*)Y}`; smash makes CGHaus_* symmetric monoidal (unit the two-point space), and a functor that fails to preserve coproducts has no right adjoint. See the nLab, [smash product](https://ncatlab.org/nlab/show/smash+product).

## Current state in the library

Absent. "smash" occurs only in comments; `Instance/Coq/ParE.v:174-181` explicitly disclaims it ("That tensor and its closure are not formalized here"). `Structure/Wedge.v` is the end/coend (dinatural) wedge, not the topological wedge sum; `Instance/Coq/Par.v:101-103` has the cartesian product of pointed sets, "NOT the smash product". The symmetric-monoidal framework exists (`Structure/Monoidal.v` + Symmetric layer) but no smash tensor instantiates it; the LAPC obstruction is available (`Adjunction/Continuity.v` `left_adjoint_preserves_colimits`) but no witnessing functor.

## Work to be done

Building on the pointed objects and pointed function space of §VII.9 (item `maclane:VII.9:def-pointed`): (a) define the wedge `Z ∨ Y`, the smash `Z ∧ Y = (Z □ Y)/(Z ∨ Y)`, and prove the smash–hom adjunction `CGHaus_*(Z ∧ Y, X) ≅ CGHaus_*(Z, X^{(*)Y})`; (b) assemble the symmetric monoidal (closed) structure on `CGHaus_*` with `∧` and the two-point unit (Exercise 2); (c) show that the cartesian-product functor `− × Y` on `Top_*` has no right adjoint, because it fails to preserve coproducts (the LAPC obstruction) — the point being that the cartesian `×`, unlike the smash `∧` of parts (a)/(b), is not the closed tensor on pointed spaces (Exercise 3, confirmed against PDF 198: the operator is `×`, not `∧`). Suggested module: `Structure/Monoidal/Smash.v` (with the LAPC witness in a satellite). In-tree donors: `Construction/Pointed.v`, `Structure/Monoidal/Symmetric.v`, `Adjunction/Continuity.v` (LAPC), #259.

## Definition of Done

- [ ] Wedge and smash defined; the smash–hom adjunction `− ∧ Y ⊣ (−)^{(*)Y}` proved.
- [ ] Symmetric monoidal (closed) structure on CGHaus_* via `∧` (Exercise 2).
- [ ] A functor in `Top_*` with no right adjoint, via LAPC and coproduct non-preservation (Exercise 3).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Structure/Monoidal/Smash.v` compiles cleanly.
- `Print Assumptions smash_hom_adjunction.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the smash is `(Z □ Y)/(Z ∨ Y)` with `− ∧ Y ⊣ (−)^{(*)Y}` and the symmetric monoidal structure; statement matches Mac Lane §VII.9 (Exercises 2-3).

## Dependencies

Depends on: maclane:VII.9:def-pointed

<!-- catalog: {"ids":["maclane:VII.9:def-smash","maclane:VII.9:ex2","maclane:VII.9:ex3"],"deps":["maclane:VII.9:def-pointed"]} -->

---8<---

---
title: "MacLane VII.9: Reduced suspension, loop space, and the Σ ⊣ Ω adjunction"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VII.9:def-suspension-loop, maclane:VII.9:ex4, maclane:VII.9:ex5]
deps_item_ids: [maclane:VII.9:def-smash]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.9 (book pp. 189-190, PDF pp. 197-198). Items `maclane:VII.9:def-suspension-loop` (reduced suspension, loop space, Σ ⊣ Ω), `maclane:VII.9:ex4` (loop space as a pullback of the path fibration), `maclane:VII.9:ex5` (counit of Σ ⊣ Ω).

## Background

With the circle `S¹ = I/{0,1}`, the reduced suspension `ΣX = X ∧ S¹` and loop space `ΩX = X^{(*)S¹}` are functors `CGHaus_* → CGHaus_*` with `Σ ⊣ Ω` (from the smash–hom adjunction); `ΩX` is the fibre of the path fibration `PX → X` (`PX = X^{(*)I}`, `f ↦ f(1)`), i.e. the pullback of `P → Id ← *`, and iterating gives `Σⁿ ⊣ Ωⁿ`. See the nLab, [loop space](https://ncatlab.org/nlab/show/loop+space).

## Current state in the library

Absent. There is no reduced suspension or loop-space functor, no circle `S¹`, and no unit interval `I` (`grep 'suspension|loop.space|circle|interval'` → only May-citation prose in `Theory/Multicategory.v`); the smash product they are defined from (item `maclane:VII.9:def-smash`) is itself not yet formalized. Pullbacks (`Structure/Pullback.v`) and adjunction counits (`Theory/Adjunction.v`) are available generically but there is no topological Σ ⊣ Ω to apply them to.

## Work to be done

Building on the smash product of §VII.9 (item `maclane:VII.9:def-smash`) and `Top`/`CGHaus` (#259): (a) define the circle `S¹ = I/{0,1}` (basepoint) and the functors `ΣX = X ∧ S¹`, `ΩX = X^{(*)S¹}`; (b) derive `Σ ⊣ Ω` from the smash–hom adjunction, and `Σⁿ ⊣ Ωⁿ` by iteration; (c) describe the counit of Σ ⊣ Ω (Exercise 5); (d) define the path space `PX = X^{(*)I}` with `π : P → Id`, `f ↦ f(1)`, and exhibit `ΩX` as the pullback of `P → Id ← *` (Exercise 4). Suggested module: `Instance/Top/Suspension.v`. In-tree donors: `Structure/Monoidal/Smash.v`, `Structure/Pullback.v`, `Theory/Adjunction.v`, #259.

## Definition of Done

- [ ] `S¹`, `ΣX = X ∧ S¹`, `ΩX = X^{(*)S¹}` defined; `Σ ⊣ Ω` (and `Σⁿ ⊣ Ωⁿ`) proved.
- [ ] The counit of Σ ⊣ Ω described (Exercise 5).
- [ ] Path space `PX`, `π : P → Id`, and `ΩX` as the pullback of `P → Id ← *` (Exercise 4).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Top/Suspension.v` compiles cleanly.
- `Print Assumptions Suspension_Loop_Adjunction.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `Σ = − ∧ S¹`, `Ω = (−)^{(*)S¹}`, `Σ ⊣ Ω`, and `ΩX` as the path-fibration pullback; statement matches Mac Lane §VII.9 (Exercises 4-5).

## Dependencies

Depends on: maclane:VII.9:def-smash

<!-- catalog: {"ids":["maclane:VII.9:def-suspension-loop","maclane:VII.9:ex4","maclane:VII.9:ex5"],"deps":["maclane:VII.9:def-smash"]} -->

---8<---

---
title: "MacLane VII.9: The left adjoint of the pointed-hom functor on pointed sets"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VII.9:ex1]
deps_item_ids: [maclane:VII.9:def-pointed]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VII.9, Exercise 1 (book p. 190, PDF p. 198). Item `maclane:VII.9:ex1`.

## Background

The functor `Set_*(S, −) : Set_* → Set_*` on pointed sets has a left adjoint — the pointed-set smash `− ∧ S` (copower/tensor of pointed sets) — giving a tensor–hom adjunction on `Set_*`. See the nLab, [pointed object](https://ncatlab.org/nlab/show/pointed+object) and [smash product](https://ncatlab.org/nlab/show/smash+product).

## Current state in the library

Absent. `Instance/Coq/Par.v` is a concrete category equivalent to `Set_*` (pointed sets, basepoint-preserving maps), and `Coslice` (`Construction/Slice.v:169`) makes `Set_* = 1/Sets` expressible, but neither the pointed-hom functor `Set_*(S, −)` nor its left adjoint (the pointed-set smash `− ∧ S`) is developed; `Par.v:222` mentions a product-based `Par_ClosedMonoidal`, not the smash.

## Work to be done

At the level of pointed sets (`Set_* ≅ Par`, or `Coslice 1 Sets`; see the pointed-objects packaging of item `maclane:VII.9:def-pointed`): define the pointed-hom functor `Set_*(S, −)` and its left adjoint, the pointed-set smash `− ∧ S`, and prove the adjunction `(− ∧ S) ⊣ Set_*(S, −)`. This is the `Set`-level, topology-free case of the smash–hom adjunction. Suggested module: `Instance/Pointed/Sets.v`. In-tree donors: `Instance/Coq/Par.v` (`≅ Set_*`), `Construction/Slice.v` (`Coslice`), `Construction/Pointed.v`.

## Definition of Done

- [ ] The pointed-hom functor `Set_*(S, −)` and the pointed-set smash `− ∧ S` defined.
- [ ] The adjunction `(− ∧ S) ⊣ Set_*(S, −)` proved.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (Instance-layer axioms per docs/AXIOMS.md documented).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.

## Verification

- `coqc -R . Category Instance/Pointed/Sets.v` compiles cleanly.
- `Print Assumptions pointed_set_smash_adjunction.` shows closed (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the left adjoint of `Set_*(S,−)` is the pointed-set smash `− ∧ S`; statement matches Mac Lane §VII.9 Exercise 1.

## Dependencies

Depends on: maclane:VII.9:def-pointed

<!-- catalog: {"ids":["maclane:VII.9:ex1"],"deps":["maclane:VII.9:def-pointed"]} -->

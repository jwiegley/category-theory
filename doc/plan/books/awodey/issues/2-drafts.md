---
title: "Awodey 2.1: Monomorphisms in Mon are exactly the injective homomorphisms"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.1:example3, awodey:2.3:example12]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed., Oxford University Press), §2.1 Example 2.3 (printed p. 32; PDF pp. 41–42) and §2.3 Example 2.12 (printed p. 40; PDF p. 49). Item IDs: `awodey:2.1:example3`, `awodey:2.3:example12`.

## Background

In a category of "structured sets" (monoids, groups, rings, vector spaces), a homomorphism is a [monomorphism](https://ncatlab.org/nlab/show/monomorphism) exactly when its underlying function is injective; Awodey proves the monoid case by probing elements with the [free monoid](https://ncatlab.org/nlab/show/free+monoid) on one generator, which represents the underlying-set functor (`|M| ≅ Hom_Mon(M(1), M)`). The representability of the forgetful functor is what turns "monic" into "injective".

## Current state in the library

There is no category **Mon** of ordinary monoids over `Sets`: `Instance/CMon.v` provides only commutative monoids, and `Theory/Algebra/Monoid/Hom.v` (line 83, `Mon(C)`) provides internal monoid *objects* in a monoidal category, neither of which characterizes its monos. A blind search (`grep -rniE 'Monic|Epic|inject' Instance/CMon.v Theory/Algebra/Monoid/Hom.v`) returns nothing establishing "monic ⟺ underlying-injective", and there is no free-monoid construction (`grep -rniE 'free monoid|FreeMonoid'` → 0 hits; `Theory/Coq/List.v` calls `list A` the underlying set of the free monoid in prose only). The only in-tree "monos are injective" result is `Instance/Sets.v:369` `injectivity_is_monic`, which is the plain `Sets` base case Awodey explicitly *contrasts* with Example 2.3. So both the enabling category and the free-object probe are missing.

## Work to be done

- Assemble a category **Mon** of monoids (setoid carrier, associative operation, unit) and monoid homomorphisms, with the forgetful functor `U : Mon ⟶ Sets`. Suggested path: `Instance/Mon.v`. In-tree donors: `Instance/CMon.v` (the commutative-monoid category is the exact template), `Instance/Comp.v` (signature/`Algebra`/`AlgHom` machinery), `Theory/Category.v`.
- Construct the free monoid `M(A)` on a setoid `A` (words/lists up to the setoid) with `U`-universal arrow, and specialize to the free monoid on one generator `M(1)`. Suggested path: `Instance/Mon/Free.v`; donor `Theory/Coq/List.v` (list concatenation monoid) and `Theory/Universal/Arrow.v`.
- Prove the representability `|M| ≅ Hom_Mon(M(1), M)`, natural in `M` (Example 2.12): the underlying-set functor is represented by `M(1)`.
- Derive that `h : M ⟶ N` is `Monic` in **Mon** iff `U h` is injective (Example 2.3), by probing with two homomorphisms out of `M(1)`.
- Optionally record the general pattern (a forgetful functor with a free left adjoint reflects and detects monos) so the group/ring/vector-space analogues are corollaries; the reflection direction may reuse `Theory/Adjunction.v:311` `adj_monic`.

## Definition of Done

- [ ] Statements are faithful to Awodey §2.1 Ex 2.3 and §2.3 Ex 2.12; all hom-level equalities use setoid `≈`, never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom` in the added code (core-theory zero-axiom discipline per `docs/AXIOMS.md`; any stdlib axiom used by the concrete layer is enumerated there).
- [ ] `Print Assumptions` is closed (or discloses only the documented `Instance/` stdlib axioms) for `Mon`, the free-monoid universal arrow, `|M| ≅ Hom_Mon(M(1), M)`, and the `Monic ⟺ injective` lemma.
- [ ] New modules registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the category **Mon** is treated as flagship-level.

## Verification

- `coqc -R . Category Instance/Mon.v` and `coqc -R . Category Instance/Mon/Free.v` compile clean.
- `Print Assumptions injective_iff_monic_Mon.` (and the representability lemma) shows no unexpected axioms.
- `nix build .#category-theory_9_1` (and an 8.20 target) succeeds.
- Reviewer confirms the statement matches Awodey Example 2.3 (monos = injective homomorphisms via `M(1)`) and Example 2.12 (`|M| ≅ Hom_Mon(M(1), M)`).

## Dependencies

Depends on: #296 (MacLane II.7 — the free monoid and its universal property; provides the monoid/free-monoid infrastructure this issue builds on). Related: the group/ring/vector-space cases of Example 2.3 additionally require categories the library does not yet have.

<!-- catalog: {"ids":["awodey:2.1:example3","awodey:2.3:example12"],"deps":["#296"]} -->

---8<---

---
title: "Awodey 2.1: The inclusion of the additive monoid of naturals into the integers is a non-surjective epimorphism"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.1:example5]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.1 Example 2.5 (printed p. 33; PDF pp. 42–43). Item ID: `awodey:2.1:example5`.

## Background

Outside `Set`, an [epimorphism](https://ncatlab.org/nlab/show/epimorphism) need not be surjective: the inclusion `(ℕ,+,0) ↪ (ℤ,+,0)` of the additive monoid of naturals into the integers is monic and epic in **Mon** yet not surjective — any two monoid homomorphisms out of `ℤ` that agree on `ℕ` are forced to agree on `−1`, hence everywhere. This is the standard counterexample to "epi = surjection" (compare the ring inclusion `ℤ → ℚ`).

## Current state in the library

No category **Mon** of monoids over `Sets` exists (`Instance/CMon.v` is commutative monoids; `Theory/Algebra/Monoid/Hom.v` is internal monoid objects), and neither `ℕ` nor `ℤ` is realized as a monoid object — a blind search (`grep -rniE 'integers|additive monoid|non-surjective epi'`) finds only header-essay mentions of "the additive monoid on ℕ" as motivation. `Instance/Ens.v` records that in `Ens` the epis are exactly the surjections (the opposite of the phenomenon this example illustrates). The takeaway "epimorphisms need not be surjective" is nowhere recorded as a lemma.

## Work to be done

- Over the category **Mon** (see the Awodey 2.1 monoid-category issue / #296), realize the additive monoids `(ℕ,+,0)` and `(ℤ,+,0)` and the inclusion homomorphism `ι : ℕ ⟶ ℤ`. Suggested path: `Instance/Mon/NatInt.v`; donors `Instance/Mon.v`, Coq's `nat`/`Z`.
- Prove `ι` is `Epic` in **Mon**: any `f, g : ℤ ⟶ M` with `f ∘ ι ≈ g ∘ ι` satisfy `f ≈ g` (drive the argument through `f(−1) ∘ f(1) ≈ unit`, forcing agreement on `−1`).
- Prove `ι` is *not* an epimorphism-that-is-surjective: exhibit that `U ι` misses `−1`, so `ι` is a non-surjective epi (and it is trivially monic).
- Record the conceptual corollary "in **Mon**, epimorphisms need not be surjective" as a short remark for downstream use (it is the contrast case in the Awodey 2.4 functor-preservation issue).

## Definition of Done

- [ ] Statement faithful to Awodey §2.1 Example 2.5; morphism equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond the documented `Instance/` stdlib axioms (`docs/AXIOMS.md`).
- [ ] `Print Assumptions` reported for the `Epic ι` lemma and the non-surjectivity witness.
- [ ] New module(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated only if judged flagship-level (not expected here).

## Verification

- `coqc -R . Category Instance/Mon/NatInt.v` compiles clean.
- `Print Assumptions nat_into_Z_epic.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statement matches Awodey Example 2.5 (`ℕ ↪ ℤ` monic + epic + non-surjective in **Mon**).

## Dependencies

Depends on: #296 (MacLane II.7 — the free monoid and its universal property; supplies the category of monoids in which `ℕ`, `ℤ` and `ι` live). Related: the Awodey 2.1 "monos in Mon are injective" issue (`awodey:2.1:example3`) shares the **Mon** infrastructure.

<!-- catalog: {"ids":["awodey:2.1:example5"],"deps":["#296"]} -->

---8<---

---
title: "Awodey 2.1: Sets is balanced — a monic epimorphism of sets is an isomorphism"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.1:remark-bimorphism-iso-sets]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.1 (printed p. 34; PDF p. 43), the unnumbered remark following Proposition 2.6. Item ID: `awodey:2.1:remark-bimorphism-iso-sets`.

## Background

A [balanced category](https://ncatlab.org/nlab/show/balanced+category) is one in which every morphism that is both monic and epic is already an isomorphism; Awodey observes that `Set` is balanced (the converse of "every iso is monic and epic"), while general categories are not. Establishing this for the library's `Sets` closes the last leg of the classical mono/epi/iso picture in the category of setoids.

## Current state in the library

Three of the four ingredients exist: `Instance/Sets.v:369` `injectivity_is_monic` (injective ⟺ `Monic`, full biconditional), `Instance/Sets.v:400` `bijective_is_iso` (injective + surjective → `IsIsomorphism`), and the forward half of `Instance/Sets.v:429` `surjectivity_is_epic`. The crucial bridge `Epic → surjective` is **missing**: `surjectivity_is_epic` ends in `Abort` at `Instance/Sets.v:476` (nothing enters the environment), because the reverse direction runs into the documented subobject-classifier size obstruction (the truth-value object lives one universe up; the cross-universe classifier is `Instance/Sets/Classifier.v`). Consequently `Monic f ∧ Epic f → IsIsomorphism f` cannot be assembled. `Theory/Morphisms.v:125` defines `Bimorphic := Epic f * Monic f` but no lemma concludes an isomorphism from it. (Searches for "balanced" hit only `BalancedMonoidal`, an unrelated notion.)

## Work to be done

- Complete `Epic h → (∀ b, ∃ a, h a ≈ b)` for `Sets`, i.e. finish the `surjectivity_is_epic` biconditional. Suggested route: use the cross-universe classifier / two-map probe already developed in `Instance/Sets/Classifier.v` (`PropSetoid`, `char_setoid`, `sets_char_*`), or the two-element / quotient-cokernel probe, resolving the size obstruction the current `Abort` records.
- Assemble `Sets_balanced : Monic h → Epic h → IsIsomorphism h` from `injectivity_is_monic` + the completed `epic → surjective` + `bijective_is_iso`. Suggested path: extend `Instance/Sets.v` (or a new `Instance/Sets/Balanced.v`).
- Phrase the result so it discharges `Bimorphic h → IsIsomorphism h` in `Sets`, giving a reusable "`Sets` is balanced" statement.

## Definition of Done

- [ ] Statement faithful to Awodey §2.1's balancedness remark; equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond the documented `Instance/` stdlib axioms; the previously-`Abort`ed `surjectivity_is_epic` reverse direction is genuinely proved (no new global axiom).
- [ ] `Print Assumptions surjectivity_is_epic.` and `Print Assumptions Sets_balanced.` reported (any classifier-level axioms disclosed against `docs/AXIOMS.md`).
- [ ] Registered in `_CoqProject` (already true for `Instance/Sets.v`; register any new file).
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits (the current `Abort` region is removed/closed).
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- `coqc -R . Category Instance/Sets.v` compiles clean with the completed lemma.
- `Print Assumptions Sets_balanced.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statement matches Awodey's remark (in `Set`, monic + epic ⇒ iso).

## Dependencies

Depends on: #245 (MacLane I.5 — epis in `Sets` are exactly the surjections; the missing `Epic → surjective` direction is precisely that issue's content, and balancedness is its immediate consequence). Related: the "fails in general" half of Awodey's remark is witnessed by the `ℕ ↪ ℤ` non-iso bimorphism (`awodey:2.1:example5`) and by the poset/Pos bimorphisms (`awodey:2.1:example4`, `awodey:2.3:example11`).

<!-- catalog: {"ids":["awodey:2.1:remark-bimorphism-iso-sets"],"deps":["#245"]} -->

---8<---

---
title: "Awodey 2.1: Every arrow in a poset is a bimorphism, and Pos is not balanced"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.1:example4, awodey:2.3:example11]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.1 Example 2.4 (printed p. 33; PDF p. 42) and §2.3 Example 2.11 (printed p. 39; PDF pp. 48–49). Item IDs: `awodey:2.1:example4`, `awodey:2.3:example11`.

## Background

In a [thin category](https://ncatlab.org/nlab/show/thin+category) (a poset or preorder viewed as a category) every hom-set has at most one arrow, so cancellation is automatic and every arrow is simultaneously monic and epic; this makes a poset the standard source of "bimorphisms" that are not isomorphisms, so **Pos** — unlike `Set` — is not balanced. Awodey sharpens this with a concrete order-preserving map that is monic and epic in **Pos** but not invertible, detected by the isomorphism invariant `|Hom(2, −)|`.

## Current state in the library

The enabling category is present but the facts are unstated. `Instance/Proset.v:33` builds a preorder as a thin category whose hom-setoid equivalence is `fun _ _ => True` (all parallel arrows equal), and `Theory/Morphisms.v` supplies `Monic`/`Epic`; so `Monic f` and `Epic f` hold by a one-line proof for every arrow, yet no lemma records it (`grep -rniE 'every arrow.*monic|thin.*monic|posetal.*monic'` → 0 hits). For Example 2.11, the reusable invariance principle *is* present — `Theory/Functor.v:227` `fobj_iso` shows every functor (in particular a representable `Hom(2, −)`) preserves isomorphisms, hence induces hom-set bijections — but there is no concrete pair of posets, no monic+epic-but-not-iso map in **Pos**, and no `|Hom(2, −)|` computation distinguishing them.

## Work to be done

- State and prove, over `Instance/Proset.v` (and `Instance/Poset.v`), that every arrow in a thin category is `Monic` and `Epic` (Example 2.4). Suggested path: add `proset_arrow_monic` / `proset_arrow_epic` to `Instance/Proset.v`.
- Build the two concrete posets of Example 2.11 (a 3-element chain `a ≤ b ≤ c`; and `x ≤ y`, `x ≤ z`) and the order-preserving bijection between them, and prove it is monic and epic in **Pos** but not an isomorphism. Suggested path: `Instance/Poset/Bimorphism.v`.
- Record the isomorphism invariant: `|Hom(2, −)|` is preserved under iso (immediate from `fobj_iso` specialized to the representable `Hom(2, −)`), and exhibit the differing counts (5 vs 6) as the obstruction to an isomorphism. The reusable "representables preserve isos" fact is already available; only the concrete counting/witness is new.

## Definition of Done

- [ ] Statements faithful to Awodey Examples 2.4 and 2.11; equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond documented `Instance/` stdlib axioms.
- [ ] `Print Assumptions` reported for `proset_arrow_monic`/`proset_arrow_epic` and the concrete non-iso bimorphism in **Pos**.
- [ ] New module(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level (not expected).

## Verification

- `coqc -R . Category Instance/Proset.v` and `coqc -R . Category Instance/Poset/Bimorphism.v` compile clean.
- `Print Assumptions pos_bimorphism_not_iso.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statements match Awodey Example 2.4 (poset arrows are bimorphisms) and Example 2.11 (a monic+epic non-iso map in **Pos**, separated by `|Hom(2, −)|`).

## Dependencies

None blocking. Related: #250 (MacLane I.5 — monic/epi cancellation and a non-invertible bimorphism) is the general home of "a bimorphism need not be an iso"; this issue supplies Awodey's poset/**Pos** instances and the general thin-category lemma. Contrast with the "`Sets` is balanced" issue (`awodey:2.1:remark-bimorphism-iso-sets`).

<!-- catalog: {"ids":["awodey:2.1:example4","awodey:2.3:example11"],"deps":[]} -->

---8<---

---
title: "Awodey 2.2: Initial and terminal objects in slice categories, coslices, and posets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.2:example9]
deps_item_ids: [awodey:2.2:def-boolean-algebra]
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.2 Example 2.9 (printed p. 36; PDF pp. 45–46). Item ID: `awodey:2.2:example9`.

## Background

Awodey's Example 2.9 tours [initial](https://ncatlab.org/nlab/show/initial+object) and terminal objects across categories; two of its cases are clean, reusable universal facts that the library still lacks — the identity `1_X` is terminal in the slice `C/X` and initial in the coslice `X/C`, and in a poset the least element is initial while the greatest is terminal. Both are instances of the general definitions already in the library.

## Current state in the library

Concrete witnesses exist for the easy cases but not for these two. Present: `Instance/Sets.v:248/265` (`Sets_Terminal` singleton, `Sets_Initial` empty setoid), `Instance/Zero.v:44` `Cat_Initial` with the point category terminal (`Instance/One.v`), and `Instance/CMon/Biproduct.v:161` `CMon_Zero` (the trivial commutative monoid is both). Missing: `Construction/Slice.v` carries **no** `Terminal`/`Initial` instance (`grep -rniE 'slice.*[Tt]erminal|coslice.*[Ii]nitial'` → 0 hits), and `Instance/Poset.v` mentions least = initial / greatest = terminal only in header prose (line 30), never as an instance. The Boolean-algebra case (`Bool`: the two-element algebra initial, the one-element terminal) has no category to live in, and the `Rings`/`Vect` cases need categories the library does not have.

## Work to be done

- Prove `1_X` is terminal in the slice `C/X` and, dually, initial in the coslice `X/C`. Suggested path: add `Slice_Terminal` and `Coslice_Initial` to `Construction/Slice.v`; donors `Construction/Slice.v:123/169` (`Slice`, `Coslice`), `Structure/Terminal.v`, `Structure/Initial.v`.
- Prove that a poset's least element is an `Initial` object and its greatest element a `Terminal` object of the thin category (turning the `Instance/Poset.v` prose into instances/lemmas, guarded by the hypothesis that such an element exists). Suggested path: `Instance/Poset.v`.
- Instantiate the `Bool` case (two-element Boolean algebra initial, one-element terminal) once the category **Bool** exists; this leg depends on the Awodey 2.2 Boolean-algebra issue.
- Note (do not attempt here) that the `Rings` (`ℤ` initial, zero ring terminal) and `Groups`/`Vect` cases require categories the library does not yet provide.

## Definition of Done

- [ ] Statements faithful to Awodey Example 2.9 (items 4–6); equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond documented `Instance/` stdlib axioms.
- [ ] `Print Assumptions` reported for `Slice_Terminal`, `Coslice_Initial`, and the poset least/greatest lemmas.
- [ ] New/edited modules registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level (not expected).

## Verification

- `coqc -R . Category Construction/Slice.v` and `coqc -R . Category Instance/Poset.v` compile clean.
- `Print Assumptions Slice_Terminal.` (and `Coslice_Initial`) shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statements match Awodey Example 2.9 items 5 (poset least/greatest) and 6 (`1_X` terminal in `C/X`, initial in `X/C`).

## Dependencies

Depends on: awodey:2.2:def-boolean-algebra (the `Bool` witness needs the category of Boolean algebras). The uniqueness-up-to-iso half of Awodey's initial/terminal discussion is handled separately (Proposition 2.8 → #247).

<!-- catalog: {"ids":["awodey:2.2:example9"],"deps":["awodey:2.2:def-boolean-algebra"]} -->

---8<---

---
title: "Awodey 2.2: Boolean algebras and the category Bool"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.2:def-boolean-algebra]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.2 Example 2.9(4) (printed p. 36; PDF p. 45), the running-prose definition of a Boolean algebra and the category **Bool**. Item ID: `awodey:2.2:def-boolean-algebra`.

## Background

A [Boolean algebra](https://ncatlab.org/nlab/show/Boolean+algebra) is a poset with `0`, `1`, join, meet and a complement satisfying the usual laws (equivalently a [complemented distributive lattice](https://en.wikipedia.org/wiki/Boolean_algebra_(structure))); the motivating example is the powerset `P(X)` under inclusion, and the two-element algebra `2 = {0,1}` is the object of truth values. The category **Bool** has Boolean algebras as objects and structure-preserving (Boolean) homomorphisms as arrows.

## Current state in the library

There is no Boolean-algebra structure and no lattice/Heyting-algebra class anywhere: `grep -rniE 'Class.*Lattice|BooleanAlgebra|HeytingAlgebra'` → 0 hits, and `find` for `*lattice*`/`*boolean*` sources → none. Every occurrence of "Boolean" is header-essay prose (`Theory/Lawvere.v`, `Theory/Equivalence.v` Stone-duality remark, `Structure/Topos.v`), Coq's `bool` used for programming, or `Instance/Comp.v:405` `Definition Bool : Group` (the two-element *group* under xor — not a Boolean algebra and not the category **Bool**). The meet/join = product/coproduct-in-a-poset dictionary appears in `Instance/Poset.v` prose but no algebra object with `0,1,∨,∧,¬` is defined. The library is universe-polymorphic, so this is a genuine content gap, fully formalizable, not out of scope.

## Work to be done

- Define a `BooleanAlgebra` structure: a carrier with order (or the equational presentation), `0`, `1`, `∨`, `∧`, `¬`, and the laws Awodey lists (bounds, the join/meet universal inequalities, `a ≤ ¬b ⟺ a ∧ b = 0`, `¬¬a = a`). Suggested path: `Structure/BooleanAlgebra.v`. Donors: `Instance/Poset.v`/`Instance/Proset.v` (order-as-thin-category), `Instance/Props.v` (propositions under implication are a Boolean-algebra-like example), the product-in-a-poset = meet dictionary.
- Define a Boolean homomorphism (preserving `0,1,∨,∧`, hence `¬`) and assemble the category **Bool**. Suggested path: `Instance/Bool.v`.
- Provide the two running examples: the powerset algebra `P(X)` (bottom `∅`, top `X`, join/meet = union/intersection, `¬A = X∖A`) and the two-element algebra `2`.
- Optionally connect to the in-tree order machinery so a single Boolean algebra is recovered as a thin (cartesian/cocartesian) category.

## Definition of Done

- [ ] Structure and category faithful to Awodey §2.2; any hom equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond documented `Instance/` stdlib axioms.
- [ ] `Print Assumptions` reported for `BooleanAlgebra`, `Bool`, the powerset example, and `2`.
- [ ] New modules registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (a Boolean-algebra structure and **Bool** are flagship-level for the order/logic side of the library).

## Verification

- `coqc -R . Category Structure/BooleanAlgebra.v` and `coqc -R . Category Instance/Bool.v` compile clean.
- `Print Assumptions Bool.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the structure and category match Awodey §2.2's definition (laws, powerset example, `2`).

## Dependencies

None blocking. Related: #389 (MacLane IV.6 — powerset lattices and Boolean algebras are cartesian closed) treats an *individual* Boolean algebra as a cartesian closed thin category; if that issue introduces a reusable Boolean/lattice structure, build **Bool** over it. #639 (MacLane App.1 — a two-valued subobject classifier is a Boolean algebra) is a distinct (topos-internal) result. This issue unblocks the Awodey 2.3 ultrafilter issue and the `Bool` leg of the Awodey 2.2 initial/terminal issue.

<!-- catalog: {"ids":["awodey:2.2:def-boolean-algebra"],"deps":[]} -->

---8<---

---
title: "Awodey 2.3: Filters, ultrafilters, and the correspondence between Boolean homomorphisms to 2 and ultrafilters"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.3:def-filter, awodey:2.3:def-ultrafilter, awodey:2.3:construction-ultrafilter-bijection, awodey:2:ex5]
deps_item_ids: [awodey:2.2:def-boolean-algebra]
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.3 (printed p. 37; PDF p. 46) — the prose definitions of filter and ultrafilter and the correspondence `Hom_Bool(B, 2) ≅ ultrafilters(B)` — together with §2.9 Exercise 5 (printed p. 55; PDF p. 64), which restates the same correspondence. Item IDs: `awodey:2.3:def-filter`, `awodey:2.3:def-ultrafilter`, `awodey:2.3:construction-ultrafilter-bijection`, `awodey:2:ex5`.

## Background

A filter in a Boolean algebra is a non-empty upward-closed, meet-closed subset; an [ultrafilter](https://ncatlab.org/nlab/show/ultrafilter) is a maximal (proper) filter, equivalently one containing exactly one of `b`, `¬b` for every `b` (see also [Wikipedia](https://en.wikipedia.org/wiki/Ultrafilter)). Awodey shows the Boolean homomorphisms `B → 2` correspond bijectively to the ultrafilters of `B` via `U_p = p^{-1}(1)` and its inverse — the algebraic heart of Stone duality and of two-valued (truth-table) semantics.

## Current state in the library

Entirely absent, because the prerequisite Boolean-algebra structure is absent (see the Awodey 2.2 Boolean-algebra issue): `grep -rniE 'ultrafilter|filter' ` finds only Haskell-style `filter` list operations, and the *ultrafilter monad* named as motivation in essays (`Theory/Kan/Extension.v` on codensity, `Theory/Monad.v`) — a different object from Awodey's maximal-filter-in-a-Boolean-algebra. `Instance/Two.v`'s `_2` is used as an enriching base / object of truth values, but no Boolean-algebra homomorphisms into it are formalized, so there is no `Hom_Bool(B, 2)` hom-set to biject with, and no filter/ultrafilter predicate over any carrier.

## Work to be done

- Over the `BooleanAlgebra` structure (from the Awodey 2.2 Boolean-algebra issue), define `Filter B` (non-empty, upward-closed, meet-closed) and `Ultrafilter B` (maximal proper filter), and prove the "exactly one of `b`, `¬b`" characterization. Suggested path: `Structure/BooleanAlgebra/Filter.v`.
- Construct the bijection `Hom_Bool(B, 2) ≅ Ultrafilter B`: `p ↦ p^{-1}(1)` and `U ↦ (b ↦ if b ∈ U then 1 else 0)`, and prove the two assignments are mutually inverse (this is simultaneously Example construction and Exercise 5). Suggested path: same module; donor `Instance/Two.v` for the target algebra `2`.

## Definition of Done

- [ ] Definitions and the bijection faithful to Awodey §2.3 and Exercise 5; any hom equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond documented `Instance/` stdlib axioms.
- [ ] `Print Assumptions` reported for `Filter`, `Ultrafilter`, and the `Hom_Bool(B,2) ≅ Ultrafilter B` bijection.
- [ ] New module(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- `coqc -R . Category Structure/BooleanAlgebra/Filter.v` compiles clean.
- `Print Assumptions hom_to_two_iff_ultrafilter.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statements match Awodey §2.3 (filter, ultrafilter, `Hom_Bool(B,2) ≅ ultrafilters`) and Exercise 5.

## Dependencies

Depends on: awodey:2.2:def-boolean-algebra (the Boolean-algebra structure and the two-element algebra `2` this development is stated over).

<!-- catalog: {"ids":["awodey:2.3:def-filter","awodey:2.3:def-ultrafilter","awodey:2.3:construction-ultrafilter-bijection","awodey:2:ex5"],"deps":["awodey:2.2:def-boolean-algebra"]} -->

---8<---

---
title: "Awodey 2.3: Well-pointed categories and having enough points"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.3:example10]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.3 Example 2.10 (printed p. 38; PDF pp. 47–48). Item ID: `awodey:2.3:example10`.

## Background

A category "has enough points" (is [well-pointed](https://ncatlab.org/nlab/show/well-pointed+category)) when the terminal object `1` is a generator/separator: two parallel arrows are equal iff they agree after precomposition with every global element `1 → A`. Awodey contrasts `Set`, `Pos` and `Top` (which have enough points) with `Mon` (where each object has a single point, so points fail to separate homomorphisms), motivating the shift to generalized elements.

## Current state in the library

Unformalized. `grep -rniE 'enough points|well-pointed|well_pointed'` finds only header-essay prose in `Structure/Terminal.v` ("categories are well-pointed, meaning `1` is a generator") and a same-name-different-notion trap in `Instance/Fun.v:230/240` (`Class Pointed` / `Class WellPointed` are *pointed endofunctors*, `point : Id ==> F` — unrelated to a category having enough points). The dual notion exists — `Adjunction/SAFT.v` `Cogenerator` is a *co*separating family — but the separator ("enough points") direction `(∀ p : 1 → a, f ∘ p ≈ g ∘ p) → f ≈ g` is not defined, and the `Pos`-yes / `Mon`-no comparison is not formalized (there is no non-commutative `Mon` instance in-tree, only `CMon`).

## Work to be done

- Define `WellPointed C` (a category with terminal object): for all `f g : a ⟶ b`, if `f ∘ p ≈ g ∘ p` for every point `p : 1 ⟶ a` then `f ≈ g` (equivalently, `1` is a separator). Suggested path: `Structure/WellPointed.v`; donors `Structure/Terminal.v`, `Structure/Constant.v` (global elements `1 ~> x`), and `Adjunction/SAFT.v` `Cogenerator` as the dual template.
- Prove `Sets` is well-pointed (points out of the singleton separate setoid morphisms), and, where the categories exist, `Pos`; record that `Mon` is *not* well-pointed (the single point cannot separate distinct homomorphisms) once a monoid category is available.
- Optionally relate `WellPointed` to the general separator notion so it reads as "the terminal object is a separating family".

## Definition of Done

- [ ] Definition faithful to Awodey §2.3 Example 2.10; equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond documented `Instance/` stdlib axioms.
- [ ] `Print Assumptions` reported for `WellPointed` and `Sets_WellPointed`.
- [ ] New module(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- `coqc -R . Category Structure/WellPointed.v` compiles clean.
- `Print Assumptions Sets_WellPointed.` shows no unexpected axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the definition matches Awodey Example 2.10 ("enough points" = terminal object separates arrows) and is distinct from the pointed-endofunctor `WellPointed` in `Instance/Fun.v`.

## Dependencies

None blocking. Related: #447 (MacLane V.7 — generating/separating sets of objects) is the general separator framework, of which well-pointedness is the terminal-object case; the `Mon`-fails-to-be-well-pointed witness would build on the Awodey 2.1 monoid-category work (`awodey:2.1:example3`).

<!-- catalog: {"ids":["awodey:2.3:example10"],"deps":[]} -->

---8<---

---
title: "Awodey 2.4: Functors preserve split monomorphisms and split epimorphisms"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.4:remark14]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.4 Remark 2.14 (printed p. 41; PDF p. 50). Item ID: `awodey:2.4:remark14`.

## Background

Because a functor preserves identities and composition, it carries a [split monomorphism](https://ncatlab.org/nlab/show/split+monomorphism) (a morphism with a left inverse, i.e. a section) to a split monomorphism, and likewise a split epimorphism to a split epimorphism. Awodey contrasts this with the forgetful functor `Mon → Set`, which fails to preserve the *non-split* epi `ℕ → ℤ` — split-ness is exactly what survives an arbitrary functor.

## Current state in the library

The building blocks are present but the lemma is not. `Theory/Morphisms.v:56/70` provide `Section`/`Retraction` (split mono/epi), and `Theory/Functor.v:13` provides `fmap_id`/`fmap_comp`, from which `fmap` preserving a `Section`/`Retraction` is a one-line consequence. The neighbouring results are proven — `Theory/Functor.v:227` `fobj_iso` (functors preserve *isomorphisms*, a strictly stronger input) and `Structure/Coequalizer/Split.v:104` `functor_preserves_split` (functors preserve split *coequalizers*, a different "split" notion) — but a blind search (`grep -rniE 'fmap.*Section|Section.*Section|map_section'`) finds no lemma `Section f → Section (fmap[F] f)` or its dual.

## Work to be done

- Prove `functor_preserves_section : Section f → Section (fmap[F] f)` and `functor_preserves_retraction : Retraction f → Retraction (fmap[F] f)` (equivalently for the `SplitMono`/`SplitEpi` synonyms), by applying `fmap` to the defining equation `section ∘ f ≈ id` and rewriting with `fmap_comp`/`fmap_id`. Suggested path: add to `Theory/Functor.v` (near `fobj_iso`) or a small `Theory/Functor/Morphisms.v`.
- Optionally record the contrast that a functor need *not* preserve a non-split epi, pointing at the `ℕ ↪ ℤ` example (the Awodey 2.1 monoid-epi issue) rather than reproving it here.

## Definition of Done

- [ ] Lemmas faithful to Awodey Remark 2.14; conclusions phrased with `≈`, never `=`.
- [ ] No `Admitted`/`admit`/`Axiom` (this is core-theory `Theory/`, zero axioms).
- [ ] `Print Assumptions functor_preserves_section.` (and the dual) is "Closed under the global context".
- [ ] Registered in `_CoqProject` (already true for `Theory/Functor.v`; register any new file).
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated only if judged flagship-level (not expected).

## Verification

- `coqc -R . Category Theory/Functor.v` compiles clean.
- `Print Assumptions functor_preserves_section.` shows the empty axiom set.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statement matches Awodey Remark 2.14 (functors preserve split monos/epis).

## Dependencies

None blocking. Related: the contrast case (`Mon → Set` does not preserve the non-split `ℕ ↪ ℤ` epi) is the Awodey 2.1 monoid-epi issue (`awodey:2.1:example5`).

<!-- catalog: {"ids":["awodey:2.4:remark14"],"deps":[]} -->

---8<---

---
title: "Awodey 2.4: The categorical axiom of choice and projective objects in Sets and Pos"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:2.4:example15, awodey:2:ex3]
deps_item_ids: []
deps_pending: []
---

## Source

Awodey, *Category Theory* (2nd ed.), §2.4 Example 2.15 (printed p. 41; PDF pp. 50–51) and §2.9 Exercise 3 (printed p. 55; PDF p. 64). Item IDs: `awodey:2.4:example15`, `awodey:2:ex3`.

## Background

The categorical axiom of choice is the statement that every epimorphism in `Set` splits: a splitting of an epi `e : E ↠ X` is exactly a choice function for the family of non-empty fibres. It is intimately tied to [projective objects](https://ncatlab.org/nlab/show/projective+object) — under choice every set is projective (lifts against every epi), and Awodey's Exercise 3 collects the companion facts for `Pos` and the closure of projectivity under retracts.

## Current state in the library

Absent. `grep -rniE 'axiom of choice|choice function'` finds only essay mentions (`Structure/Factorization.v`, `Structure/Topos.v` "the axiom of choice need not hold internally"); nothing states "every epi in `Set` splits ⟺ AC" or characterizes splittings as choice functions, and `Instance/Sets.v:429` `surjectivity_is_epic` deliberately does *not* admit the choice-dependent reverse direction. There is no `Projective` object class at all (`grep -rniE '(Class|Definition|Record).*[Pp]rojective'` → 0 hits; "projective" occurs only as "enough projectives"/"projective limit"/"projective tensor" essay prose), so the "every set / `1 ∈ Pos` is projective" and "retract of a projective is projective" facts have no home; and there is no `Pos` epi-characterization. (Idempotent splitting in `Instance/Sets/Karoubi.v` is a different statement.)

## Work to be done

- State the categorical axiom of choice for `Sets`: every `Epic e : E ⟶ X` has a section `s` with `e ∘ s ≈ id`, and characterize such sections as choice functions for the fibre family. Suggested path: `Instance/Sets/Choice.v`; donor `Instance/Sets.v` (`surjectivity_is_epic`, the fibre construction) — the choice principle may be taken as an explicit hypothesis/typeclass so the zero-axiom core is not disturbed.
- Using the projective-object class from #429, prove every set is projective (Exercise 3a) and that `1` is projective in `Pos`, with the epimorphisms of `Pos` being the surjections on objects (Exercise 3b). Suggested path: `Instance/Sets/Choice.v`, `Instance/Poset.v`.
- Prove that a retract of a projective object is projective in any category (Exercise 3c), if not already supplied by #429. Suggested path: alongside the projective-object class.

## Definition of Done

- [ ] Statements faithful to Awodey Example 2.15 and Exercise 3; equalities use `≈`, never `=`.
- [ ] No `Admitted`/`admit` and no new *global* `Axiom`; any choice principle is an explicit hypothesis or a clearly-scoped `Instance/`-layer assumption disclosed against `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the AC/epi-splitting statement, "every set is projective", and "retract of projective is projective" (choice dependency made explicit, not hidden).
- [ ] New module(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds under Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- `coqc -R . Category Instance/Sets/Choice.v` compiles clean.
- `Print Assumptions sets_epi_splits_iff_choice.` and `Print Assumptions sets_are_projective.` show exactly the intended (disclosed) choice hypothesis and no stray axioms.
- `nix build .#category-theory_9_1` succeeds.
- Reviewer confirms the statements match Awodey Example 2.15 (every epi in `Set` splits = AC; splittings = choice functions) and Exercise 3 (sets projective, `Pos` facts, retract closure).

## Dependencies

Depends on: #429 (MacLane V.4 — projective and injective objects; supplies the `Projective` object class this issue instantiates and, for Exercise 3c, the retract-closure lemma). The Awodey §2.4 projective-object *definition* itself (`awodey:2.4:def-projective`) is the same obligation as #429.

<!-- catalog: {"ids":["awodey:2.4:example15","awodey:2:ex3"],"deps":["#429"]} -->

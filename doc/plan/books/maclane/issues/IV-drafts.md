```yaml
title: "MacLane IV.1: Determination of an adjunction by its counit and by couniversal arrows"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.1:thm2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book p. 83 (PDF pp. 92–94), Theorem 2. Item covered: `maclane:IV.1:thm2`.

## Background

Mac Lane's Theorem IV.1.2 lists five mutually interchangeable presentations of an adjunction: hom-set bijection, unit plus universality, right adjoint plus a universal arrow at every object, and the two counit-side duals, together with the unit/counit form cut out by the triangle identities. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [Wikipedia: Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors).

## Current state in the library

Three of the five presentations are in force, and all round trips among them are proved.

- `Adjunction/Natural/Transformation.v:35` — `Class Adjunction_Transform` carries exactly the unit/counit data with the two triangle identities (`counit_fmap_unit`, `fmap_counit_unit`).
- `Adjunction/Natural/Transformation/Universal.v:42` and `:84` — `Adjunction_from_Transform` and `Adjunction_to_Transform`, both directions between the unit/counit form and the hom-set form.
- `Adjunction/Hom.v:154`, `:161`, `:223`, `:259` — the four conversions closing the triangle between the hom-bifunctor form, the unit/counit form and the hom-setoid form.
- `Theory/Universal/Arrow.v:185` and `:214` — `LeftAdjointFunctorFromUniversalArrows` and `AdjunctionFromUniversalArrows`: the right adjoint alone, plus a universal arrow at every object, determines the left adjoint on objects *and* arrows and yields the full adjunction.
- `Theory/Adjunction.v:404` — `left_adjoint_iso`, the "determined up to natural isomorphism" content.

The gap is precise: the two counit-side presentations — determination by the counit alone, and determination by the *left* adjoint together with a couniversal arrow at each object of the codomain — have no in-tree statement. A whole-tree search for `RightAdjoint` and for `couniversal` returns nothing; they are obtainable only by hand-dualizing the universal-arrow assembly through `Adjunction/Opposite.v:34` (`Opposite_Adjunction`, with `Opposite_Adjunction_invol` at `:60` giving the strict involution). The book's first presentation (functors plus a universal unit) is also not separated from the third (right adjoint plus a universal-arrow family).

## Work to be done

Add the counit-side half of the determination theorem, mirroring the existing unit-side development.

Suggested module: `Theory/Universal/Arrow/Couniversal.v` (or a `Section` added to `Theory/Universal/Arrow.v` if the file stays legible), plus `Adjunction/Determination.v` for the packaging.

1. Define a couniversal arrow from a functor `F : C ⟶ D` to an object `d : D` — the terminal object of the comma `F ↓ =(d)` — dual to `UniversalArrow` (`Theory/Universal/Arrow.v:127`) and to `AUniversalArrow` (`:240`).
2. Build `RightAdjointFunctorFromCouniversalArrows` and `AdjunctionFromCouniversalArrows`, either by direct construction or by transporting the existing unit-side assembly along `Opposite_Adjunction` and the definitional `C^op^op = C`. The transport route is cheap but must still expose a statement in the *covariant* orientation, so that consumers never see an `op`.
3. State the round trip: from an adjunction, recover the couniversal arrow at every object (the counit component with its unique-factorization property), and check that the two constructions are mutually inverse up to `≈`.
4. Record the first presentation separately from the third: a left adjoint, a right adjoint and a unit whose every component is universal, with the transpose recovered as `fmap[U] g ∘ η`.

In-tree donors: `Theory/Universal/Arrow.v` (the whole unit-side pattern), `Adjunction/Opposite.v`, `Construction/Comma.v`, `Structure/Terminal.v`, `Theory/Adjunction.v`'s `unit`/`counit` accessors.

## Definition of Done

- [ ] Statements are faithful to §IV.1 Theorem 2, clauses (i)–(iv), with the setoid `≈` discipline throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new code
- [ ] `Print Assumptions` reports "Closed under the global context" for the couniversal-arrow definition and for the adjunction-from-couniversal-arrows construction (docs/AXIOMS.md scoping)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Theory/Universal/Arrow/Couniversal.v
coqc -R . Category Adjunction/Determination.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

Then, in `coqtop -R . Category`, after requiring the new modules:

```coq
Print Assumptions AdjunctionFromCouniversalArrows.
```

Reviewer checks: the four clauses correspond to Mac Lane §IV.1 Theorem 2 (book p. 83) as paraphrased above; the covariant statements contain no residual `^op` in their types; the round-trip lemmas are stated with `≈`, not `=`.

## Dependencies

- Depends on: #302

<!-- catalog: {"ids":["maclane:IV.1:thm2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.1: A left adjoint exists exactly when the hom-functors are representable"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.1:cor2, maclane:IV.1:ex1]
deps_item_ids: [maclane:IV.1:thm2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book pp. 85–86 (PDF pp. 94–95), Corollary 2 and Exercise 1. Items covered: `maclane:IV.1:cor2`, `maclane:IV.1:ex1`.

## Background

A functor `G : A ⟶ X` has a left adjoint precisely when, for each object `x`, the composite `X(x, G−) : A ⟶ Set` is representable; a choice of representations is exactly a choice of universal arrows, and the exercise records this as a sixth clause of the determination theorem. See [nLab: representable functor](https://ncatlab.org/nlab/show/representable+functor) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The substantive direction is present; the biconditional is not, and the two halves do not compose.

- `Theory/Universal/Arrow.v:214` — `AdjunctionFromUniversalArrows (H : forall c, UniversalArrow c U) : Adjunction (LeftAdjointFunctorFromUniversalArrows H) U`. This is the "⇐" leg at full strength.
- `Adjunction/GAFT.v:181` — `GAFT_from_initials`, the same leg packaged from comma-initial objects.
- `Structure/UniversalProperty/Universal/Arrow.v:61` — `UniversalArrowIsUniversalProperty`, whose representing functor is `(Curried_Hom C c) ◯ U`, i.e. `d ↦ Hom_C(c, U d)`. This *is* the representability bridge — but it is stated over `AUniversalArrow c U a` (`Theory/Universal/Arrow.v:240`).
- `Theory/Profunctor/Adjunction.v:70` — `representable_adjunction : (F ⊣ U) ↔ (Repr_left F ≅ Repr_right U)`, a genuine biconditional but of the two-sided kind: it presupposes that `F` is already given, so it is not the pointwise criterion.
- `Functor/Representable.v:46` — `Class Representable`, defined but never applied to a composite `Hom(x, U −)` and never mentioned in any adjunction file.

Two concrete obstructions. First, the representability theorem lands in `AUniversalArrow` while the adjunction-building theorem consumes `UniversalArrow` (an `Initial` of the comma `=(c) ↓ U`); these are distinct classes in the same file and nothing converts between them, so the chain "representation ⇒ universal arrow ⇒ left adjoint" cannot be run end to end. Second, the easy forward implication — an adjunction yields a universal arrow, hence a representation, at every object — is nowhere constructed.

## Work to be done

Suggested modules: `Theory/Universal/Arrow.v` (for the packaging equivalence) and a new `Adjunction/Representability.v`.

1. Prove the two packagings of a universal arrow interchangeable: `AUniversalArrow c U a → UniversalArrow c U` and back, i.e. an isomorphism between the comma-initial datum and the arrow-plus-unique-factorization datum. This is the load-bearing missing lemma and is reusable well beyond this issue.
2. Construct, from any `F ⊣ U`, a universal arrow at each object (the unit component, with uniqueness read off the transpose) — the "⇒" leg.
3. Assemble the corollary as a genuine biconditional: `(∀ x, Representable ([Hom x,─] ◯ U)) ↔ { F : _ & F ⊣ U }`, with `Functor/Representable.v`'s class as the left-hand side, and check that the left adjoint built from a family of representations agrees on objects with the chosen representing objects.
4. Record the added clause of the determination theorem in both orientations: a functor together with a representation of `X(x, G−)` for every `x`, and dually a representation of `A(F−, a)` for every `a` (the couniversal-arrow side).

In-tree donors: `Structure/UniversalProperty/Universal/Arrow.v`, `Functor/Hom.v`, `Functor/Hom/Yoneda.v`, `Theory/Universal/Arrow.v`, `Theory/Adjunction.v` (`unit`, `to_adj_nat_*`).

## Definition of Done

- [ ] Statement fidelity to §IV.1 Corollary 2 and Exercise 1, with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the packaging equivalence, for the forward implication and for the biconditional
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Adjunction/Representability.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions adjunction_iff_pointwise_representable.
```

Reviewer checks: the criterion is stated pointwise (one representation per object of the domain), not as the two-sided `representable_adjunction`; the statement matches Mac Lane §IV.1 Corollary 2 (book p. 85); the dual clause is present.

## Dependencies

- Depends on: maclane:IV.1:thm2
- Depends on: #303

<!-- catalog: {"ids":["maclane:IV.1:cor2","maclane:IV.1:ex1"],"deps":["maclane:IV.1:thm2"]} -->

---8<---

```yaml
title: "MacLane IV.1: Adjoints of additive functors are additive"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.1:thm3]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book p. 85 (PDF pp. 94–95), Theorem 3. Item covered: `maclane:IV.1:thm3`.

## Background

Between Ab-enriched categories, a left adjoint of an additive functor is itself additive, and the adjunction bijection is then an isomorphism of abelian groups rather than merely of sets; dually for right adjoints. See [nLab: additive functor](https://ncatlab.org/nlab/show/additive+functor) and [Wikipedia: Additive category](https://en.wikipedia.org/wiki/Additive_category).

## Current state in the library

The enrichment side exists; the functor side does not exist at all.

- `Structure/Preadditive.v:34` — `Class Preadditive`, commutative-monoid enrichment of the hom-sets, with the opt-in `addition_scope`.
- `Structure/Additive.v:34` — `Class Additive`, adding negation.
- `Structure/Semiadditive.v` — the two semiadditivity theorems; `Instance/CMon.v` and `Instance/CMon/Biproduct.v` are the concrete witness.

There is no notion of an additive functor: the token `Functor` does not occur anywhere in `Structure/Preadditive.v`, `Structure/Additive.v` or `Structure/Semiadditive.v`, and searches for `AdditiveFunctor` and for any enriched-adjunction notion return nothing. Consequently neither the hypothesis of the theorem (an additive `G`) nor its conclusion (`F` additive, and the transpose a homomorphism of hom-monoids) can currently be stated.

## Work to be done

Suggested modules: `Structure/Preadditive/Functor.v` (the notion) and `Adjunction/Additive.v` (the theorem).

1. Define an additive functor between preadditive categories: a functor whose action on hom-sets is a homomorphism of the commutative monoids, plus the negation clause in the additive case. Prove the identity and composite are additive, so the notion has a usable API.
2. Prove that the adjunction transpose of an additive right adjoint is additive in each variable, i.e. `⌊f + g⌋ ≈ ⌊f⌋ + ⌊g⌋`, using the recovery `φ f = fmap[U] f ∘ η` together with additivity of `U` and bilinearity of composition supplied by the preadditive structure.
3. Conclude the theorem: if `U` is additive and `F ⊣ U`, then `F` is additive and each `adj` component is an isomorphism of hom-monoids (hom-groups in the additive case). State the dual for right adjoints of additive functors, transporting along `Adjunction/Opposite.v` and the opposite of a preadditive category.

In-tree donors: `Structure/Preadditive.v`, `Structure/Additive.v`, `Theory/Adjunction.v` (`unit`, `to_adj_nat_l/r`), `Adjunction/Opposite.v`, `Instance/CMon.v` for a concrete enriched category to sanity-check against.

## Definition of Done

- [ ] Statement fidelity to §IV.1 Theorem 3, with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the additive-functor class and for the transfer theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Structure/Preadditive/Functor.v
coqc -R . Category Adjunction/Additive.v
make && make todo
```

```coq
Print Assumptions left_adjoint_of_additive_is_additive.
```

Reviewer checks: the conclusion is the *pair* of claims Mac Lane makes (additivity of the adjoint, and the transpose being a hom-group isomorphism), not just the first; the dual statement is present.

## Dependencies

- Depends on: #264

<!-- catalog: {"ids":["maclane:IV.1:thm3"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.1: Paré's criterion — a left adjoint from a split idempotent"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.1:ex4]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book p. 86 (PDF p. 95), Exercise 4 (attributed to Paré). Item covered: `maclane:IV.1:ex4`.

## Background

Given functors `G : A ⟶ X`, `K : X ⟶ A` and transformations `ε : K ◯ G ⟹ Id` and `ρ : Id ⟹ G ◯ K` satisfying one of the two triangle equations, the whiskered composite `εK ∘ Kρ` is idempotent in the functor category, and `G` acquires a left adjoint exactly when that idempotent splits. See [nLab: split idempotent](https://ncatlab.org/nlab/show/split+idempotent) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The vocabulary exists; the statement does not.

- `Theory/Morphisms.v:22` — `Idempotent`, and `:85` — `SplitIdempotent`, both stated for an arbitrary category, hence usable in a functor category.
- `Instance/Fun.v` — the functor category `[X, A]` in which `εK ∘ Kρ` lives, with whiskering and the Godement product available from `Theory/Natural/Transformation.v:283`.
- `Construction/Karoubi.v` and `Construction/Karoubi/Universal.v` — the splitting machinery, including `IdempotentsSplit` and `CauchyComplete`.

Nothing asserts that `εK ∘ Kρ` is idempotent under the hypothesis, and nothing relates the existence of a left adjoint of `G` to the splitting of that idempotent. Paré is cited in-tree only for absolute colimits (`Structure/Coequalizer/Split.v:32`) and for bicategory coherence.

## Work to be done

Suggested module: `Adjunction/Pare.v`.

1. Set up the hypotheses as a record: `G`, `K`, `ε : K ◯ G ⟹ Id`, `ρ : Id ⟹ G ◯ K`, and the equation `Gε ∘ ρG ≈ id[G]` in `[A, X]`.
2. Prove `εK ∘ Kρ : K ⟹ K` is idempotent in `[X, A]`, using `Instance/Fun.v`'s composition and the whiskering lemmas.
3. Prove the "if" direction: from a splitting `α ∘ β ≈ εK ∘ Kρ` with `β ∘ α ≈ id` and `β : K ⟹ F`, build `F ⊣ G` with unit `Gβ ∘ ρ` and counit `ε ∘ αG`, discharging both triangle identities.
4. Prove the "only if" direction: a left adjoint of `G` supplies a splitting, closing the biconditional.
5. Optionally connect to `Construction/Karoubi/Universal.v`: if `[X, A]` is Cauchy complete then the hypothesis alone already yields the left adjoint.

In-tree donors: `Theory/Morphisms.v`, `Instance/Fun.v`, `Theory/Natural/Transformation.v`, `Adjunction/Natural/Transformation.v` (the unit/counit presentation of an adjunction), `Construction/Karoubi/Universal.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.1 Exercise 4, with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the idempotence lemma and for both directions of the biconditional
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Pare.v
make && make todo
```

```coq
Print Assumptions pare_left_adjoint_iff_splits.
```

Reviewer checks: the unit and counit of the constructed adjunction are literally the ones the exercise prescribes; the idempotent is the whiskered composite, not a hand-picked variant.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.1:ex4"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.1: Coproducts as the left adjoint of the diagonal functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.1:construction5]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book p. 84 (PDF p. 93), the application of Theorem 2 to products and coproducts. Item covered: `maclane:IV.1:construction5`.

## Background

Binary products make the product bifunctor a right adjoint of the diagonal `Δ : C ⟶ C × C`, with counit the pair of projections; dually binary coproducts make the coproduct bifunctor a *left* adjoint of the same diagonal, with unit the pair of injections and counit the folding map. See [nLab: diagonal functor](https://ncatlab.org/nlab/show/diagonal+functor) and [nLab: coproduct](https://ncatlab.org/nlab/show/coproduct).

## Current state in the library

The product half is present twice over; the coproduct half is missing.

- `Adjunction/Diagonal/Product.v:36` — `Diagonal_Product_Adjunction (C : Category) {Cartesian C} : Diagonal_Product C ⊣ ×(C)`, with the transposes literally the pairing `fst f △ snd f` and the projection-splitting `(exl ∘ f, exr ∘ f)`, exactly as in the book.
- `Adjunction/GAFT/Examples.v:108` — `diagonal_product_via_gaft`, the same adjunction reconstructed from the diagonal universal arrows, with `diagonal_product_via_gaft_is_diagonal` (`:121`) identifying the reflector with `Δ`.

There is no coproduct-side instance. `Adjunction/Diagonal/Product.v:19` and `Adjunction/GAFT/Examples.v:45` both remark in prose that feeding `Δ` to the machinery "would instead reconstruct the coproduct adjunction", but neither does so; a whole-tree search for a `⊣` whose left side is a coproduct bifunctor finds nothing. The book's closing generalisation — that limits and colimits in general become adjoints of the diagonal — is separately tracked (see the Dependencies below).

## Work to be done

Suggested module: `Adjunction/Diagonal/Coproduct.v`, mirroring the existing product file.

1. Define the coproduct bifunctor `+(C) : C ∏ C ⟶ C` for a `Cocartesian C` (or reuse the dual of `InternalProductFunctor`), if it is not already available in a usable form.
2. Prove `+(C) ⊣ Diagonal_Product C` in hom-set form, with the transposes the copairing and the injection-splitting, dual to the existing product proof. Preferably derive it by duality: `Cocartesian C` is `Cartesian C^op`, so `Adjunction/Opposite.v:34` plus the existing instance gives the result — but the delivered statement must be covariant, with no residual `^op` in its type.
3. Name the unit and counit explicitly: unit the pair of injections, counit the folding map `id ▽ id`, and prove them equal to the generic `unit`/`counit` of the constructed adjunction.
4. Add the corresponding sanity example alongside `Adjunction/GAFT/Examples.v`, so the "reconstruct the coproduct adjunction" prose in that file becomes a pointer to real code.

In-tree donors: `Adjunction/Diagonal/Product.v`, `Structure/Cocartesian.v`, `Functor/Diagonal.v`, `Adjunction/Opposite.v`, `Construction/Opposite.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.1 (book p. 84), with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the coproduct-diagonal adjunction and for the unit/counit identifications
- [ ] New file registered in `_CoqProject`
- [ ] The prose promises in `Adjunction/Diagonal/Product.v:19` and `Adjunction/GAFT/Examples.v:45` updated to cite the new result
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Diagonal/Coproduct.v
make && make todo
```

```coq
Print Assumptions Diagonal_Coproduct_Adjunction.
```

Reviewer checks: the delivered type is covariant (`+(C) ⊣ Δ`, no `^op`); the unit is the injection pair and the counit the folding map, as Mac Lane describes.

## Dependencies

None. (The general "all limits and colimits are adjoints of a diagonal" statement is a separate, downstream issue.)

<!-- catalog: {"ids":["maclane:IV.1:construction5"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: Connected categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.2:def1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 88 (PDF p. 97), the definition of a connected category. Item covered: `maclane:IV.2:def1`.

## Background

A category is connected when any two of its objects are joined by a finite zigzag of arrows, the directions being unconstrained. The notion controls when a limit of a constant diagram is the constant itself, and it is the shape hypothesis under which colimits become left-adjoint-left-inverses of the diagonal. See [nLab: connected category](https://ncatlab.org/nlab/show/connected+category) and [Wikipedia: Connected category](https://en.wikipedia.org/wiki/Connected_category).

## Current state in the library

Absent. A whole-tree search for the identifier `Connected` returns no hits; the English word occurs only in prose and in `Instance/FinSet/Pushout.v:398`, `:405`, where connected components of a finite span-edge relation are computed to build pushouts — a construction on a finite graph, not a predicate on categories. There is no `π₀`, no zigzag relation on objects, and no decomposition of a category into components. `Construction/Groupoid.v` mentions connectedness only in its header essay.

## Work to be done

Suggested module: `Theory/Connected.v`.

1. Define the zigzag relation on the objects of a category as a `Type`-valued inductive family: a step is a morphism in either direction, and a zigzag is a finite chain of steps. The house style for such chains is `Lib/TList.v`'s heterogeneous lists and `Instance/Omega.v`'s `le_t`, both of which avoid `Prop`-valued stdlib relations that cannot be eliminated into `Type`.
2. Prove the zigzag relation is reflexive, symmetric and transitive, and that it is preserved by every functor.
3. Define `Connected : Category → Type` as "inhabited, and any two objects are joined by a zigzag". Record the standard consequences: a category with an initial or a terminal object is connected; the terminal category is connected; a groupoid is connected exactly when its zigzag relation is total; a discrete category is connected only if it has exactly one object.
4. Provide the components construction: the quotient of the object type by the zigzag relation (as a setoid, not by an axiom), plus the full subcategory on each class, so that downstream issues can speak of "the connected components of `J`".
5. Add a small regression example, e.g. `Instance/Parallel.v`'s walking parallel pair and `Instance/Roof.v` are connected, while `Instance/Discrete.v`'s `DiscreteCat bool` is not.

In-tree donors: `Lib/TList.v`, `Instance/Omega.v` (`le_t` as the Type-valued-order precedent), `Construction/Groupoid.v`, `Instance/Parallel.v`, `Instance/Roof.v`, `Instance/Discrete.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 (book p. 88): the zigzag is finite and directions are unconstrained; `≈` discipline throughout
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` (in particular, no quotient axiom — use a setoid)
- [ ] `Print Assumptions` closed for the `Connected` predicate and the components construction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Theory/Connected.v
make && make todo
```

```coq
Print Assumptions Connected.
Print Assumptions connected_components.
```

Reviewer checks: the definition is `Type`-valued and eliminable (a `Prop`-valued zigzag would block every downstream use); the sample instances compile.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.2:def1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: Limits and colimits as adjoints of the diagonal functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.2:construction2]
deps_item_ids: [maclane:IV.1:construction5]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 87 (PDF pp. 96–97), the table of adjoints of diagonal functors. Item covered: `maclane:IV.2:construction2`.

## Background

Mac Lane tabulates the diagonal functors and their adjoints: coproduct ⊣ Δ ⊣ product; initial ⊣ (C → 1) ⊣ terminal; and in general colimit ⊣ Δ ⊣ limit for `Δ : C ⟶ [J, C]`, with unit and counit the universal cocone and cone. See [nLab: limit](https://ncatlab.org/nlab/show/limit) and [nLab: diagonal functor](https://ncatlab.org/nlab/show/diagonal+functor).

## Current state in the library

Only the binary-product row is a genuine adjunction; the general rows exist only in Kan-extension packaging.

- `Adjunction/Diagonal/Product.v:36` — `Diagonal_Product_Adjunction`, the `Δ ⊣ ×` row at full strength.
- `Theory/Kan/Extension.v:145` and `:225` — `ran_adjoint : Induced ⊣ Ran` and `lan_adjoint : Lan ⊣ Induced`, for `Induced := (− ◯ F) : [B,C] ⟶ [A,C]` (defined at `:127`). At `F := Erase J` these are the colimit/limit rows *modulo* the identification `[1, C] ≅ C`, and only when the corresponding Kan extension exists.
- `Structure/Limit/Kan/Extension.v:46` — `Kan_Limit : Lim ≅ Ran (Erase J) F ttt`, tying the right Kan extension to the per-diagram limit object.
- `Functor/Diagonal.v:33` — `Diagonal J : C ⟶ [J, C]` exists, with the `Δ[J]` notation, and its header records the colim ⊣ Δ ⊣ lim reading in prose only.
- `Instance/One/Diagonal.v:33` — `Diagonal_Unique`, a factorisation statement about `Δ`, not an adjunction.

Missing: any adjunction whose left or right adjoint is the *limit or colimit functor* `[J, C] ⟶ C`; the initial/terminal row (initial and terminal objects are defined by universal property only, in `Structure/Initial.v` and `Structure/Terminal.v`, never as adjoints of `C ⟶ 1`); the explicit unit/counit descriptions as universal cones; and Mac Lane's remark that the shape of the limit unit depends on the number of connected components of the index category.

## Work to be done

Suggested module: `Adjunction/Diagonal/Limit.v`.

1. Assuming all `J`-shaped limits exist in `C`, build the limit functor `Lim[J] : [J, C] ⟶ C` (object part the limit apex, arrow part the mediating morphism), proving functoriality from the limit universal property.
2. Prove `Δ[J] ⊣ Lim[J]`, with counit the universal cone; dually build `Colim[J]` and prove `Colim[J] ⊣ Δ[J]`, with unit the universal cocone. Derive the second from the first by duality if that is cheaper, but deliver covariant statements.
3. Identify the unit and counit with the cone/cocone data already in `Structure/Cone.v` and `Structure/Cocone.v`, so that the adjunction and the per-diagram universal property are visibly the same thing.
4. Add the degenerate rows: `C ⟶ 1` has left adjoint an initial object and right adjoint a terminal object, i.e. `Structure/Initial.v` and `Structure/Terminal.v` re-read as adjunctions over the terminal category.
5. Relate the result to the existing Kan-extension form: `Lim[J]` agrees with `Ran (Erase J) −` under `[1, C] ≅ C`, using `Structure/Limit/Kan/Extension.v:46`, so the two presentations are not left as unrelated developments.

In-tree donors: `Functor/Diagonal.v`, `Structure/Limit.v`, `Structure/Cone.v`, `Structure/Cone/Const.v`, `Theory/Kan/Extension.v`, `Structure/Limit/Kan/Extension.v`, `Adjunction/Diagonal/Product.v`, `Instance/One.v`.

## Definition of Done

- [ ] Statement fidelity to the §IV.2 table (book p. 87), with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the limit functor, for both adjunctions, and for the unit/counit identifications
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated (this is flagship-level: it closes the gap between the per-diagram limit API and the adjunction API)

## Verification

```bash
coqc -R . Category Adjunction/Diagonal/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Diagonal_Limit_Adjunction.
Print Assumptions Colimit_Diagonal_Adjunction.
```

Reviewer checks: the counit really is the universal cone of `Structure/Cone.v` (not a re-derived copy); the initial/terminal rows are stated; the Kan-extension comparison is proved, not asserted in a comment.

## Dependencies

- Depends on: maclane:IV.1:construction5

<!-- catalog: {"ids":["maclane:IV.2:construction2"],"deps":["maclane:IV.1:construction5"]} -->

---8<---

```yaml
title: "MacLane IV.2: Units and counits of the equalizer, coequalizer, pullback and pushout adjunctions"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex6]
deps_item_ids: [maclane:IV.2:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 6, together with the corresponding rows of the §IV.2 table. Item covered: `maclane:IV.2:ex6`.

## Background

For the finite shapes — the parallel pair, the span and the cospan — the diagonal functor has a left adjoint given by the coequalizer or pushout vertex and a right adjoint given by the equalizer or pullback vertex; the exercise asks for the units and counits explicitly. See [nLab: equalizer](https://ncatlab.org/nlab/show/equalizer) and [nLab: pullback](https://ncatlab.org/nlab/show/pullback).

## Current state in the library

The universal properties exist per diagram; the functors and adjunctions do not.

- `Structure/Equalizer/Fork.v` — the elementary fork API `IsEqualizer`; `Structure/Coequalizer.v` — the cofork API `IsCoequalizer`, with conversions to and from colimits.
- `Theory/Morphisms/Stability.v` — the apex-pinned `IsPullback`, with pasting and stability lemmas; `Structure/Pullback.v` and `Structure/Pushout.v` for the universal properties; `Instance/Parallel.v:80` and `Instance/Roof.v` for the walking shapes.
- `Adjunction/Diagonal/Product.v` only covers the binary-product shape.

There is no equalizer, coequalizer, pullback or pushout *functor*, hence no adjunction and no unit or counit to describe. The nearest relative, the slice base-change adjunction in `Construction/Slice/Pullback.v`, is entirely commented out (the block begins at `:121`) — see the separate slice base-change issue.

## Work to be done

Suggested module: `Adjunction/Diagonal/Finite.v`.

1. Instantiate the general limit/colimit-as-adjoint result at the three finite shapes, obtaining the equalizer and pullback functors as right adjoints of the corresponding diagonals, and the coequalizer and pushout functors as left adjoints.
2. Compute the units and counits in each case and prove them equal to the elementary data: for the equalizer row, unit the identity and counit the equalizing arrow; for the coequalizer row, unit the coequalizing arrow and counit the identity; for the pullback and pushout rows, the corresponding cone and cocone legs. These identifications are the actual content of the exercise.
3. Check the identifications against the elementary APIs (`IsEqualizer`, `IsCoequalizer`, `IsPullback`) rather than only against the generic cone machinery, so that the finite-shape users benefit.

In-tree donors: `Structure/Equalizer/Fork.v`, `Structure/Coequalizer.v`, `Structure/Pullback.v`, `Structure/Pushout.v`, `Instance/Parallel.v`, `Instance/Roof.v`, `Structure/Cone.v`, `Structure/Cocone.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 6 and the §IV.2 table (book pp. 87, 90), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for each of the four adjunctions and for the unit/counit identification lemmas
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Diagonal/Finite.v
make && make todo
```

```coq
Print Assumptions Equalizer_Diagonal_Adjunction.
Print Assumptions Pushout_Diagonal_Adjunction.
```

Reviewer checks: each unit/counit lemma names the elementary arrow Mac Lane names (equalizing arrow, coequalizing arrow, pullback and pushout legs), and is stated with `≈`.

## Dependencies

- Depends on: maclane:IV.2:construction2
- Depends on: #326

<!-- catalog: {"ids":["maclane:IV.2:ex6"],"deps":["maclane:IV.2:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.2: Limits over a disjoint union of index categories, and connected components"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex7]
deps_item_ids: [maclane:IV.2:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 7. Item covered: `maclane:IV.2:ex7`.

## Background

A limit over a coproduct of index categories is the product of the limits over the summands; every category decomposes as the coproduct of its connected components; hence all limits reduce to products of limits over connected shapes. See [nLab: connected category](https://ncatlab.org/nlab/show/connected+category) and [nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library

Absent in all three parts.

- `Construction/Coproduct.v:35` defines the *binary* coproduct of categories with its universal property in `Cat`, and carries no limit content; there is no coproduct of an indexed family of categories, which part (a) needs.
- No connectedness predicate exists anywhere in the tree, so parts (b) and (c) cannot even be stated.
- `Structure/Limit/Product.v:93` supplies indexed products (`iprod`) over `Instance/Discrete.v`'s `DiscreteCat`, which is the shape of the right-hand side of part (a).

## Work to be done

Suggested module: `Structure/Limit/Components.v`.

1. Build the coproduct of a family of categories indexed by a type (objects a dependent pair, homs the fibrewise homs), with the injections `I_k` and the universal property in `Cat`.
2. Prove part (a): for `F : ∐_k J_k ⟶ C` with each `Lim (F ◯ I_k)` existing, the limit of `F` exists and is the indexed product of the summand limits, using `Structure/Limit/Product.v`'s `iprod` and its universal property. State it as an isomorphism, and check the projections agree with restriction along the injections.
3. Prove part (b): the components decomposition — every category is isomorphic to the coproduct of its connected components — using the components construction from the connected-categories issue. Note that this must be an *isomorphism of categories* in the library's `≈`-based sense; a strict equality of object types is not required and should not be attempted.
4. Conclude part (c): every limit is a product of limits over connected shapes.

In-tree donors: `Construction/Coproduct.v`, `Instance/Discrete.v`, `Structure/Limit/Product.v`, `Structure/Limit.v`, `Instance/Cat.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 7 (book p. 90), with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the indexed coproduct of categories, part (a) and part (b)
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Limit/Components.v
make && make todo
```

```coq
Print Assumptions limit_over_coproduct_is_product.
Print Assumptions category_is_coproduct_of_components.
```

Reviewer checks: the right-hand side of part (a) uses the existing `iprod`, not a bespoke product; part (b) is proved, not assumed.

## Dependencies

- Depends on: maclane:IV.2:def1
- Depends on: #338
- Depends on: #320

<!-- catalog: {"ids":["maclane:IV.2:ex7"],"deps":["maclane:IV.2:def1"]} -->

---8<---

```yaml
title: "MacLane IV.2: Limits and colimits of a constant functor over a connected index category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex8]
deps_item_ids: [maclane:IV.2:def1, maclane:IV.2:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 8. Item covered: `maclane:IV.2:ex8`.

## Background

Over a connected index category the limit and the colimit of a constant diagram are the constant itself; equivalently, the unit of the limit adjunction is an isomorphism precisely because the index shape has a single component. See [nLab: constant functor](https://ncatlab.org/nlab/show/constant+functor) and [nLab: connected category](https://ncatlab.org/nlab/show/connected+category).

## Current state in the library

Absent. There is no connectedness predicate, so part (a)'s hypothesis is unstatable. The nearest in-tree result is `Instance/One/Diagonal.v:33`, `Diagonal_Unique`, which says the constant diagram factors through the terminal category — a factorisation statement about `Δ`, not a computation of `Lim (Δ c)`, and it carries no connectedness hypothesis. `Structure/Cone/Const.v` supplies the correspondence between cones and transformations out of `Δ(N)`, but there is no `Δ ⊣ Lim` adjunction whose unit part (b) could describe.

## Work to be done

Suggested module: `Structure/Limit/Constant.v`.

1. Prove part (a): for `J` connected and `c : C`, the constant diagram `Δ[J](c)` has limit `c` with the identity cone, and dually colimit `c`. The proof is the standard zigzag induction: a cone over a constant diagram has all legs equal along each zigzag step, so the apex maps to `c` uniquely.
2. Prove part (b): under the limit adjunction, the unit at `c` is the mediating map `c ⟶ Lim (Δ c)`; show it is an isomorphism exactly when the index is connected, and describe the general case as the mediating map into the product over the components (using the components decomposition of the previous issue if it is available, otherwise stating the connected case only).
3. Add the two obvious corollaries: over a connected shape the diagonal is fully faithful, and constant diagrams have absolute limits.

In-tree donors: `Functor/Diagonal.v`, `Structure/Cone.v`, `Structure/Cone/Const.v`, `Structure/Limit.v`, `Instance/One/Diagonal.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 8 (book p. 90), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for both parts
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Limit/Constant.v
make && make todo
```

```coq
Print Assumptions connected_limit_of_constant.
```

Reviewer checks: connectedness is genuinely used (the statement should fail for a two-object discrete shape, and a regression example should show it); the unit description matches part (b).

## Dependencies

- Depends on: maclane:IV.2:def1
- Depends on: maclane:IV.2:construction2

<!-- catalog: {"ids":["maclane:IV.2:ex8"],"deps":["maclane:IV.2:def1","maclane:IV.2:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.2: The adjoint string on the objects functor of Cat"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex9]
deps_item_ids: [maclane:IV.2:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 9 (attributed to Smythe). Item covered: `maclane:IV.2:ex9`.

## Background

The objects functor `Cat ⟶ Set` sits in an adjoint string: connected components ⊣ discrete ⊣ objects ⊣ indiscrete. See [nLab: adjoint quadruple](https://ncatlab.org/nlab/show/adjoint+quadruple) and [nLab: indiscrete category](https://ncatlab.org/nlab/show/indiscrete+category).

## Current state in the library

Only the object-level discrete construction and one direction of one transposition exist.

- `Instance/Discrete.v:37` — `DiscreteCat (A : Type) : Category`, with `hom := fun x y => x = y`.
- `Instance/Discrete.v:52` — `DiscreteCat_Functor {A C} (f : A → C) : DiscreteCat A ⟶ C`, extending a function to a functor. The file header (`:31`) calls this "the left adjoint `Set ⟶ Cat` at the level of a single functor" — accurately, since only the from-direction of the bijection is delivered.
- `Structure/Discrete.v:23`–`:24` mentions the further adjoints in prose only.

Missing: the objects functor itself (no functor of type `… ⟶ Sets` exists on `Cat` or `StrictCat`); the adjunction "discrete ⊣ objects" as an `Adjunction` term, with naturality; the connected-components functor and its adjunction; and the indiscrete (chaotic) category construction together with "objects ⊣ indiscrete". Searches for `chaotic`, `indiscrete` and `codiscrete` find prose only.

## Work to be done

Suggested modules: `Instance/Cat/Objects.v` (the objects functor and the discrete adjunction), `Instance/Indiscrete.v` (the chaotic category and its adjunction), `Instance/Cat/Components.v` (the components functor and its adjunction).

1. Define the objects functor into `Sets`, taking a category to the setoid of its objects with equality (or with isomorphism, if a choice has to be made — the exercise wants the strict version, and `StrictCat` is the natural domain in this library, so state which and say why in the header).
2. Prove `Discrete ⊣ Objects`, packaging the existing extension map with its inverse and the naturality laws.
3. Define the indiscrete category on a set (exactly one arrow in each hom-set, the hom-setoid trivial) and prove `Objects ⊣ Indiscrete`.
4. Define the connected-components functor using the components construction and prove `Components ⊣ Discrete`, completing the string.
5. Sanity-check the string on small examples: components of a discrete category are its objects; the indiscrete category on a two-element set is connected.

In-tree donors: `Instance/Discrete.v`, `Instance/Cat.v`, `Instance/StrictCat.v`, `Instance/Sets.v`, `Structure/Discrete.v`, `Theory/Adjunction.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 9 (book p. 90): all three adjunctions, in the stated order, with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for each of the three adjunctions
- [ ] New files registered in `_CoqProject`
- [ ] The prose claims in `Instance/Discrete.v:31` and `Structure/Discrete.v:23` updated to cite the proved adjunctions
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Indiscrete.v
coqc -R . Category Instance/Cat/Objects.v
coqc -R . Category Instance/Cat/Components.v
make && make todo
```

```coq
Print Assumptions Discrete_Objects_Adjunction.
Print Assumptions Objects_Indiscrete_Adjunction.
Print Assumptions Components_Discrete_Adjunction.
```

Reviewer checks: the header discloses the strictness choice made for the objects functor; all three are genuine `Adjunction` terms, not merely transposition functions.

## Dependencies

- Depends on: maclane:IV.2:def1
- Depends on: #219

<!-- catalog: {"ids":["maclane:IV.2:ex9"],"deps":["maclane:IV.2:def1"]} -->

---8<---

```yaml
title: "MacLane IV.2: Functors adjoint on the right"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.2:def2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 89 (PDF p. 98), the definition of a pair adjoint on the right (attributed to Freyd). Item covered: `maclane:IV.2:def2`.

## Background

A pair of contravariant functors `S̄ : A ⟶ X`, `T̄ : X ⟶ A` is *adjoint on the right* when there is a bijection `A(a, T̄ x) ≅ X(x, S̄ a)` natural in both variables; rewriting the contravariant functors as covariant functors out of the opposite categories turns this into an ordinary adjunction, and Mac Lane warns that adjointness on the right is not in general the same as adjointness on the left. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [Wikipedia: Galois connection](https://en.wikipedia.org/wiki/Galois_connection) for the order-theoretic shadow of the same phenomenon.

## Current state in the library

The reduction target is present, the notion itself is not.

- `Theory/Adjunction.v:130` — `Class Adjunction`, stated for arbitrary functors between arbitrary categories. Because contravariant functors are systematically rendered as functors out of an opposite category, and because `C^op^op = C` holds definitionally (`Construction/Opposite.v`), the type `S^op ⊣ T` already unfolds to `Hom_X(x, S a) ≅ Hom_A(a, T x)` with no glue.
- `Adjunction/Opposite.v:34` — `Opposite_Adjunction : F ⊣ U → U^op ⊣ F^op`, with `Opposite_Adjunction_invol` at `:60` proving `(A^op)^op = A` by `reflexivity`, which is exactly the transposition between the two ways of writing the pair.

Nothing names or states the notion: the contravariant-pair form of the bijection is never written down, no lemma records its equivalence with the opposite-category adjunction, no instance exists, and Mac Lane's non-coincidence warning has no counterpart.

## Work to be done

Suggested module: `Adjunction/Right.v`.

1. Define `AdjointOnTheRight (S : A^op ⟶ X) (T : X^op ⟶ A)` as the natural family of bijections `A(a, T x) ≅ X(x, S a)`, in the library's hom-setoid style, with the two naturality laws stated separately in each variable (mirroring the four `*_adj_nat_*` fields of `Theory/Adjunction.v`).
2. Prove the equivalence with the ordinary adjunction: `AdjointOnTheRight S T ↔ S^op ⊣ T`, and likewise `↔ T^op ⊣ S`, using the definitional involution so that the round trips are `reflexivity` wherever possible.
3. Record the symmetry: the notion is invariant under swapping the two functors, which is the formal content of "adjoint on the right" being a symmetric relation, in contrast to ordinary adjointness.
4. State — and, if a cheap witness is available, exhibit — Mac Lane's warning that a pair adjoint on the right need not be adjoint on the left. If no in-tree counterexample is currently constructible, record the obstruction in the file header rather than leaving the claim implicit.

In-tree donors: `Theory/Adjunction.v`, `Adjunction/Opposite.v`, `Construction/Opposite.v`, `Functor/Opposite.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 (book p. 89), with `≈` discipline (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the definition and for the equivalence with the opposite-category adjunction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Right.v
make && make todo
```

```coq
Print Assumptions AdjointOnTheRight.
Print Assumptions adjoint_on_the_right_iff_op.
```

Reviewer checks: the definition is stated in the contravariant-pair form of the book, not merely as an abbreviation for `S^op ⊣ T`; the symmetry lemma is present; the warning is addressed one way or the other.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.2:def2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: The dual-object functor is adjoint to itself on the right"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.2:construction3]
deps_item_ids: [maclane:IV.2:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 88 (PDF pp. 97–98), the vector-space duality adjunction. Item covered: `maclane:IV.2:construction3`.

## Background

Dualisation into a fixed object is contravariant and self-adjoint on the right: the bijection `C(V, D W) ≅ C(W, D V)` makes `D^op` a left adjoint of `D`, with unit the canonical map into the double dual. For finite-dimensional spaces the two functors are inverse isomorphisms; in general the adjunction is what survives. See [nLab: dual vector space](https://ncatlab.org/nlab/show/dual+vector+space) and [Wikipedia: Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors).

## Current state in the library

Only the functorial skeleton exists, and the one place the double dual appears it is *assumed* invertible — a hypothesis strictly stronger than the situation the book describes.

- `Structure/Monoidal/StarAutonomous.v:229` — `dual (d : C) : C^op ⟶ C`, the internal-hom-into-a-fixed-object functor, the abstract form of `V ↦ C(V, K)`.
- `Structure/Monoidal/StarAutonomous.v:252` — `double_dual (d : C) : C ⟶ C := dual d ◯ (dual d)^op`.
- `Structure/Monoidal/StarAutonomous.v:271` — the class field `star_double_dual` *posits* `x ≅ double_dual d x`. That is precisely what fails in infinite dimension, so this is not an instance of the book's construction.
- `Adjunction/Opposite.v:34` — the op-duality of adjunctions on which the book's rewriting of the bijection rests.

Missing: the self-adjunction itself (neither the bijection `C(V, D W) ≅ C(W, D V)` nor `(dual d)^op ⊣ dual d` is stated or proved); the canonical, not-assumed-invertible morphism `x ⟶ double_dual d x`; and any concrete category of vector spaces in which to instantiate it.

## Work to be done

Suggested module: `Structure/Monoidal/Dual.v` (abstract) plus an instance once a category of vector spaces exists.

1. In a symmetric monoidal closed base (`SymMonClosed`, `Structure/Monoidal/StarAutonomous.v:109`), define the canonical dualisation morphism `η_x : x ⟶ (x ⇒ d) ⇒ d` as the transpose of the symmetry-twisted evaluation, and prove it natural. This is the missing primitive: today the double dual exists only as a functor and only inside a class that already assumes `η` invertible.
2. Prove the symmetric bijection `C(x, y ⇒ d) ≅ C(y, x ⇒ d)`, natural in both variables, and package it as `(dual d)^op ⊣ dual d`, using the "adjoint on the right" notion.
3. Identify the unit with `η` and the counit with `η^op`, as Mac Lane does.
4. Record that when `η` is invertible the adjunction upgrades to an equivalence (and, in the star-autonomous case, that this is exactly the standing assumption), so the relationship with the existing star-autonomous development is explicit rather than implicit.
5. Instantiate for finite-dimensional vector spaces once that category is available, recovering the isomorphism-of-categories statement.

In-tree donors: `Structure/Monoidal/StarAutonomous.v`, `Structure/Monoidal/Closed.v`, `Structure/Monoidal/Symmetric.v`, `Adjunction/Opposite.v`, `Theory/Isomorphism.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 (book p. 88), including the explicit unit and counit, with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the canonical double-dual morphism and for the self-adjunction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Structure/Monoidal/Dual.v
make && make todo
```

```coq
Print Assumptions dual_self_adjoint_on_the_right.
Print Assumptions double_dual_unit.
```

Reviewer checks: the canonical double-dual morphism is constructed, not assumed invertible; the adjunction is stated over `SymMonClosed`, not over the cartesian-bundled `ClosedMonoidal`, since a cartesian base would trivialise the example.

## Dependencies

- Depends on: maclane:IV.2:def2
- Depends on: #237
- Depends on: #244

<!-- catalog: {"ids":["maclane:IV.2:construction3"],"deps":["maclane:IV.2:def2"]} -->

---8<---

```yaml
title: "MacLane IV.2: The forgetful functor from R-modules to abelian groups has both adjoints"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex2]
deps_item_ids: [maclane:IV.6:construction1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 89 (PDF p. 98), Exercise 2. Item covered: `maclane:IV.2:ex2`.

## Background

Forgetting the module structure of an `R`-module has a left adjoint, extension of scalars along `Z ⟶ R`, and a right adjoint, coextension of scalars into the abelian group of additive maps out of `R`. See [nLab: extension of scalars](https://ncatlab.org/nlab/show/extension+of+scalars) and [Wikipedia: Change of rings](https://en.wikipedia.org/wiki/Change_of_rings).

## Current state in the library

Absent, and the ambient categories do not exist. `ls Instance/` shows no `Ab` and no `R-Mod`; the only concrete algebraic category in the tree is `Instance/CMon.v` (commutative monoids over setoids, with `CMon_Forget : CMon ⟶ Sets` at `:169` and no left adjoint). Every occurrence of "R-Mod" and "module" in `.v` files is background-essay prose, e.g. `Structure/Abelian.v:68`–`:69` and `Theory/Equivalence.v:79`. There is no tensor product over a ring and no additive-map hom construction.

## Work to be done

Suggested modules: `Instance/Module/BaseChange.v` (or wherever the module categories land once they exist).

1. Once the categories of abelian groups and of `R`-modules are available, define the forgetful functor between them.
2. Construct the extension-of-scalars functor `A ↦ R ⊗_Z A` and prove it left adjoint to the forgetful functor, with unit `a ↦ 1 ⊗ a`.
3. Construct the coextension functor `A ↦ Hom_Z(R, A)` with its `R`-action by translation, and prove it right adjoint to the forgetful functor, with counit evaluation at `1`.
4. Note the shape of the argument: both adjunctions follow from the tensor-hom adjunction over `Z` together with the module axioms, so the proof should reuse the module tensor-hom development rather than repeating it.

In-tree donors: `Theory/Universal/Arrow.v` (the universal-arrow route to an adjunction), `Structure/Preadditive.v`, `Instance/CMon.v` as the template for a setoid-based algebraic category.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 2 (book p. 89), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for both adjunctions
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Module/BaseChange.v
make && make todo
```

```coq
Print Assumptions extension_of_scalars_adjunction.
Print Assumptions coextension_of_scalars_adjunction.
```

Reviewer checks: both adjoints are delivered (the exercise's point is that there are two); the unit and counit are the maps named above.

## Dependencies

- Depends on: #256
- Depends on: #258
- Depends on: maclane:IV.6:construction1

<!-- catalog: {"ids":["maclane:IV.2:ex2"],"deps":["maclane:IV.6:construction1"]} -->

---8<---

```yaml
title: "MacLane IV.2: The universal enveloping algebra is left adjoint to the commutator functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex3]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 89 (PDF p. 98), Exercise 3. Item covered: `maclane:IV.2:ex3`.

## Background

Sending an associative algebra to the Lie algebra on the same module with the commutator bracket has a left adjoint, the universal enveloping algebra; the Poincaré–Birkhoff–Witt theorem is what makes the unit injective. See [nLab: universal enveloping algebra](https://ncatlab.org/nlab/show/universal+enveloping+algebra) and [Wikipedia: Universal enveloping algebra](https://en.wikipedia.org/wiki/Universal_enveloping_algebra).

## Current state in the library

Absent. Searches for `Lie`, `enveloping`, `Poincaré` and `Birkhoff` find only incidental prose: `Theory/Lawvere.v:87` lists Lie algebras among algebraic theories, and `Structure/Group.v:46`, `:93` mention Lie groups and Hopf algebras in a header essay. There is no category of associative algebras, no category of Lie algebras, no commutator functor and no enveloping-algebra construction.

Worth recording for whoever takes this on: the in-tree machinery in which these categories could eventually be *presented* is the Lawvere-theory spine (`Theory/Lawvere.v`, with `Theory/Lawvere/Model.v`'s `Models T C`), but no such theory is instantiated, so this is not partial coverage.

## Work to be done

Suggested modules: `Instance/Lie.v` and `Adjunction/Enveloping.v`, or a Lawvere-theory presentation under `Instance/Lawvere/`.

1. Build the category of associative unital algebras over a commutative ring and the category of Lie algebras (module plus alternating bilinear bracket satisfying Jacobi), as setoid-based categories in the `Instance/CMon.v` style.
2. Define the commutator functor from associative algebras to Lie algebras.
3. Construct the enveloping algebra as the quotient of the tensor algebra by the commutator relations, using the existing quotient machinery (`Construction/Quotient.v` is a hom-congruence quotient, so a genuinely object-level quotient may have to be built; say so in the header if it is).
4. Prove the adjunction by the universal property of the quotient — note that the adjunction itself does *not* need PBW; PBW is what shows the unit is injective, and should be stated separately (and may be deferred, with the deferral disclosed).

In-tree donors: `Theory/Universal/Arrow.v`, `Theory/Lawvere.v`, `Theory/Lawvere/Model.v`, `Construction/Quotient.v`, `Instance/CMon.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 3 (book p. 89), with `≈` discipline
- [ ] The file header discloses whether PBW is proved or deferred
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the adjunction
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Lie.v
coqc -R . Category Adjunction/Enveloping.v
make && make todo
```

```coq
Print Assumptions enveloping_adjunction.
```

Reviewer checks: the adjunction is proved without appealing to PBW; if PBW is deferred, the header says so and no statement silently depends on it.

## Dependencies

- Depends on: #258
- Depends on: #293

<!-- catalog: {"ids":["maclane:IV.2:ex3"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: Adjoining an identity to a ring as a left adjoint"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex4]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 89 (PDF p. 98), Exercise 4. Item covered: `maclane:IV.2:ex4`.

## Background

The Dorroh extension, which freely adjoins an identity to a ring without one, is left adjoint to the functor forgetting the identity from unital rings to rngs. See [nLab: rng](https://ncatlab.org/nlab/show/rng) and [Wikipedia: Rng (algebra)](https://en.wikipedia.org/wiki/Rng_(algebra)).

## Current state in the library

Absent. There is no category of rings, unital or otherwise: `Structure/Monoid.v` and `Structure/Group.v` are about monoid and group *objects* internal to a monoidal or cartesian category, not about `Rng`. Searches for "adjoin … identity", "unitalization" and "Dorroh" return nothing (the only near-match tree-wide is `Adjunction/Compose.v:29`, "the identity functor is self-adjoint"). `Instance/CMon.v` is the only concrete algebraic category and carries no analogous construction.

## Work to be done

Suggested module: `Instance/Rng.v` plus `Adjunction/Unitalization.v`.

1. Build the category of rngs (rings without an assumed identity) and the category of unital rings, with the forgetful functor between them.
2. Construct the Dorroh extension `R ↦ Z × R` with the twisted multiplication, and prove it is a unital ring.
3. Prove the adjunction, with unit the inclusion `r ↦ (0, r)`; the transposition is the standard extension of a rng homomorphism to the adjoined identity.
4. Record the two obvious corollaries: the unit is monic, and the forgetful functor is faithful (unlike the exterior-algebra case in the neighbouring exercise).

In-tree donors: `Theory/Universal/Arrow.v`, `Instance/CMon.v` as the setoid-algebra template, `Structure/Preadditive.v` for the additive-group part.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 4 (book p. 89), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the adjunction
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Rng.v
coqc -R . Category Adjunction/Unitalization.v
make && make todo
```

```coq
Print Assumptions unitalization_adjunction.
```

Reviewer checks: the unit is the inclusion, and the transposition is proved unique.

## Dependencies

- Depends on: #257

<!-- catalog: {"ids":["maclane:IV.2:ex4"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: A monoid is a group exactly when its translations have adjoints"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex5]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 5. Item covered: `maclane:IV.2:ex5`.

## Background

Viewing a monoid as a discrete category with multiplication as a bifunctor, left and right translation are endofunctors; when the monoid is a group, inversion supplies right adjoints for them, and the exercise asks whether the converse holds. See [nLab: delooping](https://ncatlab.org/nlab/show/delooping) and [Wikipedia: Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors).

## Current state in the library

Absent. Nothing constructs a monoid as a *discrete* category with its multiplication as a bifunctor. The candidates all miss: `Structure/Group.v` is about group objects internal to a cartesian category; `Instance/Comp.v:382`'s `Group := Algebra GroupOp GroupEq` is universal-algebra data; `Construction/Groupoid.v` is the core groupoid; and `Theory/Bicategory/OneObject.v` deloops a *monoidal category* into a bicategory, not a monoid into a discrete category. No translation functor exists, and nothing asserts that a translation has an adjoint.

## Work to be done

Suggested module: `Instance/Monoid/Translation.v`.

1. Build the discrete category on the carrier of a monoid, together with the multiplication bifunctor. Note the deliberate difference from the usual delooping: here the objects are the elements, not a single object, so the hom-type is equality and functoriality is a coherence condition on multiplication.
2. Define the two translation endofunctors and prove them functorial.
3. Prove that for a group the translations have right adjoints given by multiplication by the inverse, with unit and counit the identity (the discrete setting collapses the triangle identities to the group laws).
4. Address the converse, which is the interesting half: if every left translation of a monoid has a right adjoint, the monoid is a group. State the result if it holds in this discrete formulation, or exhibit the obstruction; either way, record the finding in the header rather than leaving the exercise's question open in code.

In-tree donors: `Instance/Discrete.v`, `Functor/Bifunctor.v`, `Theory/Adjunction.v`, `Instance/Comp.v` for a concrete monoid/group presentation.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 5 (book p. 90), with `≈` discipline
- [ ] The converse direction is either proved or its failure documented in the file header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the translation adjunctions
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Monoid/Translation.v
make && make todo
```

```coq
Print Assumptions translation_adjunction_of_group.
```

Reviewer checks: the category really is discrete (homs are equalities), matching the exercise; the converse is addressed.

## Dependencies

- Depends on: #220

<!-- catalog: {"ids":["maclane:IV.2:ex5"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: The cokernel-pair functor is left adjoint to the equalizer functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex10]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 10. Item covered: `maclane:IV.2:ex10`.

## Background

In a category with cokernel pairs and equalizers, taking an arrow to its cokernel pair is a functor from the arrow category to the category of parallel pairs, and it is left adjoint to the functor taking a parallel pair to its equalizing arrow. See [nLab: cokernel pair](https://ncatlab.org/nlab/show/cokernel+pair) and [nLab: equalizer](https://ncatlab.org/nlab/show/equalizer).

## Current state in the library

Both endpoints are expressible; nothing in between exists.

- `Construction/Arrow.v:110` — `Arrow {C} : Category := (Id[C] ↓ Id[C])`, the arrow category.
- `Instance/Parallel.v:80` — the walking parallel pair, with `Structure/Equalizer.v` giving equalizers as limits over it and `Structure/Equalizer/Fork.v` the elementary fork API.
- `Structure/Regular.v:46` — `kernel_pair`, a chosen pullback of `f` along `f`, object-level only, with no functoriality and no dual.

There is no cokernel-pair construction at all (searches for `cokernel pair` and `CokernelPair` return nothing; `Structure/Kernel.v`'s cokernels are the zero-object notion, a different concept), no equalizer functor, and no adjunction between them.

## Work to be done

Suggested module: `Adjunction/CokernelPair.v`.

1. Define the cokernel pair of an arrow as the pushout of the arrow against itself, and prove it functorial on the arrow category.
2. Define the equalizer functor from the category of parallel pairs (functors out of `Instance/Parallel.v`'s shape, or the equivalent explicit category) to the arrow category, using the equalizing arrow as the object part.
3. Prove the adjunction, transposing "a map from the cokernel pair" into "a map into the equalizer" by the two universal properties.
4. Record the two units: the unit at an arrow is the comparison into the equalizer of its cokernel pair, and the counit is the coequalizing comparison; both are worth naming, since the exercise is really about them.

In-tree donors: `Construction/Arrow.v`, `Instance/Parallel.v`, `Structure/Pushout.v`, `Structure/Equalizer/Fork.v`, `Structure/Coequalizer.v`, `Structure/Regular.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 10 (book p. 90), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for both functors and for the adjunction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/CokernelPair.v
make && make todo
```

```coq
Print Assumptions CokernelPair_Equalizer_Adjunction.
```

Reviewer checks: the cokernel-pair functor is genuinely functorial (both laws proved, not `Program`-defaulted); the adjunction direction matches the book.

## Dependencies

- Depends on: #323

<!-- catalog: {"ids":["maclane:IV.2:ex10"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: A left adjoint to the coslice projection"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex11]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 11. Item covered: `maclane:IV.2:ex11`.

## Background

If a category has finite coproducts, the projection from the coslice under an object has a left adjoint sending an object to the coproduct injection into the coproduct with that object. See [nLab: under category](https://ncatlab.org/nlab/show/under+category) and [Wikipedia: Comma category](https://en.wikipedia.org/wiki/Comma_category).

## Current state in the library

The projection exists; the adjoint does not.

- `Construction/Slice.v:169` — `Coslice (C : Category) (c : C) : Category`, with `Comma_Coslice` at `:181` identifying it with the corresponding comma category.
- `Construction/Comma.v:204` — `comma_proj2 : Comma ⟶ B`, which through `Comma_Coslice` *is* the projection of the exercise.
- `Construction/Comma/Adjunction.v` contains the Lawvere comma-isomorphism characterisation of adjunctions, not a projection-adjoint result.

Missing entirely: the functor sending an object `c` to the coproduct injection `a ⟶ a + c`, the adjunction, and the coproduct-injection unit. A search over slice, coslice and comma files for `⊣` finds only the commented-out slice base-change stub.

## Work to be done

Suggested module: `Construction/Slice/Coslice.v` (or an extension of `Construction/Slice.v`).

1. Define the functor `C ⟶ (a ↓ C)` taking `c` to the injection `a ⟶ a + c` and an arrow `f : c ⟶ c'` to `id + f`, proving functoriality from the coproduct universal property.
2. Prove it left adjoint to the projection, with the transposition given by the copairing.
3. Name the unit and counit: the unit at `c` is the right injection, and the counit at an object `a ⟶ x` of the coslice is the copairing of that structure map with the identity.
4. State the dual for slices and products, since the library will want it and it is one `Opposite` transport away; deliver it covariantly.

In-tree donors: `Construction/Slice.v`, `Construction/Comma.v`, `Structure/Cocartesian.v`, `Adjunction/Opposite.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 11 (book p. 90), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the adjunction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Slice/Coslice.v
make && make todo
```

```coq
Print Assumptions Coslice_Projection_Adjunction.
```

Reviewer checks: the unit is literally the coproduct injection; the dual slice statement, if delivered, has no residual `^op` in its type.

## Dependencies

- Depends on: #289

<!-- catalog: {"ids":["maclane:IV.2:ex11"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.2: Copowers and powers as an adjunction with a parameter"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.2:ex12, maclane:IV.7:ex1]
deps_item_ids: [maclane:IV.7:thm3]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.2, book p. 90 (PDF p. 99), Exercise 12, and §IV.7, book p. 102 (PDF p. 111), Exercise 1. Items covered: `maclane:IV.2:ex12`, `maclane:IV.7:ex1`.

## Background

For a fixed set, the copower functor is left adjoint to the power functor, and the defining bijection is naturally read as an adjunction with the set as parameter. See [nLab: copower](https://ncatlab.org/nlab/show/copower) and [nLab: two-variable adjunction](https://ncatlab.org/nlab/show/two-variable+adjunction).

## Current state in the library

Absent. Searches for `copower`, `cotensor` and `tensoring` return nothing; the only "power" notions in the tree are Lawvere finite powers (`law_pow`), the endomorphism-operad `pow`, and topos power objects `Pow a := Ω ^ a` — none is the set-indexed power functor.

Two near-misses, neither of which is coverage: `Structure/Limit/Product.v:93`'s `iprod` gives set-indexed products over `Instance/Discrete.v`'s `DiscreteCat`, so the power *object* is one step away; and `Structure/Limit/Weighted.v:101`'s `WeightedLimit`, instantiated at the terminal shape with a constant weight, is the power by definition (dually `WeightedColimit` at `:370` is the copower). Neither functor is constructed and no part of the bijection is proved.

## Work to be done

Suggested module: `Structure/Limit/Power.v`.

1. Define the power and copower of an object by a set, either as the indexed product and coproduct over the discrete category on that set, or as the weighted limit and colimit at the terminal shape; pick one and prove the two presentations agree.
2. Build the power and copower functors on the object variable and prove functoriality.
3. Prove the adjunction: the copower functor is left adjoint to the power functor, with the transposition given by the indexed universal properties.
4. Extend to the parameter: a function between index sets induces transformations between the copower and power functors, and these two are conjugate; conclude that the copower/power bijection is an adjunction with the index set as parameter, natural in all three variables.

In-tree donors: `Structure/Limit/Product.v`, `Structure/Limit/Weighted.v`, `Instance/Discrete.v`, `Structure/Cocartesian.v`, `Theory/Adjunction.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.2 Exercise 12 and §IV.7 Exercise 1 (book pp. 90, 102), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the two functors, the adjunction, and the parameter naturality
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Limit/Power.v
make && make todo
```

```coq
Print Assumptions Copower_Power_Adjunction.
```

Reviewer checks: the two presentations of the power (indexed product vs weighted limit) are proved to agree, so the file does not fork the API; the parameter half is genuinely proved, not asserted.

## Dependencies

- Depends on: maclane:IV.7:thm3
- Depends on: #321
- Depends on: #320

<!-- catalog: {"ids":["maclane:IV.2:ex12","maclane:IV.7:ex1"],"deps":["maclane:IV.7:thm3"]} -->

---8<---

```yaml
title: "MacLane IV.3: Fullness and faithfulness of a right adjoint through its counit"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.3:thm1, maclane:IV.3:lem1, maclane:IV.3:ex5]
deps_item_ids: [maclane:IV.3:remark1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book pp. 90–92 (PDF pp. 99–101), Theorem 1 with its supporting lemma, and Exercise 5. Items covered: `maclane:IV.3:thm1`, `maclane:IV.3:lem1`, `maclane:IV.3:ex5`.

## Background

A right adjoint is faithful exactly when every counit component is epi, and full exactly when every counit component is a split mono; combining, it is fully faithful exactly when the counit is an isomorphism. The proof runs through a Yoneda-transfer lemma: the natural transformation induced by an arrow is monic exactly when the arrow is epi, and epi exactly when the arrow is split monic. See [nLab: fully faithful functor](https://ncatlab.org/nlab/show/fully+faithful+functor) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Only one instance of one direction is present, and it is a special case.

- `Construction/Reflective.v:92` — `reflective_counit_iso`: for a reflective subcategory (full inclusion with a left adjoint), the counit is a componentwise isomorphism, the inverse being the fullness-lifted unit. `Construction/Reflective/Idempotent.v:175` (`reflective_counit_IsIso`) restates it.
- `Theory/Equivalence/Adjoint.v:73` — `adj_equiv_counit_iso`, again a special case with extra hypotheses.
- `Theory/Adjunction.v:311` — `adj_monic`, the only place fullness/faithfulness meets an adjunction: if the *left* adjoint is faithful and `f` is monic, the transpose is left-cancellable. This is the categorical dual of half of Exercise 5, in the opposite orientation, and is never instantiated at `Opposite_Adjunction` to reach the book's orientation.
- The `Epic`/`Monic` vocabulary (`Theory/Morphisms.v`) and the `Full`/`Faithful` classes (`Theory/Functor.v:331`, `:342`) exist but are never connected through a counit; a whole-tree inspection of every `Epic` occurrence finds none touching a counit.
- The Yoneda development (`Functor/Hom/Yoneda.v:133`, `:182`, `:231`, `:253`) proves the bijection and the embeddings' full faithfulness, but contains no monic/epi transfer; there are no `Monic`/`Epic` occurrences in `Functor/Hom.v`, `Functor/Hom/Yoneda.v`, `Functor/Representable.v`, `Theory/Natural/Transformation.v` or `Instance/Fun.v`.

Missing: both directions of "faithful ⟺ counit epi"; both directions of "full ⟺ counit split monic"; the combined "fully faithful ⟺ counit iso" for an arbitrary right adjoint; the Yoneda transfer lemma; and the transpose formulation of Exercise 5 in the book's orientation, together with its converse.

## Work to be done

Suggested modules: `Functor/Hom/Transfer.v` (the lemma) and `Adjunction/FullFaithful.v` (the theorem).

1. Prove the transfer lemma: for `f : b ⟶ a`, the induced transformation `A(a,−) ⟹ A(b,−)` is monic in the functor category exactly when `f` is epi, and epi exactly when `f` is split monic. Use the Yoneda bijection already in `Functor/Hom/Yoneda.v`, and the pointwise characterisation of monos and epis in a functor category.
2. Prove Theorem 1 (i): the right adjoint is faithful ⟺ every counit component is epi. Both directions.
3. Prove Theorem 1 (ii): the right adjoint is full ⟺ every counit component is a split mono. Both directions.
4. Conclude: fully faithful ⟺ every counit component is an isomorphism, and check that `reflective_counit_iso` becomes a corollary rather than an independent proof.
5. Prove Exercise 5 in the book's orientation — the right adjoint is faithful ⟺ the inverse transpose carries epis to epis — and relate it to `adj_monic` by the opposite adjunction, so the two are visibly the same fact.

In-tree donors: `Functor/Hom/Yoneda.v`, `Theory/Morphisms.v`, `Theory/Functor.v` (`Full`, `Faithful`), `Theory/Adjunction.v`, `Adjunction/Opposite.v`, `Construction/Reflective.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 Theorem 1, its lemma, and Exercise 5 (book pp. 90–92); `≈` discipline (never `=` on morphisms)
- [ ] Both directions of each biconditional are proved
- [ ] `Construction/Reflective.v:92` re-derived from, or explicitly related to, the general theorem
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the transfer lemma and for each part of the theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated (flagship-level: this is the standard tool for recognising reflective subcategories)

## Verification

```bash
coqc -R . Category Functor/Hom/Transfer.v
coqc -R . Category Adjunction/FullFaithful.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions right_adjoint_faithful_iff_counit_epic.
Print Assumptions right_adjoint_full_iff_counit_split_monic.
```

Reviewer checks: the statements quantify over an arbitrary adjunction, not over a subcategory inclusion; "split monic" is the library's `Section`/split notion from `Theory/Morphisms.v`, not plain `Monic`.

## Dependencies

- Depends on: maclane:IV.3:remark1
- Depends on: #316

<!-- catalog: {"ids":["maclane:IV.3:thm1","maclane:IV.3:lem1","maclane:IV.3:ex5"],"deps":["maclane:IV.3:remark1"]} -->

---8<---

```yaml
title: "MacLane IV.3: Fullness of an adjoint and invertibility of the unit-counit composites"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.3:ex3, maclane:IV.3:ex6]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 92 (PDF p. 101), Exercises 3 and 6. Items covered: `maclane:IV.3:ex3`, `maclane:IV.3:ex6`.

## Background

Fullness of one of the two adjoints forces good behaviour of the whiskered unit and counit: the composite `Gε` becomes invertible with inverse `ηG`, and monic unit components become epi. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [nLab: fully faithful functor](https://ncatlab.org/nlab/show/fully+faithful+functor).

## Current state in the library

Only one of the two required inverse laws is available, and only unconditionally.

- `Theory/Adjunction.v:288` — `fmap_counit_unit : fmap[U] ε ∘ η ≈ id[U x]`, one of the two triangle identities, holding for every adjunction. This is one half of Exercise 6.
- `Construction/Reflective.v:92` — `reflective_counit_iso`, two-sided invertibility of the counit against the unit, but only for a full reflective-subcategory inclusion: a stronger conclusion (the counit itself is invertible, not just its image) under stronger hypotheses (the right adjoint is full *and* faithful).

Missing: the other law `ηG ∘ Gε ≈ id` under the hypothesis that one of the two adjoints is full, hence the invertibility of `Gε` for an arbitrary adjunction; and the whole of Exercise 3 — no lemma anywhere asserts anything about an adjunction unit component being monic or epic (the apparent hits are monoidal-unitor isomorphism cancellations and equivalence-unit cancellations, which are unrelated objects).

## Work to be done

Suggested module: `Adjunction/Fullness.v`.

1. Prove Exercise 6: for an adjunction in which either adjoint is full, the whiskered counit `Gε : GFG ⟹ G` is invertible with inverse the whiskered unit `ηG`. The missing direction is `ηG ∘ Gε ≈ id`; obtain it by transposing across the adjunction and using fullness to lift the comparison.
2. Prove Exercise 3 in Mac Lane's orientation: for an adjunction whose left-listed functor is full and whose unit components are monic, every unit component is also epi.
3. State both results so that `reflective_counit_iso` and the adjoint-equivalence counit isomorphism become instances, rather than parallel developments.

In-tree donors: `Theory/Adjunction.v` (`unit`, `counit`, both triangle corollaries), `Theory/Functor.v` (`Full`), `Theory/Morphisms.v` (`Monic`, `Epic`), `Construction/Reflective.v`, `Theory/Equivalence/Adjoint.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 Exercises 3 and 6 (book p. 92), with `≈` discipline
- [ ] The hypothesis is "either adjoint is full", as the book states, not the stronger "fully faithful"
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for both exercises
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Fullness.v
make && make todo
```

```coq
Print Assumptions whiskered_counit_iso_of_full.
```

Reviewer checks: the new inverse law is proved, not re-derived from the existing triangle identity; the statements are about `Gε` and `ηG` as natural transformations, not only componentwise.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.3:ex3","maclane:IV.3:ex6"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.3: Monomorphisms and epimorphisms in a functor category are pointwise"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.3:remark1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 91 (PDF p. 100), the remark on pointwise monos and epis. Item covered: `maclane:IV.3:remark1`.

## Background

A natural transformation with all components monic (respectively epic) is monic (epic) in the functor category, and over sets the converse holds too, because the relevant pullback and pushout are computed pointwise. See [nLab: functor category](https://ncatlab.org/nlab/show/functor+category) and [nLab: epimorphism](https://ncatlab.org/nlab/show/epimorphism).

## Current state in the library

Absent. `Instance/Fun.v` and the files under `Theory/Natural/` contain no occurrence of `Epic` or `Monic`: the functor-category development states nothing about monos or epis, pointwise or otherwise. Searches for "pointwise" find only pointwise products, pointwise monoid laws and pointwise monoidal structure. The only structural result on a functor category is `Instance/Fun/Cartesian.v:111` (`Functor_Category_Cartesian`, pointwise products).

## Work to be done

Suggested module: `Instance/Fun/Morphisms.v`.

1. Prove the easy direction in full generality: componentwise monic implies monic in `[C, D]`, and componentwise epic implies epic.
2. Prove the converse for `[C, Sets]`, using the pointwise computation of the relevant limit and colimit: a monomorphism is detected by its kernel pair and an epimorphism by its cokernel pair, both of which are computed componentwise in a functor category into sets.
3. Add the corollaries the rest of the library wants: a natural transformation is an isomorphism exactly when all components are (if this is not already available, state it here); and monos in a presheaf category are the pointwise injections, which the subobject-classifier work will need.
4. Keep the general-`D` and the `Sets` statements clearly separated, since only the latter is a biconditional.

In-tree donors: `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Theory/Morphisms.v`, `Instance/Sets.v` (`injectivity_is_monic` at `:369`, `surjectivity_is_epic` at `:429`), `Structure/Regular.v` (kernel pairs), `Structure/Pushout.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 (book p. 91): implication in general, biconditional over sets; `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for each direction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Fun/Morphisms.v
make && make todo
```

```coq
Print Assumptions pointwise_monic_is_monic.
Print Assumptions sets_functor_monic_iff_pointwise.
```

Reviewer checks: the general direction does not silently assume the codomain is `Sets`; the `Sets` converse uses the pointwise (co)limit computation rather than an ad hoc argument.

## Dependencies

- Depends on: #323
- Depends on: #339

<!-- catalog: {"ids":["maclane:IV.3:remark1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.3: Concrete reflective and coreflective subcategories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.3:construction1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 92 (PDF p. 101), the examples of reflective and coreflective subcategories. Item covered: `maclane:IV.3:construction1`.

## Background

The standard examples: abelian groups are reflective in groups with abelianisation as reflector; complete metric spaces are reflective in metric spaces with completion; compact Hausdorff spaces are reflective in completely regular spaces with the Stone–Čech compactification; torsion abelian groups are coreflective in abelian groups with the torsion subgroup. See [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and [nLab: Stone–Čech compactification](https://ncatlab.org/nlab/show/Stone-Cech+compactification).

## Current state in the library

The machinery exists; not one of the four examples does.

- `Construction/Reflective.v:60` — `Record Reflective`, packaging a full subcategory with a reflector and the adjunction; `Construction/Reflective.v:92` — `reflective_counit_iso`.
- `Construction/Reflective/Idempotent.v:345` — `Idempotent_Reflective`, the one in-tree instance of the record, built from an idempotent monad rather than from a concrete category.
- `Construction/Subcategory.v` — the subcategory and inclusion vocabulary.

Searches for abelianisation, torsion, Stone, compactification and metric spaces return nothing but header prose; `ls Instance/*.v` confirms there is no `Grp`, `Ab`, `Top` or `Met`, the nearest algebraic category being `Instance/CMon.v`.

## Work to be done

Suggested modules: under `Instance/`, one file per example, e.g. `Instance/Grp/Abelianization.v`.

1. Abelian groups in groups: the reflector is the quotient by the commutator subgroup, the unit the quotient projection; the transposition is the universal property of that quotient. This is the cheapest of the four and should land first.
2. Torsion abelian groups in abelian groups: the coreflector is the torsion subgroup, the counit its inclusion. Note this is a *co*reflection, so the delivered statement should use the coreflective packaging rather than the reflective one with an `op` in the type.
3. Complete metric spaces in metric spaces with uniformly continuous maps: the reflector is completion. The universal-arrow form of this is already a filed obligation, so the increment here is the reflectivity packaging.
4. Compact Hausdorff spaces in completely regular spaces: the Stone–Čech compactification. This is much the largest of the four and may be split off if it dominates the PR.

In-tree donors: `Construction/Reflective.v`, `Construction/Subcategory.v`, `Theory/Universal/Arrow.v`, `Instance/CMon.v` as the setoid-algebra template.

## Definition of Done

- [ ] Statement fidelity to §IV.3 (book p. 92), with `≈` discipline
- [ ] Each example is delivered as an inhabitant of the existing `Reflective` record (or its coreflective dual), not as a bespoke re-statement
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for each example (stdlib axioms permitted in `Instance/`, per docs/AXIOMS.md, but they must be enumerated)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: these are the first concrete witnesses of the reflective-subcategory machinery

## Verification

```bash
coqc -R . Category Instance/Grp/Abelianization.v
make && make todo
```

```coq
Print Assumptions Ab_Reflective_in_Grp.
```

Reviewer checks: each reflector's unit is the map Mac Lane names; the coreflective example is stated covariantly.

## Dependencies

- Depends on: #229
- Depends on: #255
- Depends on: #256
- Depends on: #259
- Depends on: #308

<!-- catalog: {"ids":["maclane:IV.3:construction1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.3: Torsion-free abelian groups form a reflective subcategory"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.3:ex2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 92 (PDF p. 101), Exercise 2. Item covered: `maclane:IV.3:ex2`.

## Background

Quotienting an abelian group by its torsion subgroup is left adjoint to the inclusion of the full subcategory of torsion-free abelian groups, making that subcategory reflective. See [nLab: torsion subgroup](https://ncatlab.org/nlab/show/torsion+subgroup) and [Wikipedia: Torsion-free abelian group](https://en.wikipedia.org/wiki/Torsion-free_abelian_group).

## Current state in the library

Absent, and the ambient category is missing. A whole-tree search for "torsion" returns nothing; there is no `Ab`, `Grp` or `AbGrp` instance. `Instance/CMon.v` (commutative monoids over setoids) is the nearest algebraic hom-category and carries no torsion theory; `Structure/Group.v` is about internal group objects, not the category of groups. The reflective-subcategory *machinery* does exist (`Construction/Reflective.v`); what is missing is any concrete algebraic instance of it, of which this is one.

## Work to be done

Suggested module: `Instance/Ab/TorsionFree.v`.

1. Define the torsion subgroup of an abelian group and prove it is a subgroup.
2. Cut out the full subcategory of torsion-free abelian groups using `Construction/Subcategory.v`, and prove the inclusion full and faithful.
3. Build the reflector `A ↦ A / T(A)` and prove the quotient is torsion-free.
4. Prove the adjunction (every homomorphism into a torsion-free group kills the torsion subgroup, hence factors uniquely), and package the whole as an inhabitant of `Reflective`.

In-tree donors: `Construction/Reflective.v`, `Construction/Subcategory.v`, `Theory/Universal/Arrow.v`, `Instance/CMon.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 Exercise 2 (book p. 92), with `≈` discipline
- [ ] Delivered as an inhabitant of the existing `Reflective` record
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` reported and any stdlib axioms enumerated per docs/AXIOMS.md
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Ab/TorsionFree.v
make && make todo
```

```coq
Print Assumptions TorsionFree_Reflective.
```

Reviewer checks: the subcategory is full; the reflector's unit is the quotient projection.

## Dependencies

- Depends on: #256

<!-- catalog: {"ids":["maclane:IV.3:ex2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.3: Posets are reflective in preorders, and T0-spaces in Top"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.3:ex4]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 92 (PDF p. 101), Exercise 4. Item covered: `maclane:IV.3:ex4`.

## Background

Collapsing the equivalence classes of a preorder yields a poset, and this is the reflector of the full inclusion of posets into preorders; the topological analogue is the Kolmogorov quotient exhibiting T0-spaces as reflective in all spaces. See [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and [Wikipedia: Kolmogorov space](https://en.wikipedia.org/wiki/Kolmogorov_space).

## Current state in the library

Absent, and both ambient categories are missing.

- `Instance/Proset.v:20` builds a *single* preordered set as a thin category (`Proset {A R} (P : PreOrder R) : Category`) and its own header says "See also `Ord`, for the category of preordered sets" — no such instance exists in the tree. `Instance/Poset.v` is likewise a single poset.
- There is no `Instance/Top.v` and no topology development at all, so the second half has no ambient category either.

Both halves are unstatable today; nothing about these categories is foundationally obstructed here, they are simply not built.

## Work to be done

Suggested modules: `Instance/Ord.v` (the category of preorders and monotone maps), `Instance/Ord/Poset.v`, and a topological counterpart once `Top` exists.

1. Build the category of preordered sets with monotone maps, and the full subcategory of posets.
2. Construct the poset reflection: quotient the carrier by the symmetric part of the preorder, as a setoid quotient (no quotient axiom), and prove the induced order antisymmetric.
3. Prove the adjunction and package it as `Reflective`.
4. For the topological half, construct the Kolmogorov quotient and prove the analogous reflection. This half may be split into its own PR if `Top` lands separately.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Construction/Reflective.v`, `Construction/Subcategory.v`, `Construction/Quotient.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 Exercise 4 (book p. 92), with `≈` discipline
- [ ] The quotient is a setoid construction, with no new axiom
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the poset reflection
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Ord.v
coqc -R . Category Instance/Ord/Poset.v
make && make todo
```

```coq
Print Assumptions Poset_Reflective_in_Ord.
```

Reviewer checks: the new `Ord` really is the category of *all* preorders with monotone maps, not a single preorder as a thin category — the distinction is exactly what `Instance/Proset.v:20` flags.

## Dependencies

- Depends on: #223
- Depends on: #259

<!-- catalog: {"ids":["maclane:IV.3:ex4"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.3: A full reflective subcategory inherits limits"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.3:ex7]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3, book p. 92 (PDF p. 101), Exercise 7. Item covered: `maclane:IV.3:ex7`.

## Background

If a full reflective subcategory sits inside a category where a diagram has a limit, that limit lies in the subcategory: the inclusion creates limits, because it is a right adjoint and is fully faithful. See [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and [nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library

Absent. `Construction/Reflective.v` is 115 lines and ends at `reflective_counit_iso`; neither it, nor `Construction/Reflective/Idempotent.v`, nor `Construction/Localization.v`, nor `Construction/Localization/Universal.v` contains any occurrence of `Limit` or `Complete`. `Construction/Subcategory.v` has no limit content.

The final step of the classical proof *is* present but never assembled: `Theory/Equivalence/Limit.v:401` (`ff_reflects_limit`) says a fully faithful functor reflects limits. `Adjunction/Continuity.v:202` (`right_adjoint_preserves_limits`) applies to the inclusion but gives preservation, not creation, so it is a near-miss rather than coverage.

## Work to be done

Suggested module: `Construction/Reflective/Limit.v`.

1. Prove the exercise: for a full reflective subcategory, if a diagram in the subcategory has a limit in the ambient category then it has a limit in the subcategory, and the inclusion preserves it. The proof composes: the inclusion preserves limits as a right adjoint, the counit is an isomorphism by `reflective_counit_iso`, and `ff_reflects_limit` transports the universal property back.
2. State the consequence in the form users want: a full reflective subcategory of a complete category is complete.
3. Note the colimit half — colimits in the subcategory are computed by reflecting the ambient colimit — and either prove it or scope it out explicitly in the header.

In-tree donors: `Construction/Reflective.v`, `Theory/Equivalence/Limit.v`, `Adjunction/Continuity.v`, `Structure/Limit.v`, `Structure/Complete.v`, `Structure/Limit/Preservation.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.3 Exercise 7 (book p. 92), with `≈` discipline
- [ ] The completeness corollary is stated
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the inheritance theorem
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Reflective/Limit.v
make && make todo
```

```coq
Print Assumptions reflective_inherits_limits.
```

Reviewer checks: the proof uses the cone-level preservation vocabulary where required (`Structure/Limit/Preservation.v` distinguishes apex-only from cone-level preservation, and the apex-only form is known to be insufficient in this library).

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.3:ex7"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.4: Skeletons and skeletal categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.4:def3, maclane:IV.4:remark1, maclane:IV.4:ex1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book pp. 93, 95 (PDF pp. 102, 104): the definition of a skeleton and of a skeletal category, the remark that a category is equivalent to each of its skeletons, and Exercise 1. Items covered: `maclane:IV.4:def3`, `maclane:IV.4:remark1`, `maclane:IV.4:ex1`.

## Background

A skeleton is a full subcategory containing exactly one object from each isomorphism class; the inclusion of a skeleton is an equivalence, any two skeletons of a category are isomorphic, and two categories are equivalent exactly when their skeletons are isomorphic. See [nLab: skeleton](https://ncatlab.org/nlab/show/skeleton) and [Wikipedia: Skeleton (category theory)](https://en.wikipedia.org/wiki/Skeleton_(category_theory)).

## Current state in the library

There is no general definition; only per-instance skeletality, and a deliberate design decision against the existence statement.

- `Test/Poset.v:102` and `:150` — `poset_nat_skeletal`, `poset_two_skeletal`: "mutually related objects are equal" for two concrete thin categories. They never mention `≅`, and they sit in `Test/` as regression guards for an unrelated fix.
- `Instance/FinSet.v:15` — FinSet is built *as* a skeleton (objects are natural numbers), but is nowhere asserted to be a skeleton *of* anything, and there is no in-tree category of all finite sets for it to be equivalent to.
- `Theory/Equivalence.v:92`–`:99` — an explicit design disclosure: every category is equivalent to its skeleton, but the *existence* of a skeleton is equivalent to the axiom of choice, so "the library states every law up to `≈` and confines skeletons to concrete instances".

Missing: a `Skeletal` predicate; a "skeleton of" relation or construction; and the two theorems about a given skeleton. Searches for `Class Skeletal`, `Definition Skeleton` and `Record Skeleton` return nothing.

## Work to be done

The design disclosure must be respected: the existence of skeletons is not to be assumed, so this issue is scoped to the choice-free content — the predicate, the relation, and everything provable about a skeleton that is *given*.

Suggested module: `Theory/Skeleton.v`.

1. Define `Skeletal (C : Category)` as: isomorphic objects are equal. Prove `Instance/FinSet.v`'s FinSet skeletal, replacing the ad hoc `Test/Poset.v` lemmas' role with a reusable notion.
2. Define "`A` is a skeleton of `C`" as a full subcategory together with, for each object of `C`, a chosen isomorphic object of `A` and a proof that it is the unique such. Note that this packages the choice as *data*, which is exactly how the library keeps such statements axiom-free.
3. Prove: the inclusion of a skeleton is an equivalence, and the chosen isomorphisms assemble into a natural isomorphism `Id ≅ K ◯ T` with `T ◯ K` the identity on the skeleton. This is the remark.
4. Prove Exercise 1: any two skeletons of a category are isomorphic categories; and two categories are equivalent exactly when their given skeletons are isomorphic.
5. Update the `Theory/Equivalence.v` essay to point at the new file, keeping its statement about the axiom of choice — which now applies only to the *existence* claim that this issue deliberately does not make.

In-tree donors: `Construction/Subcategory.v`, `Theory/Equivalence.v`, `Theory/Equivalence/FullFaithful.v`, `Theory/Isomorphism.v`, `Instance/FinSet.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.4 (book pp. 93, 95), with `≈` discipline
- [ ] No existence-of-skeletons claim is made, and the header says why
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the predicate, the skeleton relation and both theorems
- [ ] New file registered in `_CoqProject`
- [ ] `Theory/Equivalence.v`'s design essay updated to cite the new file
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Theory/Skeleton.v
make && make todo
```

```coq
Print Assumptions skeleton_inclusion_is_equivalence.
Print Assumptions skeletons_are_isomorphic.
```

Reviewer checks: no use of choice anywhere; the "exactly one object per isomorphism class" condition is stated as data plus uniqueness, matching the book.

## Dependencies

- Depends on: #238

<!-- catalog: {"ids":["maclane:IV.4:def3","maclane:IV.4:remark1","maclane:IV.4:ex1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.4: An isomorphism-dense full subcategory is reflective"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.4:prop2]
deps_item_ids: [maclane:IV.4:def3]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book p. 94 (PDF p. 103), Proposition 2. Item covered: `maclane:IV.4:prop2`.

## Background

If every object of a category is isomorphic to some object of a full subcategory, the inclusion is an equivalence and is part of an adjoint equivalence whose counit is the identity; in particular such a subcategory is reflective. See [nLab: essentially surjective functor](https://ncatlab.org/nlab/show/essentially+surjective+functor) and [nLab: equivalence of categories](https://ncatlab.org/nlab/show/equivalence+of+categories).

## Current state in the library

Every ingredient exists; the specialisation does not.

- `Theory/Equivalence/FullFaithful.v:160` — `FF_ESO_Equivalence`: full + faithful + essentially surjective implies an equivalence.
- `Theory/Equivalence/Adjoint.v:333` — `Equivalence_to_AdjointEquivalence`, refining any equivalence into an adjoint equivalence.
- `Construction/Subcategory.v:69` — `Full`, with `Incl : Sub ⟶ C` at `:59` and `Full_Implies_Full_Functor` at `:74`.
- `Theory/Equivalence.v:141` — `EssentiallySurjective`, whose data is exactly iso-density.
- `Construction/Reflective.v:60` — `Reflective`.

No in-tree statement performs the specialisation to a subcategory inclusion. The three existing applications of `FF_ESO_Equivalence` (`cauchy_complete_embed_equiv`, `Idempotent_EM_Equivalence`, `RT_Equivalence`) are not subcategory inclusions. There is also no generic `Faithful (Incl C S)` instance — faithfulness of an inclusion is asserted in comments and proved per instance. Finally, the book's *identity* counit is not representable in the delivered form, where the counit is only a componentwise isomorphism, and reflectivity is never concluded.

## Work to be done

Suggested module: `Construction/Subcategory/Dense.v`.

1. Provide the missing generic instance: the inclusion of any subcategory is faithful. This is small, reusable, and currently re-proved per instance.
2. Prove the proposition: for a full subcategory whose inclusion is essentially surjective, the inclusion is an equivalence, and specialise `Equivalence_to_AdjointEquivalence` to obtain an adjoint equivalence.
3. Conclude reflectivity: package the quasi-inverse as a reflector and deliver an inhabitant of `Reflective`.
4. Address the identity counit honestly. The library's adjoint equivalences deliver a counit that is a componentwise isomorphism, not the identity; either construct the strictified version explicitly (choosing the representative to be the object itself where possible) or record in the header why the `≈`-based house style delivers the isomorphism form instead. Do not silently claim the strict form.
5. Note the skeleton case as a corollary once the skeleton development lands.

In-tree donors: the five files cited above, plus `Theory/Equivalence/Bundled.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.4 Proposition 2 (book p. 94), with `≈` discipline
- [ ] The counit strictness question is resolved or explicitly disclosed in the header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the generic faithful-inclusion instance and for the proposition
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Subcategory/Dense.v
make && make todo
```

```coq
Print Assumptions Incl_Faithful.
Print Assumptions dense_full_subcategory_reflective.
```

Reviewer checks: the generic faithful-inclusion instance is actually used by the proposition (not bypassed); the reflectivity conclusion is delivered as the existing `Reflective` record.

## Dependencies

- Depends on: maclane:IV.4:def3

<!-- catalog: {"ids":["maclane:IV.4:prop2"],"deps":["maclane:IV.4:def3"]} -->

---8<---

```yaml
title: "MacLane IV.4: Left-adjoint-left-inverses and their characterization"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.4:def-left-adjoint-left-inverse, maclane:IV.4:ex4]
deps_item_ids: [maclane:IV.4:prop2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book pp. 94–95 (PDF pp. 103–104): the definition of a left-adjoint-left-inverse and Exercise 4. Items covered: `maclane:IV.4:def-left-adjoint-left-inverse`, `maclane:IV.4:ex4`.

## Background

A functor is a left-adjoint-left-inverse of another when the two form an adjunction whose counit is the identity, so the left adjoint is simultaneously a left inverse. Having such a partner is equivalent to being a full, faithful, injective-on-objects right adjoint, and equivalently to being (up to isomorphism of categories) the inclusion of a full reflective subcategory. See [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Absent. There is no functor-level left-inverse notion and no adjunction-with-identity-counit predicate: the only `is_left_inverse`/`is_right_inverse` occurrences are the morphism-level fields of `IsIsomorphism` in `Theory/Morphisms.v`.

The nearest relatives, all checked and none of them the statement:

- `Adjunction/Compose.v:72` — `Adjunction_Id_counit`, proving the counit of the identity adjunction is the identity. That is the degenerate case, stated only for the identity adjunction and never abstracted into a predicate.
- `Construction/Reflective.v:92` — `reflective_counit_iso`: the counit of a full reflective subcategory is an *isomorphism*, strictly weaker than the identity.
- `Construction/Localization/Universal.v:126` — `reflection_retract : Refl ◯ Iota ≈ Id`, again `≈` rather than identity.

There is no injective-on-objects notion and no "isomorphism of categories onto a subcategory" statement, so none of the three conditions of the exercise can be phrased today.

## Work to be done

Suggested module: `Adjunction/LeftInverse.v`.

1. Define a left-adjoint-left-inverse: an adjunction together with a proof that the counit is the identity transformation. Because the house style states laws up to `≈`, decide and disclose whether "identity" means the identity transformation on the nose or `≈ nat_id`; the latter is the usable form and should be the definition, with the strict form noted.
2. Define injectivity on objects for a functor, and prove the basic closure properties.
3. Prove the three-way equivalence of Exercise 4: (a) the functor has a left-adjoint-left-inverse; (b) it has a left adjoint and is full, faithful and injective on objects; (c) it factors as an isomorphism onto a full reflective subcategory followed by the inclusion.
4. Record the two supplied examples: the identity adjunction, and the inclusion of a full isomorphism-dense subcategory once that result is available.

In-tree donors: `Theory/Adjunction.v`, `Adjunction/Compose.v`, `Construction/Reflective.v`, `Construction/Subcategory.v`, `Theory/Functor.v` (`Full`, `Faithful`), `Theory/Equivalence.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.4 (book pp. 94–95), with `≈` discipline; the identity-counit convention disclosed in the header
- [ ] All three implications of the equivalence proved
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the definition and for the characterisation
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/LeftInverse.v
make && make todo
```

```coq
Print Assumptions LeftAdjointLeftInverse.
Print Assumptions lali_characterization.
```

Reviewer checks: condition (b)'s "injective on objects" is a real condition on the functor's object map, not essential injectivity; the equivalence is a genuine three-way statement, not two implications.

## Dependencies

- Depends on: maclane:IV.4:prop2

<!-- catalog: {"ids":["maclane:IV.4:def-left-adjoint-left-inverse","maclane:IV.4:ex4"],"deps":["maclane:IV.4:prop2"]} -->

---8<---

```yaml
title: "MacLane IV.4: A full, faithful, surjective-on-objects functor has a left-adjoint-right-inverse"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.4:ex3]
deps_item_ids: [maclane:IV.4:def-left-adjoint-left-inverse]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book p. 95 (PDF p. 104), Exercise 3. Item covered: `maclane:IV.4:ex3`.

## Background

Strengthening essential surjectivity to on-the-nose surjectivity on objects lets the quasi-inverse be chosen so that the unit of the adjoint equivalence is the identity; the quasi-inverse is then a left-adjoint-right-inverse. See [nLab: equivalence of categories](https://ncatlab.org/nlab/show/equivalence+of+categories) and [nLab: adjoint equivalence](https://ncatlab.org/nlab/show/adjoint+equivalence).

## Current state in the library

The weaker statement is present; the strict refinement is not.

- `Theory/Equivalence/FullFaithful.v:160` — `FF_ESO_Equivalence`, which applies to the exercise's hypotheses since strict surjectivity entails essential surjectivity.
- `Theory/Equivalence/Adjoint.v:333` — `Equivalence_to_AdjointEquivalence`, delivering unit and counit as componentwise isomorphisms.
- `Theory/Equivalence.v:141` — `EssentiallySurjective`.

Missing: any surjective-on-objects vocabulary (searches find only prose); any statement that under strict surjectivity the quasi-inverse can be chosen with the object equation holding on the nose and the unit being the identity; and any left-adjoint-right-inverse packaging.

Worth noting for the implementer: the transport idiom this needs is already executed once in-tree for a different functor — `Construction/Grothendieck/RoundTrip.v:1579` (`RT_EssSurj`) builds `EssentiallySurjective` from an on-the-nose object equality using `eq_refl` and the identity isomorphism. The pattern exists but is never stated generically.

## Work to be done

Suggested module: `Theory/Equivalence/Strict.v`.

1. Define surjectivity on objects for a functor (a section of the object map, as data, so no choice is used).
2. Prove that it entails essential surjectivity with identity witnesses, generalising the `RoundTrip` idiom.
3. Prove the exercise: full + faithful + surjective-on-objects yields an adjoint equivalence whose unit is the identity, hence the quasi-inverse is a left-adjoint-right-inverse of the given functor.
4. Define the left-adjoint-right-inverse notion dually to the left-adjoint-left-inverse one, and state the dual of the characterisation if it is cheap.

In-tree donors: `Theory/Equivalence/FullFaithful.v`, `Theory/Equivalence/Adjoint.v`, `Theory/Equivalence.v`, `Construction/Grothendieck/RoundTrip.v` (for the idiom), `Adjunction/LeftInverse.v` (new).

## Definition of Done

- [ ] Statement fidelity to §IV.4 Exercise 3 (book p. 95), with `≈` discipline; the unit is the identity, as the exercise asks, or the deviation is disclosed
- [ ] Surjectivity on objects is data, not an existential requiring choice
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the theorem
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Theory/Equivalence/Strict.v
make && make todo
```

```coq
Print Assumptions ff_surjective_adjoint_equivalence.
```

Reviewer checks: the identity unit is genuinely delivered (or the deviation is documented); nothing in the proof appeals to choice.

## Dependencies

- Depends on: maclane:IV.4:def-left-adjoint-left-inverse

<!-- catalog: {"ids":["maclane:IV.4:ex3"],"deps":["maclane:IV.4:def-left-adjoint-left-inverse"]} -->

---8<---

```yaml
title: "MacLane IV.4: The colimit functor as a left-adjoint-left-inverse of the diagonal"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.4:ex5]
deps_item_ids: [maclane:IV.4:def-left-adjoint-left-inverse, maclane:IV.2:def1, maclane:IV.2:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book p. 95 (PDF p. 104), Exercise 5. Item covered: `maclane:IV.4:ex5`.

## Background

Over a connected index category the colimit of a constant diagram is the constant itself, so the colimit functor can be chosen to be a left inverse of the diagonal as well as its left adjoint. See [nLab: connected category](https://ncatlab.org/nlab/show/connected+category) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Absent on every front. There is no connected-category notion; the general colimit-as-left-adjoint-of-the-diagonal exists only in Kan-extension form (`Theory/Kan/Extension.v:225`, `lan_adjoint : Lan ⊣ Induced`, over the precomposition functor at `:127`), and `Adjunction/Diagonal/Product.v:37` is only the binary shape. `Functor/Diagonal.v:33` defines `Δ[J] : C ⟶ [J, C]` with its notation, but no adjunction to it exists, so there is nothing whose counit could be shown to be the identity.

## Work to be done

Suggested module: `Structure/Limit/Constant.v` (alongside the constant-diagram results) or a new `Adjunction/Diagonal/Connected.v`.

1. Using the colimit-as-left-adjoint result and the constant-diagram computation over a connected index, show the counit of the colimit adjunction is an isomorphism, and that the colimit functor can be chosen so that it is the identity.
2. Conclude that the colimit functor is a left-adjoint-left-inverse of the diagonal, in the sense of the left-adjoint-left-inverse issue.
3. State the dual (limit over a connected index is a right-adjoint-right-inverse), which is the same proof under duality.
4. Include a negative regression example: over a two-object discrete shape the counit is not invertible, so the connectedness hypothesis is doing work.

In-tree donors: `Functor/Diagonal.v`, `Structure/Cocone.v`, `Structure/Limit.v`, `Theory/Kan/Extension.v`, `Adjunction/LeftInverse.v` (new), `Theory/Connected.v` (new).

## Definition of Done

- [ ] Statement fidelity to §IV.4 Exercise 5 (book p. 95), with `≈` discipline
- [ ] The connectedness hypothesis is genuinely used, with a regression example showing failure without it
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the result
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Diagonal/Connected.v
make && make todo
```

```coq
Print Assumptions colimit_is_lali_of_diagonal.
```

Reviewer checks: the statement is about the general `Δ[J]`, not the binary product diagonal.

## Dependencies

- Depends on: maclane:IV.4:def-left-adjoint-left-inverse
- Depends on: maclane:IV.2:def1
- Depends on: maclane:IV.2:construction2

<!-- catalog: {"ids":["maclane:IV.4:ex5"],"deps":["maclane:IV.4:def-left-adjoint-left-inverse","maclane:IV.2:def1","maclane:IV.2:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.4: Adjoint equivalences compose"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.4:ex2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.4, book p. 95 (PDF p. 104), Exercise 2. Item covered: `maclane:IV.4:ex2`.

## Background

Equivalences of categories compose, and the corresponding statement for adjoint equivalences holds too: the composite of two adjoint equivalences is an adjoint equivalence, with unit and counit built from the constituents. See [nLab: adjoint equivalence](https://ncatlab.org/nlab/show/adjoint+equivalence) and [Wikipedia: Equivalence of categories](https://en.wikipedia.org/wiki/Equivalence_of_categories).

## Current state in the library

Part (a) is present; part (b) is not.

- `Theory/Equivalence/Bundled.v:94` — `EquivalenceOfCategories_Compose`, built from the two proved cells at `:72` and `:83`.
- `Theory/Equivalence/Bundled.v:115` — `Equivalence_trans`, the bundled transitivity of `C ≃ D`.
- `Theory/Equivalence/Adjoint.v:333` — `Equivalence_to_AdjointEquivalence`.

There is no named composition of adjoint equivalences: the whole tree mentions `AdjointEquivalence` in three files, and none of them composes two of them. `Adjunction/Compose.v:173` composes plain adjunctions but is never linked to adjoint equivalences.

## Work to be done

Suggested module: an addition to `Theory/Equivalence/Adjoint.v`.

1. Prove that the composite of two adjoint equivalences is an adjoint equivalence. The short route is: forget to equivalences, compose with `EquivalenceOfCategories_Compose`, and re-refine with `Equivalence_to_AdjointEquivalence`, whose right adjoint is definitionally the composite of the two right adjoints.
2. Do the work that route leaves out: compare the resulting unit and counit with the ones computed from the constituents via `Adjunction/Compose.v:173`, and prove them `≈`. Without this comparison the composition is opaque to callers, which is the real content of the exercise.
3. Record the identity adjoint equivalence and the inverse of an adjoint equivalence, so the three groupoid laws are available together.

In-tree donors: `Theory/Equivalence/Bundled.v`, `Theory/Equivalence/Adjoint.v`, `Adjunction/Compose.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.4 Exercise 2(b) (book p. 95), with `≈` discipline
- [ ] The unit/counit comparison with the constituent adjunctions is proved
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the composition
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Theory/Equivalence/Adjoint.v
make && make todo
```

```coq
Print Assumptions AdjointEquivalence_Compose.
```

Reviewer checks: the comparison lemmas are present, not just the existence of a composite.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.4:ex2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.5: Galois connections are adjunctions between preorders"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.5:def1, maclane:IV.5:thm1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book pp. 95–96 (PDF pp. 104–105), Theorem 1 and the definition of a Galois connection. Items covered: `maclane:IV.5:def1`, `maclane:IV.5:thm1`.

## Background

A Galois connection between preorders is exactly an adjunction between them regarded as thin categories: the transposition biconditional is the hom-set bijection, naturality is automatic because hom-sets are subsingletons, the unit and counit are the two comparison inequalities, and the triangle identities become the round-trip equations. See [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection) and [Wikipedia: Galois connection](https://en.wikipedia.org/wiki/Galois_connection).

## Current state in the library

Only the categorical half is formal; the order-theoretic packaging and the bridge are missing.

- `Instance/Proset.v:33` — `Proset {A R} (P : PreOrder R) : Category`, with `hom := R` and a trivial hom-setoid, so a preorder regarded as a thin category is available and `@Adjunction (Proset P) (Proset Q) L R` is a writable in-tree type.
- `Theory/Adjunction.v:130` — `Class Adjunction`, with its four naturality fields.
- `Instance/Props.v:94` — `Props_Closed`, the currying bijection on the thin category `Props`. Note this is a `Closed` structure, not an in-tree `⊣` term: there is no `Closed → Adjunction` derivation anywhere in the tree, so it is not an example of a thin-category adjunction as such.
- `Instance/Poset.v:37`–`:100` and `Theory/Adjunction.v:78`–`:79` — the identification of poset adjunctions with Galois connections, stated in the background essays only.

Missing: any named `GaloisConnection` definition, in either the monotone or the antitone packaging; any lemma converting the pointwise biconditional into an `Adjunction` between the thin categories, or back; the uniqueness of the adjoint in the thin case; and the round-trip equations that Mac Lane derives from the triangle identities.

## Work to be done

Suggested module: `Instance/Proset/Galois.v`.

1. Define a Galois connection between preorders as a pair of monotone maps with the transposition biconditional, in the monotone form Mac Lane uses (one map into the opposite), and derive the antitone reading.
2. Prove both directions of the bridge: a Galois connection yields an `Adjunction` between the corresponding `Proset` categories, and conversely. Naturality should be discharged by thinness, and this should be visible in the proof rather than buried.
3. Prove uniqueness: in a thin setting the adjoint is determined, so any two right adjoints of the same map agree.
4. Derive the round-trip laws from the triangle identities, and the poset corollaries (the two composites are idempotent, and the three-fold composites collapse).

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Theory/Adjunction.v`, `Adjunction/Natural/Transformation.v`, `Instance/Props.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 Theorem 1 and its definition (book pp. 95–96), with `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the definition, both directions of the bridge, and the uniqueness and round-trip results
- [ ] New file registered in `_CoqProject`
- [ ] The essays in `Instance/Poset.v` and `Theory/Adjunction.v` updated to cite the proved bridge instead of asserting it
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Instance/Proset/Galois.v
make && make todo
```

```coq
Print Assumptions GaloisConnection.
Print Assumptions galois_iff_adjunction.
```

Reviewer checks: the definition is stated order-theoretically (a biconditional on elements), not as an abbreviation for `Adjunction`; the collapse of naturality to thinness is proved, not assumed.

## Dependencies

- Depends on: #223

<!-- catalog: {"ids":["maclane:IV.5:def1","maclane:IV.5:thm1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.5: The Galois connection of a group acting on a set"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.5:construction1]
deps_item_ids: [maclane:IV.5:def1, maclane:IV.5:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 96 (PDF p. 105), the Galois connection of a group action. Item covered: `maclane:IV.5:construction1`.

## Background

For a group acting on a set, sending a subset to its pointwise stabiliser and a set of group elements to its fixed-point set is the classical Galois connection, of which the correspondence between intermediate fields and subgroups is the original instance. See [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection) and [Wikipedia: Fundamental theorem of Galois theory](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory).

## Current state in the library

Absent. `Structure/Group.v:109` declares only `GroupObject`, an internal group object in a monoidal category, with no action, no subgroup lattice and no fixed-point operator. `Instance/Poset.v` declares only the poset instance and the order relation; every Galois hit tree-wide is background prose.

## Work to be done

Suggested module: `Instance/Group/Galois.v`.

1. Define a group acting on a set (a monoid action suffices for the construction; the group structure is what makes the closed elements interesting).
2. Build the two powerset preorders and the two operators: stabiliser of a subset, fixed points of a set of group elements.
3. Prove the transposition biconditional and package the pair as a Galois connection.
4. Prove the two closure operators idempotent and identify the closed elements: closed subsets of the group are the stabiliser subgroups, closed subsets of the set are the fixed-point sets.

In-tree donors: `Instance/Proset.v`, the powerset-preorder construction (see the dependency below), `Structure/Group.v`, `Instance/Ens.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 (book p. 96), with `≈` discipline
- [ ] Delivered as an inhabitant of the `GaloisConnection` definition, not a bespoke restatement
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` reported, with any stdlib axioms enumerated per docs/AXIOMS.md
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Group/Galois.v
make && make todo
```

```coq
Print Assumptions group_action_galois.
```

Reviewer checks: the stabiliser really is proved to be a subgroup; the closed-element identification is proved, not asserted.

## Dependencies

- Depends on: maclane:IV.5:def1
- Depends on: maclane:IV.5:construction2
- Depends on: #255

<!-- catalog: {"ids":["maclane:IV.5:construction1"],"deps":["maclane:IV.5:def1","maclane:IV.5:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.5: The powerset preorder and the direct-image/inverse-image adjunction"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.5:construction2]
deps_item_ids: [maclane:IV.5:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 96 (PDF p. 105), direct image left adjoint to inverse image. Item covered: `maclane:IV.5:construction2`.

## Background

A function induces a direct-image and an inverse-image map between powersets, monotone for inclusion, and the direct image is left adjoint to the inverse image. This is the base case of every later "quantifiers as adjoints" statement. See [nLab: image](https://ncatlab.org/nlab/show/image) and [nLab: power set](https://ncatlab.org/nlab/show/power+set).

## Current state in the library

Absent, and even the carrier is missing.

- Searches for "direct image" and "inverse image" over all `.v` files return nothing.
- `Theory/Subobject/Functor.v:35` (`sub_reindex`) with `Sub : C^op ⟶ Sets` at `:180` is the inverse-image half in subobject form, but has no left adjoint (that file contains no adjoint at all).
- `Instance/Sets/Image.v:143` (`Sets_Image_Factorization`) is an epi-mono factorisation of a single morphism, not an image functor.
- `Instance/Ens.v:55` declares `EnsT (T : Type)` whose objects are subsets of a fixed type, but its morphisms are not inclusions, so it is neither thin nor the inclusion order.

The powerset of a set, ordered by inclusion, does not exist as a category in the tree. That carrier is what several other Chapter IV items need, so it is the main deliverable here.

## Work to be done

Suggested module: `Instance/Powerset.v`.

1. Build the powerset preorder of a setoid as a thin category: objects are predicates respecting the setoid equality, and a morphism is an inclusion. Use `Instance/Proset.v`'s pattern so that the resulting category is definitionally thin.
2. Define the direct-image and inverse-image maps for a function between setoids, prove them monotone, and hence functors between the powerset categories.
3. Prove the adjunction — direct image left adjoint to inverse image — via the transposition biconditional, and package it both as a Galois connection and as an `Adjunction` between the thin categories.
4. Record the standard consequences the rest of Chapter IV needs: inverse image preserves all meets and joins, direct image preserves joins, and the unit and counit are the two comparison inclusions.

In-tree donors: `Instance/Proset.v`, `Instance/Sets.v`, `Instance/Ens.v`, `Theory/Subobject.v`, `Theory/Subobject/Functor.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 (book p. 96), with `≈` discipline
- [ ] The powerset category respects setoid equality (predicates are `Proper`), so it composes with the rest of `Instance/Sets.v`
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the powerset category and the adjunction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level (this carrier is reused by several later items)

## Verification

```bash
coqc -R . Category Instance/Powerset.v
make && make todo
```

```coq
Print Assumptions Powerset.
Print Assumptions image_preimage_adjunction.
```

Reviewer checks: the order is inclusion (contrast `Instance/Ens.v:55`, whose homs are not inclusions); the adjunction direction matches the book.

## Dependencies

- Depends on: maclane:IV.5:def1
- Depends on: #227
- Depends on: #311

<!-- catalog: {"ids":["maclane:IV.5:construction2"],"deps":["maclane:IV.5:def1"]} -->

---8<---

```yaml
title: "MacLane IV.5: Boolean connectives as adjoints on a powerset"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.5:construction3]
deps_item_ids: [maclane:IV.5:construction2, maclane:IV.1:construction5]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 96 (PDF p. 105), the Boolean connectives as adjoints. Item covered: `maclane:IV.5:construction3`.

## Background

On a powerset, intersection is right adjoint and union left adjoint to the diagonal, and for a fixed subset, intersecting with it is left adjoint to "union with its complement" — so conjunction, disjunction and implication all arise as adjoints. See [nLab: Heyting algebra](https://ncatlab.org/nlab/show/Heyting+algebra) and [nLab: Boolean algebra](https://ncatlab.org/nlab/show/Boolean+algebra).

## Current state in the library

Three separate deficits, on top of a general result that does apply.

- `Adjunction/Diagonal/Product.v:36` — `Diagonal_Product_Adjunction` supplies the meet half in complete generality, applicable to any thin cartesian category.
- `Instance/Props.v:69`, `:80`, `:94` — `Props_Cartesian` (product is conjunction), `Props_Cocartesian` (coproduct is disjunction) and `Props_Closed` (exponential is implication) realise the connectives in a concrete thin category, with the file's header stating that the exponential bijection witnesses the implication adjunction.
- `Instance/Two/Monoidal.v:80`, `:98` — the two-element order gets meets and a top, but no `Closed` instance.

What is missing: the powerset of a set as a category, so the construction has no witness at its stated site; the join half of the diagonal adjunction (union left adjoint to the diagonal), which exists only as a prose parenthetical at `Adjunction/Diagonal/Product.v:19`; and the Boolean form of the implication adjunction, since no complement operation, Boolean algebra or lattice structure is defined anywhere in the tree — only the intuitionistic shadow in `Instance/Props.v` is available.

## Work to be done

Suggested module: `Instance/Powerset/Boolean.v`.

1. Instantiate the diagonal adjunctions at the powerset category: intersection is the right adjoint, union the left adjoint. The meet half follows from the existing general instance once the powerset is cartesian; the join half needs the coproduct-diagonal result.
2. Define the complement on a powerset (classically, or over a decidable predicate if the file is to stay constructive — decide and disclose in the header), and prove the implication adjunction: intersecting with a fixed subset is left adjoint to union with its complement.
3. Show the intuitionistic form (relative pseudo-complement) holds without complements, so that the constructive core is separated from the classical statement.
4. Sanity-check against `Instance/Props.v`: the powerset of a one-element set reproduces `Props` up to isomorphism.

In-tree donors: `Adjunction/Diagonal/Product.v`, `Instance/Props.v`, `Instance/Two/Monoidal.v`, `Structure/Cartesian/Closed.v`, the powerset category (new).

## Definition of Done

- [ ] Statement fidelity to §IV.5 (book p. 96), with `≈` discipline
- [ ] The classical/constructive split is disclosed in the file header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the constructive part; any classical axiom used in the Boolean part is enumerated per docs/AXIOMS.md
- [ ] `Print Assumptions` closed for the meet and join adjunctions
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Powerset/Boolean.v
make && make todo
```

```coq
Print Assumptions powerset_meet_adjunction.
Print Assumptions powerset_implication_adjunction.
```

Reviewer checks: the join half is a real adjunction, not a comment; the classical complement is confined to the clearly-marked Boolean section.

## Dependencies

- Depends on: maclane:IV.5:construction2
- Depends on: maclane:IV.1:construction5

<!-- catalog: {"ids":["maclane:IV.5:construction3"],"deps":["maclane:IV.5:construction2","maclane:IV.1:construction5"]} -->

---8<---

```yaml
title: "MacLane IV.5: Quantifiers as adjoints to substitution"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.5:construction4]
deps_item_ids: [maclane:IV.5:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 96 (PDF pp. 105–106), the quantifiers as adjoints. Item covered: `maclane:IV.5:construction4`.

## Background

Along a projection, the inverse-image (substitution) map between powersets has the existential quantifier as left adjoint and the universal quantifier as right adjoint; geometrically, substitution is the cylinder, the existential its projection, and the universal the largest subset whose cylinder fits inside. This is the base case of a hyperdoctrine. See [nLab: existential quantifier](https://ncatlab.org/nlab/show/existential+quantifier) and [nLab: hyperdoctrine](https://ncatlab.org/nlab/show/hyperdoctrine).

## Current state in the library

Absent. Every "quantifier" and "hyperdoctrine" occurrence is background prose (`Theory/Adjunction.v:75`–`:76`, `Construction/Slice.v:93`, `Structure/Pullback.v:124`, `Structure/Topos.v:38`, `:85`, `Tools/Abstraction.v:144`); searches for "existential quantifier" and "universal quantifier" return nothing.

The one near-miss is correctly excluded: in `Construction/Slice/Pullback.v`, `Bang_Functor` (`:50`) and `Star_Functor` (`:67`) are live, but the adjunction `Base_Functor_Adjunction` is entirely inside a comment block (`:121`–`:127`) and the right adjoint survives only as a commented `Production` stub (`:114`–`:119`), so neither leg of the triple is proved even in its slice-level generalisation.

## Work to be done

Suggested module: `Instance/Powerset/Quantifier.v`.

1. For a function between setoids, define the two quantifier operators on powersets: the existential (which coincides with the direct image) and the universal.
2. Prove the two transposition biconditionals, giving the adjoint triple: existential ⊣ substitution ⊣ universal.
3. Specialise to a projection out of a product, recovering Mac Lane's cylinder reading, and record the Beck–Chevalley compatibility with substitution along a second variable if it is cheap — it is what makes the family a hyperdoctrine.
4. Connect explicitly to the slice-level generalisation: note in the header that the corresponding slice adjoint triple is the subject of the base-change issue and is currently only a commented stub.

In-tree donors: the powerset category and image/preimage adjunction (new), `Instance/Sets.v`, `Construction/Slice/Pullback.v` for the intended generalisation, `Structure/Topos.v` for the eventual internal-logic reading.

## Definition of Done

- [ ] Statement fidelity to §IV.5 (book p. 96), with `≈` discipline
- [ ] Both adjunctions of the triple are proved
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for both adjunctions
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Instance/Powerset/Quantifier.v
make && make todo
```

```coq
Print Assumptions exists_substitution_adjunction.
Print Assumptions substitution_forall_adjunction.
```

Reviewer checks: the existential is proved equal to the direct image, as the book observes; the universal is the "largest subset whose cylinder fits" and this characterisation is proved.

## Dependencies

- Depends on: maclane:IV.5:construction2

<!-- catalog: {"ids":["maclane:IV.5:construction4"],"deps":["maclane:IV.5:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.5: The orthogonal complement as a Galois connection"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.5:ex1]
deps_item_ids: [maclane:IV.5:def1, maclane:IV.5:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 97 (PDF p. 106), Exercise 1. Item covered: `maclane:IV.5:ex1`.

## Background

On an inner-product space, taking orthogonal complements is an antitone self-map of the subset order that forms a Galois connection with itself; the closed elements are the closed subspaces. See [Wikipedia: Orthogonal complement](https://en.wikipedia.org/wiki/Orthogonal_complement) and [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection).

## Current state in the library

Absent, and the ambient structure does not exist. Searches for "inner product", "orthogonal complement" and "sesquilinear" all return nothing; the only Hilbert-space mentions are prose. `Theory/Orthogonality.v:43` declares `Class Orthogonal` with the unique-lifting property of a factorization system — a homonym, unrelated to a perpendicularity operator. The library has no linear algebra of any kind.

## Work to be done

Suggested module: `Instance/InnerProduct/Galois.v`.

1. Introduce enough linear-algebraic structure to state the exercise: a module over an ordered field with a symmetric bilinear form, or an abstract "orthogonality relation" satisfying the two properties actually used. The second option is much cheaper and is the recommended scope: the exercise's content is the Galois connection, not the analysis.
2. Define the perpendicular operator on the powerset of the carrier and prove it antitone.
3. Prove the self-adjunction: a subset is contained in the perpendicular of another exactly when the second is contained in the perpendicular of the first, and package it as a Galois connection.
4. Identify the closed elements, connecting to the general closed-elements result.

In-tree donors: the powerset category (new), the Galois-connection definition (new), `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 Exercise 1 (book p. 97), with `≈` discipline
- [ ] The header states which abstraction of "inner product" was chosen and why
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the Galois connection
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/InnerProduct/Galois.v
make && make todo
```

```coq
Print Assumptions perp_galois.
```

Reviewer checks: the new orthogonality notion is not confused with `Theory/Orthogonality.v`'s factorization-system class — the header must say so explicitly, since the names collide.

## Dependencies

- Depends on: maclane:IV.5:def1
- Depends on: maclane:IV.5:construction2

<!-- catalog: {"ids":["maclane:IV.5:ex1"],"deps":["maclane:IV.5:def1","maclane:IV.5:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.5: Closed elements of a Galois connection and the fixed points of an adjunction"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.5:ex2]
deps_item_ids: [maclane:IV.5:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 97 (PDF p. 106), Exercise 2. Item covered: `maclane:IV.5:ex2`.

## Background

In a Galois connection between posets the closed elements on each side coincide with the image of the opposite map, and the two sets of closed elements are in bijection; the exercise asks whether this generalises to an arbitrary adjunction, where the answer is the equivalence between the fixed points of the induced monad and those of the induced comonad. See [nLab: idempotent monad](https://ncatlab.org/nlab/show/idempotent+monad) and [Wikipedia: Galois connection](https://en.wikipedia.org/wiki/Galois_connection).

## Current state in the library

One side of the general statement is present, in a stronger form than the exercise asks, but the other side and the poset instance are missing.

- `Construction/Reflective/Idempotent.v:224` — `MLocal_Subcategory`, whose objects are those where the monad unit is invertible: the categorified closed elements of the domain.
- `Construction/Reflective/Idempotent.v:345` — `Idempotent_Reflective`, exhibiting them as a full reflective subcategory.
- `Construction/Reflective/Idempotent.v:464` — `Idempotent_EM_Equivalence`, the equivalence with the Eilenberg–Moore category, with the converse leg `Reflective_IdempotentMonad` at `:198`.
- `Construction/Localization.v:184` — `unit_at_local_iso`; `Construction/Reflective.v:92` — `reflective_counit_iso`.

Missing: the codomain side (a search for `IdempotentComonad` returns nothing), hence the two-sided bijection between the closed elements of the two sides; the identification of the closed elements with the image of the right adjoint; the poset instantiation, since no Galois connection exists in-tree; and any treatment of the non-idempotent case that the exercise's closing question raises.

## Work to be done

Suggested module: `Construction/Reflective/FixedPoints.v`, plus a poset instantiation alongside the Galois-connection file.

1. Define the comonad-side dual (the objects where the comonad counit is invertible) and prove the dual of the existing reflective result, so both sides are available.
2. Prove the two-sided statement: any adjunction restricts to an equivalence between the full subcategory of monad-fixed objects and the full subcategory of comonad-fixed objects.
3. Prove that on each side the fixed objects are exactly those in the essential image of the corresponding adjoint — the categorified form of "closed elements = image of R".
4. Instantiate at a Galois connection between posets to recover the exercise as stated, where the equivalence collapses to a bijection because the categories are thin.
5. Address the closing question: state precisely what survives without idempotency (the fixed-point equivalence holds for any adjunction; it is the *reflectivity* that needs idempotency), and record it in the header.

In-tree donors: `Construction/Reflective/Idempotent.v`, `Construction/Reflective.v`, `Construction/Localization.v`, `Comonad/Core.v`, `Comonad/Coalgebra.v`, `Theory/Equivalence/FullFaithful.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 Exercise 2 (book p. 97), with `≈` discipline
- [ ] Both sides of the fixed-point equivalence are proved
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the comonad-side dual and for the equivalence
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Construction/Reflective/FixedPoints.v
make && make todo
```

```coq
Print Assumptions adjunction_fixed_point_equivalence.
```

Reviewer checks: the general statement is proved for an arbitrary adjunction, not only an idempotent one; the poset instance is a genuine specialisation, not a re-proof.

## Dependencies

- Depends on: maclane:IV.5:def1

<!-- catalog: {"ids":["maclane:IV.5:ex2"],"deps":["maclane:IV.5:def1"]} -->

---8<---

```yaml
title: "MacLane IV.5: Base change is right adjoint to composition on slices"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.5:ex3]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5, book p. 97 (PDF p. 106), Exercise 3. Item covered: `maclane:IV.5:ex3`.

## Background

In a category with pullbacks, post-composition with an arrow is a functor between slice categories, and it has a right adjoint given by pulling back along that arrow. See [nLab: base change](https://ncatlab.org/nlab/show/base+change) and [nLab: over category](https://ncatlab.org/nlab/show/over+category).

## Current state in the library

Both functors are built and proved functorial; the adjunction — the entire content of the exercise — is commented out, and two places in the documentation claim it as done.

- `Construction/Slice/Pullback.v:50` — `Bang_Functor (f : a ~> b) : Slice C a ⟶ Slice C b`, post-composition with `f`, all obligations closed by `Qed`.
- `Construction/Slice/Pullback.v:67` — `Star_Functor (f : c ~> a) : Slice C a ⟶ Slice C c`, the pullback functor, under a section-wide `Hypothesis pullbacks` at `:63`, again fully discharged.
- `Construction/Slice/Pullback.v:121`–`:127` — `Base_Functor_Adjunction` exists only as a comment block, and the commented statement is even mis-oriented (`Star_Functor f ⊣ Bang_Functor f`, the reverse of the correct direction); the file's own header at `:38`–`:40` flags this.
- `Construction/Slice/Pullback.v:114`–`:119` — the further right adjoint survives only as a commented stub.
- Two documentation overclaims must be fixed as part of this work: `Structure/Pullback.v:129`–`:130` says the base-change adjunction "is built in `Construction/Slice/Pullback.v` as `Bang_Functor ⊣ Star_Functor`", and `Construction/Slice.v:88`–`:90` says "with the adjunction Σ_f ⊣ f^* recorded in that file's header". Both point at a comment.

A whole-tree enumeration of `⊣` occurrences confirms there is no term of the required type anywhere.

## Work to be done

Suggested module: `Construction/Slice/Pullback.v` (finish the existing file).

1. Prove `Bang_Functor f ⊣ Star_Functor f`, in the correct orientation, by transposing a slice morphism through the pullback universal property. Unit and counit should be named: the unit is the comparison into the pullback, the counit the pullback projection.
2. Delete the mis-oriented commented stub, so no future reader repeats the confusion.
3. Correct the two documentation overclaims to cite the now-real theorem.
4. If the further right adjoint (dependent product) is in reach for the same PR, add it; otherwise leave the stub removed and record the deferral explicitly in the header rather than as commented code.

In-tree donors: `Construction/Slice.v`, `Structure/Pullback.v`, `Theory/Morphisms/Stability.v` (pullback pasting and transport), `Theory/Adjunction.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.5 Exercise 3 (book p. 97), in the correct orientation, with `≈` discipline
- [ ] The commented-out mis-oriented stub is removed, not left alongside the proof
- [ ] `Structure/Pullback.v:129` and `Construction/Slice.v:88` corrected to cite the proved result
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the adjunction (the section `Hypothesis pullbacks` is a parameter of the section, not an axiom — check that it appears as a hypothesis of the statement)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if flagship-level

## Verification

```bash
coqc -R . Category Construction/Slice/Pullback.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Base_Functor_Adjunction.
```

Reviewer checks: the delivered orientation is dependent-sum-on-the-left, matching the book and contradicting the deleted stub; both documentation sites now point at real code.

## Dependencies

- Depends on: #333

<!-- catalog: {"ids":["maclane:IV.5:ex3"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.6: The tensor-hom adjunction for modules"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.1:construction4, maclane:IV.6:construction1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.1, book p. 80 (PDF p. 89), the tensor-hom isomorphism for modules; and §IV.6, book p. 98 (PDF p. 107), the same as an adjunction determined by the evaluation counit. Items covered: `maclane:IV.1:construction4`, `maclane:IV.6:construction1`.

## Background

Over a commutative ring, tensoring with a fixed module is left adjoint to the internal hom out of that module, with the adjunction determined by the evaluation counit; the isomorphism is natural in all three module arguments. See [nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category) and [Wikipedia: Tensor-hom adjunction](https://en.wikipedia.org/wiki/Tensor-hom_adjunction).

## Current state in the library

The abstract statement is in force at exactly the right generality; the concrete instance is absent, and there is no non-cartesian witness anywhere.

- `Structure/Monoidal/StarAutonomous.v:109` — `Class SymMonClosed`, symmetric monoidal closed, with `exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z`, the derived `eval' := uncurry' id`, and `ump_exponents' : ∃! h, f ≈ eval' ∘ (h ⨂ id)` — precisely the "determined by the evaluation counit" shape.
- `Structure/Monoidal/Closed.v:46` — `Class ClosedMonoidal`, whose first field is `closed_is_cartesian : @CartesianMonoidal C`. That bundling forces the tensor to be a cartesian product, so this class provably cannot host a module tensor.
- `Structure/Monoidal/Closed.v:83` — `eval`, with `ump_exponents` at `:88`.

`SymMonClosed` has zero instances in the tree, and `ClosedMonoidal`'s only two instances (`CCC_ClosedMonoidal`, `Coq_ClosedMonoidal`) are cartesian. There is no ring, no module category, no tensor product of modules, and hence no instance of the tensor-hom adjunction at a genuinely non-cartesian tensor. Naturality is packaged as the per-object isomorphism plus the universal property rather than as a stated three-variable naturality.

## Work to be done

Suggested modules: `Instance/Module.v` (the category), `Instance/Module/Tensor.v` (the monoidal structure), `Instance/Module/Closed.v` (the closed structure).

1. Build the category of modules over a commutative ring as a setoid-based category, following the `Instance/CMon.v` template.
2. Construct the tensor product of modules by its universal property with respect to bilinear maps (the universal-element formulation is already a filed obligation, so reuse it rather than re-deriving), and prove it a symmetric monoidal structure.
3. Construct the internal hom (the module of linear maps with the pointwise action) and prove the closed structure, delivering an inhabitant of `SymMonClosed` — the first non-cartesian one in the tree.
4. State the adjunction in the two forms the book uses: the natural isomorphism in all three variables, and the "determined by evaluation" form, checking they agree.
5. Update docs/INHABITATION.md: this supplies the first concrete model of the symmetric-monoidal-closed spine, which several parametric results currently await.

In-tree donors: `Structure/Monoidal/StarAutonomous.v`, `Structure/Monoidal/Symmetric.v`, `Instance/CMon.v`, `Structure/Preadditive.v`, `Theory/Universal/Arrow.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.1 (book p. 80) and §IV.6 (book p. 98), with `≈` discipline
- [ ] The instance is of `SymMonClosed`, not of the cartesian-bundled `ClosedMonoidal`
- [ ] Three-variable naturality is stated explicitly, not only implied by the universal property
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the structural part; any stdlib axioms used in the instance layer enumerated per docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the monoidal and closed instances
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md and docs/INHABITATION.md updated (flagship-level: first non-cartesian closed monoidal witness)

## Verification

```bash
coqc -R . Category Instance/Module.v
coqc -R . Category Instance/Module/Tensor.v
coqc -R . Category Instance/Module/Closed.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Module_SymMonClosed.
Print Assumptions module_tensor_hom_natural.
```

Reviewer checks: the tensor is genuinely not the cartesian product (a regression example should show the two differ); the counit is the evaluation map Mac Lane names.

## Dependencies

- Depends on: #258
- Depends on: #306
- Depends on: #265

<!-- catalog: {"ids":["maclane:IV.1:construction4","maclane:IV.6:construction1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.6: Powerset lattices and Boolean algebras are cartesian closed"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.6:ex1]
deps_item_ids: [maclane:IV.5:construction2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.6, book p. 98 (PDF p. 107), Exercise 1. Item covered: `maclane:IV.6:ex1`.

## Background

Any powerset ordered by inclusion, and more generally any Boolean algebra viewed as a preorder, is a cartesian closed category: the product is meet and the exponential is the relative pseudo-complement. See [nLab: Heyting algebra](https://ncatlab.org/nlab/show/Heyting+algebra) and [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

The "lattice as a thin cartesian closed category" content is carried out for exactly one preorder.

- `Instance/Props.v:39` — `Props`, objects propositions and morphisms implications, with a trivial hom-setoid, hence thin.
- `Instance/Props.v:69` — `Props_Cartesian` (product is conjunction); `:94` — `Props_Closed` (exponential is implication).
- `Instance/Proset.v:33` — `Proset`, a preorder as a thin category, with no lattice or closure structure attached.
- `Instance/Two/Monoidal.v:80`, `:98` — `Two_Cartesian` and `Two_Terminal` for the two-element order; no `Closed` instance exists for it, and `Instance/Two.v:85`–`:89` only remarks in prose on the Heyting/Boolean reading.

Neither half of the exercise is instantiated. The powerset order is never constructed as a category — `Instance/Ens.v`'s `EnsT T` has subsets as objects but its morphisms are not inclusions, so it is neither thin nor the inclusion order and carries no cartesian or closed structure; effectively only the one-element case is present, as `Props`. And no Boolean-algebra structure exists anywhere in the tree. An enumeration of every `Closed` instance in the tree contains no poset, lattice or powerset instance.

## Work to be done

Suggested module: `Instance/Powerset/Closed.v`, plus `Structure/Lattice.v` if a general lattice notion is wanted.

1. Prove the powerset preorder cartesian, with terminal object the whole set and product the intersection.
2. Prove it closed, with exponential the relative pseudo-complement, and check the transposition is the expected inclusion equivalence.
3. Introduce Boolean algebras (or Heyting algebras with complement) as a structure, and prove any of them cartesian closed when regarded as a thin category — this is the general half (b), of which the powerset is an instance.
4. Give `Instance/Two.v` the resulting `Closed` instance, discharging the prose remark there.

In-tree donors: the powerset category (new), `Instance/Props.v`, `Instance/Proset.v`, `Instance/Two/Monoidal.v`, `Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.6 Exercise 1 (book p. 98), both halves, with `≈` discipline
- [ ] `Instance/Two.v`'s prose remark replaced by a real instance
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the constructive part; classical assumptions, if any, confined and enumerated
- [ ] `Print Assumptions` closed for both instances
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Powerset/Closed.v
make && make todo
```

```coq
Print Assumptions Powerset_Closed.
Print Assumptions Boolean_Closed.
```

Reviewer checks: the exponential is the relative pseudo-complement, and the proof does not secretly assume classical logic in the Heyting half.

## Dependencies

- Depends on: maclane:IV.5:construction2

<!-- catalog: {"ids":["maclane:IV.6:ex1"],"deps":["maclane:IV.5:construction2"]} -->

---8<---

```yaml
title: "MacLane IV.6: The entailment preorder of a theory is cartesian closed"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.6:ex2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.6, book p. 98 (PDF p. 107), Exercise 2. Item covered: `maclane:IV.6:ex2`.

## Background

The sentences of a theory, preordered by entailment relative to its axioms, form a cartesian closed category: conjunction is the product and implication the exponential, the transposition being the deduction theorem. This is the Lindenbaum–Tarski construction. See [nLab: Lindenbaum–Tarski algebra](https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra) and [Wikipedia: Lindenbaum–Tarski algebra](https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra).

## Current state in the library

The mathematical content is formalised once, for one fixed "theory": the ambient logic.

- `Instance/Props.v:19` ff. — the header states the reading exactly: a morphism is an implication, the category is thin, so a hom is inhabited exactly when one proposition entails another, and the exponential is implication because "cartesian closure is the deduction theorem".
- `Instance/Props.v:39`, `:69`, `:94` — `Props`, `Props_Cartesian` (product is conjunction), `Props_Closed` (exponential is implication).
- `Instance/Lambda.v:291` — `Lambda_Closed`, the syntactic cartesian closed category of the simply-typed lambda calculus, but of types and terms with semantic morphism equality: not thin, and not an entailment preorder.

What is missing is the exercise's quantification over theories: there is no syntax of sentences, no axiom set, no derivability relation and no Lindenbaum–Tarski quotient anywhere in the tree, and `Props` is not parameterised by a theory (its entailment is the ambient intuitionistic implication of the meta-logic, not a relativised `T ⊢ p → q`).

## Work to be done

Suggested module: `Instance/Theory/Lindenbaum.v`.

1. Introduce a minimal syntax of propositional sentences over a signature, with a derivability relation relative to a set of axioms. Keep it small: the exercise needs conjunction, implication and truth, not a full first-order system, and the header should say so.
2. Build the entailment preorder as a thin category, parameterised by the theory.
3. Prove it cartesian (product is conjunction, terminal is truth) and closed (exponential is implication, transposition is the deduction theorem).
4. Show that at the empty theory over the ambient logic the construction reproduces `Instance/Props.v`'s structure up to the obvious comparison, so the new file subsumes rather than duplicates it.
5. If a first-order or classical variant is wanted, note in the header that the cartesian-closure content is unchanged and only the entailment relation differs.

In-tree donors: `Instance/Props.v`, `Instance/Lambda.v` (for the syntactic-category idioms), `Construction/Quotient.v`, `Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.6 Exercise 2 (book p. 98), including the quantification over theories, with `≈` discipline
- [ ] The scope of the syntax fragment is disclosed in the file header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the cartesian and closed instances
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Theory/Lindenbaum.v
make && make todo
```

```coq
Print Assumptions Lindenbaum_Closed.
```

Reviewer checks: the category is genuinely parameterised by a theory (instantiating at two different axiom sets gives two different categories); the transposition really is the deduction theorem for the chosen derivability relation.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.6:ex2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.6: Internal composition in a cartesian closed category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.6:ex4]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.6, book p. 98 (PDF p. 107), Exercise 4. Item covered: `maclane:IV.6:ex4`.

## Background

Every cartesian closed category has an internal composition morphism between exponentials that reduces to ordinary composition of functions in sets, and it is associative; this is what makes such a category enriched over itself. See [nLab: internal hom](https://ncatlab.org/nlab/show/internal+hom) and [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

Absent. No morphism between exponentials of that shape is declared anywhere: searches for the type shape and for the obvious names return nothing. `Functor/Hom/Internal.v:40` supplies only the internal-hom bifunctor's action on morphisms.

The apparent counter-example is not one: `Structure/Closed.v:175` does contain a `hom_compose` field of the right shape, but it sits inside a comment block spanning `:154`–`:195`, and the file header at `:26` says the class is "sketched but commented out below" — CLAUDE.md independently records `Structure/Closed.v` as an incomplete Eilenberg–Kelly stub whose class is not in force. `Construction/Enriched.v:117` (`ecompose`) and `:127` (`ecompose_assoc`) are *fields* of the V-category class, and no cartesian closed category is enriched over itself in-tree, so they do not supply the morphism either.

## Work to be done

Suggested module: `Structure/Cartesian/Closed/Composition.v`.

1. Construct the internal composition morphism as the transpose of the double evaluation, and prove it natural in all three objects.
2. Prove it agrees with ordinary composition in `Sets` and in `Coq` (the two concrete cartesian closed instances), which is the "agrees with composition of functions" half of the exercise.
3. Prove associativity, and the two unit laws against the internal identity (the transpose of a projection), so the data is a genuine enrichment.
4. As a payoff, exhibit a cartesian closed category as enriched over itself, discharging the currently-unwitnessed self-enrichment and closing the gap that leaves `Construction/Enriched.v`'s `ecompose` without a cartesian-closed example.

In-tree donors: `Structure/Cartesian/Closed.v` (`curry`, `uncurry`, `eval`, `ump_exponents`), `Functor/Hom/Internal.v`, `Construction/Enriched.v`, `Instance/Sets/Cartesian/Closed.v`, `Instance/Coq.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.6 Exercise 4 (book p. 98), with `≈` discipline
- [ ] Associativity and the agreement with set-level composition are both proved
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the composition morphism and for associativity
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated if the self-enrichment lands (flagship-level)

## Verification

```bash
coqc -R . Category Structure/Cartesian/Closed/Composition.v
make && make todo
```

```coq
Print Assumptions internal_compose.
Print Assumptions internal_compose_assoc.
```

Reviewer checks: the new code does not revive the commented `Structure/Closed.v` stub, which is a different (Eilenberg–Kelly) presentation; the `Sets` agreement lemma is stated pointwise on setoid morphisms.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.6:ex4"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.6: Cartesian closure is not inherited by functor categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.6:ex5]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.6, book p. 98 (PDF p. 107), Exercise 5. Item covered: `maclane:IV.6:ex5`.

## Background

Cartesian closure of a category does not pass to functor categories out of an arbitrary shape: extra hypotheses (smallness of the shape and completeness of the target) are needed, and without them a counterexample exists. See [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category) and [nLab: functor category](https://ncatlab.org/nlab/show/functor+category).

## Current state in the library

Absent in both directions.

- `Instance/Fun/Cartesian.v:111` — `Functor_Category_Cartesian (C D : Category) (_ : @Cartesian D) : @Cartesian (@Fun C D)`, pointwise products. This is the only structure lemma for functor categories in the tree; a search for a corresponding closure instance returns nothing.
- `Instance/Fun.v:105` remarks in prose that a functor category is cartesian closed when the source is small and the target is cartesian closed and complete, with no proof.
- `Instance/Cat/Cartesian/Closed.v:47` — `Cat_Closed` uses a functor category *as the exponential of* `Cat`; that is closure of `Cat`, not of an arbitrary functor category.
- The two "not cartesian closed" remarks in the tree (`Instance/Coq/Par.v:219`, `Instance/Coq/ParE.v:177`) concern partiality Kleisli categories and are unrelated.

Neither the positive statement under hypotheses nor the exercise's counterexample exists.

## Work to be done

Suggested module: `Instance/Fun/Closed.v`.

1. Exhibit the counterexample: a cartesian closed target and a shape for which the functor category fails to be cartesian closed. The cleanest route in this library is to show that the required exponential would force a left adjoint to a product functor that provably does not exist for the chosen shape — state the failure as a theorem, not as a comment.
2. Prove the positive companion under the hypotheses `Instance/Fun.v:105` names, at least for presheaf-shaped cases, so the file records both sides. If the general positive result is too large for one PR, scope it out explicitly and keep the counterexample.
3. Replace the prose claim at `Instance/Fun.v:105` with a pointer to whichever of the two is delivered.

In-tree donors: `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Structure/Cartesian/Closed.v`, `Instance/Cat/Cartesian/Closed.v`, `Adjunction/Continuity.v` (for the adjoint-preservation obstruction argument).

## Definition of Done

- [ ] Statement fidelity to §IV.6 Exercise 5 (book p. 98): a genuine counterexample, not a remark; `≈` discipline
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the counterexample
- [ ] New file registered in `_CoqProject`
- [ ] `Instance/Fun.v:105`'s prose claim updated
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Fun/Closed.v
make && make todo
```

```coq
Print Assumptions functor_category_not_closed.
```

Reviewer checks: the counterexample is a proved negation, not an unproved remark; the scope of any deferred positive result is disclosed in the header.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.6:ex5"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.7: Maps of adjunctions"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.7:def1, maclane:IV.7:prop1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book p. 99 (PDF p. 108): the definition of a map of adjunctions and Proposition 1. Items covered: `maclane:IV.7:def1`, `maclane:IV.7:prop1`.

## Background

A map of adjunctions is a pair of functors making both functor squares commute strictly and making the two hom-set bijections agree; the agreement condition is equivalent to a single unit condition and equally to a single counit condition. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [nLab: mate](https://ncatlab.org/nlab/show/mate).

## Current state in the library

Absent. Nothing in the tree quantifies over a pair of functors making both squares commute, and no lemma writes either the unit condition or the counit condition. Searches for a morphism, map or transformation of adjunctions return nothing, and there is no two-category-of-adjunctions development.

The nearest relative is `Theory/Bicategory/Mates.v`, which sets up exactly this configuration — two internal adjunctions and two bounding 1-cells — but fills the squares with a genuine 2-cell rather than requiring strict commutation, and never packages a map of adjunctions. `Instance/Adj.v:29`'s header discusses morphisms of adjunctions but explicitly declines to impose any condition on them.

## Work to be done

Suggested module: `Adjunction/Map.v`.

1. Define a map of adjunctions: two adjunctions, functors `K` and `L` between the respective codomains and domains, the two strict commutation equations for the functor squares, and the hom-set compatibility condition stated for all transposable arrows.
2. Prove Proposition 1: under the two square equations, hom-set compatibility is equivalent to the unit condition, and equally to the counit condition. Both equivalences, both directions.
3. Prove that maps of adjunctions compose and that identities are maps of adjunctions, so the notion has the API the following sections need.
4. Note the relation to the mates machinery in the header: the map-of-adjunctions notion is the strict special case in which the mate 2-cells are identities, so the two developments are visibly related rather than parallel.

A modelling decision must be made and disclosed: "the functor squares commute" is an equality of functors, which in this library is usually stated up to `≈`. Deliver the `≈` version (which is the usable one) and record what is lost relative to Mac Lane's strict formulation.

In-tree donors: `Theory/Adjunction.v`, `Adjunction/Hom.v`, `Adjunction/Natural/Transformation.v`, `Theory/Functor.v` (functor equality up to `≈`), `Theory/Bicategory/Mates.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.7 (book p. 99), with `≈` discipline and the strictness decision disclosed in the header
- [ ] Both equivalences of Proposition 1, in both directions
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the definition and for Proposition 1
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Map.v
make && make todo
```

```coq
Print Assumptions MapOfAdjunctions.
Print Assumptions map_of_adjunctions_unit_iff_counit.
```

Reviewer checks: the hom-set condition is quantified over all arrows, not checked at one distinguished argument; the composition lemma is present.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.7:def1","maclane:IV.7:prop1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.7: Conjugate natural transformations and the four characterizations of conjugacy"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.7:def2, maclane:IV.7:thm2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book pp. 99–100 (PDF pp. 108–110): the definition of conjugate natural transformations and Theorem 2. Items covered: `maclane:IV.7:def2`, `maclane:IV.7:thm2`.

## Background

Given two adjunctions between the same pair of categories, a transformation between the left adjoints and one between the right adjoints are *conjugate* when they correspond under the two transposes; this is equivalent to each of four pasting equations, and each transformation determines its partner uniquely, giving a bijection. See [nLab: mate](https://ncatlab.org/nlab/show/mate) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The library supplies an *operator* computing the partner, at greater generality than the book, but never the conjugacy *relation* and never the defining hom-set square.

- `Theory/Bicategory/Mates.v:476` — `mate`, the pasting composite; `:480` — `mate_inv`; `:489` and `:498` — `mate_roundtrip_left` and `mate_roundtrip_right`; `:515` — `mate_iso`, packaging the two as an isomorphism of 2-cell setoids in `Sets`. All of this is over an arbitrary bicategory with arbitrary bounding 1-cells, of which Mac Lane's setting is the case where both bounding cells are identities.
- `Instance/Cat/Bicategory/Adjunction.v:244` — `Cat_mate_unfold_raw`, the classical conjugate formula componentwise in `Cat`; `:260` — `Cat_mate_unfold`, the same through the transpose; `:163` — `Cat_BicatAdjunction_Adjunction_iff`, so the machinery applies to ordinary adjunctions.
- `Theory/Bicategory/Adjunction.v:347` — `mate_charac`, the unit characterisation, but only in the degenerate case of two right adjoints of a single 1-cell.
- `Instance/Adj.v:29` — the file's own caveat names the conjugacy condition and explicitly declines to impose it.

Missing: any predicate expressing conjugacy of a *pair*; the defining hom-set square, phrased in the two transposes; the equivalence of that square with `τ ≈ mate σ`; the two pasting characterisations that are not the definitions of `mate` and `mate_inv`; and any ordinary-category restatement, so that a caller must currently transport by hand along the bicategorical bridge.

## Work to be done

Suggested module: `Adjunction/Conjugate.v`.

1. Define `Conjugate σ τ` for two adjunctions between the same pair of categories: the hom-set square, stated for all transposable arrows, using the library's `⌊−⌋` transposes.
2. Prove the four characterisations equivalent to it. Two of them are the pasting composites that already define `mate` and `mate_inv`, so those legs reduce to unfolding plus the existing round trips; the other two — the counit equation and the unit equation — must be proved, and neither is stated anywhere today.
3. Prove the bijection: each transformation between left adjoints has a unique conjugate, and dually, recovering `mate_iso` as the specialisation with identity bounding cells and stating it in ordinary-category vocabulary.
4. Provide the specialisation lemma explicitly, so that consumers of `F ⊣ U` never have to route through `Cat_BicatAdjunction_Adjunction_iff` by hand.

In-tree donors: `Theory/Bicategory/Mates.v`, `Instance/Cat/Bicategory/Adjunction.v`, `Theory/Adjunction.v`, `Adjunction/Natural/Transformation.v`, `Theory/Natural/Transformation.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.7 (book pp. 99–100): the definition is the hom-set square, and all four characterisations are proved equivalent to it; `≈` discipline
- [ ] The bijection is stated in ordinary-category terms, not only bicategorically
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the conjugacy predicate, the four equivalences and the bijection
- [ ] New file registered in `_CoqProject`
- [ ] `Instance/Adj.v`'s caveat updated to cite the now-available conjugacy condition
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated (flagship-level: it upgrades the mate operator to the mate relation)

## Verification

```bash
coqc -R . Category Adjunction/Conjugate.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Conjugate.
Print Assumptions conjugate_characterizations.
Print Assumptions conjugate_bijection.
```

Reviewer checks: the definition is the hom-set square quantified over all arrows, not the value of the square at one distinguished argument; the two genuinely new characterisations (unit form and counit form) are proved, not assumed.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:IV.7:def2","maclane:IV.7:thm2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.7: The category of adjunctions and conjugate pairs"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.7:construction1]
deps_item_ids: [maclane:IV.7:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book p. 101 (PDF p. 110), the category of adjunctions between two fixed categories. Item covered: `maclane:IV.7:construction1`.

## Background

Conjugate pairs compose, so the adjunctions between two fixed categories form a category whose arrows are conjugate pairs, equipped with two forgetful functors onto the two relevant functor categories, one of them contravariant. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [nLab: 2-category](https://ncatlab.org/nlab/show/2-category).

## Current state in the library

A category of adjunctions exists but is, by its own admission, the wrong one.

- `Instance/Adj.v:43` — `Adj (C D : Category) : Category`, objects the triples of two functors plus an adjunction, homs the bare product of a transformation between the left adjoints and one between the right adjoints, composition componentwise.
- `Instance/Adj.v:29`–`:41` — the file's `CAVEAT` states outright that the standard construction takes conjugate pairs as morphisms, that the hom defined there imposes no such condition, that this is "why every category obligation discharges trivially", and that the result is "a genuine category but a coarser one".

Three further gaps. The composition-of-conjugate-pairs lemma is proved nowhere — `Theory/Bicategory/Mates.v:52`–`:55` explicitly descopes the composition functoriality of mates (descope ledger entry 10). Mac Lane's second component runs in the opposite direction to the in-tree one, so the contravariance of the second forgetful functor has no counterpart. And neither forgetful functor is defined; in fact `Adj` has no consumers anywhere in the tree.

## Work to be done

Suggested module: `Instance/Adj.v` (tighten in place) plus a new `Instance/Adj/Forgetful.v`.

1. Prove that conjugate pairs are closed under componentwise composition and contain the identities. This is the substantive lemma the current file avoids by not imposing the condition.
2. Redefine the hom of the category of adjunctions to be the conjugate pairs, with Mac Lane's variance: the second component runs from the second right adjoint to the first. Keep the old coarse category if anything depends on it — nothing currently does — and say in the header which is which.
3. Build the two forgetful functors: one onto the functor category of left adjoints, and one from the opposite of the category of adjunctions onto the functor category of right adjoints.
4. Remove the `CAVEAT`, replacing it with a pointer to the conjugacy condition now imposed.

In-tree donors: `Instance/Adj.v`, `Instance/Fun.v`, `Theory/Bicategory/Mates.v`, `Theory/Natural/Transformation.v`, `Instance/Adjoints.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.7 (book p. 101), including the variance of the second component; `≈` discipline
- [ ] The `CAVEAT` in `Instance/Adj.v` is discharged, not merely edited
- [ ] Both forgetful functors are defined and proved functorial
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the category and the two functors
- [ ] Files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Adj.v
coqc -R . Category Instance/Adj/Forgetful.v
make && make todo
```

```coq
Print Assumptions Adj.
Print Assumptions Adj_Forget_Left.
```

Reviewer checks: the category laws now rest on the composition-of-conjugates lemma rather than discharging trivially; the second forgetful functor is contravariant, as the book has it.

## Dependencies

- Depends on: maclane:IV.7:def2

<!-- catalog: {"ids":["maclane:IV.7:construction1"],"deps":["maclane:IV.7:def2"]} -->

---8<---

```yaml
title: "MacLane IV.7: Adjunctions with a parameter"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.7:thm3, maclane:IV.7:remark1, maclane:IV.7:ex2]
deps_item_ids: [maclane:IV.7:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book pp. 101–102 (PDF pp. 110–111): Theorem 3, the motivating remark, and Exercise 2. Items covered: `maclane:IV.7:thm3`, `maclane:IV.7:remark1`, `maclane:IV.7:ex2`.

## Background

If a bifunctor has, for each value of its second argument, a right adjoint in the first, then those right adjoints assemble uniquely into a bifunctor contravariant in the parameter, for which the adjunction bijection is natural in all three variables; uniqueness of conjugates supplies the functoriality. The currying bijection in sets and the tensor-hom bijection for modules are the standard examples. See [nLab: two-variable adjunction](https://ncatlab.org/nlab/show/two-variable+adjunction) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Absent as a theorem; the examples exist only in their per-object form.

- Searches for parametrised, parameterised or two-variable adjunctions return nothing.
- `Functor/Hom/Internal.v:40` — `InternalHomFunctor : C^op ∏ C ⟶ C`, built by hand out of `curry` with its functor laws proved directly. It takes no family of adjunctions as input, claims no uniqueness, and asserts no three-variable naturality, so it is a witness of the theorem's conclusion in one case, not a proof of the theorem.
- `Instance/Sets/Cartesian/Closed.v:38` (`Sets_Closed`) and `Instance/Coq.v:167` (`Coq_Closed`) supply the underlying currying bijection of the first example.
- `Theory/Universal/Arrow.v:185` — `LeftAdjointFunctorFromUniversalArrows`, the object-indexed one-variable analogue of the assembly this theorem performs.
- `Theory/Dinatural.v:51` (`Dinatural`), `Structure/Wedge.v` and `Structure/End.v` exist and are the shape Exercise 2's answer takes, but nothing links them to an adjunction unit.

A load-bearing negative: `Structure/Cartesian/Closed.v:51` shows the `Closed` class asks only for the family `exp_iso` plus the beta law, with *no naturality field in any variable*; `ClosedMonoidal` has the same shape. So even the conclusion of the theorem cannot currently be phrased against the closed structures, and the parameter reading of the currying bijection — that post-composition with a map of the parameter and the induced map of internal homs are conjugate — is nowhere stated.

## Work to be done

Suggested module: `Adjunction/Parameter.v`.

1. Define an adjunction with a parameter: a bifunctor together with, for each parameter value, a right adjoint and the hom-set bijection.
2. Prove Theorem 3: the right adjoints extend uniquely to a bifunctor contravariant in the parameter such that the bijection is natural in all three variables. The functoriality comes from uniqueness of conjugates, so the proof should invoke the conjugacy bijection rather than recomputing it.
3. Prove the dual form (starting from the right-adjoint bifunctor).
4. Instantiate at the currying bijection: show that for a cartesian closed category, mapping the parameter gives conjugate transformations between the product functors and between the internal homs, and conclude the naturality of the currying bijection in the parameter — the clause the `Closed` class does not currently carry. State it as a standalone lemma so `Structure/Cartesian/Closed.v`'s users can consume it.
5. Answer Exercise 2: identify the property of the unit corresponding to naturality in the parameter, using the dinaturality/wedge vocabulary already in `Theory/Dinatural.v` and `Structure/Wedge.v`.
6. Note the module tensor-hom example as an instance to be added once the module categories exist; do not leave it as an unproved claim.

In-tree donors: `Functor/Bifunctor.v`, `Functor/Hom/Internal.v`, `Structure/Cartesian/Closed.v`, `Theory/Dinatural.v`, `Structure/Wedge.v`, `Theory/Universal/Arrow.v`, `Adjunction/Conjugate.v` (new).

## Definition of Done

- [ ] Statement fidelity to §IV.7 Theorem 3, its remark, and Exercise 2 (book pp. 101–102), with `≈` discipline
- [ ] The uniqueness clause of Theorem 3 is proved, not just existence
- [ ] The currying instance is delivered, including naturality in the parameter
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the theorem, its dual, and the currying instance
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated (flagship-level)

## Verification

```bash
coqc -R . Category Adjunction/Parameter.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions ParametrizedAdjunction.
Print Assumptions parametrized_right_adjoint_bifunctor.
```

Reviewer checks: the assembled bifunctor is proved *unique*, which is the whole point of the theorem; the currying instance proves parameter naturality rather than assuming it.

## Dependencies

- Depends on: maclane:IV.7:def2
- Depends on: #239

<!-- catalog: {"ids":["maclane:IV.7:thm3","maclane:IV.7:remark1","maclane:IV.7:ex2"],"deps":["maclane:IV.7:def2"]} -->

---8<---

```yaml
title: "MacLane IV.7: Choosing right adjoints functorially"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.7:ex3]
deps_item_ids: [maclane:IV.7:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book p. 102 (PDF p. 111), Exercise 3. Item covered: `maclane:IV.7:ex3`.

## Background

The functors admitting a right adjoint span a full subcategory of a functor category; choosing a right adjoint for each and sending a transformation to its conjugate makes the choice into a functor, contravariant in the transformations. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [nLab: mate](https://ncatlab.org/nlab/show/mate).

## Current state in the library

Absent. The closest in-tree analogue of the arrow part is the mate operator (`Theory/Bicategory/Mates.v:476`, with the componentwise formula at `Instance/Cat/Bicategory/Adjunction.v:260`), which at identity bounding cells does supply the assignment from a transformation between left adjoints to one between right adjoints. What is entirely missing is the item's substance: the full subcategory of a functor category cut out by "has a right adjoint", the choice of a right adjoint on objects, and the two functor laws. `Theory/Bicategory/Mates.v:52`–`:56` explicitly descopes mate functoriality (descope ledger entry 10), which is exactly the identity and composition laws this exercise needs.

## Work to be done

Suggested module: `Adjunction/Choice.v`.

1. Cut out the full subcategory of the functor category on the functors that admit a right adjoint, using `Construction/Subcategory.v`. Note that "admits a right adjoint" must be carried as data (a chosen adjoint), not as a bare existential, so that the choice in the exercise is constructive rather than an appeal to choice.
2. Define the object part of the assignment (the chosen right adjoint) and the arrow part (the conjugate of a given transformation), and prove the two functor laws — identity and composition — which is where the descoped mate functoriality has to be supplied.
3. Deliver the result as a functor from the opposite of that subcategory to the functor category of right adjoints.
4. Record the independence-of-choice statement: two different choices of right adjoints give naturally isomorphic functors, which is what makes the construction well behaved.

In-tree donors: `Theory/Bicategory/Mates.v`, `Instance/Cat/Bicategory/Adjunction.v`, `Construction/Subcategory.v`, `Instance/Fun.v`, `Theory/Adjunction.v` (`right_adjoint_iso`), `Adjunction/Conjugate.v` (new).

## Definition of Done

- [ ] Statement fidelity to §IV.7 Exercise 3 (book p. 102), with `≈` discipline
- [ ] The choice of right adjoints is data, so no axiom of choice is used
- [ ] Both functor laws proved (this is the descoped mate functoriality; the descope note in `Theory/Bicategory/Mates.v` should be updated if it is discharged here)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the functor
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Choice.v
make && make todo
```

```coq
Print Assumptions RightAdjointFunctor.
```

Reviewer checks: no choice axiom appears in `Print Assumptions`; the composition law is proved for conjugates, not inherited from the underlying transformations.

## Dependencies

- Depends on: maclane:IV.7:def2

<!-- catalog: {"ids":["maclane:IV.7:ex3"],"deps":["maclane:IV.7:def2"]} -->

---8<---

```yaml
title: "MacLane IV.7: Adjoint squares and the Palmquist mates bijection"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.7:ex4, maclane:IV.7:ex5]
deps_item_ids: [maclane:IV.7:def2, maclane:IV.7:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.7, book p. 103 (PDF p. 112), Exercises 4 (Kelly) and 5 (Palmquist). Items covered: `maclane:IV.7:ex4`, `maclane:IV.7:ex5`.

## Background

An adjoint square consists of two adjunctions, two connecting functors, and two transformations satisfying a commuting hom-set condition; each transformation determines the other. Palmquist's variant establishes a bijection between transformations out of one composite and into another. See [nLab: mate](https://ncatlab.org/nlab/show/mate) and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The mate machinery instantiates to the right shape and is in some ways stronger than the exercises, but the exercises' own statements are not present.

- `Theory/Bicategory/Mates.v:476`, `:480`, `:489`, `:498`, `:515` — `mate`, `mate_inv`, the two round trips, and `mate_iso`, over an arbitrary bicategory with arbitrary bounding 1-cells. Instantiated in `Cat` with the two connecting functors as the bounding cells, `mate` sends a transformation of the shape Exercise 4 calls the first one to a transformation of the shape it calls the second — so "each determines the other" is genuinely covered.
- `Instance/Cat/Bicategory/Adjunction.v:244` and `:260` — the componentwise unfoldings; `:163` — the bridge to ordinary adjunctions.
- `Theory/Bicategory/Mates.v:183`, `:245`, `:306`, `:330`, `:390`, `:450` — the two factor bijections (`precomp` and `postcomp`) with their round trips, which are exactly the two factors Palmquist's bijection is composed from; `Instance/Cat/Bicategory/Adjunction.v:187` and `:214` specialise them to ordinary functors.

Missing for Exercise 4: the adjoint-square *condition* itself, quantified over all transposable arrows. At one distinguished argument the condition collapses to the componentwise formula already proved, so what the library has is the value the square forces at one point, taken as the definition of `mate`, with the "for all arrows" half absent; and the exercise's first ask — several equivalent unit/counit expressions of the condition — has exactly one in-tree expression, the pasting composite that defines `mate`.

Missing for Exercise 5: the composite bijection is never assembled. Neither the forward and backward maps, nor the associator bookkeeping lining up the two factors, nor the round trips, nor the packaging as an isomorphism of setoids, nor the `Cat`-level unfolding to ordinary natural transformations.

## Work to be done

Suggested module: `Adjunction/Square.v`.

1. Define an adjoint square by Mac Lane's condition: the hom-set square commutes for every transposable arrow. State it in ordinary-category vocabulary, over `F ⊣ U`, not bicategorically.
2. Prove the condition equivalent to `τ ≈ mate σ`, i.e. that the mate operator computes exactly the partner the condition demands. This is what turns the existing operator into a characterisation.
3. Give the several unit/counit expressions the exercise asks for, and prove them equivalent — at least the unit form, the counit form, and the two pasting forms.
4. Assemble Palmquist's bijection: instantiate the two factor bijections at the shapes required, supply the associator splice, prove both round trips, and package the result as an isomorphism of the two transformation setoids, with the `Cat` unfolding.
5. Note in the header that the identity-bounding-cell case recovers the conjugate pairs of the preceding section.

In-tree donors: `Theory/Bicategory/Mates.v`, `Instance/Cat/Bicategory/Adjunction.v`, `Theory/Adjunction.v`, `Adjunction/Conjugate.v` (new), `Theory/Natural/Transformation.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.7 Exercises 4 and 5 (book p. 103), with `≈` discipline
- [ ] The adjoint-square condition is quantified over all arrows, and proved equivalent to the mate equation
- [ ] Palmquist's bijection is delivered with both round trips
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the condition, the characterisation and the bijection
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Adjunction/Square.v
make && make todo
```

```coq
Print Assumptions AdjointSquare.
Print Assumptions adjoint_square_iff_mate.
Print Assumptions palmquist_bijection.
```

Reviewer checks: the statements are in ordinary-category vocabulary so that a caller holding `F ⊣ U` needs no bicategorical transport; the "for all arrows" quantification is present.

## Dependencies

- Depends on: maclane:IV.7:def2
- Depends on: maclane:IV.7:def1

<!-- catalog: {"ids":["maclane:IV.7:ex4","maclane:IV.7:ex5"],"deps":["maclane:IV.7:def2","maclane:IV.7:def1"]} -->

---8<---

```yaml
title: "MacLane IV.8: Horizontal composition of conjugate pairs makes Adj two-dimensional"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.8:thm2, maclane:IV.8:ex1, maclane:IV.8:remark1]
deps_item_ids: [maclane:IV.7:def2, maclane:IV.7:construction1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.8, book p. 104 (PDF p. 113): Theorem 2, Exercise 1, and the closing remark. Items covered: `maclane:IV.8:thm2`, `maclane:IV.8:ex1`, `maclane:IV.8:remark1`.

## Background

Conjugate pairs compose horizontally by the Godement product, the composite is again conjugate for the composite adjunctions, and horizontal composition is a bifunctor between the hom-categories, so the category of categories and adjunctions is two-dimensional in the same sense that Cat is. See [nLab: 2-category](https://ncatlab.org/nlab/show/2-category) and [nLab: mate](https://ncatlab.org/nlab/show/mate).

## Current state in the library

The Cat half of the remark is present at full strength; the adjunction half is not present at all.

- `Theory/Bicategory.v:254` — `hcompose {x y z} : bicat y z ∏ bicat x y ⟶ bicat x z`, a field of the bicategory class: horizontal composition *is* a bifunctor of hom-categories, exactly the remark's shape, for a general bicategory.
- `Instance/Cat/Bicategory.v:64` — `Cat_Hcompose : ([D, E] ∏ [C, D]) ⟶ [C, E]`, whose `fmap_comp` obligation is the middle-four interchange law; `:127` — `Cat_Bicategory`. Together these discharge the remark's closing clause.
- `Instance/Adjoints.v:133` — `Adjoints`, the 1-category of categories and adjunctions, whose hom-sets the remark upgrades to categories.
- `Instance/Adj.v:43` — a hom-category of adjunctions exists, but with no conjugacy condition on its arrows (see its own caveat at `:29`).
- `Theory/Natural/Transformation.v:283` — `nat_hcompose`, the Godement product; `Adjunction/Compose.v:173` — composition of adjunctions.

Missing: the theorem that a horizontal composite of conjugate pairs is conjugate for the composite adjunctions; the bifunctor and the interchange law at the level of conjugate pairs (`Theory/Bicategory/Mates.v:52`–`:55` explicitly descopes exactly this, as descope ledger entry 10); and any bicategory or strict 2-category whose 0-cells are categories and whose 1-cells are adjunctions — the only `Build_Bicategory` uses in the tree are `Cat_Bicategory`, the monoidal delooping, and the lax-transformation construction.

## Work to be done

Suggested module: `Instance/Adj/Bicategory.v`.

1. Prove Theorem 2: the Godement composite of two conjugate pairs is conjugate for the composite adjunctions. This is the load-bearing lemma and needs the conjugacy relation from the preceding section.
2. Prove Exercise 1: horizontal composition of conjugate pairs is a bifunctor between the hom-categories, and derive the interchange law between horizontal and vertical composition of conjugate pairs from its functoriality.
3. Assemble the bicategory (or strict 2-category, if the composition of adjunctions is strictly associative in this library — check and disclose which) whose 0-cells are categories, 1-cells adjunctions, and 2-cells conjugate pairs.
4. Update the descope note in `Theory/Bicategory/Mates.v:52`–`:55` if this discharges it, or narrow it precisely if only part is discharged.

In-tree donors: `Theory/Bicategory.v`, `Instance/Cat/Bicategory.v`, `Instance/Adj.v`, `Instance/Adjoints.v`, `Adjunction/Compose.v`, `Theory/Natural/Transformation.v`, `Adjunction/Conjugate.v` (new).

## Definition of Done

- [ ] Statement fidelity to §IV.8 (book p. 104), with `≈` discipline
- [ ] The interchange law is *derived* from bifunctoriality, as the exercise asks, not proved independently
- [ ] The strict-versus-weak choice for the assembled 2-dimensional structure is disclosed in the header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the composition theorem, the bifunctor, and the assembled structure
- [ ] New file registered in `_CoqProject`
- [ ] The descope note in `Theory/Bicategory/Mates.v` updated
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md index updated (flagship-level)

## Verification

```bash
coqc -R . Category Instance/Adj/Bicategory.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions conjugate_hcompose.
Print Assumptions Adj_Bicategory.
```

Reviewer checks: the horizontal composite is the Godement product of `Theory/Natural/Transformation.v:283`, not a bespoke definition; the conjugacy of the composite is proved for the composite adjunction built by `Adjunction/Compose.v:173`.

## Dependencies

- Depends on: maclane:IV.7:def2
- Depends on: maclane:IV.7:construction1
- Depends on: #283

<!-- catalog: {"ids":["maclane:IV.8:thm2","maclane:IV.8:ex1","maclane:IV.8:remark1"],"deps":["maclane:IV.7:def2","maclane:IV.7:construction1"]} -->

---8<---

```yaml
title: "MacLane IV.8: The free-ring adjunction as a composite in two ways"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.8:ex2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.8, book p. 104 (PDF p. 113), Exercise 2. Item covered: `maclane:IV.8:ex2`.

## Background

The free ring on a set arises as a composite adjunction in two ways: through abelian groups, and through monoids; the two composites agree because the free-ring construction is the monoid ring of the free monoid and equally the free abelian group on the free monoid. See [Wikipedia: Monoid ring](https://en.wikipedia.org/wiki/Monoid_ring) and [nLab: free object](https://ncatlab.org/nlab/show/free+object).

## Current state in the library

Absent, and none of the three categories exists. Searches for a category of rings, of abelian groups or of monoids-as-a-category-of-sets-with-structure return only background prose. The only algebraic categories in-tree are `Theory/Algebra/Monoid/Hom.v:83` (`Mon`, the category of *internal* monoids in a monoidal category, with `Mon_Forget : Mon ⟶ C` at `:93` and no left adjoint) and `Instance/CMon.v:140` (`CMon`, with `CMon_Forget : CMon ⟶ Sets` at `:169`, again with no left adjoint). Not one of the six functors the exercise needs is defined.

The composition machinery, by contrast, is in place: `Adjunction/Compose.v:173` composes adjunctions, and `Instance/Adjoints.v:55` records the composite in the category of adjunctions.

## Work to be done

Suggested module: `Instance/Rng/Free.v`.

1. Once the categories of rings, abelian groups and monoids are available, construct the four intermediate free functors: free abelian group on a set, free monoid on a set, monoid ring of a monoid, and free ring on an abelian group.
2. Prove each is left adjoint to the corresponding forgetful functor.
3. Compose the two chains with `Adjunction/Compose.v:173`, obtaining two adjunctions whose right adjoint is the forgetful functor from rings to sets.
4. Prove the two composites isomorphic — that is the actual content of the exercise, and it should be stated as a natural isomorphism of the two left adjoints, with the corresponding statement for the units.

In-tree donors: `Adjunction/Compose.v`, `Instance/Adjoints.v`, `Theory/Universal/Arrow.v`, `Instance/CMon.v`, `Theory/Adjunction.v:404` (`left_adjoint_iso`, for the uniqueness argument).

## Definition of Done

- [ ] Statement fidelity to §IV.8 Exercise 2 (book p. 104), with `≈` discipline
- [ ] The agreement of the two composites is proved, not merely both composites constructed
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` reported for each adjunction, with stdlib axioms enumerated per docs/AXIOMS.md
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Rng/Free.v
make && make todo
```

```coq
Print Assumptions free_ring_via_ab.
Print Assumptions free_ring_composites_agree.
```

Reviewer checks: both routes are built and compared; the comparison is a natural isomorphism, not a bare object-level equality.

## Dependencies

- Depends on: #256
- Depends on: #257
- Depends on: #296

<!-- catalog: {"ids":["maclane:IV.8:ex2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.8: Bimodule tensor adjunctions and their composites"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IV.8:ex3]
deps_item_ids: [maclane:IV.6:construction1, maclane:IV.7:thm3]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.8, book p. 104 (PDF p. 113), Exercise 3. Item covered: `maclane:IV.8:ex3`.

## Background

Tensoring with a bimodule is left adjoint to the hom out of it; the family is an adjunction with the bimodule as parameter, and composing two such adjunctions corresponds to tensoring the bimodules. See [nLab: bimodule](https://ncatlab.org/nlab/show/bimodule) and [Wikipedia: Tensor-hom adjunction](https://en.wikipedia.org/wiki/Tensor-hom_adjunction).

## Current state in the library

Absent, with no ring, module or bimodule anywhere in code; every `Mod`, `R-Mod` and `bimodule` hit is background prose.

The near-miss is correctly excluded: `Structure/Cartesian/Closed.v:43`, `Structure/Monoidal/Closed.v:46` and `Structure/Monoidal/StarAutonomous.v:109` carry the *endo* tensor-hom adjunction within one monoidal category. The exercise's adjunction runs *between two different module categories* along a bimodule, which the endo form cannot express. There is also no vehicle at all for part (b): searches for parametrised adjunctions return nothing.

## Work to be done

Suggested module: `Instance/Module/Bimodule.v`.

1. Define bimodules over a pair of rings, and the tensor product of a right module with a bimodule.
2. Prove part (a): tensoring with a bimodule is left adjoint to the hom out of it, as a pair of functors between the two module categories.
3. Prove part (b): the family is an adjunction with the bimodule as parameter, using the parametrised-adjunction theorem rather than re-deriving the functoriality.
4. Prove part (c): the composite of two such adjunctions is the adjunction of the tensor product of the two bimodules, comparing the composite left adjoint with the tensor by the composite bimodule up to natural isomorphism.

In-tree donors: the module category and its tensor (see the dependency), `Adjunction/Compose.v`, `Adjunction/Parameter.v` (new), `Theory/Adjunction.v:404`, `Theory/Profunctor.v` (the bimodule/profunctor analogy, useful for the composite's shape).

## Definition of Done

- [ ] Statement fidelity to §IV.8 Exercise 3 (book p. 104), all three parts, with `≈` discipline
- [ ] Part (c) compares the composite with the tensor-product bimodule, not merely asserts it
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` reported, with stdlib axioms enumerated per docs/AXIOMS.md
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Module/Bimodule.v
make && make todo
```

```coq
Print Assumptions bimodule_tensor_hom_adjunction.
Print Assumptions bimodule_adjunction_composite.
```

Reviewer checks: the adjunction is between two different module categories (the endo form would not satisfy the exercise); part (b) uses the parametrised-adjunction theorem.

## Dependencies

- Depends on: maclane:IV.6:construction1
- Depends on: maclane:IV.7:thm3
- Depends on: #258

<!-- catalog: {"ids":["maclane:IV.8:ex3"],"deps":["maclane:IV.6:construction1","maclane:IV.7:thm3"]} -->

---8<---

```yaml
title: "MacLane IV.9: A subobject classifier for the category of sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.9:construction1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.9, book p. 105 (PDF p. 114), characteristic functions and the subobject classifier of the category of sets. Item covered: `maclane:IV.9:construction1`.

## Background

Every subset is the pullback of a two-element truth inclusion along its characteristic function, and that square determines the subset, so the two-element inclusion is a subobject classifier for sets. See [nLab: subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier) and [Wikipedia: Subobject classifier](https://en.wikipedia.org/wiki/Subobject_classifier).

## Current state in the library

The literal two-element classifier is instantiated only for *finite* sets, and for the library's category of setoids the classifier content exists but one universe up, deliberately.

- `Instance/FinSet/Classifier.v:353` — `FinSet_Classifier : SubobjectClassifier FinSet FinSet_Terminal`, with a two-element truth object and the membership-in-the-image characteristic function, both classifying obligations discharged; `:335` — `finset_monic_iff_injective`; `:264` — `FinSet_Pullbacks`, the tree's only `HasPullbacks` instance.
- `Instance/Sets/Classifier.v:151`, `:158`, `:186` — `PropSetoid`, `sets_true`, `char_setoid`; `:224` — `sets_char_pullback`; `:283` — `sets_char_unique`; `:341` — `sets_char_subobject`, the one-level shadow.
- `Structure/SubobjectClassifier.v:187` — `classifier_classifies`, the "this square determines the subobject" content.

The obstruction is documented in `Instance/Sets/Classifier.v:29`–`:45`: morphism equivalence in this library is `Type`-valued, so the truth-value setoid must live one universe up, and the one-level pullback form is argued there to be unstatable in that encoding. Consequently there is no `SubobjectClassifier Sets` instance (the tree contains exactly one instance of the class), no `HasPullbacks Sets`, and no `ElementaryTopos Sets`.

## Work to be done

Suggested module: `Instance/Sets/Classifier.v` (extend) plus `Instance/Sets/Pullback.v`.

1. Supply `HasPullbacks Sets`, which is missing and is needed by everything downstream (the classifying square, the topos assembly, base change).
2. Attack the universe obstruction directly rather than around it. Either (a) find an encoding of the truth object that stays at one level — for instance a two-element setoid together with a proof-relevant membership predicate, or a `Prop`-valued shadow with a decidability discipline — and deliver a genuine `SubobjectClassifier Sets` instance; or (b) prove, and record in the file, that no such instance exists in this encoding, upgrading the current in-file argument from prose to a theorem.
3. Whichever path is taken, keep the existing cross-universe theorems and relate them to the outcome, so that the file has one story rather than two.
4. Update `Instance/Sets.v:103`, `:424`–`:425` and `Theory/Sheaf.v:84`, which currently discuss the classifier for sets in prose.

In-tree donors: `Instance/Sets/Classifier.v`, `Instance/FinSet/Classifier.v` (the working template), `Structure/SubobjectClassifier.v`, `Theory/Morphisms/Stability.v` (`IsPullback`), `Instance/Sets/Image.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.9 (book p. 105), with `≈` discipline
- [ ] `HasPullbacks Sets` delivered
- [ ] Either a `SubobjectClassifier Sets` instance, or a proved impossibility in the current encoding, with the choice disclosed in the header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` beyond what docs/AXIOMS.md already permits for `Instance/`
- [ ] `Print Assumptions` reported for the new instances
- [ ] Files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md and docs/INHABITATION.md updated (flagship-level either way)

## Verification

```bash
coqc -R . Category Instance/Sets/Pullback.v
coqc -R . Category Instance/Sets/Classifier.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Sets_Pullbacks.
Print Assumptions Sets_Classifier.
```

Reviewer checks: no universe inconsistency is hidden behind a `Type` annotation; if the impossibility route is taken, the theorem is about this encoding specifically and says so.

## Dependencies

- Depends on: #333

<!-- catalog: {"ids":["maclane:IV.9:construction1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane IV.9: Subobject classifiers for functor categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.9:construction2, maclane:IV.9:remark1]
deps_item_ids: [maclane:IV.9:construction1, maclane:IV.3:remark1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.9, book pp. 105–106 (PDF pp. 114–115): the classifier for the category of functions, and the remark that every set-valued functor category has one. Items covered: `maclane:IV.9:construction2`, `maclane:IV.9:remark1`.

## Background

For the arrow shape the classifier is an explicit three-element object mapping onto a two-element one; in general the classifier of a set-valued functor category is the functor of sieves, and Mac Lane leaves finding it to the reader. See [nLab: sieve](https://ncatlab.org/nlab/show/sieve) and [nLab: subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier).

## Current state in the library

Absent for every functor category.

- The only structure instance on any functor category in the tree is `Instance/Fun/Cartesian.v:111` (`Functor_Category_Cartesian`, pointwise products); `ls Instance/Fun/` contains only that file. There is no terminal object, no closed structure, no pullbacks and no classifier for a functor category.
- Sieves are never defined in code.
- `Theory/Subobject/Functor.v` builds the subobject presheaf by reindexing (its `SubFunctor` occurrences at `:27` and `:199` are section delimiters, not a subfunctor development), so the poset of subfunctors of a presheaf does not exist either.
- `Theory/Sheaf.v:84`'s mention of a presheaf topos carrying a classifier is narrative prose in a background essay.

## Work to be done

Suggested modules: `Theory/Sieve.v` and `Instance/Fun/Classifier.v`.

1. Define sieves on an object of a small category and prove they form a presheaf, with restriction along morphisms.
2. Prove that subfunctors of a set-valued functor correspond to natural families of sieves, which is the content of the classification.
3. Supply the prerequisites the classifier needs on a functor category: terminal object and pullbacks, both pointwise.
4. Deliver a `SubobjectClassifier` instance for the functor category, with the sieve presheaf as the truth object and the maximal sieve as the truth arrow.
5. Specialise to the arrow shape and check the classifier really is Mac Lane's explicit three-element construction, so the general answer visibly subsumes the worked example.

In-tree donors: `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Structure/SubobjectClassifier.v`, `Theory/Subobject.v`, `Theory/Subobject/Functor.v`, `Instance/FinSet/Classifier.v` (the working template), `Construction/Arrow.v`, `Instance/Two.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.9 (book pp. 105–106), including the identification of the arrow-shape case with the explicit construction; `≈` discipline
- [ ] Pointwise terminal and pullback instances for functor categories delivered
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` beyond what docs/AXIOMS.md permits at the instance layer
- [ ] `Print Assumptions` reported for the sieve presheaf and the classifier
- [ ] New files registered in `_CoqProject`
- [ ] `Theory/Sheaf.v:84`'s prose updated to cite the proved classifier
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md and docs/INHABITATION.md updated (flagship-level)

## Verification

```bash
coqc -R . Category Theory/Sieve.v
coqc -R . Category Instance/Fun/Classifier.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Sieve_Presheaf.
Print Assumptions Fun_Classifier.
```

Reviewer checks: the arrow-shape specialisation is proved, not asserted; the monos used are the pointwise ones, which requires the pointwise mono characterisation.

## Dependencies

- Depends on: maclane:IV.9:construction1
- Depends on: maclane:IV.3:remark1
- Depends on: #339
- Depends on: #277

<!-- catalog: {"ids":["maclane:IV.9:construction2","maclane:IV.9:remark1"],"deps":["maclane:IV.9:construction1","maclane:IV.3:remark1"]} -->

---8<---

```yaml
title: "MacLane IV.10: Sets and presheaf categories as elementary toposes"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.10:remark1]
deps_item_ids: [maclane:IV.9:construction1, maclane:IV.9:remark1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.10, book p. 107 (PDF p. 116), the remark that sets and presheaves form toposes. Item covered: `maclane:IV.10:remark1`.

## Background

The category of sets is an elementary topos, and so is the category of set-valued presheaves on any small category. See [nLab: topos](https://ncatlab.org/nlab/show/topos) and [Wikipedia: Topos](https://en.wikipedia.org/wiki/Topos).

## Current state in the library

Neither half is proved; one topos exists, over a different category.

- `Instance/FinSet/Topos.v:38` — `FinSet_Topos : ElementaryTopos FinSet`, a genuine, fully computable elementary topos — but of skeletal *finite* sets.
- For the category of setoids: `Instance/Sets.v:248` (`Sets_Terminal`), `Instance/Sets/Cartesian.v:32` (`Sets_Cartesian`), `Instance/Sets/Cartesian/Closed.v:38` (`Sets_Closed`) are instances, and the classifier content exists as the cross-universe theorems `sets_char_pullback` (`Instance/Sets/Classifier.v:224`), `sets_char_unique` (`:283`) and `sets_char_subobject` (`:341`). There is no `HasPullbacks Sets`, no `SubobjectClassifier Sets` and no `ElementaryTopos Sets`; a tree-wide search finds exactly one instance of each of those three classes, all for FinSet.
- For presheaves: `Theory/Sheaf.v:127` (`Presheaves := [U^op, C]`) exists as a category, with no topos structure whatever — no terminal object, no exponentials, no pullbacks, no classifier. `Instance/Fun/Cartesian.v:111` is the only structural instance on any functor category.

The setoid half is blocked by a documented and deliberate universe obstruction (`Instance/Sets/Classifier.v:29`–`:45`); the presheaf half is simply unbuilt.

## Work to be done

Suggested modules: `Instance/Sets/Topos.v` and `Instance/Fun/Topos.v`.

1. Assemble `ElementaryTopos Sets` once the pullbacks and the classifier for the category of setoids are available; if the classifier work concludes that no one-level instance exists in this encoding, record that verdict here instead and state precisely which of Mac Lane's clause fails and why.
2. Build the remaining structure a presheaf category needs: terminal object, pointwise pullbacks, and exponentials by the Yoneda formula. The exponential is the substantial part and may deserve its own file.
3. Assemble `ElementaryTopos` for the presheaf category using the sieve classifier.
4. Update docs/INHABITATION.md and the `Structure/Topos.v` header: the presheaf topos would be the second concrete witness after FinSet, and the first infinite one.
5. Note the known in-tree gap that `ElementaryTopos` carries pullbacks explicitly because the pullback-from-equalizer reduction is not available; the assembly must therefore supply pullbacks directly.

In-tree donors: `Instance/FinSet/Topos.v` (the assembly template), `Structure/Topos.v`, `Instance/Sets/Classifier.v`, `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Functor/Hom/Yoneda.v`, `Theory/Sheaf.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.10 (book p. 107), both halves, with `≈` discipline
- [ ] Each half is either delivered as an `ElementaryTopos` instance or accompanied by a recorded, argued obstruction
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` beyond what docs/AXIOMS.md permits at the instance layer
- [ ] `Print Assumptions` reported for each topos instance
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md and docs/INHABITATION.md updated (flagship-level)

## Verification

```bash
coqc -R . Category Instance/Fun/Topos.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions Presheaf_Topos.
```

Reviewer checks: the presheaf exponential is proved, not postulated; the FinSet topos is not silently offered as the witness for either of Mac Lane's two claims.

## Dependencies

- Depends on: maclane:IV.9:construction1
- Depends on: maclane:IV.9:remark1
- Depends on: #333

<!-- catalog: {"ids":["maclane:IV.10:remark1"],"deps":["maclane:IV.9:construction1","maclane:IV.9:remark1"]} -->

---8<---

```yaml
title: "MacLane IV.10: Every elementary topos has finite colimits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IV.10:remark2]
deps_item_ids: [maclane:IV.2:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.10, book p. 107 (PDF p. 116), the remark that the topos axioms yield finite colimits. Item covered: `maclane:IV.10:remark2`.

## Background

A topos is finitely cocomplete even though the axioms mention only finite limits, a power object and a classifier; the standard proof (Paré) shows the contravariant power-object functor is monadic, so colimits in the topos are limits in the opposite category. See [nLab: topos](https://ncatlab.org/nlab/show/topos) and [Wikipedia: Topos](https://en.wikipedia.org/wiki/Topos).

## Current state in the library

Absent, but unusually well supplied with donors.

- `Structure/Topos.v` — `ElementaryTopos` carries terminal, products, pullbacks, the closed structure and a classifier, with only two derived consequences in the tree: `Pow` at `:129` and `relations_iso` at `:146`. Nothing produces an initial object, coproducts, coequalizers or pushouts from the axioms.
- `Structure/Complete.v:119` — `Cocomplete` is defined but only ever consumed as a hypothesis (`Theory/Adamek/Corollaries.v:51`, `:61`), never established for any category.
- The monadicity machinery this proof needs is in-tree and complete: `Monad/Monadicity/Beck.v` (Beck's precise theorem, with conservativity derived from creation), `Monad/Monadicity/Crude.v`, `Monad/Comparison.v`, `Monad/Monadicity/BeckObjects.v`, `Structure/Coequalizer/{Split,Reflexive}.v`.

The conclusion is fully expressible with `Structure/Cocartesian.v`, `Structure/Initial.v`, `Structure/Pushout.v` and `Structure/Coequalizer.v`, so this is a genuine gap rather than an inexpressible statement.

## Work to be done

Suggested module: `Structure/Topos/Colimits.v`.

1. Build the contravariant power-object functor on a topos and prove it self-adjoint on the right (the two-sided transposition through the relations isomorphism `relations_iso`).
2. Prove it monadic, using the in-tree Beck machinery — the crude form may suffice, and if so say which hypotheses are discharged and how.
3. Conclude that the opposite category is the Eilenberg–Moore category of the induced monad, hence has all finite limits that the base has, and transport back to obtain finite colimits in the topos: initial object, binary coproducts, coequalizers and pushouts.
4. Check the result on `Instance/FinSet/Topos.v`, where the colimits are independently computable, as a sanity example.
5. Consider recording the theorem in the "adjoint on the right" vocabulary from §IV.2, since the power-object functor is the flagship example of that notion.

In-tree donors: `Structure/Topos.v`, `Monad/Monadicity/Beck.v`, `Monad/Monadicity/Crude.v`, `Monad/Comparison.v`, `Structure/Coequalizer/Reflexive.v`, `Structure/Cocartesian.v`, `Structure/Initial.v`, `Instance/FinSet/Topos.v`.

## Definition of Done

- [ ] Statement fidelity to §IV.10 (book p. 107), with `≈` discipline
- [ ] Each of the four finite colimit shapes is derived, not just an abstract cocompleteness claim
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter`
- [ ] `Print Assumptions` closed for the monadicity result and for the colimit constructions
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 and 8.20 via the nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md and docs/INHABITATION.md updated (flagship-level: the first topos consequence beyond the two currently derived)

## Verification

```bash
coqc -R . Category Structure/Topos/Colimits.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Print Assumptions power_object_monadic.
Print Assumptions topos_has_finite_colimits.
```

Reviewer checks: the proof genuinely uses the in-tree Beck machinery rather than reproving monadicity; the FinSet sanity example agrees with the independently computed colimits.

## Dependencies

- Depends on: maclane:IV.2:def2

<!-- catalog: {"ids":["maclane:IV.10:remark2"],"deps":["maclane:IV.2:def2"]} -->


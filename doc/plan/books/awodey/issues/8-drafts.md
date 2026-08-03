```yaml
title: "Awodey 8.2: The hom-bifunctor and its two exponential transposes in Cat"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.2:construction-hom-bifunctor-transposes]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.2 (The Yoneda
embedding), printed page 193 (PDF page 202). Item:
`awodey:8.2:construction-hom-bifunctor-transposes`.

## Background

Awodey introduces the two curried hom-functors — `k : C^op ⟶ Sets^C` sending
an object to its covariant representable, and `y : C ⟶ Sets^(C^op)` sending an
object to its contravariant representable — not as ad-hoc definitions but as
the two exponential transposes of the single hom-bifunctor
`Hom_C : C^op × C ⟶ Sets`, taken in the cartesian closed category of
categories. See the nLab on the
[hom-functor](https://ncatlab.org/nlab/show/hom-functor) and on the
[exponential object](https://ncatlab.org/nlab/show/exponential+object).

## Current state in the library

All four functors exist, and each is exactly what the book describes, but they
are four mutually independent definitions with no transposition lemma between
them:

- `Functor/Hom.v:49` — `Hom (C : Category) : C^op ∏ C ⟶ Sets`, the bifunctor,
  with `fmap (f, g) q = snd f ∘ q ∘ fst f`;
- `Functor/Hom.v:60` — `Curried_Hom (C : Category) : C^op ⟶ [C, Sets]`, which
  is Awodey's `k` verbatim: object action `x ↦ Hom(x, −)`, arrow action
  sending `f : x ~{C^op}~> y` to the transformation with components
  `g ↦ g ∘ op f`, i.e. the reversed-direction precomposition the book
  emphasises;
- `Functor/Hom.v:134` — `CoHom (C : Category) : C ∏ C^op ⟶ Sets`, and
  `Functor/Hom.v:146` — `Curried_CoHom C := Curried_Hom C^op : C ⟶ [C^op, Sets]`,
  which is Awodey's `y` (legitimate because `(C^op)^op = C` holds by
  reflexivity, `Construction/Opposite.v:126`).

What is missing is the *identification* the book makes: nothing states that
`Curried_Hom C` is an exponential transpose of `Hom C`. `Cat` is cartesian
closed in-tree (`Instance/Cat/Cartesian/Closed.v:47`, `Cat_Closed`, with
`exponent_obj := @Fun`), so `curry` and `uncurry` of
`Structure/Cartesian/Closed.v` are available at `Cat` and both sides of the
equation typecheck — but `rg 'curry|uncurry' Functor/Hom.v Functor/Hom/Yoneda.v`
returns 0 hits. Relatedly, `Functor/Hom.v:131` defines
`CoHom_Alt C := Hom C ◯ Swap` and the comment at `Functor/Hom.v:126-130`
asserts that `CoHom_Alt` and `CoHom` "are the same bifunctor" — an equation the
file never proves.

## Work to be done

Suggested module: extend `Functor/Hom.v` directly (the four definitions all
live there), or add a small satellite `Functor/Hom/Transpose.v` if the section
structure of `Functor/Hom.v` makes in-file placement awkward.

1. Prove `curry (Hom C) ≈ Curried_Hom C` as an equation in `Cat`, where
   `curry` is taken at `Cat_Cartesian`/`Cat_Closed` and `≈` is `Cat`'s
   hom-setoid `Functor_Setoid` (`Instance/Cat.v:145`, i.e. natural isomorphism
   of functors — say so explicitly in the statement's comment, since the
   equation is *not* on the nose).
2. Prove the mate `uncurry (Curried_Hom C) ≈ Hom C`, so the transposition is
   available in both directions.
3. Derive the `y` case as the instance at `C^op`, giving
   `curry (CoHom C) ≈ Curried_CoHom C` — the book's remark that `y` is "`k` for
   `C^op`" then becomes an in-tree fact rather than a naming convention.
4. Discharge the promised `CoHom_Alt C ≈ CoHom C` (or, if the two genuinely
   differ up to the product-swap isomorphism only, state it with the explicit
   comparison and correct the comment at `Functor/Hom.v:126-130`).

In-tree donors: `Structure/Cartesian/Closed.v:43` (`Class Closed`, whose
`curry`/`uncurry` are derived from `exp_iso` at line 51),
`Instance/Cat/Cartesian/Closed.v:47` (`Cat_Closed`),
`Instance/Cat/Cartesian.v:39` (`Cat_Cartesian`), `Instance/Fun.v:108` (`Fun`),
`Construction/Product.v` (the product of categories), `Instance/Cat.v:145`
(`Functor_Setoid`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.2: the transposition is stated for the
      hom-*bifunctor* of an arbitrary category, and all equalities of
      morphisms use `≈`, never `=`.
- [ ] Both directions (`curry (Hom C) ≈ Curried_Hom C` and
      `uncurry (Curried_Hom C) ≈ Hom C`) are proved, plus the `C^op` instance
      recovering `y`.
- [ ] The comment claim at `Functor/Hom.v:126-130` (`CoHom_Alt` and `CoHom`
      "are the same bifunctor") is either proved or softened to what the file
      actually establishes.
- [ ] No `Admitted`, `admit`, or `Axiom` in the touched files.
- [ ] `Print Assumptions` closed under the global context for each new lemma
      (`Functor/` is inside the axiom-free scoping of docs/AXIOMS.md).
- [ ] Any new file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (`nix build .#category-theory_8_19`,
      `nix build .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Functor/Hom.v          # or Functor/Hom/Transpose.v
coqc -R . Category Functor/Hom/Yoneda.v   # downstream still compiles
```

In `coqtop`/`rocq repl` after loading the file:

```coq
Print Assumptions Hom_curry_Curried_Hom.   (* expected: Closed under the global context *)
Print Assumptions CoHom_Alt_CoHom.
```

Then `make` on Rocq 9.1 and `nix build .#category-theory_8_19`. Review item:
"statement matches Awodey §8.2, printed p. 193 — `k` and `y` are the two
exponential transposes of `Hom_C`, not independent definitions".

## Dependencies

None. This issue only relates definitions that are already in-tree.

<!-- catalog: {"ids":["awodey:8.2:construction-hom-bifunctor-transposes"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 8.2/8.4: Lower sets, the principal-down-set embedding, and the thin-category Yoneda criterion"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.2:construction-poset-lower-sets, awodey:8.4:remark-yoneda-propositional-calculus]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.2 (The Yoneda
embedding), printed page 194 (PDF page 203), and §8.4 (Applications of the
Yoneda Lemma), printed page 201 (PDF page 210). Items:
`awodey:8.2:construction-poset-lower-sets`,
`awodey:8.4:remark-yoneda-propositional-calculus`.

## Background

For a poset `P`, the down-closed subsets ordered by inclusion form the poset
`Low(P)`, and sending each element to its principal down-set `↓p` is a
monotone injection that also *reflects* the order — the poset shadow of the
Yoneda embedding, with lower sets playing the role of presheaves (nLab,
[lower set](https://ncatlab.org/nlab/show/lower+set); Wikipedia,
[Upper and lower sets](https://en.wikipedia.org/wiki/Upper_set)). Awodey's §8.4
remark is the same fact read logically: two formulas are interderivable as soon
as they are entailed by exactly the same formulas, which is Corollary 8.5 in a
[thin category](https://ncatlab.org/nlab/show/thin+category), where naturality
of a family of arrows is automatic.

## Current state in the library

Neither the construction nor the criterion exists.

- No lower sets anywhere. `rg -i 'lower set|down-?closed|downset|down-?set|order ideal'`
  over `*.v` returns only prose: `Construction/Slice.v:81` ("the slice `P/p` is
  the principal down-set of `p`"), `Theory/Sheaf.v:80` and
  `Construction/Localization.v:101` (both about sieves). There is no `Low(P)`,
  no `↓ : P → Low(P)`, and no order-reflection lemma.
- The thin categories themselves are in-tree: `Instance/Proset.v:33`
  (`Proset {A} {R} (P : PreOrder R) : Category`), `Instance/Poset.v:116`
  (`Poset`), and `Instance/Props.v:39` (`Props`, propositions and implications,
  whose hom-setoid is trivial, so `P ~> Q` is inhabited exactly when `P` entails
  `Q` and `P ≅ Q` is interderivability). `Instance/Props.v` proves only the
  bicartesian-closed structure of `Props`; the category is consumed nowhere
  else in the tree.
- The general theorem the remark specializes is present —
  `Theory/Functor.v:355` `FullyFaithful : ∀ x y, F x ≅ F y → x ≅ y` with
  `Functor/Hom.v:96` `Yoneda_Full` and `Functor/Hom.v:85` `Yoneda_Faithful`,
  all stated for an arbitrary category — but the specialization is never made,
  and neither is the bridging observation that makes it usable in a thin
  category: that a *pointwise* family of arrows between representables is
  automatically natural when hom-setoids are trivial, so a pointwise hom
  equivalence already yields a natural isomorphism of representables. There is
  no lemma of the shape `(∀ θ, (θ ~> φ) ↔ (θ ~> ψ)) → φ ≅ ψ`.

## Work to be done

Suggested modules: `Instance/Poset/LowerSet.v` (new satellite of
`Instance/Poset.v`) for the order-theoretic half, and a short section in
`Instance/Props.v` (or `Instance/Proset.v`) for the thin-category criterion.

1. Define, for a preorder `R` on `A`, the type of lower sets (a predicate
   `S : A → Type`/`Prop` with `∀ a' a, R a' a → S a → S a'`), the poset
   `Low(P)` of lower sets ordered by inclusion, and the principal lower set
   `↓p := fun q => R q p`.
2. Prove `↓` monotone, injective (for a poset, i.e. with antisymmetry), and
   **order-reflecting**: `↓p ⊆ ↓q ↔ p ≤ q`. The reflection direction is the
   content Awodey is after (reflexivity of `≤` supplies `p ∈ ↓p`).
3. Prove the thin-category bridge: in a category whose hom-setoids are trivial
   (`Instance/Props.v`'s `Props`, and any `Proset`), any family
   `∀ x, (x ~> a) → (x ~> b)` respecting nothing at all is a natural
   transformation `[Hom ─,a] ⟹ [Hom ─,b]`; hence
   `(∀ θ, (θ ~> φ) ↔ (θ ~> ψ)) → φ ≅ ψ` follows from `FullyFaithful` +
   `Yoneda_Full`/`Yoneda_Faithful` at that category. State the corollary in
   `Props` in the book's logical reading (interderivability from a common
   entailment behaviour).
4. Record the comparison: `Low(P)` is the poset case of the presheaf category
   and `↓` is the Yoneda embedding — at minimum as a lemma that the two
   order-reflection statements agree, so that a later sieve development
   (Awodey's §8.8 glosses a sieve as the generalisation of a lower set — see
   #403) can point at this file for the poset case.

In-tree donors: `Instance/Proset.v:33`, `Instance/Poset.v:116`,
`Instance/Props.v:39`, `Theory/Functor.v:355` (`FullyFaithful`),
`Functor/Hom.v:85`/`:96` (`Yoneda_Faithful`/`Yoneda_Full`),
`Functor/Hom.v:146` (`Curried_CoHom`, the embedding itself).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.2 and §8.4: `↓` is proved
      order-*reflecting*, not merely monotone and injective, and the logical
      corollary is stated as interderivability (isomorphism in the thin
      category), with `≈`/`≅` never replaced by `=` on morphisms.
- [ ] The thin-category naturality bridge is proved as a reusable lemma, not
      inlined into a single corollary.
- [ ] The lower-set poset is built over the library's existing preorder/poset
      presentation (`Instance/Proset.v`, `Instance/Poset.v`) rather than a new
      ad-hoc order structure.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` closed under the global context for `Low`, `↓`, the
      order-reflection lemma and the `Props` corollary — or, if a classical
      axiom is genuinely needed for the powerset-style construction, it is
      declared and justified in docs/AXIOMS.md under the `Instance/` scoping.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (`nix build .#category-theory_8_19`,
      `nix build .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Instance/Poset/LowerSet.v
coqc -R . Category Instance/Props.v
```

```coq
Print Assumptions principal_lower_set_reflects.
Print Assumptions props_interderivable_of_hom_equiv.
```

Review items: "statement matches Awodey §8.2 printed p. 194 (`↓` reflects the
order)" and "statement matches Awodey §8.4 printed p. 201 (interderivability
from equal entailment behaviour)".

## Dependencies

None blocking. Related filed work: the general reflection statement is #428's
and #316's neighbourhood, and the sieve generalisation of lower sets is
scoped to #403.

<!-- catalog: {"ids":["awodey:8.2:construction-poset-lower-sets","awodey:8.4:remark-yoneda-propositional-calculus"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 8.6: Colimits in a functor category are pointwise, and presheaf categories are cocomplete"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.6:prop8, awodey:8.6:cor9]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.6 (Colimits in
categories of diagrams), Proposition 8.8 and Corollary 8.9, printed pages
202–203 (PDF pages 211–212). Items: `awodey:8.6:prop8`, `awodey:8.6:cor9`. (The
book leaves Proposition 8.8's proof as an exercise.)

## Background

If `D` has colimits of a given shape then so does `[C, D]`, and they are
computed objectwise — equivalently, every evaluation functor `ev_c : [C,D] ⟶ D`
preserves colimits (nLab,
[functor category](https://ncatlab.org/nlab/show/functor+category):
"If `D` has limits or colimits of a certain shape, then so does `[C,D]` and
they are computed pointwise"). Specialising to `D = Sets` gives cocompleteness
of presheaf categories, the fact every later construction in this chapter rests
on (nLab, [cocontinuous functor](https://ncatlab.org/nlab/show/cocontinuous+functor)).

## Current state in the library

Nothing of the colimit side exists for functor categories.

- `Structure/Complete.v:119` defines
  `Cocomplete {C} := ∀ (D : Category) (F : D ⟶ C), Colimit F` (with
  `Colimit F := Limit (F^op)`), but the definition has **no inhabitant
  anywhere in the tree** — every occurrence is a hypothesis
  (`Theory/Adamek/Corollaries.v:51,61`).
- `ls Instance/Fun/` shows a single satellite file, `Cartesian.v`. There is no
  `Cocartesian` instance for `@Fun`, so not even pointwise binary *co*products
  of functors exist, let alone general colimits.
- There is no evaluation functor `[C,D] ⟶ D` in the tree at all (see #424), so
  the proposition's second clause has no subject; the preservation vocabulary
  does exist (`Structure/Limit/Preservation.v:196` `PreservesColimit`, `:232`
  `PreservesAllColimits`).
- `Sets` is not proved cocomplete: `rg 'Colimit' Instance/Sets.v Instance/Sets/*.v`
  returns 0 hits. What exists is piecewise — `Sets_Cocartesian`,
  `Instance/Sets/Pushout.v:185` (`HasPushouts`), and the coend of
  `Instance/Sets/Coend.v` — none of it connected to `Structure/Limit.v`'s
  `Colimit`.
- `Instance/Fun.v:101-106` states the pointwise-inheritance principle only as
  an nLab-citing header comment, closing with "Instance/Fun/Cartesian.v
  instantiates the cartesian case".

## Work to be done

Suggested module: `Instance/Fun/Colimit.v` (new), mirroring the limit-side
work of #425 rather than duplicating it.

1. Given `J`, `A : J ⟶ [C, D]` and colimits in `D` of shape `J`, build the
   colimiting cocone in `[C, D]` objectwise: the colimit functor sends `c` to
   `colim_j (A j c)`, with the action on `f : c ~> c'` induced by the universal
   property of the colimit at `c`.
2. Prove the universal property in `[C,D]` from `D`'s, componentwise, and hence
   `Cocomplete D → Cocomplete [C, D]`.
3. Prove `PreservesAllColimits (ev_c)` for the evaluation functor of #424,
   which is Awodey's canonical isomorphism `colim_j (A_j c) ≅ (colim_j A_j) c`.
4. Corollary (Awodey 8.9): `Cocomplete [C^op, Sets]` — i.e. `Cocomplete Presheaves`
   (`Theory/Sheaf.v:127`) — obtained by feeding a `Cocomplete Sets` witness
   (#329) into (2). If the `Cocomplete Sets` witness is not yet available, land
   (1)–(3) and open the corollary as a follow-up rather than assuming it.

In-tree donors: `Instance/Fun.v:108` (`Fun`), `Instance/Fun/Cartesian.v:111`
(`Functor_Category_Cartesian` — the shape of a pointwise construction, with the
UMP discharged componentwise), `Structure/Limit.v:113`/`:158`
(`Limit`/`Colimit`), `Structure/Cone.v` (`Cone`/`Cocone`),
`Structure/Limit/Preservation.v:196,232`, `Structure/Complete.v:119`,
`Theory/Sheaf.v:127` (`Presheaves`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.6: the colimit in `[C,D]` is *defined*
      objectwise and *proved* to be a colimit there; the comparison
      `colim_j (A_j c) ≅ (colim_j A_j) c` is stated, and all equalities of
      morphisms use `≈`.
- [ ] `Cocomplete D → Cocomplete [C, D]` is proved (not just the binary
      coproduct case).
- [ ] `PreservesAllColimits` is proved for the evaluation functor.
- [ ] The presheaf corollary `Cocomplete [C^op, Sets]` is either proved or
      explicitly scoped out with its blocker (`Cocomplete Sets`, #329) named in
      the file header.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for each principal
      artifact — note `Instance/` is outside the axiom-free core scoping of
      docs/AXIOMS.md, so any stdlib axiom pulled in via `Sets` must be recorded
      there.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (the first `Cocomplete` inhabitant in
      the library is flagship-level).

## Verification

```sh
coqc -R . Category Instance/Fun/Colimit.v
```

```coq
Print Assumptions Functor_Category_Cocomplete.
Print Assumptions ev_PreservesAllColimits.
```

Then `make` on Rocq 9.1 and `nix build .#category-theory_8_20`. Review item:
"statement matches Awodey §8.6, Proposition 8.8 and Corollary 8.9, printed
pp. 202–203".

## Dependencies

Depends on: #424 (the evaluation functor `ev_c : [C,D] ⟶ D`, whose subject this
issue needs for the preservation clause)
Depends on: #425 (the limit direction of pointwise computation in a functor
category — this issue is the colimit direction and should reuse, not duplicate,
its cone/cocone plumbing)
Depends on: #329 (cocompleteness of `Sets`, for the presheaf corollary)

<!-- catalog: {"ids":["awodey:8.6:prop8","awodey:8.6:cor9"],"deps":["#424","#425","#329"]} -->

---8<---

```yaml
title: "Awodey 8.6: The category of elements is equivalent to the Yoneda slice y/P"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.6:remark-elements-slice-equivalence]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.6 (Colimits in
categories of diagrams), asserted without proof inside the proof of
Proposition 8.10, printed page 205 (PDF page 214). Item:
`awodey:8.6:remark-elements-slice-equivalence`.

## Background

For a presheaf `P`, the category of elements of `P` is equivalent to the full
subcategory `y/P` of the slice `Sets^(C^op)/P` spanned by the arrows into `P`
whose domain is representable — this is what licenses treating an element
`x ∈ P(c)` as an arrow `y c → P` and the elements category as an index category
of representables over `P` (nLab,
[category of elements](https://ncatlab.org/nlab/show/category+of+elements) and
[over category](https://ncatlab.org/nlab/show/slice+category)).

## Current state in the library

The statement has no in-tree subject and no in-tree ingredients wired together.

- There is no category of elements: `rg -i 'category of elements'` finds a
  single hit, the header comment `Construction/Grothendieck.v:108`, which
  remarks that restricting the fibres of the Grothendieck construction to sets
  "recovers the category of elements el(F)" — a mathematical aside, not an
  in-tree definition. Filing the construction itself is #345.
- Slices exist (`Construction/Slice.v:123` `Slice (C : Category) (c : C)`), but
  the slice is never taken in a functor or presheaf category
  (`rg -n 'Slice'` shows only `Construction/Slice.v` and
  `Construction/Slice/Pullback.v`).
- Full-subcategory machinery exists generically —
  `Construction/Subcategory.v:50` (`Sub`) and `:59` (`Incl`) — but is never
  applied to representables.
- `Functor/Representable.v:46`'s `Representable` class is covariant only
  (`F : C ⟶ Sets` with `represented : [Hom repr_obj,─] ≅ F`), so "the domain is
  representable" cannot even be phrased for a presheaf without first passing to
  `C^op`, which no file does.
- Consequently no equivalence of any kind relates elements to a slice; the only
  presheaf-adjacent equivalence in the tree is
  `Construction/Grothendieck/Fiber.v`'s `fiber_grothendieck_equiv`, about fibres
  of a Grothendieck construction.

## Work to be done

Suggested module: `Construction/Elements/Slice.v` (new satellite of whichever
file #345 lands the category of elements in).

1. Define the *contravariant* representability predicate on presheaves (either
   by instantiating `Functor/Representable.v`'s class at `C^op` and exporting a
   presheaf-facing alias, or by a small dedicated predicate
   `IsRepresentable (P : C^op ⟶ Sets) := ∃ c, [Hom ─,c] ≅ P`).
2. Define `y/P` as the full subcategory of `Slice Presheaves P`
   (`Construction/Subcategory.v:50`) cut out by that predicate.
3. Build the comparison functor `el(P) ⟶ y/P` sending `(c, x)` to the arrow
   `y c → P` that the Yoneda correspondence associates with `x ∈ P(c)`, and an
   arrow `h` to the evident triangle; prove functoriality using the Yoneda
   bijection.
4. Prove it is an equivalence (`Theory/Equivalence.v:151`
   `EquivalenceOfCategories`, or full + faithful + essentially surjective via
   `Theory/Equivalence/FullFaithful.v:160`). Essential surjectivity is exactly
   "every arrow `y c → P` is `x` for a unique `x ∈ P(c)`", i.e. the Yoneda
   lemma again.

In-tree donors: `Functor/Hom/Yoneda.v:133` (`Yoneda_Lemma`),
`Functor/Hom.v:146` (`Curried_CoHom`, the embedding),
`Construction/Slice.v:123`, `Construction/Subcategory.v:50,59`,
`Theory/Equivalence.v:151`, `Theory/Equivalence/FullFaithful.v:160`,
`Theory/Sheaf.v:127` (`Presheaves`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.6, printed p. 205: the equivalence is
      with the **full** subcategory of the slice spanned by representable
      domains, and it is proved as an equivalence of categories (not merely a
      bijection of objects); morphism equalities use `≈`.
- [ ] The comparison functor is *defined* (not merely asserted to exist) and
      its two round trips or its full/faithful/eso data are proved.
- [ ] A contravariant representability predicate for presheaves is exported for
      reuse (the tree currently has only the covariant class).
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for the comparison
      functor and the equivalence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Construction/Elements/Slice.v
```

```coq
Print Assumptions elements_yoneda_slice_equiv.
```

Review item: "statement matches Awodey §8.6, printed p. 205 — `∫_C P ≃ y/P`,
with `y/P` the full subcategory of `Sets^(C^op)/P` on representable domains".

## Dependencies

Depends on: #345 (the category of elements of a set-valued functor, and its
projection — this issue's domain)
Depends on: #316 (naturality of the Yoneda isomorphism, used to make the
comparison functorial)

<!-- catalog: {"ids":["awodey:8.6:remark-elements-slice-equivalence"],"deps":["#345","#316"]} -->

---8<---

```yaml
title: "Awodey 8.6: The Yoneda embedding is the free cocompletion of a small category"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.6:prop11]
deps_item_ids: [awodey:8.6:prop8]
deps_pending: [awodey:9.x:prop16]
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.6 (Colimits in
categories of diagrams), Proposition 8.11, printed page 206 (PDF page 215).
Item: `awodey:8.6:prop11`. The book gives only a proof sketch and defers the
full argument to its adjoints chapter (Proposition 9.16).

## Background

For a small category `C`, the Yoneda embedding `y : C ⟶ Sets^(C^op)` is the
*free cocompletion*: every functor `F : C ⟶ E` into a cocomplete `E` extends,
uniquely up to natural isomorphism, to a colimit-preserving functor
`F_! : Sets^(C^op) ⟶ E` with `F_! ∘ y ≅ F` (nLab,
[free cocompletion](https://ncatlab.org/nlab/show/free+cocompletion);
[Yoneda embedding](https://ncatlab.org/nlab/show/Yoneda+embedding)). The
extension is computed by the density presentation of a presheaf: `F_! P` is the
colimit of `F` over the category of elements of `P`.

## Current state in the library

Absent, and every ingredient is missing too.

- `rg -i 'free cocompletion'` returns exactly two hits, both header prose:
  `Instance/Fun.v:63` ("for a small category, its free cocompletion") and
  `Theory/Sheaf.v:117`. Neither is an assertion in Coq.
- No universal property of `[C^op, Sets]` is stated anywhere; the embedding
  itself exists (`Functor/Hom.v:146` `Curried_CoHom`) and is full and faithful
  (`Functor/Hom.v:85`, `:96`), but nothing more is claimed about it.
- The Kan-extension route is unavailable: `Theory/Kan/Extension.v:222` defines
  `Class LeftKan := { Lan : [A,C] ⟶ [B,C]; lan_adjoint : Lan ⊣ Induced }` and
  `:234` `LocalLeftKan`, but neither is ever instantiated — least of all at the
  Yoneda embedding — and `Theory/Kan/Extension.v:386`'s
  `left_adjoints_preserve` is an explicitly abandoned sketch that ends in
  `Abort.` at line 438, so it cannot be used to get colimit preservation.
- The two things the proof consumes are themselves open: the density
  presentation of a presheaf (#346) and the category of elements (#345);
  cocompleteness of presheaf categories is itself catalogued from §8.6 of this
  chapter and is not yet filed.
- `rg -i 'Yoneda.*preserv|preserv.*Yoneda'` — 0 hits.

## Work to be done

Suggested module: `Construction/Cocompletion.v` (new), or
`Functor/Hom/Yoneda/Cocompletion.v` if it is preferable to keep it beside the
embedding.

1. For small `C`, cocomplete `E` and `F : C ⟶ E`, define
   `F_! P := colim_{(c,x) ∈ el(P)} F c`, using the colimit supplied by `E`'s
   cocompleteness over the elements category of #345.
2. Make `F_!` a functor `[C^op, Sets] ⟶ E`: a natural transformation
   `P ⟹ Q` induces a functor of elements categories over `C`, hence a
   comparison of colimits.
3. Prove `F_! ◯ y ≅ F` (naturally), using that `el(y c)` has a terminal object
   `(c, id c)`.
4. Prove `PreservesAllColimits F_!` (`Structure/Limit/Preservation.v:232`).
5. Prove uniqueness: any colimit-preserving `G : [C^op, Sets] ⟶ E` with
   `G ◯ y ≅ F` is naturally isomorphic to `F_!` — via the density presentation
   (#346), which writes every `P` as a colimit of representables that `G` must
   preserve.

In-tree donors: `Functor/Hom.v:146` (`Curried_CoHom`),
`Functor/Hom/Yoneda.v:133` (`Yoneda_Lemma`), `Structure/Complete.v:119`
(`Cocomplete`), `Structure/Limit.v:158` (`Colimit`),
`Structure/Limit/Preservation.v:232`, `Theory/Coend/Yoneda.v:174`
(`coyoneda_reduction`) and `Construction/Profunctor/Laws.v:236`
(`prof_unit_left_iso`) as the coend-shaped statements of the same density fact,
`Theory/Kan/Extension.v:222` if the Kan-extension packaging is preferred.

## Definition of Done

- [ ] Statement fidelity to Awodey §8.6, Proposition 8.11: existence of a
      colimit-preserving `F_!` with `F_! ∘ y ≅ F`, **and** uniqueness up to
      natural isomorphism; all functor/transformation equalities are `≅`/`≈`,
      never `=`.
- [ ] Colimit preservation of `F_!` is proved, not assumed.
- [ ] The smallness hypothesis on `C` is discharged honestly: either as a real
      hypothesis or by the library's universe-polymorphic stand-in, and the
      file header says which (cf. `Structure/Complete.v:27-37`).
- [ ] No `Admitted`, `admit`, or `Axiom`; in particular the result must not be
      routed through `Theory/Kan/Extension.v:386`, which is an aborted sketch.
- [ ] `Print Assumptions` closed under the global context for `F_!`, the
      triangle isomorphism, the preservation lemma and the uniqueness lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

```sh
coqc -R . Category Construction/Cocompletion.v
```

```coq
Print Assumptions free_cocompletion_extend.
Print Assumptions free_cocompletion_unique.
```

Review item: "statement matches Awodey §8.6, Proposition 8.11, printed p. 206 —
uniqueness is *up to natural isomorphism*, and the extension is required to
preserve colimits".

## Dependencies

Depends on: #345 (the category of elements, the index of the defining colimit)
Depends on: #346 (the density theorem, which the uniqueness half consumes)
Depends on: `awodey:8.6:prop8` (cocompleteness of presheaf categories, needed to
know `[C^op, Sets]` is the cocompletion being characterised)

Pending, not yet catalogued: Awodey defers the full proof to Proposition 9.16
of his adjoints chapter (`awodey:9.x:prop16`), which chapter 9 will inventory.

<!-- catalog: {"ids":["awodey:8.6:prop11"],"deps":["#345","#346","awodey:8.6:prop8"]} -->

---8<---

```yaml
title: "Awodey 8.7: Exponentials of presheaves and cartesian closure of Sets^(C^op)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.7:def-presheaf-exponential, awodey:8.7:prop13, awodey:8.7:thm14]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.7 (Exponentials
in categories of diagrams), display (8.5) and Proposition 8.13, printed page 208
(PDF pages 217–218), and Theorem 8.14, printed page 209 (PDF page 218). Items:
`awodey:8.7:def-presheaf-exponential`, `awodey:8.7:prop13`, `awodey:8.7:thm14`.

## Background

Exponentials of presheaves cannot be computed objectwise; the formula forced by
Yoneda plus the exponential adjunction is
`Q^P(c) := Hom(y c × P, Q)`, the set of natural transformations out of the
product of the representable at `c` with `P`, with restriction along
`h : c' → c` given by precomposition with `y h × 1_P` (nLab,
[closed monoidal structure on presheaves](https://ncatlab.org/nlab/show/closed+monoidal+structure+on+presheaves),
which states exactly `[X,Y](c) = Hom(y(c) × X, Y)`; see also
[exponential object](https://ncatlab.org/nlab/show/exponential+object)).

## Current state in the library

Presheaf categories have binary products and nothing else.

- `Instance/Fun/Cartesian.v:111` gives
  `Functor_Category_Cartesian (C D : Category) (_ : @Cartesian D) : @Cartesian (@Fun C D)`,
  with the product built objectwise (`fun c => fobj[F] c × fobj[G] c`) and the
  universal property discharged componentwise.
- There is **no** `@Terminal (@Fun _ _)` instance, so not even finite products
  are available (`rg 'Terminal (@Fun|Terminal (Fun'` — 0 hits), and
  `ls Instance/Fun/` shows `Cartesian.v` as the only satellite.
- There is **no** `@Closed (@Fun _ _)` instance. The complete list of `Closed`
  instances in the tree is `Coq_Closed`, `Product_Closed`, `Sets_Closed`
  (`Instance/Sets/Cartesian/Closed.v:38`), `Props_Closed`, `Hom_Closed` (AST),
  `Lambda_Closed`, `Algs_Closed`, `Rel_Closed`, `FinSet_Closed` and `Cat_Closed`.
  `Instance/Cat/Cartesian/Closed.v:47`'s `Cat_Closed` is the exponential
  `[C,D]` **in `Cat`**, a different claim, and is not an internal hom of
  presheaves.
- `rg 'exponent_obj'` has no occurrence in any functor-category file, and
  `rg 'curry|uncurry' Instance/Fun.v Instance/Fun/Cartesian.v` returns 0 hits —
  no transpose of natural transformations is defined.
- `Instance/Fun.v:101-106` records the general cartesian-closure fact only as an
  nLab-citing header comment, closing "Instance/Fun/Cartesian.v instantiates the
  cartesian case".

## Work to be done

Suggested modules: `Instance/Fun/Terminal.v` and `Instance/Fun/Closed.v` (new
satellites of `Instance/Fun.v`, alongside the existing `Instance/Fun/Cartesian.v`).

1. Terminal presheaf: `@Terminal (@Fun C D)` from `@Terminal D`, objectwise.
   With `Instance/Fun/Cartesian.v:111` this gives finite products in `[C, D]`.
2. Define the exponential presheaf. For `C` small and `P Q : C^op ⟶ Sets`, set
   `Q^P c :=` the hom-setoid `[[[C^op, Sets]]]([Hom ─,c] × P, Q)` — the
   notation at `Instance/Fun.v:122` already packages a functor category's
   hom-setoid as a `Sets` object, which is exactly display (8.5) — with
   `fmap h := ` precomposition with `[Hom ─,h] × id[P]`. Prove the two functor
   laws (they are precomposition laws for `Curried_CoHom`).
3. Prove Proposition 8.13: `X × P ~> Q ≊ X ~> Q^P` in `[C^op, Sets]`, natural
   in `X`, and package it as `exp_iso` of `Structure/Cartesian/Closed.v:51`,
   yielding `@Closed (@Fun C^op Sets) _`. Two routes are available: the book's
   (write `X` as a colimit of representables via #346, then use Awodey's
   Lemma 8.12, filed separately from §8.7), or a direct componentwise
   transposition using only the
   Yoneda lemma — the direct route is likely shorter here and avoids depending
   on the colimit development; whichever is taken, say so in the header.
4. Theorem 8.14 (first clause): assemble finite products + exponentials as the
   cartesian closed structure of `[C^op, Sets]`.

Note on scope: the *second* clause of Theorem 8.14 — that `y` preserves
products and exponentials — is Awodey's §8.9 Exercise 4 and is filed as its own
issue; it is out of scope here.

In-tree donors: `Instance/Fun.v:108` (`Fun`) and `:122` (the hom-setoid
notation), `Instance/Fun/Cartesian.v:111`, `Functor/Hom.v:146`
(`Curried_CoHom`), `Functor/Hom/Yoneda.v:133` (`Yoneda_Lemma`),
`Structure/Cartesian/Closed.v:43,51,75` (`Closed`, `exp_iso`, `eval`),
`Instance/Sets/Cartesian/Closed.v:38` (`Sets_Closed`, the base case),
`Theory/Sheaf.v:127` (`Presheaves`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.7: the exponential is the display-(8.5)
      formula `Q^P(c) = Nat(y c × P, Q)` (not an objectwise formula), the
      transposition isomorphism is proved **natural in `X`**, and all morphism
      equalities are `≈`.
- [ ] `@Terminal (@Fun C D)` and `@Closed (@Fun C^op Sets) _` are both
      registered instances, so `[C^op, Sets]` is cartesian closed in the
      library's own vocabulary.
- [ ] The functoriality of `Q^P` in the object argument (contravariance via
      `[Hom ─,h] × id`) is proved, since this is exactly the point at which the
      naive objectwise formula fails.
- [ ] The header states which proof route was taken and, if the direct route is
      used, records that the book's route goes through density.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` closed under the global context for the exponential
      object, `exp_iso` and the assembled instances — or, if `Sets`'s stdlib
      axioms leak in, they are recorded in docs/AXIOMS.md under the `Instance/`
      scoping.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (first cartesian closed functor
      category in the tree; also update the `Instance/Fun.v` header comment,
      which currently only cites nLab for this).

## Verification

```sh
coqc -R . Category Instance/Fun/Terminal.v
coqc -R . Category Instance/Fun/Closed.v
```

```coq
Print Assumptions Functor_Category_Closed.
Print Assumptions presheaf_exp_iso.
```

Then `make` on Rocq 9.1 and both nix targets. Review items: "the exponential
object matches Awodey display (8.5), printed p. 208" and "Proposition 8.13's
naturality in `X` is proved, not asserted".

## Dependencies

Depends on: #316 (naturality of the Yoneda isomorphism, used in the
transposition proof)

Relation to other filed work (not blocking this issue): this supplies the
cartesian-closure component of #404 (presheaf categories as elementary
toposes), the exact analogue of #403 supplying the classifier component; and it
unblocks `awodey:8:ex4` and `awodey:8.7:lem12`.

<!-- catalog: {"ids":["awodey:8.7:def-presheaf-exponential","awodey:8.7:prop13","awodey:8.7:thm14"],"deps":["#316"]} -->

---8<---

```yaml
title: "Awodey 8.7/8.9 Ex 5: (− × B) as a left adjoint, and its preservation of all colimits"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.7:lem12, awodey:8:ex5]
deps_item_ids: [awodey:8.6:prop8, awodey:8.7:def-presheaf-exponential]
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.7 (Exponentials
in categories of diagrams), Lemma 8.12, printed pages 206–207 (PDF pages
215–216), and §8.9 (Exercises), Exercise 5, printed page 212 (PDF page 221).
Items: `awodey:8.7:lem12`, `awodey:8:ex5`. The two are the same statement at
different generality — the exercise is the `Sets` case that the lemma's proof
reduces to — so they form one development.

## Background

In a cartesian closed category the functor `(− × b)` is a left adjoint (its
right adjoint being `(−)^b`) and therefore preserves all colimits; concretely
`colim_j (A_j × b) ≅ (colim_j A_j) × b` (nLab,
[cocontinuous functor](https://ncatlab.org/nlab/show/cocontinuous+functor);
[cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category)).
Awodey uses this for presheaves to construct the exponential transposition of
Proposition 8.13, and sets the `Sets` case as an exercise.

## Current state in the library

Only the finite shapes are covered, and the adjunction that would give the
general statement is not packaged.

- `Structure/BiCCC.v:90` proves `prod_coprod_r {x y z} : x × (y + z) ≅ x × y + x × z`
  and `:221` `prod_zero_r {x} : x × 0 ≅ 0`, under
  `Cartesian` + `Cocartesian` + `Closed` — i.e. exactly the binary-coproduct and
  initial-object (empty colimit) instances of the statement, phrased as
  isomorphisms of objects rather than as colimit preservation. The file header
  even gives Awodey's reason ("each functor `_ × x` has a right adjoint `_ ^ x`,
  hence preserves all colimits") without proving it.
- The one-variable functor `(− × b) : C ⟶ C` does not exist. The only product
  functors in the tree are bifunctors: `Functor/Product/Internal.v:34`
  (`C ∏ C ⟶ C`) and `Functor/Construction/Product.v` (products of functors);
  `ProductFunctor_fst` slices only at the monoidal unit.
- The adjunction is not packaged: `Structure/Cartesian/Closed.v:43`'s
  `Class Closed` carries only the per-triple hom-setoid isomorphism
  `exp_iso {x y z} : x × y ~> z ≊ x ~> z^y` (`:51`), and no `Adjunction` record
  `(− × b) ⊣ (−)^b` exists anywhere. Consequently
  `Adjunction/Continuity.v:223`'s `left_adjoint_preserves_colimits`
  (`PreservesAllColimits`) can never be applied to it.
- No `PreservesColimit` witness exists for any product functor, and `Sets` has
  no colimits assembled (`rg 'Colimit' Instance/Sets.v Instance/Sets/*.v` — 0
  hits), so even the exercise's statement currently has no subject.

## Work to be done

Suggested modules: `Structure/Cartesian/Closed/Adjunction.v` (new) for the
adjunction and the preservation theorem; instantiations may live beside the
`Sets` and functor-category closed structures.

1. Define, for a fixed `b` in a cartesian `C`, the functor `(− × b) : C ⟶ C`
   (object `x ↦ x × b`, arrow `f ↦ first f`), and for a closed `C` the functor
   `(−)^b : C ⟶ C`.
2. Build `Adjunction ((− × b)) ((−)^b)` from `exp_iso`: unit, counit and the two
   triangle identities, or the hom-set form of `Theory/Adjunction.v`. The unit
   half is the subject of #682 and should be reused rather than redone.
3. Derive `PreservesAllColimits (− × b)` via
   `Adjunction/Continuity.v:223`.
4. Exercise 5: instantiate at `Sets` (`Instance/Sets/Cartesian/Closed.v:38`)
   to get `A × colim_i B_i ≅ colim_i (A × B_i)`.
5. Lemma 8.12: instantiate at `[C^op, Sets]` once presheaves are closed (the
   Awodey §8.7 exponential issue) and cocomplete (the Awodey §8.6 colimits
   issue), giving `colim_j (A_j × B) ≅ (colim_j A_j) × B` for presheaves.
6. Check the two finite cases of `Structure/BiCCC.v` are recovered as instances
   (or state explicitly why they are proved independently), so the tree does not
   end up with two unrelated accounts of the same fact.

In-tree donors: `Structure/Cartesian/Closed.v:43,51,75`, `Structure/BiCCC.v:90,221`,
`Theory/Adjunction.v`, `Adjunction/Continuity.v:223`,
`Structure/Limit/Preservation.v:196,232`, `Instance/Sets/Cartesian/Closed.v:38`,
`Functor/Product/Internal.v:34`.

## Definition of Done

- [ ] Statement fidelity to Awodey §8.7 Lemma 8.12 and §8.9 Exercise 5: the
      conclusion is preservation of **all** (small) colimits, not only the
      binary/nullary cases, and the isomorphism is stated with `≅`/`≈`.
- [ ] `(− × b) ⊣ (−)^b` exists as a genuine `Adjunction` between functors, so
      the general RAPL/LAPC machinery applies to it.
- [ ] `PreservesAllColimits (− × b)` is proved once, generically, and both the
      `Sets` and presheaf statements are corollaries.
- [ ] The relationship to `Structure/BiCCC.v`'s `prod_coprod_r`/`prod_zero_r` is
      stated (recovered as instances, or explicitly noted as an independent
      elementary proof).
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for the adjunction and
      the preservation theorem (`Structure/` is inside the axiom-free scoping of
      docs/AXIOMS.md).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Structure/Cartesian/Closed/Adjunction.v
coqc -R . Category Structure/BiCCC.v
```

```coq
Print Assumptions prod_right_adjoint.
Print Assumptions prod_PreservesAllColimits.
```

Review items: "statement matches Awodey §8.7 Lemma 8.12 (arbitrary small index
category, presheaf-valued)" and "statement matches §8.9 Exercise 5 (`A × −` on
`Sets`)".

## Dependencies

Depends on: #682 (the currying adjunction `(− × B) ⊣ (−)^B` and its unit)
Depends on: #329 (cocompleteness of `Sets`, so that the Exercise-5 statement has
colimits to preserve)
Depends on: `awodey:8.6:prop8` (cocompleteness of presheaf categories)
Depends on: `awodey:8.7:def-presheaf-exponential` (presheaves must be closed
before Lemma 8.12 can be stated there)

<!-- catalog: {"ids":["awodey:8.7:lem12","awodey:8:ex5"],"deps":["#682","#329","awodey:8.6:prop8","awodey:8.7:def-presheaf-exponential"]} -->

---8<---

```yaml
title: "Awodey 8.9 Ex 4: The Yoneda embedding preserves products and exponentials"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:8:ex4]
deps_item_ids: [awodey:8.7:def-presheaf-exponential]
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.9 (Exercises),
Exercise 4, printed page 212 (PDF page 221). Item: `awodey:8:ex4`. The exercise
supplies the half of Theorem 8.14 (§8.7, printed p. 209, PDF p. 218) that the
book leaves undone.

## Background

The Yoneda embedding preserves whatever products and exponentials the source
category happens to have: `y(a × b) ≅ y a × y b` and `y(a^b) ≅ (y a)^(y b)` in
the presheaf category (nLab,
[Yoneda embedding](https://ncatlab.org/nlab/show/Yoneda+embedding);
[exponential object](https://ncatlab.org/nlab/show/exponential+object)). Both
follow from the hom-set universal properties, which is why the book calls the
first "a few lines of calculation".

## Current state in the library

The product half exists in substance but only inside a representability
wrapper; the exponential half cannot even be written.

- `Structure/UniversalProperty/Cartesian.v:60` proves
  `CartesianProductIsUniversalProperty : IsUniversalProperty C^op (fun z => IsCartesianProduct x y z) …`,
  whose representing functor is supplied in the proof term as
  `[Hom ─,x] × [Hom ─,y]` (with `×` the pointwise presheaf product of
  `Instance/Fun/Cartesian.v:111`). Unfolded, this says: `z` is a product of `x`
  and `y` **iff** `y z ≅ y x × y y` — so preservation (and reflection) of binary
  products by `y` is derivable, but it is never stated as a preservation
  theorem, and the identification of the representing presheaf lives in the
  proof term rather than in the statement.
- `Functor/Structure/Cartesian.v:49` (`CartesianFunctor`) and
  `Functor/Structure/Cartesian/Closed.v:49` (`ClosedFunctor`) exist as classes
  but are instantiated only for the Cayley embedding
  (`Construction/Cayley.v:322,326`) — never for `Curried_CoHom`.
  `rg -i 'Yoneda.*preserv|preserv.*Yoneda'` returns 0 hits.
- The exponential half is not merely unproved but unstatable: no functor
  category in the tree has exponentials (`ls Instance/Fun/` shows only
  `Cartesian.v`; there is no `@Closed (@Fun _ _)` instance), so `(y a)^(y b)`
  does not denote.

## Work to be done

Suggested module: `Functor/Hom/Yoneda/Preservation.v` (new), or a section
appended to `Functor/Hom/Yoneda.v`.

1. Prove `CartesianFunctor (Curried_CoHom C)` for a cartesian `C`: the
   comparison `y(a × b) → y a × y b` is the pairing of `y exl` and `y exr`, and
   it is invertible because a morphism `x → a × b` is exactly a pair of
   morphisms — the hom-set universal property, componentwise. Also supply the
   terminal case (`y 1 ≅ 1`) once `Instance/Fun/Terminal.v` exists.
2. Reconcile with `Structure/UniversalProperty/Cartesian.v:60`: state the
   preservation theorem as a first-class result and note in the header that the
   representability proposition already contained it, so the two do not drift.
3. Prove `ClosedFunctor (Curried_CoHom C)` for a cartesian closed `C`, i.e.
   `y(a^b) ≅ (y a)^(y b)` in `[C^op, Sets]`, using the display-(8.5)
   exponential: `(y a)^(y b) (c) = Nat(y c × y b, y a) ≅ Hom(c × b, a) ≅ Hom(c, a^b) = y(a^b)(c)`,
   naturally in `c` — each step being Yoneda plus the exponential adjunction of
   `C`.
4. Record that this closes the clause Awodey defers in Theorem 8.14.

In-tree donors: `Functor/Hom.v:146` (`Curried_CoHom`), `Functor/Hom.v:85,96`,
`Functor/Hom/Yoneda.v:133,231`, `Instance/Fun/Cartesian.v:111`,
`Structure/UniversalProperty/Cartesian.v:60`,
`Functor/Structure/Cartesian.v:49`, `Functor/Structure/Cartesian/Closed.v:49`,
`Structure/Cartesian/Closed.v:51` (`exp_iso`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.9 Exercise 4: both clauses (products and
      exponentials) are proved, for products *that exist in `C`* — the
      hypotheses are `Cartesian C` and `Closed C`, not extra structure on the
      presheaf category beyond what §8.7 supplies.
- [ ] The preservation results are stated using the library's existing
      `CartesianFunctor`/`ClosedFunctor` vocabulary, so they compose with the
      rest of the preservation theory.
- [ ] The comparison morphisms are the canonical ones (built from `y exl`,
      `y exr`, `y eval`), not ad-hoc isomorphisms.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for both instances.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Functor/Hom/Yoneda/Preservation.v
```

```coq
Print Assumptions Yoneda_CartesianFunctor.
Print Assumptions Yoneda_ClosedFunctor.
```

Review item: "statement matches Awodey §8.9 Exercise 4 and closes the deferred
clause of Theorem 8.14, printed p. 209".

## Dependencies

Depends on: `awodey:8.7:def-presheaf-exponential` (the presheaf exponential and
cartesian closure of `[C^op, Sets]`, without which the exponential clause cannot
be stated)

<!-- catalog: {"ids":["awodey:8:ex4"],"deps":["awodey:8.7:def-presheaf-exponential"]} -->

---8<---

```yaml
title: "Awodey 8.8: The subobject functor is representable — naturality of the classifying bijection and uniqueness of Ω"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.8:remark-sub-representable]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.8 (Topoi), the
prose remark following Definition 8.15, printed page 210 (PDF page 219). Item:
`awodey:8.8:remark-sub-representable`.

## Background

The defining pullback condition on a subobject classifier is exactly the
requirement that the subobject functor `Sub_E(−) : E^op ⟶ Sets` be
representable, with `Sub_E(−) ≅ Hom_E(−, Ω)`; uniqueness of `Ω` up to
isomorphism is then a special case of uniqueness of representing objects (nLab,
[subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier);
[representable functor](https://ncatlab.org/nlab/show/representable+functor)).

## Current state in the library

Both sides of the isomorphism exist; the isomorphism between them does not.

- `Structure/SubobjectClassifier.v:187` proves
  `classifier_classifies (x : C) : @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}`
  — but **objectwise**, one `Sets`-isomorphism per `x`, with `to := char` and
  `from := sub_reindex h truth_subobject` and both round trips proved
  (`:159`, `:174`).
- `Theory/Subobject/Functor.v:180` defines `Sub : C^op ⟶ Sets` by chosen-pullback
  reindexing, functorial via `sub_reindex_id` (`:143`) and `sub_reindex_comp`
  (`:152`).
- Nothing connects them. There is no lemma relating `char (sub_reindex f s)` to
  `char s ∘ f`, so the family of isomorphisms is never exhibited as a morphism —
  let alone an isomorphism — in `[C^op, Sets]`, and `Sub` is never compared with
  `[Hom ─, Ω]`. The sole consumer of `classifier_classifies` is
  `Structure/Topos.v:146` (`relations_iso`), which composes it objectwise with
  `exp_iso`.
- `Functor/Representable.v:46`'s `Representable` class is covariant only
  (`F : C ⟶ Sets`, `represented : [Hom repr_obj,─] ≅ F`), so the presheaf `Sub`
  cannot be declared an instance without passing to `C^op`, which no file does;
  and `Structure/UniversalProperty.v:175`'s
  `univ_property_unique_up_to_unique_iso` is never instantiated at the
  classifier predicate.
- No uniqueness statement about `Ω` exists (`rg -i 'classifier.*uniq|Omega.*uniq'`
  — 0 hits).

## Work to be done

Suggested module: extend `Structure/SubobjectClassifier.v` (the natural home,
which already has the objectwise theorem), with the representability packaging
possibly in a small satellite.

1. Prove the naturality lemma: for `f : y ~> x` and a subobject `s` of `x`,
   `char (sub_reindex f s) ≈ char s ∘ f`. This is the pullback-pasting argument
   (`Theory/Morphisms/Stability.v` supplies the pasting toolkit) and is the
   whole content of the remark.
2. Assemble `sub_classifier_natural : Sub ≅ [Hom ─, Ω]` as an isomorphism in
   `[C^op, Sets]` (an isomorphism of presheaves, not a family), using
   `classifier_classifies` componentwise plus (1).
3. Package representability: either instantiate `Functor/Representable.v:46` at
   `C^op` and export a presheaf-facing alias, or instantiate
   `Structure/UniversalProperty.v`'s `IsUniversalProperty` at the
   classifier predicate.
4. Derive the uniqueness statement Awodey gives: any two subobject classifiers
   on the same `C` have isomorphic `Ω`, by a canonical isomorphism compatible
   with `truth` — via `Structure/UniversalProperty.v:175`
   (`univ_property_unique_up_to_unique_iso`) or directly from (2).

In-tree donors: `Structure/SubobjectClassifier.v:44,72,159,174,187`,
`Theory/Subobject/Functor.v:143,152,180`, `Theory/Subobject.v`,
`Theory/Morphisms/Stability.v` (pullback pasting),
`Structure/UniversalProperty.v:72,175`, `Functor/Representable.v:46`,
`Functor/Hom.v:146` (`Curried_CoHom`).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.8, printed p. 210: the classification
      bijection is upgraded to a **natural** isomorphism of presheaves
      `Sub ≅ Hom(−, Ω)`, and uniqueness of `Ω` is derived from it rather than
      asserted; all morphism equalities use `≈`.
- [ ] The naturality lemma `char (sub_reindex f s) ≈ char s ∘ f` is proved as a
      standalone reusable lemma.
- [ ] The uniqueness statement is compatible with `truth` (not merely an
      isomorphism of the underlying objects).
- [ ] The contravariant representability packaging is exported (the tree
      currently has only the covariant class).
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for the naturality
      lemma, the presheaf isomorphism and the uniqueness result
      (`Structure/`, `Theory/` are inside the axiom-free scoping of
      docs/AXIOMS.md).
- [ ] Any new file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated for `Structure/Topos.v`'s entry, which
      currently advertises the objectwise `classifier_classifies` as the
      classification theorem.

## Verification

```sh
coqc -R . Category Structure/SubobjectClassifier.v
coqc -R . Category Structure/Topos.v
```

```coq
Print Assumptions char_reindex.
Print Assumptions sub_classifier_natural.
Print Assumptions classifier_unique.
```

Review item: "statement matches Awodey §8.8, printed p. 210 — representability
of `Sub_E(−)` **is** the defining condition, and uniqueness of `Ω` follows from
uniqueness of representing objects".

## Dependencies

None blocking; all ingredients are in-tree.

<!-- catalog: {"ids":["awodey:8.8:remark-sub-representable"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 8.8: The fundamental theorem of topos theory — every slice of a topos is a topos"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:8.8:remark-topos-properties]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.8 (Topoi), the
closure remark stated without proof immediately after Definition 8.16, printed
page 210 (PDF page 219). Item: `awodey:8.8:remark-topos-properties` — the
slice half. (The remark's other half, that every topos has finite colimits, is
already filed as #405; this issue is the "every slice of a topos is again a
topos" half, which no filed issue covers.)

## Background

Slicing a topos over any of its objects yields a topos again — the *fundamental
theorem of topos theory* (nLab,
[over-topos](https://ncatlab.org/nlab/show/over-topos), citing McLarty 1992
Thm. 17.4; see also [topos](https://ncatlab.org/nlab/show/topos)). Awodey states
it without proof and refers the reader to Mac Lane–Moerdijk, Johnstone and
McLarty.

## Current state in the library

Absent, and the slice construction carries no structural instances at all.

- `Structure/Topos.v:112` defines
  `Class ElementaryTopos (C : Category) := { topos_terminal; topos_cartesian;
  topos_pullbacks; topos_closed; topos_classifier }`, with exactly one inhabitant
  in the tree: `Instance/FinSet/Topos.v:38` (`FinSet_Topos`).
- `Construction/Slice.v:123` defines `Slice (C : Category) (c : C)` (and `:169`
  `Coslice`) and nothing else: there is no `Terminal`, `Cartesian`,
  `HasPullbacks`, `Closed` or `SubobjectClassifier` instance for a slice, so not
  one of the five `ElementaryTopos` fields can currently be assembled for `C/c`.
- The only `HasPullbacks` instance in the tree is
  `Instance/FinSet/Classifier.v:264` (plus the op-transport in
  `Structure/Pushout.v`), which is another blocker for the slice's finite-limit
  fields.
- The base-change machinery needed for slice exponentials is a stub:
  `Construction/Slice/Pullback.v:50` defines `Bang_Functor f` (`Σ_f`) and `:67`
  `Star_Functor f` (`f*`), but the adjunction is commented out — lines 114–125
  are `(* Program Definition Production … *)` and
  `(* Program Definition Base_Functor_Adjunction … *)` — and the file header
  itself records the orientation erratum.
- Both files advertise the theorem in prose only: `Construction/Slice.v:109-115`
  calls it "the headline theorem about this construction not yet formalized
  here", while `Structure/Topos.v:95-98` says "The library exercises both
  readings. Construction/Slice.v records the fundamental theorem of topos
  theory … and names [ElementaryTopos] as its target" — which reads as an
  in-tree claim and overstates what exists.

## Work to be done

Suggested module: `Construction/Slice/Topos.v` (new), building on
`Construction/Slice/Pullback.v`.

1. Finite limits in `C/c` from finite limits in `C`: the terminal object of
   `C/c` is `id[c]`; the product of `f : x → c` and `g : y → c` is their
   pullback in `C`; pullbacks in `C/c` are pullbacks in `C`. This alone needs
   `HasPullbacks C` and gives `topos_terminal`, `topos_cartesian`,
   `topos_pullbacks`.
2. The classifier of `C/c`: take `Ω_{C/c} := (π₂ : Ω × c → c)` with truth
   `⟨truth ∘ one, id⟩`, and prove the classifying-square universal property by
   transporting `Sub_{C/c}(f) ≅ Sub_C(dom f)` — the step where
   `Theory/Subobject/Functor.v`'s reindexing and the classifier's `char` do the
   work.
3. Exponentials in `C/c`: this is the hard clause and needs the dependent
   product `Π_f` (right adjoint to base change `f*`), which the library does not
   have. Either finish the commented-out adjunction of
   `Construction/Slice/Pullback.v:114-125` and build `Π_f` (see #384, #387), or
   scope this clause out explicitly and land (1)+(2) with the closed field
   stated as the remaining obligation — do not leave it silently missing.
4. Assemble `ElementaryTopos (Slice C c)` from `ElementaryTopos C`.

In-tree donors: `Construction/Slice.v:123`, `Construction/Slice/Pullback.v:50,67`,
`Structure/Topos.v:112`, `Structure/SubobjectClassifier.v:44`,
`Theory/Morphisms/Stability.v` (pullback pasting and stability),
`Theory/Subobject/Functor.v:180`, `Instance/FinSet/Topos.v:38` (the only
existing witness, useful as a sanity target: `Slice FinSet n` should come out a
topos).

## Definition of Done

- [ ] Statement fidelity to Awodey §8.8, printed p. 210: the conclusion is
      `ElementaryTopos (Slice C c)` for **every** object `c` of a topos `C`,
      with all five fields supplied; morphism equalities use `≈`.
- [ ] The slice classifier is proved to classify (the pullback square and its
      uniqueness clause), not merely defined.
- [ ] If the exponential clause is deferred, the file header states precisely
      what is missing (the dependent product `Π_f`) and the issue stays open on
      that clause rather than being closed as done.
- [ ] While touching these files, fix the two header overclaims found during
      the coverage audit: `Structure/Topos.v:95-98` asserts that the library
      "exercises both readings" and that `Construction/Slice.v` "records the
      fundamental theorem of topos theory … and names `[ElementaryTopos]` as
      its target", when `Construction/Slice.v:109-115` only records it as a
      not-yet-formalized headline. Either make the claim true (this issue) or
      soften both headers.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for the assembled
      instance and each structural field.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level; the `Structure/Topos.v`
      entry should record what is and is not proved about slices).

## Verification

```sh
coqc -R . Category Construction/Slice/Topos.v
coqc -R . Category Structure/Topos.v
```

```coq
Print Assumptions Slice_Topos.
Print Assumptions Slice_Classifier.
```

Sanity witness: check `Slice FinSet 2` is accepted as an `ElementaryTopos`.
Review item: "statement matches Awodey §8.8, printed p. 210 (the fundamental
theorem of topos theory, cited there to Mac Lane–Moerdijk / Johnstone /
McLarty)".

## Dependencies

Depends on: #387 (base change is right adjoint to composition on slices — the
adjunction the exponential clause needs)
Depends on: #384 (quantifiers as adjoints to substitution, i.e. the `Π_f` half
of the base-change adjoint triple)

Related: #405 covers the remark's other half (every topos has finite colimits).

<!-- catalog: {"ids":["awodey:8.8:remark-topos-properties"],"deps":["#387","#384"]} -->

---8<---

```yaml
title: "Awodey 8.9 Ex 6: The subobject classifiers of Sets^2 and Sets^ω, and finite-set diagrams as a topos"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:8:ex6]
deps_item_ids: [awodey:8.7:def-presheaf-exponential]
deps_pending: []
```

## Source

Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52), §8.9 (Exercises),
Exercise 6 parts (a) and (b), printed page 212 (PDF page 221). Item:
`awodey:8:ex6`.

## Background

Part (a) asks for the classifiers of the diagram categories over the two-element
poset `0 < 1` and over the poset of naturals: computing the sieves of those
shapes gives a three-element `Ω` in the arrow-category case and
`Ω(n) ≅ {n, n+1, …, ∞}` in the `ω` case (nLab,
[subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier);
[arrow category](https://ncatlab.org/nlab/show/arrow+category)). Part (b) asks
for a topos of *finite*-set diagrams, which is the finitary analogue of the
presheaf topos and the natural companion of the library's computable `FinSet`
witness.

## Current state in the library

None of it exists, and the general machinery it would instantiate is itself
open.

- The only `SubobjectClassifier` instance in the tree is
  `Instance/FinSet/Classifier.v:354` (`@SubobjectClassifier FinSet FinSet_Terminal`),
  and the only `ElementaryTopos` inhabitant is `Instance/FinSet/Topos.v:38`
  (`FinSet_Topos`) — which is `FinSet` itself, **not** the category of
  `2`-indexed diagrams of finite sets that the exercise asks about.
- `Instance/Sets/Classifier.v` deliberately supplies cross-universe *theorems*
  rather than an instance (its header explains the size obstruction), so even
  the `Sets` base case is not an instance.
- No functor category has any of `Terminal`, `HasPullbacks`, `Closed` or a
  classifier, so neither `[_2, Sets]` nor `[Omega, Sets]` nor `[_2, FinSet]` can
  be assembled today.
- The shapes are available: `Instance/Two.v:134` defines `_2` (two objects and
  one non-identity arrow, thin, hom-setoids by `Morphism_equality`), and
  `Instance/Omega.v:72` defines `Omega`, the ordinal ω as a `Type`-valued
  preorder used for Adámek chains. `Instance/Two.v:174`'s `_2_as_Set : _2 ⟶ Sets`
  is a single diagram, not the category of them.
  `Construction/Arrow.v:110` defines `Arrow {C} := (Id[C] ↓ Id[C])` and carries
  no structural instances.

## Work to be done

Suggested modules: `Instance/Fun/Classifier/Two.v` and
`Instance/Fun/Classifier/Omega.v` (or a single `Instance/Fun/Examples.v`), plus
`Instance/FinSet/Diagrams.v` for part (b).

1. Part (a), first case: instantiate the general sieve classifier (#403) at
   `_2` and **compute** it — the sieves on the domain object are
   `∅`, `{TwoXY}` and the total sieve, so `Ω(TwoX)` has three elements while
   `Ω(TwoY)` has two; state the resulting classifier concretely and prove it is
   the classifier (either by transport from the general theorem or directly).
   Sanity example in the style of `Instance/FinSet/Topos.v:53`: the cardinality
   facts should hold by computation where the encoding allows.
2. Part (a), second case: the same for `Omega`, giving
   `Ω(n) ≅ {m : m ≥ n} ∪ {∞}` — i.e. sieves on `n` are the down-closed sets of
   arrows into `n`, indexed by their least element or by "empty".
3. Part (b): build `[_2, FinSet]` (or the skeletal finite analogue that fits the
   library's `FinSet`) and assemble an `ElementaryTopos` instance for it,
   checking each field stays inside finite sets — in particular that the
   classifier and the exponentials of finite diagrams are again finite.
4. Where the general presheaf results (#403, #404, and the Awodey §8.7
   presheaf-exponential issue) are not yet available, say so in the header and
   prove the small cases directly rather than assuming the general theorem.

In-tree donors: `Instance/Two.v:134`, `Instance/Omega.v:72`,
`Instance/FinSet.v`, `Instance/FinSet/Classifier.v:264,354`,
`Instance/FinSet/Topos.v:38,53`, `Instance/FinSet/Closed.v:132`,
`Instance/Fun.v:108`, `Structure/SubobjectClassifier.v:44`,
`Structure/Topos.v:112`, `Construction/Arrow.v:110`.

## Definition of Done

- [ ] Statement fidelity to Awodey §8.9 Exercise 6: both classifiers are
      *determined explicitly* (the exercise asks for the objects, not merely for
      an existence proof), and part (b) concludes with an `ElementaryTopos`
      instance for the finite-diagram category.
- [ ] Each classifier is proved to classify (pullback square + uniqueness), with
      morphism equalities as `≈`.
- [ ] Computable sanity examples in the style of
      `Instance/FinSet/Topos.v:53` (`Pow 2 = 4` by `eq_refl`) are supplied where
      the encoding permits — e.g. the three-element `Ω` at the domain object of
      `_2`.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` on each classifier instance; any stdlib axioms
      inherited from `Sets` are recorded in docs/AXIOMS.md under the
      `Instance/` scoping (`FinSet` is expected to stay axiom-free).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
coqc -R . Category Instance/Fun/Classifier/Two.v
coqc -R . Category Instance/Fun/Classifier/Omega.v
coqc -R . Category Instance/FinSet/Diagrams.v
```

```coq
Print Assumptions Two_Diagrams_Classifier.
Print Assumptions Omega_Diagrams_Classifier.
Print Assumptions FinSet_Two_Diagrams_Topos.
```

Review item: "the classifiers match Awodey §8.9 Exercise 6 (a) — three elements
over the domain object of `2`, and the `ω`-indexed family over `ω` — and part
(b) yields a genuine `ElementaryTopos` instance".

## Dependencies

Depends on: #403 (subobject classifiers for functor categories — the general
sieve construction these examples instantiate)
Depends on: #404 (presheaf categories as elementary toposes)
Depends on: `awodey:8.7:def-presheaf-exponential` (exponentials of diagrams,
needed for the topos structure in part (b))

<!-- catalog: {"ids":["awodey:8:ex6"],"deps":["#403","#404","awodey:8.7:def-presheaf-exponential"]} -->

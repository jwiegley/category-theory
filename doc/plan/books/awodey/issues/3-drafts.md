```yaml
title: "Awodey 3.2: The coproduct bifunctor + : C ∏ C ⟶ C"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:3.2:construction-coproduct-functor]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed., Oxford Logic Guides 49), Chapter 3
"Duality", §3.2 Coproducts, printed page 65, PDF page 74. Unnumbered
construction following Proposition 3.11. Item ID:
`awodey:3.2:construction-coproduct-functor`.

## Background

In a category with binary coproducts, the empty coproduct is an initial
object, the coproduct of a pair of arrows assembles the two summands, and
these data organize into a bifunctor of two variables out of the product
category — the exact dual of the binary-product bifunctor. See the nLab on
[coproduct](https://ncatlab.org/nlab/show/coproduct) and on
[bifunctor](https://ncatlab.org/nlab/show/bifunctor).

## Current state in the library

The object action, the arrow action, and all the functor laws are already
in `Structure/Cocartesian.v`: the coproduct object `Coprod` (`x + y`), the
arrow action `cover f g : x + z ~> y + w` (`Structure/Cocartesian.v:151`),
and the laws `cover_id`, `cover_comp`, `cover_respects`
(`Structure/Cocartesian.v:285`), together with the initial-object-as-empty-
coproduct facts `coprod_zero_l`/`coprod_zero_r` under `Context @Initial C`
(`Structure/Cocartesian.v:373`). What is missing is the final packaging:
there is no `Functor (C ∏ C) C` instance assembling `Coprod`/`cover` into a
single bifunctor record. This is a genuinely one-sided gap — the product
dual is already packaged as `InternalProductFunctor : C ∏ C ⟶ C` in
`Functor/Product/Internal.v` (notation `×(C)`, consumed in
`Adjunction/GAFT/Examples.v`), whereas no `InternalCoproductFunctor`
exists (`rg InternalCoproduct` returns no hits). Note `Functor/Coproduct.v`
is the different codiagonal `C ∐ C ⟶ C` out of the coproduct *category*,
not this bifunctor.

## Work to be done

- Add `Functor/Coproduct/Internal.v` (mirroring `Functor/Product/Internal.v`)
  defining `InternalCoproductFunctor : C ∏ C ⟶ C` for a category `C` with
  binary coproducts, with object map `Coprod` and morphism map `cover`.
- Discharge the functor obligations directly from the existing `cover_id`,
  `cover_comp`, and `cover_respects` in `Structure/Cocartesian.v`; the whole
  construction can be obtained by duality from `InternalProductFunctor`
  read in `C^op` (the coproduct is `@Cartesian (C^op)`), matching how the
  rest of `Structure/Cocartesian.v` is built.
- Introduce a notation dual to `×(C)` (e.g. `+(C)`) and, optionally, a
  short sanity lemma relating its arrow action to `cover`.

In-tree donors: `Structure/Cocartesian.v` (`Coprod`, `cover`, `cover_id`,
`cover_comp`, `cover_respects`), `Functor/Product/Internal.v`
(`InternalProductFunctor`, the exact template), `Construction/Product.v`.

## Definition of Done

- [ ] `InternalCoproductFunctor : C ∏ C ⟶ C` defined for any `C` with
  binary coproducts, faithful to Awodey §3.2 (object map = binary
  coproduct, arrow map = coproduct of arrows), stated with the setoid `≈`
  discipline throughout (never `=` on morphisms).
- [ ] The empty-coproduct-is-initial observation is available (reuse
  `coprod_zero_l`/`coprod_zero_r`); no separate re-proof required.
- [ ] No `Admitted`/`admit`/`Axiom`; the file stays within the axiom-free
  core-theory scope of `docs/AXIOMS.md`.
- [ ] `Print Assumptions InternalCoproductFunctor` reported and closed under
  the global context.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Functor/Coproduct/Internal.v` compiles.
- `Print Assumptions InternalCoproductFunctor.` → closed under the global
  context.
- Reviewer confirms the statement matches Awodey §3.2 (coproduct functor
  `+ : C × C → C`, dual to the product functor) and that the arrow action
  agrees with `cover`.

## Dependencies

None (all component data are already in-tree).

<!-- catalog: {"ids":["awodey:3.2:construction-coproduct-functor"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 3.2: The coproduct universal property — representability and uniqueness up to isomorphism"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:3.2:prop12, awodey:3:ex1]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), Chapter 3 "Duality": Proposition 3.12
(coproducts are unique up to isomorphism), §3.2, printed page 66, PDF page
75; and Exercise 1(a,b), §3.5, printed page 76, PDF page 85. Item IDs:
`awodey:3.2:prop12`, `awodey:3:ex1`.

## Background

A coproduct is determined by a universal property, so any two coproducts of
the same pair are canonically isomorphic, and the property is equivalent to
a representable hom-set bijection `Hom(A+B, Z) ≅ Hom(A,Z) × Hom(B,Z)`,
natural in `Z`. See the nLab on
[universal property](https://ncatlab.org/nlab/show/universal+property) and
[coproduct](https://ncatlab.org/nlab/show/coproduct).

## Current state in the library

The general theorem "an object satisfying a representable universal property
is unique up to unique isomorphism" is proved for any representable
universal property in `Structure/UniversalProperty.v:175`
(`univ_property_unique_up_to_unique_iso`), and the *product* side is packaged
as a universal property in `Structure/UniversalProperty/Cartesian.v:60`
(`CartesianProductIsUniversalProperty`, giving `Hom(z, x×y) ≅ Hom(z,x) ×
Hom(z,y)`). The coproduct's own copairing uniqueness exists as `merge_inv`
(`Structure/Cocartesian.v:196`). What is missing is the dual wiring: the
coproduct UMP is not registered as an `IsUniversalProperty` instance, so
neither the named corollary "any two coproducts of `A, B` are canonically
isomorphic" (Prop 3.12) nor the representable characterization
`Hom(A+B, Z) ≅ Hom(A,Z) × Hom(B,Z)` (Exercise 1) is derived in-tree; only
the element-level copairing bijection `merge_inv` and the product-side
statements are present. There is no coproduct universal-property file
(`rg Cocartesian Structure/UniversalProperty/` → no hits).

## Work to be done

- Add `Structure/UniversalProperty/Cocartesian.v` dualizing
  `Structure/UniversalProperty/Cartesian.v`: register the binary coproduct
  (as a product in `C^op`) as an `IsUniversalProperty` instance and derive,
  via `univ_property_unique_up_to_unique_iso`, the corollary that any two
  objects satisfying the coproduct UMP for a fixed pair are uniquely
  isomorphic (Prop 3.12).
- State and prove the representable characterization
  `Hom(A+B, Z) ≅ Hom(A,Z) × Hom(B,Z)` in `Sets`, natural in `Z`, with the
  forward map `f ↦ (f ∘ inl, f ∘ inr)`; obtain the product form of
  Exercise 1(b) by duality (it already exists as
  `CartesianProductIsUniversalProperty`).
- Keep the proofs by duality from the product side wherever possible
  (`@Cartesian (C^op)` and the existing `merge_inv`/`merge_inl_inr`).

In-tree donors: `Structure/UniversalProperty.v`
(`univ_property_unique_up_to_unique_iso`),
`Structure/UniversalProperty/Cartesian.v`
(`CartesianProductIsUniversalProperty`, the template),
`Structure/Cocartesian.v` (`merge`, `merge_inv`, `merge_inl_inr`),
`Functor/Hom.v`.

## Definition of Done

- [ ] Coproduct registered as an `IsUniversalProperty` instance and the
  corollary "two coproducts of a fixed pair are uniquely isomorphic" (Prop
  3.12) derived, setoid `≈` throughout.
- [ ] The representable bijection `Hom(A+B, Z) ≅ Hom(A,Z) × Hom(B,Z)`
  (Exercise 1(a)) stated as an isomorphism of hom-setoids, natural in `Z`,
  with the product form (Exercise 1(b)) recorded by duality.
- [ ] No `Admitted`/`admit`/`Axiom`; within the axiom-free core scope of
  `docs/AXIOMS.md`.
- [ ] `Print Assumptions` closed for each principal artifact.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/UniversalProperty/Cocartesian.v` compiles.
- `Print Assumptions` on the uniqueness corollary and the hom-bijection →
  closed under the global context.
- Reviewer confirms fidelity to Awodey Prop 3.12 and Exercise 1
  (coproduct uniqueness up to iso; the copairing hom-set bijection).

## Dependencies

None (the universal-property machinery and the coproduct copairing UMP are
in-tree).

<!-- catalog: {"ids":["awodey:3.2:prop12","awodey:3:ex1"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 3.3: Subsets as equalizers of their characteristic functions in Sets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:3.3:construction-char-function]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), Chapter 3 "Duality", §3.3 Equalizers,
printed pages 67–68, PDF pages 76–77. Unnumbered construction (the
characteristic-function development around the two-element object). Item ID:
`awodey:3.3:construction-char-function`.

## Background

Every subset of a set is recovered as the equalizer of its characteristic
map into the two-element object `2` and the constant "true" map, so subsets
of `A` correspond to maps `A → 2`. This is the elementary, equalizer-based
face of the subobject-classifier correspondence. See the nLab on
[equalizer](https://ncatlab.org/nlab/show/equalizer) and on
[subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier).

## Current state in the library

The abstract half is already present: the subobject-classifier bijection
`SubObj x ≅ (x ~> Ω)` in `Sets` is proved as `classifier_classifies`
(`Structure/SubobjectClassifier.v:187`), with the characteristic morphism
`char` (`Structure/SubobjectClassifier.v:49`) and its classifying pullback
of `truth`; the `Sets` realization is `Instance/Sets/Classifier.v`
(`char_setoid`, `sets_char_pullback`, `sets_char_unique`), and `FinSet`
realizes the truth-value object literally as `Ω = 2`
(`Instance/FinSet/Classifier.v`). What is missing is Awodey's *equalizer*
presentation: the in-tree classifier exhibits a subobject via a **pullback**
of `truth`, whereas Awodey exhibits a subset `U ⊆ A` as the **equalizer** of
`χ_U` and the constant-true map `A → 1 → 2`. `Sets` currently has no
equalizer construction at all (see the sibling obligation to complete
`Sets` limits, MacLane V.1 — issue #407), so the concrete
"subset = equalizer of `χ_U` and `true!`" statement cannot be formed yet.

## Work to be done

- Once `Sets` has equalizers (issue #407), state and prove: for a subobject
  `m : U ↪ A` in `Sets`, `m` is the equalizer of its characteristic map
  `χ_U : A → Ω` (or `→ 2` in the decidable `FinSet` presentation) and the
  constant-true map `true ∘ ! : A → Ω`.
- Connect this equalizer presentation to the existing
  `classifier_classifies`, showing the two routes to a subobject (pullback
  of `truth`, equalizer of `χ_U` and `true!`) agree; add the result to
  `Instance/Sets/Classifier.v` (or a new `Instance/Sets/Equalizer.v` for the
  underlying equalizer) and, where the literal `2` is wanted, mirror it in
  `Instance/FinSet/Classifier.v`.
- Keep the truth-value/predicate handling as in the existing
  cross-universe `Sets` classifier (`char_setoid`), avoiding funext.

In-tree donors: `Structure/SubobjectClassifier.v` (`char`,
`classifier_classifies`), `Instance/Sets/Classifier.v`
(`char_setoid`, `sets_char_pullback`), `Instance/FinSet/Classifier.v`
(`Ω = 2`), `Structure/Equalizer/Fork.v` (`IsEqualizer`, `equalizer_monic`).

## Definition of Done

- [ ] A subobject in `Sets` is proved to be the equalizer of its
  characteristic map and the constant-true map, faithful to Awodey §3.3,
  setoid `≈` throughout (never `=` on morphisms).
- [ ] The equalizer route is reconciled with the existing pullback-of-`truth`
  classifier (`classifier_classifies`).
- [ ] No `Admitted`/`admit`/`Axiom`; the `Sets`/`FinSet` layers may use only
  the stdlib axioms already enumerated in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the principal artifact.
- [ ] Any new file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile of the touched `Instance/Sets/*` (and `FinSet`) files.
- `Print Assumptions` on the subset-as-equalizer lemma.
- Reviewer confirms the statement matches Awodey §3.3 (`U` is the equalizer
  of `χ_U` and `true!`; `Hom(A,2) ≅ P(A)` is the associated bijection,
  already present as `classifier_classifies`).

## Dependencies

Depends on: #407 (MacLane V.1: Completeness of Sets by cone sets — supplies
equalizers in `Sets`).

<!-- catalog: {"ids":["awodey:3.3:construction-char-function"],"deps":["#407"]} -->

---8<---

```yaml
title: "Awodey 3.5 Ex 6: Kernel relations, quotients, and generated equivalence relations in Sets"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:3:ex6]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), Chapter 3 "Duality", §3.5 Exercises,
Exercise 6(a,b,c,d), printed pages 76–77, PDF pages 85–86. Item ID:
`awodey:3:ex6`.

## Background

The kernel relation of a function `f : A → B` (the pairs `(x,x')` with
`f x = f x'`) is an equivalence relation and is exactly the kernel pair of
`f`; conversely quotients by equivalence relations are coequalizers, and the
equivalence relation generated by an arbitrary relation is the kernel of
that coequalizer. See the nLab on
[kernel pair](https://ncatlab.org/nlab/show/kernel+pair) and on
[coequalizer](https://ncatlab.org/nlab/show/coequalizer).

## Current state in the library

The general categorical notions are present: `kernel_pair f` is the pullback
of `f` along itself (`Structure/Regular.v:46`), and a regular epi is the
coequalizer of its own kernel pair (`Structure/Regular.v:71`,
`regular_coeq`). The `Sets`-specific quotient-by-a-generated-equivalence
technique exists but only for pushouts (`Instance/Sets/Pushout.v`, an
inductive smallest-equivalence relation, funext-free). What is missing is
the concrete `Sets` content of this exercise: (a) the kernel relation of `f`
as a binary relation on `A` shown to be an equivalence relation (and to be
the kernel pair); (b) the kernel of a quotient map `A → A/R` is `R`; (c) for
an arbitrary relation `R`, the projection `A → A/⟨R⟩` onto the quotient by
the generated equivalence relation `⟨R⟩` is the coequalizer of the two
projections `R ⇉ A`; (d) `⟨R⟩` is the kernel of that coequalizer. The
generated equivalence relation `⟨R⟩` and the kernel-of-a-quotient results
are not formalized (`rg 'generated equivalence' `/`'least equivalence
relation'` → no hits).

## Work to be done

- In a new `Instance/Sets/Kernel.v` (or extending `Instance/Sets/Pushout.v`'s
  generated-equivalence machinery), define the kernel relation of a `Sets`
  morphism `f` and prove it is an equivalence relation and coincides with
  the kernel pair `kernel_pair f` (part a).
- Prove that the kernel of the quotient projection `A → A/R` for an
  equivalence relation `R` is `R` (part b).
- Reusing the inductive smallest-equivalence relation `⟨R⟩` (as in
  `Instance/Sets/Pushout.v`), prove `A → A/⟨R⟩` is the coequalizer of the
  two projections `R ⇉ A` (part c), which depends on `Sets` having
  coequalizers (issue #315).
- Prove `⟨R⟩` is the kernel of that coequalizer (part d).

In-tree donors: `Structure/Regular.v` (`kernel_pair`, `regular_coeq`),
`Instance/Sets/Pushout.v` (inductive generated-equivalence quotient),
`Structure/Coequalizer.v` (`IsCoequalizer`), the `Sets` coequalizer from
issue #315, the `Sets` kernel-pair/pullback content from issue #333.

## Definition of Done

- [ ] Parts (a)–(d) formalized for `Sets`, faithful to Awodey Exercise 6,
  with the setoid `≈` discipline (never `=` on morphisms).
- [ ] The kernel relation is proved to be an equivalence relation and to
  agree with the categorical `kernel_pair`.
- [ ] No `Admitted`/`admit`/`Axiom` beyond the stdlib axioms already
  enumerated in `docs/AXIOMS.md` for the `Sets` layer.
- [ ] `Print Assumptions` reported for each principal result.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile of the new `Instance/Sets/*` file(s).
- `Print Assumptions` on the four parts.
- Reviewer confirms fidelity to Awodey Exercise 6(a–d): kernel relation as an
  equivalence relation, kernel of a quotient `= R`, `A → A/⟨R⟩` as the
  coequalizer of `R ⇉ A`, and `⟨R⟩` as the kernel of that coequalizer.

## Dependencies

Depends on: #315 (MacLane III.1: Quotient setoids and coequalizers in Sets —
supplies the `Sets` coequalizer of a parallel pair).
Depends on: #333 (MacLane III.4: Pullbacks and kernel pairs in Sets —
supplies the concrete kernel pair in `Sets`).

<!-- catalog: {"ids":["awodey:3:ex6"],"deps":["#315","#333"]} -->

---8<---

```yaml
title: "Awodey 3.5 Ex 5: The category of posets has all coequalizers"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:3:ex5]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), Chapter 3 "Duality", §3.5 Exercises,
Exercise 5 (starred), printed page 76, PDF page 85. Item ID:
`awodey:3:ex5`.

## Background

Coequalizers in the category **Pos** of posets and monotone maps are formed
by quotienting the codomain poset by the least congruence (a preorder
generated from the coequalized pairs), then taking the induced partial
order. See the nLab on
[coequalizer](https://ncatlab.org/nlab/show/coequalizer) and on
[Pos](https://ncatlab.org/nlab/show/Pos).

## Current state in the library

The elementary coequalizer API (`IsCoequalizer`, `HasCoequalizers`) is in
`Structure/Coequalizer.v`, and `coequalizer_epic`
(`Structure/Coequalizer.v:83`) is available. The blocker is that the
category **Pos** of posets and monotone maps does not yet exist in-tree:
`Instance/Poset.v` is a *single* poset viewed as a thin category, not the
category of all posets, and the "[Ord]" category referenced in
`Instance/Proset.v` is never actually defined. Consequently there is no
`HasCoequalizers` instance for **Pos** (`rg 'category of posets'` /
`'HasCoequalizers.*Pos'` → no hits). This exercise is downstream of first
constructing **Pos** (Awodey §1.4 — issue #641).

## Work to be done

- Building on the category **Pos** from issue #641, construct the coequalizer
  of a parallel pair `f, g : A ⇉ B` of monotone maps: take the quotient of
  the carrier of `B` by the equivalence relation generated by `{(f a, g a)}`,
  order it by the preorder generated from `B`'s order through the projection,
  and antisymmetrize to a partial order; verify the projection is monotone
  and satisfies the coequalizer UMP `IsCoequalizer`.
- Assemble a `HasCoequalizers Pos` instance.
- Suggested module path: `Instance/Poset/Coequalizer.v` (or alongside the
  **Pos** construction added by issue #641).

In-tree donors: `Structure/Coequalizer.v` (`IsCoequalizer`,
`HasCoequalizers`, `coequalizer_epic`), the generated-equivalence quotient
technique in `Instance/Sets/Pushout.v`, and the **Pos** category from issue
#641.

## Definition of Done

- [ ] `HasCoequalizers Pos` (or the coequalizer of an arbitrary monotone
  parallel pair) constructed, faithful to Awodey Exercise 5, with the setoid
  `≈` discipline (never `=` on morphisms).
- [ ] The quotient order is verified to be a genuine partial order and the
  projection is monotone and satisfies the coequalizer UMP.
- [ ] No `Admitted`/`admit`/`Axiom` beyond the stdlib axioms enumerated in
  `docs/AXIOMS.md` for the concrete-instance layer.
- [ ] `Print Assumptions` reported for the principal artifact.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile of the new `Instance/Poset/*` file.
- `Print Assumptions` on the `HasCoequalizers Pos` witness.
- Reviewer confirms the statement matches Awodey Exercise 5 (**Pos** has all
  coequalizers, via the quotient poset).

## Dependencies

Depends on: #641 (Awodey 1.4: Pos, the category of posets and monotone maps —
supplies the category **Pos**).

<!-- catalog: {"ids":["awodey:3:ex5"],"deps":["#641"]} -->

---8<---

```yaml
title: "Awodey 3.4: Presentations of algebras by generators and relations as coequalizers of free algebras"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:3.4:example20, awodey:3.4:remark21]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), Chapter 3 "Duality", §3.4
Coequalizers: Example 3.20 (presentations of algebras by generators and
relations; finitely presented algebras), printed pages 72–74, PDF pages
81–83; and Warning 3.21 (presentations are not unique; the finiteness
restriction is inessential), printed page 74, PDF page 83. Item IDs:
`awodey:3.4:example20`, `awodey:3.4:remark21`.

## Background

In a category of algebras with free algebras `F(n)` and all coequalizers, an
algebra presented by generators and relations is the coequalizer
`F(m) ⇉ F(n) → F(n)/(l=r)`, satisfying the expected universal property; the
same algebra admits many such presentations. See the nLab on
[free object](https://ncatlab.org/nlab/show/free+object) and Wikipedia on
[Presentation of a monoid](https://en.wikipedia.org/wiki/Presentation_of_a_monoid).

## Current state in the library

Presentation-by-generators-and-relations with a universal property is
present, but only for PROPs and phrased as a *congruence quotient* of the
free category rather than as a coequalizer of free algebras:
`Construction/PROP/Presentation.v` builds `PresentedCat`/`PresentedPROP`
(the free PROP quotiented by the congruence generated by a signature's
axioms) with the projection `PresentedProj`, and
`Construction/PROP/Presentation/Universal.v` gives its universal property.
The non-uniqueness content of Warning 3.21 is captured, again only for
PROPs, by the two "adding" Tietze moves in `Construction/PROP/Tietze.v`
(add a derivable equation; add a definable generator), with the
equivalence-of-presentations packaging deferred per that file's header.
Missing: the general "category of algebras with free algebras and
coequalizers" setting; the presentation stated explicitly as the coequalizer
`F(m) ⇉ F(n) → Q` of a pair of maps between free algebras; the notion of a
finitely presented algebra in that form; and the general
`F(R) ⇉ F(G) → F(G)/(r₁=r₂)` statement of the finiteness-inessential remark
(`rg 'finitely presented'` / `'coequalizer.*free algebra'` → only the
PROP congruence-quotient headers, none as a coequalizer of free algebras).

## Work to be done

- Over the category of algebras of a variety and its free-algebra adjunction
  (issues #440 and #441), define the algebra presented by a pair of maps
  `l, r : F(m) → F(n)` between free algebras as the coequalizer `q : F(n) → Q`
  in the algebra category, and prove the universal property: any algebra with
  chosen elements satisfying the stipulated relations receives a unique
  homomorphism out of `Q` (Example 3.20). Record the finitely-presented case
  and generalize to arbitrary generator/relation sets
  `F(R) ⇉ F(G) → F(G)/(r₁=r₂)` (Warning 3.21).
- Formalize the non-uniqueness content: exhibit distinct presentations of the
  same algebra (e.g. adjoining a redundant generator with a defining
  relation) — reuse the Tietze "adding" moves of `Construction/PROP/Tietze.v`
  where applicable, or state the coequalizer-level analogue.
- Suggested module path: `Construction/Algebra/Presentation.v` (or under the
  variety/Lawvere development), reusing the `Sets`/algebra coequalizer.

In-tree donors: `Construction/PROP/Presentation.v` and
`Construction/PROP/Presentation/Universal.v` (the congruence-quotient
template and its UMP), `Construction/PROP/Tietze.v` (non-uniqueness moves),
`Structure/Coequalizer.v` (`IsCoequalizer`), and the variety algebra
category + free-algebra adjunction from issues #440/#441.

## Definition of Done

- [ ] The presented algebra defined as the coequalizer `F(m) ⇉ F(n) → Q` of
  free algebras with its universal property, faithful to Awodey Example
  3.20, setoid `≈` throughout (never `=` on morphisms).
- [ ] The general generators/relations form `F(R) ⇉ F(G) → F(G)/(r₁=r₂)`
  (finiteness inessential) recorded, and the non-uniqueness of presentations
  (Warning 3.21) witnessed by an explicit redundant-generator example.
- [ ] No `Admitted`/`admit`/`Axiom` beyond the axioms already enumerated in
  `docs/AXIOMS.md` for whatever layer the algebra category lives in.
- [ ] `Print Assumptions` reported for each principal artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- Single-file compile of the new presentation file.
- `Print Assumptions` on the presented-algebra UMP and the non-uniqueness
  witness.
- Reviewer confirms fidelity to Awodey Example 3.20 (presentation as a
  coequalizer of free algebras, with UMP) and Warning 3.21 (non-uniqueness;
  finiteness inessential).

## Dependencies

Depends on: #440 (MacLane V.6: The category of algebras of a variety).
Depends on: #441 (MacLane V.6: The free-algebra adjunction for a variety).

<!-- catalog: {"ids":["awodey:3.4:example20","awodey:3.4:remark21"],"deps":["#440","#441"]} -->

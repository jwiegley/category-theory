```yaml
title: "Awodey 7.1: Injectivity and surjectivity of a functor on objects and on arrows"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.1:def1, awodey:7.1:construction-codiagonal]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.1 "Functor categories" (functors and
subcategories), printed pages 152–153, PDF pages 161–162. Items covered:
`awodey:7.1:def1` (Definition 7.1), `awodey:7.1:construction-codiagonal`.

## Background

Awodey's Definition 7.1 lists four separate conditions on a functor: injective
or surjective on the collection of objects, injective or surjective on the
collection of arrows, and the two hom-set conditions — faithfulness
(injectivity of each hom-map) and fullness (surjectivity of each hom-map). Only
the last two are invariant notions in the sense of the nLab's
[full and faithful functor](https://ncatlab.org/nlab/show/full+and+faithful+functor);
the object- and arrow-level conditions are the non-invariant ("evil") ones,
whose distinction from fullness/faithfulness is exactly the point of the
codiagonal example, and which the nLab also records as the non-invariant
definition of a
[full subcategory](https://ncatlab.org/nlab/show/full+subcategory).

## Current state in the library

Two of the four conditions exist. `Theory/Functor.v:331` defines
`Class Full` in the choice-carrying house style (a chosen section
`prefmap {x y} (g : F x ~> F y) : x ~> y` with
`fmap_sur : fmap[F] (prefmap g) ≈ g`), and `Theory/Functor.v:342` defines
`Class Faithful` as `fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g → f ≈ g`.

The other two conditions have no in-tree vocabulary at all:

- there is no predicate on `fobj` expressing injectivity or surjectivity on
  objects. The only object-level relative is
  `Theory/Equivalence.v:141`'s `Class EssentiallySurjective` (`eso_obj : D → C`,
  `eso_iso (d : D) : F (eso_obj d) ≅ d`), which is the up-to-isomorphism
  weakening, not Awodey's strict surjectivity;
- there is no total arrow collection to quantify over — homs are an indexed
  family `hom : obj → obj → Type` — so the arrow-level clauses must first be
  phrased over the total space `{x : C & {y : C & x ~> y}}`;
- `Lib/Setoid.v:117`/`:121` provide `Class injective`/`Class surjective`, but
  for setoid *functions*, not for functors.

Consequently Awodey's separating example is unstatable. The codiagonal functor
itself exists — `Functor/Coproduct.v:61` defines
`CoproductFunctor : C ∐ C ⟶ C` with `fobj := sum_obj`, `fmap := sum_map` — but
no `Faithful CoproductFunctor` instance is proved, and there is no way in-tree
to say that it fails injectivity on arrows, which is the whole point of the
example.

## Work to be done

Suggested module: a new `Functor/Properties.v` (top-level `Functor/`
directory, alongside `Functor/Bifunctor.v` and `Functor/Coproduct.v`), plus a
short addition to `Functor/Coproduct.v` for the separating example.

1. Define the total arrow space of a category,
   `Definition TotalHom (C : Category) := {x : C & {y : C & x ~> y}}`, with the
   setoid whose equivalence relates two triples that share domain and codomain
   and have `≈`-equal morphisms (proof-relevant equality of the object indices
   must be handled explicitly — mirror the `hom_cast`/`Morphism_equality`
   idiom already used in `Instance/Discrete.v:37`).
2. Define `InjectiveOnObjects`, `SurjectiveOnObjects` as predicates on `fobj`,
   and `InjectiveOnArrows`, `SurjectiveOnArrows` as predicates on the induced
   map of total arrow spaces. Keep the library's discipline: surjectivity in
   the "chosen preimage" style if it is to be used constructively (matching
   `Full` at `Theory/Functor.v:331`), otherwise as a bare existential — either
   way, document the choice in the file header as `Theory/Functor.v:320-330`
   does for `Full`.
3. Prove the implications that do hold: injective on arrows ⇒ faithful;
   surjective on arrows ⇒ full; injective on objects + injective on arrows is
   what a "strictly injective" embedding means. State explicitly that
   `InjectiveOnObjects` is not invariant under isomorphism of functors.
4. Prove `Faithful CoproductFunctor` for `Functor/Coproduct.v:61`'s ∇, and
   prove that ∇ is *not* injective on arrows whenever `C` has at least one
   morphism (the two summand copies of the same arrow have equal image but
   distinct total-arrow indices). This is the separating witness for
   faithfulness ⊊ injectivity on arrows.

In-tree donors: `Theory/Functor.v` (`Full`, `Faithful`),
`Functor/Coproduct.v`, `Instance/Cat/Cocartesian.v:40` (`Cat_Cocartesian`,
the ambient in which ∇ = [Id, Id] lives), `Lib/Setoid.v` for the setoid
plumbing.

## Definition of Done

- [ ] All four conditions of the book's definition are stated, with
      statement fidelity to Awodey §7.1: hom-level conditions use the setoid
      `≈`, never `=`, on morphisms; only the object/arrow-index components use
      propositional equality, and the header says why.
- [ ] `Faithful CoproductFunctor` is proved, and the failure of injectivity on
      arrows for ∇ is proved (not merely remarked).
- [ ] The implications injective-on-arrows ⇒ faithful and
      surjective-on-arrows ⇒ full are proved.
- [ ] While touching `Functor/Coproduct.v`: its header claims ∇ is "furnished
      by the universal property of the coproduct in `Cat`" and is "the unique
      functor with `[Id,Id] ∘ inl = Id` and `[Id,Id] ∘ inr = Id`", but the file
      proves neither equation (the functor is defined directly by case
      analysis). Either prove the two UMP equations and the uniqueness clause,
      or soften the header to match what is proved.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` is closed under the global context for each new
      principal artifact (the four predicates and the two ∇ results), per the
      `Theory/`+`Functor/` scoping of docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (`nix build .#category-theory_8_19`,
      `.#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (here:
      only if `Functor/Properties.v` becomes the canonical home for functor
      property vocabulary).

## Verification

```bash
coqc -R . Category Functor/Properties.v
coqc -R . Category Functor/Coproduct.v
make
make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Functor.Properties.
Print Assumptions InjectiveOnObjects.
Print Assumptions InjectiveOnArrows.
Require Import Category.Functor.Coproduct.
Print Assumptions Codiagonal_Faithful.
Print Assumptions Codiagonal_not_InjectiveOnArrows.
```

Review item: the four conditions match Awodey §7.1 (printed p. 152), and the
codiagonal example matches the separating claim on printed p. 153.

## Dependencies

Depends on: #231 (MacLane I.3: Full and faithful functors, subcategories, and
reflection of monics) — the fullness/faithfulness half of the same definition.

<!-- catalog: {"ids":["awodey:7.1:def1","awodey:7.1:construction-codiagonal"],"deps":["#231"]} -->

---8<---

```yaml
title: "Awodey 7.1: Monoids, groups, posets and sets embed fully and faithfully in Cat"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.1:example2]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.1, Example 7.2, printed page 153, PDF
page 162. Item covered: `awodey:7.1:example2`.

## Background

Awodey's Example 7.2 observes that the four standard ways of regarding an
algebraic or order structure as a category — a monoid or group as a one-object
category (the nLab's [delooping](https://ncatlab.org/nlab/show/delooping)), a
poset as a thin category, a set as a discrete category — are not merely
object assignments but full and faithful functors into `Cat`, because a functor
between the resulting categories is *exactly* a homomorphism, a monotone map,
or an arbitrary function respectively. Full-and-faithfulness is what licenses
treating these as [full subcategories](https://ncatlab.org/nlab/show/full+subcategory)
of `Cat`, and hence `Cat` as a common home for comparing structures of
different kinds.

## Current state in the library

None of the four embeddings exists as a functor, so no clause of the example is
stated.

- There is no category of monoids over `Sets` and no category of groups.
  `Theory/Algebra/Monoid/Hom.v:83` builds `Mon : Category` whose objects are
  `{ x : C & Monoid x }` — monoid *objects* in a monoidal `C`, with
  `Mon_Forget : Mon ⟶ C` at `:93` — and `Instance/CMon.v` gives commutative
  monoids over setoids; neither is accompanied by a delooping construction
  turning a monoid into a one-object category.
- There is no category `Pos` of posets and monotone maps. `Instance/Proset.v:33`
  turns a single preorder into a thin category
  (`Program Definition Proset ... homset := fun A B => {| Setoid.equiv := fun _ _ => True |}`),
  and `Instance/Poset.v:116` does the same for a poset, but the assignment is
  not packaged as a functor. The only monotone-map correspondence in the tree
  is `Construction/Enriched/Two.v:183`,
  `Theorem EnrichedFunctor_Two_monotone (P Q : TwoPreorder) : EnrichedFunctor _2 ... ↔ MonotoneMap P Q`,
  which is about functors *enriched* over the walking arrow, in a framework
  never connected to the ordinary functors between `Proset P` and `Proset Q`.
- There is no functor `Sets ⟶ Cat` built from `Instance/Discrete.v:37`'s
  `DiscreteCat`; the file supplies only the other leg,
  `DiscreteCat_Functor : (A → C) → DiscreteCat A ⟶ C` (`:52`), and its header
  (`Instance/Discrete.v:31`) explicitly scopes the `Set ⟶ Cat` left adjoint out,
  keeping the construction "at the level of a single functor".
- Consequently no `Full`/`Faithful` instance is proved for any of them.

## Work to be done

Suggested module: `Instance/Cat/Embeddings.v`, with the delooping construction
itself in `Instance/Delooping.v` if it is not already delivered by its own
issue (see Dependencies).

1. Define the delooping of a monoid and of a group as a one-object category,
   and lift it to functors `Mon ⟶ Cat` and `Grp ⟶ Cat` (object part: the
   one-object category; arrow part: a homomorphism read as a functor).
2. Define `Pos ⟶ Cat` (a poset as a thin category, a monotone map as a functor)
   and `Sets ⟶ Cat` (a setoid as a discrete category, a function as a functor).
   For the discrete case, reuse `Instance/Discrete.v:37`'s `DiscreteCat` for the
   object part and `DiscreteCat_Functor` machinery for the arrow part.
3. Prove `Full` and `Faithful` for each of the four functors, in the library's
   choice-carrying style: for `Full`, exhibit `prefmap` explicitly — the
   inverse construction *is* the mathematical content (a functor between
   deloopings is a homomorphism; a functor between thin categories is a
   monotone map; a functor between discrete categories is a function).
4. Optionally record the resulting full subcategories via
   `Construction/Subcategory.v` (`Full` at `:69`,
   `Full_Implies_Full_Functor` at `:74`).

In-tree donors: `Instance/Cat.v`, `Instance/Discrete.v`, `Instance/Proset.v`,
`Instance/Poset.v`, `Theory/Functor.v` (`Full`, `Faithful`),
`Construction/Subcategory.v`.

## Definition of Done

- [ ] Four functors into `Cat` are defined and each is proved `Full` and
      `Faithful`, matching Awodey §7.1 Example 7.2 (printed p. 153); all
      morphism-level equations use `≈`, never `=`.
- [ ] The `Full` witnesses are the honest inverse constructions (functor ↦
      homomorphism / monotone map / function), not opaque existentials.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` reported for each of the four `Full`/`Faithful`
      instances; any stdlib axiom inherited from the `Instance/` layer is
      cross-checked against docs/AXIOMS.md and recorded there if new.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (this is the first systematic
      "structures embed in Cat" statement in the tree).

## Verification

```bash
coqc -R . Category Instance/Cat/Embeddings.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Cat.Embeddings.
Print Assumptions Deloop_Mon_Full.   (* and _Faithful *)
Print Assumptions Pos_to_Cat_Full.   (* and _Faithful *)
Print Assumptions Sets_to_Cat_Full.  (* and _Faithful *)
```

Review item: each clause matches Awodey §7.1 Example 7.2, printed p. 153.

## Dependencies

Depends on: #220 (MacLane I.2: Delooping monoids and groups into one-object
categories)
Depends on: #219 (MacLane I.2: Discrete categories are exactly sets)
Depends on: #223 (MacLane I.2: Preorders as thin categories, with partial and
linear orders)
Depends on: #255 (MacLane I.6: Grp, the category of groups)
Depends on: #503 (MacLane VII.3: Finite products in the category of monoids) —
for the category of monoids over `Sets`
Depends on: #641 (Awodey 1.4: Pos, the category of posets and monotone maps)
Depends on: #231 (MacLane I.3: Full and faithful functors, subcategories, and
reflection of monics)

<!-- catalog: {"ids":["awodey:7.1:example2"],"deps":["#220","#219","#223","#255","#503","#641","#231"]} -->

---8<---

```yaml
title: "Awodey 7.2: Hom(X,2) as a Boolean algebra and the powerset as a functor Sets^op ⟶ BA"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.2:example4]
deps_item_ids: [awodey:7.5:construction-sets-double-dual]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.2, Example 7.4, printed page 157, PDF
pages 166–167. Item covered: `awodey:7.2:example4`.

## Background

For the two-element
[Boolean algebra](https://ncatlab.org/nlab/show/Boolean+algebra) 2, the hom-set
`Hom_Sets(X, 2)` carries the pointwise Boolean structure, and the classical
bijection between characteristic functions and subsets transports it onto the
[power set](https://ncatlab.org/nlab/show/power+set) `P(X)`, with meet/join/
complement becoming intersection/union/relative complement. Precomposition then
makes both `Hom(−,2)` and `P` contravariant functors into Boolean algebras, and
the bijection is natural in `X` — the first step of the Stone development that
follows in §7.3.

## Current state in the library

The powerset-as-contravariant-functor content is present at topos generality;
the Boolean-algebra content and the naturality are not.

- Present: `Theory/Subobject/Functor.v:180` defines
  `Sub : C^op ⟶ Sets` by chosen-pullback reindexing (functor laws discharged
  by `sub_reindex_id`/`sub_reindex_comp`), and
  `Structure/SubobjectClassifier.v:187` proves
  `Theorem classifier_classifies (x : C) : @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}`,
  i.e. the bijection `P(X) ≅ Hom(X, Ω)` pointwise at each object.
  `Instance/FinSet/Classifier.v:353` instantiates the classifier with `Ω := 2`.
- Missing: there is no Boolean algebra structure anywhere — no
  `BoolAlg`/`BooleanAlgebra` class, no meet/join/complement operations, no
  Boolean laws. The nearest structures are `Instance/Props.v` (a Heyting
  *pre*algebra of `Prop`s as a thin category: `Terminal`, `Initial`,
  `Cartesian`, `Cocartesian`, `Closed` — implication, but no complement) and
  `Instance/Two/Monoidal.v` (`two_meet` with `Two_Cartesian`/`Two_Terminal` —
  meet and top only, no join, no negation).
- Missing: the pointwise Boolean structure on `Hom(X,2)`, its transport onto
  `P(X)`, and any lift of either functor to a category of Boolean algebras.
- Missing: naturality. `classifier_classifies` is stated separately at each
  object `x` with no claim that the family is natural in `x` — precisely the
  half of the example that makes it a statement about functors rather than
  about individual sets.

## Work to be done

Suggested modules: `Instance/BoolAlg/Powerset.v` (this issue), on top of the
category `BA` of Boolean algebras and the contravariant powerset functor on
`Sets` delivered by the issues listed under Dependencies.

1. Give `Hom_Sets(X, 2)` the pointwise Boolean algebra structure (0, 1, meet,
   join, complement) and prove the Boolean laws, working in the setoid category
   `Sets` with `≈` throughout.
2. Prove that precomposition `h* : Hom(X,2) → Hom(Y,2)` along `h : Y → X` is a
   Boolean homomorphism, obtaining `Hom(−,2) : Sets^op ⟶ BA`.
3. Transport the structure along the characteristic-function/subset bijection
   to obtain `P^BA : Sets^op ⟶ BA` with `V_{φ∧ψ} = V_φ ∩ V_ψ`,
   `V_{φ∨ψ} = V_φ ∪ V_ψ`, `V_{¬φ} = X ∖ V_φ`, `V_1 = X`, `V_0 = ∅`.
4. Prove the bijection is a **natural** isomorphism
   `Hom(−,2) ≅ P^BA` in `[Sets^op, BA]`, i.e. the square with `h*` and the
   inverse-image map `h^{-1}` commutes for every `h : Y → X`.
5. Optionally connect to the topos-level story: exhibit
   `classifier_classifies` at `Sets`/`FinSet` as the underlying-`Sets` shadow
   of this natural isomorphism, and (this is the honest increment) prove the
   naturality that `Structure/SubobjectClassifier.v:187` currently lacks.

In-tree donors: `Theory/Subobject.v`, `Theory/Subobject/Functor.v` (`Sub`, the
reindexing functor laws), `Structure/SubobjectClassifier.v`,
`Instance/Sets.v`, `Instance/Two/Monoidal.v`.

## Definition of Done

- [ ] `Hom(X,2)` carries a proved Boolean algebra structure and `Hom(−,2)` is a
      functor `Sets^op ⟶ BA`, faithful to Awodey §7.2 Example 7.4 (printed
      p. 157); all equations between morphisms use `≈`.
- [ ] `P^BA : Sets^op ⟶ BA` is defined and the transport of the operations onto
      subsets is proved clause by clause.
- [ ] The isomorphism `Hom(−,2) ≅ P^BA` is proved **natural**, not merely
      pointwise.
- [ ] No `Admitted`, `admit`, or `Axiom` in the new files.
- [ ] `Print Assumptions` reported for the functor and for the natural
      isomorphism; any stdlib axioms are the ones docs/AXIOMS.md already scopes
      for `Instance/`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if this becomes the entry point of a
      Boolean-algebra spine.

## Verification

```bash
coqc -R . Category Instance/BoolAlg/Powerset.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.BoolAlg.Powerset.
Print Assumptions Hom_Two_BoolAlg.
Print Assumptions Powerset_BA_Functor.
Print Assumptions char_subset_natural.
```

Review item: the operations, the transport table, and the naturality square
match Awodey §7.2 Example 7.4, printed pp. 157 (PDF 166–167).

## Dependencies

Depends on: #653 (Awodey 2.2: Boolean algebras and the category Bool)
Depends on: `awodey:7.5:construction-sets-double-dual` — the contravariant
powerset functor `P : Sets^op ⟶ Sets` on which the `BA`-valued lift rides

<!-- catalog: {"ids":["awodey:7.2:example4"],"deps":["#653","awodey:7.5:construction-sets-double-dual"]} -->

---8<---

```yaml
title: "Awodey 7.3: The ultrafilter functor Ult : BA^op ⟶ Sets and the covariant ultrafilter endofunctor on Sets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.3:construction-ult-functor, awodey:7.3:construction-covariant-ultrafilter-functor, awodey:7.3:remark-ult-powerset-not-inverse]
deps_item_ids: [awodey:7.2:example4]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.3 "Stone duality", printed pages
158–159, PDF pages 167–169. Items covered:
`awodey:7.3:construction-ult-functor`,
`awodey:7.3:construction-covariant-ultrafilter-functor`,
`awodey:7.3:remark-ult-powerset-not-inverse`.

## Background

An [ultrafilter](https://ncatlab.org/nlab/show/ultrafilter) in a Boolean
algebra `B` is the same thing as a homomorphism `B → 2`, and the assignment
`B ↦ Ult(B)` with `Ult(h) = h^{-1}` is a contravariant functor
`BA^op ⟶ Sets`. Composing it with the powerset functor in the other direction
gives the covariant ultrafilter endofunctor of `Sets` whose unit sends a point
to its principal ultrafilter — the functor and unit of what later becomes the
ultrafilter monad, and one half of the adjunction underlying
[Stone duality](https://ncatlab.org/nlab/show/Stone+duality).

## Current state in the library

Nothing of this exists. Verified by exhaustive search: `rg -nw 'Ult'` and
`rg -nw 'Filter'` return zero hits in `*.v`; `rg -i 'ultrafilter'` returns
exactly three hits, all background-essay prose — `Theory/Monad.v:65` (Manes'
compact-Hausdorff-algebras remark), `Theory/Kan/Extension.v:39` and `:86`
(Leinster and Kennison–Gildenhuys citations naming the codensity/ultrafilter
monad, which is *not* constructed: `Theory/Kan/Extension.v` declares only
`Induced` (`:127`), `RightKan` (`:140`), `LocalRightKan` (`:154`), `LeftKan`
(`:222`), `LocalLeftKan` (`:234`) and the preservation lemmas). `rg -i 'stone'`
returns only bibliography, the nearest being the background essay at
`Theory/Equivalence.v:119-123`, which cites Stone 1936 as an example of a
duality but attaches no theorem.

The source category is missing too: there is no `BoolAlg`/`BooleanAlgebra`
class anywhere, so neither `Ult(B) ≅ Hom_BA(B, 2)` nor the action
`Ult(h) = h^{-1}` is even statable. There is no principal/non-principal
distinction (`rg -i 'principal'` finds only the unrelated "principal ideal"
poset remark at `Construction/Slice.v:80`).

## Work to be done

Suggested module: `Instance/BoolAlg/Ultrafilter.v`.

1. Define an ultrafilter in a Boolean algebra as a subset closed under meet
   and upward closure, containing 1, proper, and maximal; prove the standard
   equivalence with primeness (`∀ x, x ∈ U ∨ ¬x ∈ U`) — see Dependencies, the
   definition itself belongs to the already-filed filters/ultrafilters issue,
   this issue consumes it.
2. Prove the bijection `Ult(B) ≅ Hom_BA(B, 2)`, `U ↦ χ_U`, `χ ↦ χ^{-1}(1)`,
   and prove it natural in `B`.
3. Define `Ult : BA^op ⟶ Sets` with `Ult(h) := h^{-1}` and prove that the
   inverse image of an ultrafilter along a Boolean homomorphism is an
   ultrafilter (Awodey's computation `Ult(h)(U) = (χ_U ∘ h)^{-1}(1)`), then
   discharge the functor laws.
4. Define the covariant endofunctor `U := Ult ∘ (P^BA)^op : Sets ⟶ Sets`, with
   `U(f)(V) = {W ⊆ Y | f^{-1}(W) ∈ V}`, and prove functoriality.
5. Define `η_X : X → U(X)`, `η(x) = {W ⊆ X | x ∈ W}` (the principal
   ultrafilter) and prove `η : Id ⟹ U` is a natural transformation
   (`U(f) ∘ η_X ≈ η_Y ∘ f`), using `Theory/Natural/Transformation.v`.
6. Record Awodey's negative remark: `(P^BA)^op` and `Ult` are **not** mutually
   inverse. Either prove `η_X` is not surjective in general (this needs a
   non-principal ultrafilter, hence the Boolean prime ideal theorem / ultrafilter
   lemma — admissible in the `Instance/` layer per docs/AXIOMS.md, but it must
   be declared there), or scope it out explicitly in the file header with the
   obstruction named. The adjunction that replaces the equivalence is deferred
   by the book to the chapter on adjoints and is **not** in this issue's scope.

In-tree donors: `Theory/Natural/Transformation.v`, `Instance/Sets.v`,
`Functor/Opposite.v`, `Construction/Opposite.v`, and the `P^BA` functor from
Awodey §7.2 Example 7.4.

## Definition of Done

- [ ] `Ult : BA^op ⟶ Sets` is defined with proved functor laws, and
      `Ult(B) ≅ Hom_BA(B,2)` is proved natural in `B`.
- [ ] The covariant endofunctor `U` on `Sets` is defined with proved functor
      laws.
- [ ] `η : Id ⟹ U` is a proved natural transformation (naturality square, not
      just the components).
- [ ] The non-equivalence remark is either proved or explicitly scoped out in
      the file header, with the choice principle it would need named and
      cross-referenced to docs/AXIOMS.md.
- [ ] Statement fidelity to Awodey §7.3 (printed pp. 158–159); `≈` used for
      all morphism equations.
- [ ] No `Admitted`, `admit`, or `Axiom` beyond any explicitly declared and
      documented choice principle.
- [ ] `Print Assumptions` reported for `Ult`, `U` and `η`, with the axiom
      footprint reconciled against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (the ultrafilter functor is a
      flagship-adjacent construction, referenced by the monad essays at
      `Theory/Monad.v:65` and `Theory/Kan/Extension.v:86`).

## Verification

```bash
coqc -R . Category Instance/BoolAlg/Ultrafilter.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.BoolAlg.Ultrafilter.
Print Assumptions Ult.
Print Assumptions Ult_hom_iso.
Print Assumptions UltSets.       (* the covariant endofunctor *)
Print Assumptions ultrafilter_unit.
```

Review item: the object assignment, the action `Ult(h) = h^{-1}`, the formula
for `U(f)`, and `η(x)` all match Awodey §7.3, printed pp. 158–159.

## Dependencies

Depends on: #653 (Awodey 2.2: Boolean algebras and the category Bool)
Depends on: #654 (Awodey 2.3: Filters, ultrafilters, and the correspondence
between Boolean homomorphisms to 2 and ultrafilters)
Depends on: `awodey:7.2:example4` — the powerset functor `P^BA : Sets^op ⟶ BA`

<!-- catalog: {"ids":["awodey:7.3:construction-ult-functor","awodey:7.3:construction-covariant-ultrafilter-functor","awodey:7.3:remark-ult-powerset-not-inverse"],"deps":["#653","#654","awodey:7.2:example4"]} -->

---8<---

```yaml
title: "Awodey 7.3: The Stone representation φ_B : B → P(Ult(B)) and the Stone representation theorem"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.3:construction-stone-representation, awodey:7.3:prop5, awodey:7:ex2]
deps_item_ids: [awodey:7.3:construction-ult-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.3, printed page 160 (PDF page 169) for
the construction and Proposition 7.5; §7.10 Exercise 2, printed page 186 (PDF
page 195) for the naturality. Items covered:
`awodey:7.3:construction-stone-representation`, `awodey:7.3:prop5`,
`awodey:7:ex2`.

## Background

The Stone representation embeds every Boolean algebra into a powerset algebra:
`φ_B(b) = {V ∈ Ult(B) | b ∈ V}` is an injective Boolean homomorphism
`B → P(Ult(B))`, so every Boolean algebra is (isomorphic to) a field of sets —
[Stone's representation theorem](https://en.wikipedia.org/wiki/Stone%27s_representation_theorem_for_Boolean_algebras),
the discrete shadow of full
[Stone duality](https://ncatlab.org/nlab/show/Stone+duality). Injectivity is
where a choice principle enters: separating two distinct elements requires an
ultrafilter containing one and not the other (the Boolean prime ideal theorem).

## Current state in the library

Entirely absent. `rg -i 'prime ideal'` and `rg -i 'ultrafilter lemma'` return
zero hits; `rg -i 'clopen'` returns zero hits; `rg 'field of sets'` returns zero
hits. `rg -i 'stone'` returns only bibliography, the closest being the
background essay at `Theory/Equivalence.v:119-121` citing Stone's 1936
*Transactions of the AMS* paper as motivation inside the equivalence-of-
categories discussion — the in-tree examples that essay then lists (`Monadic`,
`Karoubi`, `RoundTrip_Equivalence`, `Idempotent_EM_Equivalence`) are all
Stone-free.

Neither `B` (no Boolean algebra class) nor `P(Ult(B))` (no ultrafilter set, no
powerset algebra) is expressible, so neither `φ_B`, nor its injectivity, nor
its naturality has any in-tree counterpart. This is not out of scope: the
library already accepts stdlib axioms in its `Instance/` layer (docs/AXIOMS.md),
so a choice-principle-dependent injectivity argument is admissible there — the
item is simply unbuilt.

## Work to be done

Suggested module: `Instance/BoolAlg/Stone.v`.

1. Define `φ_B : B → P(Ult(B))`, `φ_B(b) := {V ∈ Ult(B) | b ∈ V}`, and prove it
   is a Boolean homomorphism (each operation clause separately).
2. Prove `φ` is **natural**: for every Boolean homomorphism `h : A → B` the
   square `F(h) ∘ φ_A ≈ φ_B ∘ h` commutes, where
   `F := P^BA ∘ Ult^op : BA ⟶ BA`. This is §7.10 Exercise 2 and it upgrades the
   construction to a natural transformation `Id_BA ⟹ F`.
3. Prove injectivity of `φ_B`. State the choice principle used (Boolean prime
   ideal theorem / ultrafilter lemma) as an explicit hypothesis of the theorem
   rather than a global `Axiom`, so that the statement remains an axiom-free
   conditional in the library's house style, and record the instantiation
   options in the header.
4. Conclude the representation theorem: every Boolean algebra is isomorphic to
   a subalgebra of a powerset algebra (`B ≅ image φ_B`, a field of sets on
   `X := Ult(B)`), and note the identification of `F(B)` with the "double dual"
   `Hom_Sets(Hom_BA(B,2), 2)` that Exercise 2 points out.
5. Update docs/INHABITATION.md if the theorem is stated conditionally over the
   choice hypothesis with no in-tree witness of that hypothesis.

In-tree donors: the `Ult` functor and `P^BA` from §7.3/§7.2,
`Theory/Natural/Transformation.v`, `Theory/Morphisms.v` (`Monic`),
`Instance/Sets/Image.v` (concrete images, for the "algebra of subsets" form).

## Definition of Done

- [ ] `φ_B` is defined and proved a Boolean homomorphism.
- [ ] Naturality of `φ` (Exercise 2) is proved as a `Transform`, not merely
      component-wise.
- [ ] Injectivity is proved under an explicitly stated choice hypothesis
      (never a bare global `Axiom`), and the representation theorem is
      concluded from it, matching Awodey Proposition 7.5, printed p. 160.
- [ ] All morphism-level equations use `≈`.
- [ ] No `Admitted`/`admit`; no new global `Axiom` — the choice principle is a
      hypothesis.
- [ ] `Print Assumptions` reported for `φ`, its naturality, and the
      representation theorem; result reconciled against docs/AXIOMS.md, and
      docs/INHABITATION.md updated if the theorem is conditional-only.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level: the first
      representation theorem in the tree).

## Verification

```bash
coqc -R . Category Instance/BoolAlg/Stone.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.BoolAlg.Stone.
Print Assumptions stone_map.
Print Assumptions stone_map_natural.
Print Assumptions stone_representation.
```

Review item: `φ_B(b)`, the naturality square, and the statement of the
representation theorem match Awodey §7.3, printed p. 160, and §7.10 Exercise 2,
printed p. 186.

## Dependencies

Depends on: `awodey:7.3:construction-ult-functor` — the `Ult` functor and the
covariant composite `F = P^BA ∘ Ult^op`
Depends on: #653 (Awodey 2.2: Boolean algebras and the category Bool)
Depends on: #654 (Awodey 2.3: Filters, ultrafilters, and the correspondence
between Boolean homomorphisms to 2 and ultrafilters)

<!-- catalog: {"ids":["awodey:7.3:construction-stone-representation","awodey:7.3:prop5","awodey:7:ex2"],"deps":["awodey:7.3:construction-ult-functor","#653","#654"]} -->

---8<---

```yaml
title: "Awodey 7.9: Finite Stone duality — BA_fin is equivalent to Sets_fin^op"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.9:prop30, awodey:7.9:lem31, awodey:7.9:lem32, awodey:7:ex7, awodey:7.9:example29]
deps_item_ids: [awodey:7.2:example4, awodey:7.3:construction-ult-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.9 "Examples of equivalences", printed
pages 183–185, PDF pages 192–194 (Example 7.29, Proposition 7.30, Lemmas 7.31
and 7.32); §7.10 Exercise 7, printed page 187, PDF page 196. Items covered:
`awodey:7.9:prop30`, `awodey:7.9:lem31`, `awodey:7.9:lem32`, `awodey:7:ex7`,
`awodey:7.9:example29`.

## Background

Finite [Stone duality](https://en.wikipedia.org/wiki/Stone_duality) is the
discrete, topology-free case of the general theorem: the category of finite
Boolean algebras is equivalent to the opposite of the category of finite sets,
with the powerset functor one way and the atoms functor the other. It is also
Awodey's illustration of the general shape of duality results, which are
equivalences `C ≃ D^op` rather than isomorphisms, because the two round trips
recover objects only up to isomorphism — see the nLab's
[Stone duality](https://ncatlab.org/nlab/show/Stone+duality).

## Current state in the library

Nothing of the duality exists, and one side of it does not exist as a category.

- No Boolean algebras: `rg -iln 'boolean'` returns 16 files and every hit is
  prose — `Theory/Equivalence.v:120` (Stone citation), `Instance/Two.v:85-88`
  ("Boolean algebra `[_2]`" as a posetal aside), `Theory/Lawvere.v:87` (a list
  of algebraic theories). No atoms either: `rg -in '\batom'` finds one hit,
  `Solver/Reify.v:33` (reification jargon), and `rg -in '\batomic\b'` and
  `rg -in 'join-prime'` find none.
- The finite-sets side exists only in skeletal form: `Instance/FinSet.v:116`,
  `Program Definition FinSet : Category := {| obj := nat; hom := fun m n => Fin.t m → Fin.t n; homset := fun m n => fun_setoid (Fin.t m) (Fin.t n); ... |}`,
  which is Awodey's `Ord_fin`, not `Sets_fin`; the library has no finiteness
  predicate on setoids and no category of finite sets, and
  `Theory/Equivalence.v:98` explicitly confines skeletons to concrete instances
  such as this one.
- The general equivalence apparatus is fully available:
  `Theory/Equivalence.v:151` `Class EquivalenceOfCategories` (`quasi_inverse`,
  `equivalence_counit`, `equivalence_unit`), `:163`
  `Equivalence_to_Cat_Iso : C ≅[Cat] D`, `Theory/Equivalence/FullFaithful.v:160`
  `FF_ESO_Equivalence`, and `Construction/Opposite.v:126` `op_invol`. What is
  missing is any instance of the shape `C ≃ D^op`: no duality theorem is proved
  anywhere in the tree. (`Instance/Rel.v:38` claims a self-duality
  `Rel ≅ Rel^op` in its header essay, but the file's definitions — `Rel:45`,
  `Rel_Initial:90`, `Rel_Cartesian:97`, `Rel_Cocartesian:127`, `Rel_Closed:146`,
  `Relation_Functor:167` — contain no such functor or isomorphism.)

Note a presentational subtlety a reviewer must not miss: `Instance/Cat.v:145`
sets `homset := @Functor_Setoid` and `Theory/Functor.v:148` defines that
setoid's `equiv` as a natural isomorphism, so the library's `≅[Cat]` *already
means* equivalence. The book's isomorphism-versus-equivalence contrast must
therefore be drawn against strict/on-the-nose equality of functors, and the
issue should say so in the file header.

## Work to be done

Suggested module: `Instance/BoolAlg/FiniteDuality.v`.

1. Define the atoms of a Boolean algebra (`0 < a` and `b < a → b = 0`) and the
   full subcategory `BA_fin` of finite Boolean algebras.
2. Prove Lemma 7.31: for a finite `B`, the atoms of `B` are in bijection with
   the ultrafilters of `B`, via `a ↦ ↑a` and `U ↦ ⋀U`, with both round trips
   (Awodey's argument: `↑a` is an ultrafilter because for each `b` either
   `a ∧ b = a` or `a ∧ b = 0`; `⋀U ∈ U` by finiteness and meet-closure; `↑⋀U = U`
   by the complement argument).
3. Prove Lemma 7.32: every element of a finite `B` is the join of the atoms
   below it, and atoms are join-prime.
4. Define the atoms functor `A : BA_fin^op ⟶ Sets_fin`, including the action on
   a homomorphism `h` (for each atom `a'` of `B'` the unique atom `a` of `B`
   with `a' ≤ h(b) ↔ a ≤ b`, obtained as `⋀ h^{-1}(↑a')`), and prove
   functoriality.
5. Prove Exercise 7: for finite `B` the Stone map `φ_B : B → P(Ult(B))` is an
   isomorphism of Boolean algebras (this is `β_B`, and Lemma 7.32 is exactly
   what makes it surjective).
6. Assemble the equivalence: `α_X : X ≅ A(P(X))`, `x ↦ {x}`, and
   `β_B : B ≅ P(A(B))`, both proved natural, hence
   `BA_fin ≃ Sets_fin^op` via `Theory/Equivalence.v:151` or
   `Theory/Equivalence/FullFaithful.v:160`.
7. Bridge to the in-tree skeletal `FinSet` (`Instance/FinSet.v:116`): either
   state the duality against `FinSet^op` directly, or state it against a
   category of finite sets and compose with the skeleton equivalence (see
   Dependencies).
8. Record, in the file header, that this is the tree's first duality of the
   shape `C ≃ D^op` (Awodey Example 7.29) and note the `≅[Cat]` subtlety above.

In-tree donors: `Theory/Equivalence.v`, `Theory/Equivalence/FullFaithful.v`,
`Construction/Opposite.v`, `Instance/FinSet.v`, `Instance/FinSet/Product.v`,
`Instance/FinSet/Classifier.v`, `Construction/Subcategory.v` (for `BA_fin` as a
full subcategory of `BA`).

## Definition of Done

- [ ] Atoms are defined and Lemmas 7.31 and 7.32 are proved (printed pp.
      184–185).
- [ ] The atoms functor `A` is defined with proved functoriality, including the
      non-trivial action on homomorphisms.
- [ ] Exercise 7 (`φ_B` an isomorphism for finite `B`, printed p. 187) is
      proved.
- [ ] `α` and `β` are proved natural and assembled into an
      `EquivalenceOfCategories`, matching Proposition 7.30, printed p. 183.
- [ ] The duality is presented in the `C ≃ D^op` shape of Example 7.29, and the
      file header records that the library's `≅[Cat]` already means equivalence
      (`Instance/Cat.v:145`, `Theory/Functor.v:148`), so the book's contrast is
      against strict equality of functors.
- [ ] All morphism equations use `≈`.
- [ ] No `Admitted`, `admit`, or `Axiom` (the finite case needs no choice
      principle — this must be checked, since the general case does).
- [ ] `Print Assumptions` reported for the atoms functor, both natural
      isomorphisms, and the equivalence; reconciled against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship: the first duality theorem in
      the tree) and docs/INHABITATION.md updated with the concrete witness.

## Verification

```bash
coqc -R . Category Instance/BoolAlg/FiniteDuality.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.BoolAlg.FiniteDuality.
Print Assumptions atoms_ultrafilters_iso.   (* Lemma 7.31 *)
Print Assumptions finite_join_of_atoms.     (* Lemma 7.32 *)
Print Assumptions stone_finite_iso.         (* Exercise 7 *)
Print Assumptions finite_stone_duality.     (* Proposition 7.30 *)
```

Review item: the statements match Awodey §7.9, printed pp. 183–185, and §7.10
Exercise 7, printed p. 187.

## Dependencies

Depends on: #653 (Awodey 2.2: Boolean algebras and the category Bool)
Depends on: #238 (MacLane I.4: The skeleton equivalence between finite sets and
finite ordinals) — for bridging `Sets_fin` and the in-tree skeletal `FinSet`
Depends on: `awodey:7.2:example4` — the powerset functor into Boolean algebras
Depends on: `awodey:7.3:construction-ult-functor` — the ultrafilter functor

<!-- catalog: {"ids":["awodey:7.9:prop30","awodey:7.9:lem31","awodey:7.9:lem32","awodey:7:ex7","awodey:7.9:example29"],"deps":["#653","#238","awodey:7.2:example4","awodey:7.3:construction-ult-functor"]} -->

---8<---

```yaml
title: "Awodey 7.9: Complete atomic Boolean algebras and the discrete Stone duality caBA ≃ Sets^op"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.9:remark-caba]
deps_item_ids: [awodey:7.9:prop30]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.9, unnumbered closing remark, printed
page 185, PDF page 194. Item covered: `awodey:7.9:remark-caba`.

## Background

Dropping finiteness but keeping completeness and atomicity recovers the duality
in full generality on the discrete side: the category of
[complete Boolean algebras](https://ncatlab.org/nlab/show/complete+Boolean+algebra)
that are atomic, with complete (join-preserving) homomorphisms, is equivalent to
`Sets^op` via the powerset. This is the atomic, topology-free case of
[Stone duality](https://en.wikipedia.org/wiki/Stone_duality); the general
theorem, requiring Stone spaces and continuous maps, is out of reach here since
the library has no category of topological spaces.

## Current state in the library

Absent, and one direction of the statement is currently unstatable. `rg -in
'complete atomic'` and `rg -in 'caBA'` return zero hits. There is no Boolean
algebra class at all (see the finite-duality issue for the full negative log),
hence no notion of a complete Boolean algebra, no completeness of a
homomorphism, and no atomicity predicate. `rg -in 'Instance Top\b|Definition
Top\b'` returns zero hits, confirming that no category of topological spaces
exists, so the Stone-space half of the general theorem cannot be stated either
and must be scoped out.

The target side is available: `Instance/Sets.v` supplies `Sets` and
`Construction/Opposite.v:106` supplies `C^op` with `op_invol` at `:126`.

## Work to be done

Suggested module: `Instance/BoolAlg/CABA.v`.

1. Define completeness of a Boolean algebra (every subset has a join),
   completeness of a homomorphism (preserves those joins), and atomicity (every
   non-zero element dominates an atom); assemble the category `caBA`.
2. Prove that `P(X)` is a complete atomic Boolean algebra for every set `X` and
   that inverse image along any function is a complete homomorphism, giving
   `P : Sets^op ⟶ caBA`.
3. Prove the two natural isomorphisms — `X ≅ A(P(X))` (singletons) and
   `B ≅ P(A(B))` (an element is the join of the atoms below it, now using
   completeness in place of finiteness) — and assemble
   `caBA ≃ Sets^op`.
4. State in the file header exactly what is *not* being proved: the full Stone
   duality between all Boolean algebras and Stone spaces (Johnstone,
   *Stone Spaces*), which needs a category of topological spaces the library
   does not have. Cross-reference docs/INHABITATION.md.
5. Note whether the isomorphism `B ≅ P(A(B))` needs any choice principle in the
   library's constructive setting, and, if it does, state it as a hypothesis
   rather than an axiom.

In-tree donors: `Instance/Sets.v`, `Construction/Opposite.v`,
`Theory/Equivalence.v`, `Theory/Equivalence/FullFaithful.v`, and the atoms
machinery from the finite-duality issue.

## Definition of Done

- [ ] `caBA` is defined (complete, atomic, complete homomorphisms) and
      `P : Sets^op ⟶ caBA` is proved a functor.
- [ ] `caBA ≃ Sets^op` is proved via `EquivalenceOfCategories`, with both
      comparison families proved natural, matching Awodey's remark on printed
      p. 185.
- [ ] The file header discloses that the full Stone duality (Boolean algebras
      versus Stone spaces) is out of scope and why.
- [ ] All morphism equations use `≈`.
- [ ] No `Admitted`, `admit`, or `Axiom`; any choice principle appears as an
      explicit hypothesis.
- [ ] `Print Assumptions` reported for the functor and the equivalence;
      reconciled against docs/AXIOMS.md, and docs/INHABITATION.md updated.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated.

## Verification

```bash
coqc -R . Category Instance/BoolAlg/CABA.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.BoolAlg.CABA.
Print Assumptions Powerset_caBA.
Print Assumptions caBA_Sets_duality.
```

Review item: the definitions of complete/atomic/complete-homomorphism and the
statement of the duality match Awodey §7.9, printed p. 185.

## Dependencies

Depends on: `awodey:7.9:prop30` — the finite duality, whose atoms machinery and
comparison families this generalizes
Depends on: #653 (Awodey 2.2: Boolean algebras and the category Bool)

<!-- catalog: {"ids":["awodey:7.9:remark-caba"],"deps":["awodey:7.9:prop30","#653"]} -->

---8<---

```yaml
title: "Awodey 7.5: The contravariant powerset functor on Sets, the double-powerset unit, and P(A+B) ≅ P(A) × P(B)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.5:construction-sets-double-dual, awodey:7:ex9, awodey:7:ex1]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.5 "Natural transformations", printed
page 167, PDF page 176 (the `Sets` analogue of the double dual); §7.10
Exercise 9, printed page 188, PDF page 197; §7.10 Exercise 1, printed page 186,
PDF page 195. Items covered: `awodey:7.5:construction-sets-double-dual`,
`awodey:7:ex9`, `awodey:7:ex1`.

## Background

Replacing the ground field by 2 turns the vector-space duality story into the
[power set](https://ncatlab.org/nlab/show/power+set) story: `A* = P(A) ≅ Sets(A,2)`,
the dual of a map is its inverse image, and transposing evaluation twice gives
`η_A : A → PP(A)`, `η_A(a) = {U ⊆ A | a ∈ U}`. Unlike the finite-dimensional
case, `η_A` is never an isomorphism — by
[Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem) `A` is
strictly smaller than `P(A)` — yet it is still natural, which is the point of
the example. The same functor turns coproducts into products, giving the
exponential-law corollary of Exercise 1.

## Current state in the library

- There is no powerset functor on `Sets`. `rg -iln 'powerset|power set'`
  returns exactly one file, `Structure/Topos.v`, whose only power construct is
  `Definition Pow {C} {H : ElementaryTopos C} (a : C) : C := Ω ^ a`
  (`Structure/Topos.v:129`) — an object map with no `fmap`, hence no functor,
  a fortiori no `P ∘ P` and no `η : Id ⟹ PP`.
- The nearest relative is the *subobject* functor: `Theory/Subobject/Functor.v:30`
  opens `Context `{@HasPullbacks C}` before defining
  `Sub : C^op ⟶ Sets` at `:180`; but `rg HasPullbacks` finds exactly one
  instance in the whole tree, `FinSet_Pullbacks`
  (`Instance/FinSet/Classifier.v:264`), so `Sub` is not available at `Sets`.
- The double-dual apparatus that does exist assumes what Awodey constructs:
  `Structure/Monoidal/StarAutonomous.v:252` defines
  `double_dual (d : C) : C ⟶ C := dual d ◯ (dual d)^op` and `:261`'s
  `Class StarAutonomous` *posits* `star_double_dual {x : C} : x ≅ double_dual dualizer x`
  as a field. That is an isomorphism, so it cannot model the powerset `η`,
  which is never invertible.
- Exercise 1's first clause is present, and in greater generality than the book
  asks: `Structure/BiCCC.v:134` proves
  `#[export] Program Instance exp_coprod {x y z : C} : x^(y + z) ≅ x^y × x^z`
  with both round trips discharged, instantiating at `Coq` (`Instance/Coq.v:167`
  `Coq_Closed`, `:141` `Coq_Cartesian`, `:199` `Coq_Cocartesian`) and at
  `FinSet`. What is missing from Exercise 1 is the powerset clause
  `P(A+B) ≅ P(A) × P(B)`, and the book's stated route: there is no theorem that
  a representable functor preserves limits — only RAPL for right adjoints at
  `Adjunction/Continuity.v:198-202`.

## Work to be done

Suggested module: `Instance/Sets/Powerset.v`.

1. Define the powerset of a setoid (the setoid of `≈`-closed predicates, with
   extensional equality of subsets as the hom-setoid equivalence — this keeps
   the construction funext-free, in the style of `Instance/Sets/End.v` and
   `Instance/FinSet/Closed.v`).
2. Define `P : Sets^op ⟶ Sets` with `P(f) := f^{-1}` and prove the functor laws.
3. Define the covariant composite `PP := P ∘ P^op : Sets ⟶ Sets` and prove
   functoriality.
4. Define `η_A : A → PP(A)`, `η_A(a) = {U ⊆ A | a ∈ U}`, and prove
   `η : Id ⟹ PP` is a natural transformation (Exercise 9). Where the book
   derives `η` by transposing the membership relation twice, either follow that
   route through the closed structure of `Sets` or give the direct definition
   and prove it agrees.
5. Prove `η_A` is never an isomorphism (Cantor), or scope that clause out
   explicitly in the header if the diagonal argument is disproportionate.
6. Prove `P(A + B) ≅ P(A) × P(B)` (Exercise 1, second clause), preferably by
   exhibiting `P ≅ Hom(−, 2)` and reusing `Structure/BiCCC.v:134`'s
   `exp_coprod`; record in the header that the book's own route needs
   "representables preserve limits", which the tree does not yet have (see
   Dependencies).

In-tree donors: `Instance/Sets.v`, `Instance/Sets/End.v` (funext-free setoid
subobject idiom), `Structure/BiCCC.v` (`exp_coprod`),
`Theory/Natural/Transformation.v`, `Functor/Hom.v`.

## Definition of Done

- [ ] `P : Sets^op ⟶ Sets` is defined with proved functor laws, funext-free.
- [ ] `η : Id ⟹ PP` is proved a natural transformation (Exercise 9, printed
      p. 188), with the naturality square, not just the components.
- [ ] `P(A+B) ≅ P(A) × P(B)` is proved (Exercise 1, printed p. 186).
- [ ] Cantor's obstruction (`η_A` is never invertible) is proved or explicitly
      scoped out in the header, matching Awodey's remark on printed p. 167.
- [ ] All morphism equations use `≈`; subset equality is the setoid
      equivalence, never `=`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for `P`, `PP`, `η`, and the coproduct
      isomorphism; reconciled against docs/AXIOMS.md (`Instance/` layer).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (the powerset functor is a reusable
      construction consumed by the Boolean-algebra and Stone issues).

## Verification

```bash
coqc -R . Category Instance/Sets/Powerset.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Sets.Powerset.
Print Assumptions Powerset.
Print Assumptions double_powerset_unit.
Print Assumptions powerset_coprod.
```

Review item: `η_A(a)`, the naturality square, and the coproduct clause match
Awodey §7.5 printed p. 167, §7.10 Exercises 9 and 1, printed pp. 188 and 186.

## Dependencies

Depends on: #311 (MacLane III.1: A universal element for the contravariant
power-set functor)
Depends on: #428 (MacLane V.4: Hom-functors are continuous) — the book's stated
route for Exercise 1

<!-- catalog: {"ids":["awodey:7.5:construction-sets-double-dual","awodey:7:ex9","awodey:7:ex1"],"deps":["#311","#428"]} -->

---8<---

```yaml
title: "Awodey 7.7: The category of directed graphs as the functor category Sets^Γ"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.7:example17]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.7 "Examples of functor categories",
Example 7.17, printed page 172, PDF pages 181–182. Item covered:
`awodey:7.7:example17`.

## Background

A directed graph — the nLab's [quiver](https://ncatlab.org/nlab/show/quiver) —
is a pair of sets with source and target maps, and a graph homomorphism is a
pair of maps making two squares commute; that data is exactly a
[presheaf](https://ncatlab.org/nlab/show/presheaf) on the two-object,
two-parallel-arrow category Γ and a natural transformation between two such.
Identifying the category of graphs with `Sets^Γ` immediately yields structural
consequences, notably cartesian closure.

## Current state in the library

Both sides of the identification exist but are never identified.

- `Instance/Parallel.v:80` defines
  `Program Definition Parallel : Category := {| obj := ParObj; hom := fun x y => ∃ b : bool, ParHom b x y; ... |}`
  — two objects and two parallel non-identity arrows, exactly Awodey's Γ (see
  the header, `Instance/Parallel.v:15-25`).
- `Instance/Parallel.v:166` defines one presheaf on it,
  `Presheaf_Graph : Parallel^op ⟶ Sets` with `ParX ↦ nat` (vertices),
  `ParY ↦ nat * nat` (edges) and `fmap true ↦ fst`, `false ↦ snd` — a single
  graph, not a correspondence. The identification appears only as a comment
  ("a presheaf on the parallel-pair category x ⇉ y is a graph (quiver)").
- `Construction/Free/Quiver.v:358` defines
  `#[export] Instance QuiverCategory : Category` over `QuiverHomomorphism` with
  the hom-setoid `QuiverHomomorphismEquivalence`. But the in-tree `Quiver` uses
  `edges : nodes → nodes → Type`, an indexed family, rather than a single edge
  set with source and target maps; homomorphisms preserve source and target by
  typing rather than by two commuting squares, and the translation between the
  two presentations is not proved.
- There is no functor, equivalence or isomorphism between `QuiverCategory` and
  `[Parallel^op, Sets]`, and no functor category anywhere in the tree carries
  cartesian closed structure, so Awodey's corollary "graphs are cartesian
  closed" has no route.

## Work to be done

Suggested module: `Instance/Parallel/Graphs.v`.

1. Define the "two sets plus source/target" presentation of a graph as a
   category `Graph` in `Sets` (objects: `G₁, G₀` with `s, t : G₁ → G₀`;
   morphisms: pairs making both squares commute, with `≈` for the commutation).
2. Prove `Graph ≅ [Parallel^op, Sets]` — ideally an isomorphism of categories,
   at minimum an `EquivalenceOfCategories` — by translating a presheaf into its
   source/target data and back.
3. Relate the indexed-family presentation to the source/target presentation:
   build the comparison functor between `Construction/Free/Quiver.v:358`'s
   `QuiverCategory` and `Graph` and prove it full and faithful (state honestly
   whether it is an equivalence, given the proof-relevant `edges` family).
4. Derive Awodey's corollary: `[Parallel^op, Sets]` is cartesian closed, hence
   so is the category of graphs. This rides on presheaf categories being
   cartesian closed (see Dependencies) — do not re-prove it here.

In-tree donors: `Instance/Parallel.v`, `Instance/Fun.v:108` (`Fun`, with the
`[C, D]` notation), `Construction/Free/Quiver.v`, `Instance/Sets.v`,
`Theory/Equivalence.v`.

## Definition of Done

- [ ] The source/target presentation of graphs is defined as a category, with
      homomorphisms given by the two commuting squares, matching Awodey §7.7
      Example 7.17 (printed p. 172).
- [ ] `Graph ≅ [Parallel^op, Sets]` (or `≃`, with the weaker conclusion stated
      explicitly) is proved in both directions.
- [ ] The comparison with `QuiverCategory` is proved full and faithful, and the
      header states precisely how the indexed-family presentation relates.
- [ ] The cartesian-closure corollary is derived, not assumed.
- [ ] All morphism equations use `≈`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for the comparison functors and the
      isomorphism/equivalence.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the graph/presheaf identification
      becomes a documented flagship.

## Verification

```bash
coqc -R . Category Instance/Parallel/Graphs.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Parallel.Graphs.
Print Assumptions Graph_Presheaf_iso.
Print Assumptions Quiver_Graph_comparison.
Print Assumptions Graph_Closed.
```

Review item: the graph/homomorphism definitions and the identification with
`Sets^Γ` match Awodey §7.7 Example 7.17, printed p. 172.

## Dependencies

Depends on: #404 (MacLane IV.10: Sets and presheaf categories as elementary
toposes) — supplies cartesian closure of `Sets^C`

<!-- catalog: {"ids":["awodey:7.7:example17"],"deps":["#404"]} -->

---8<---

```yaml
title: "Awodey 7.7: The functor category of two posets is the exponential poset, and Pos ⟶ Cat preserves cartesian closed structure"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.7:example19, awodey:7.7:prop20]
deps_item_ids: [awodey:7.1:example2]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.7, Example 7.19 and Proposition 7.20,
printed pages 174–175, PDF pages 183–184. Items covered:
`awodey:7.7:example19`, `awodey:7.7:prop20`.

## Background

For posets `P, Q` regarded as thin categories, a natural transformation between
two monotone maps exists (and is then unique) exactly when the maps are ordered
pointwise, because the hom-sets are subsingletons; hence the
[functor category](https://ncatlab.org/nlab/show/functor+category) `Q^P` *is*
the exponential poset. Proposition 7.20 packages this: the inclusion of posets
into categories preserves the
[cartesian closed](https://ncatlab.org/nlab/show/cartesian+closed+category)
structure — terminal object, binary products and exponentials computed in `Pos`
agree with those computed in `Cat`.

## Current state in the library

The functor category between two thin categories is never formed and nothing is
proved about it.

- `Instance/Proset.v:33` gives
  `Program Definition Proset ... homset := fun A B => {| Setoid.equiv := fun _ _ => True |}`
  — thin categories from preorders — and `Instance/Poset.v:116` the poset
  version; but there is no proof that ordinary functors `Proset P ⟶ Proset Q`
  are exactly monotone maps. The only monotone-map correspondence in the tree,
  `Construction/Enriched/Two.v:183`
  (`EnrichedFunctor_Two_monotone (P Q : TwoPreorder) : EnrichedFunctor _2 ... ↔ MonotoneMap P Q`,
  with `MonotoneMap` at `:175`), is about functors *enriched* over the walking
  arrow, in a framework never bridged to the ordinary one.
- There is no statement that hom-sets of a functor category into a thin
  category are subsingletons, hence no uniqueness of natural transformations
  there, and no "there is a transformation `f ⟹ g` iff `f ≤ g` pointwise".
- There is no category `Pos`, hence no inclusion `Pos ⟶ Cat` and no exponential
  poset to compare with.
- The vocabulary for the preservation statement *does* exist and should be
  used: `Functor/Structure/Cartesian.v:49` defines `Class CartesianFunctor`,
  and `Functor/Structure/Cartesian/Closed.v:49` defines `Class ClosedFunctor`
  (both registered in `_CoqProject`), alongside `TerminalFunctor`. The library
  also has `Instance/Cat/Cartesian.v:39` `Cat_Cartesian`, `Instance/One.v:54`
  `Cat_Terminal` and `Instance/Cat/Cartesian/Closed.v:47` `Cat_Closed`
  (`exponent_obj := @Fun`), i.e. the whole `Cat` side of the comparison.

## Work to be done

Suggested module: `Instance/Pos/Cat.v` (the inclusion and its preservation
properties), with the thin-functor-category lemmas in the same file.

1. Prove that a functor between thin categories is exactly a monotone map
   (object part monotone; arrow part forced), and that the hom-setoids of
   `[Proset P, Proset Q]` are subsingletons.
2. Prove: there exists a natural transformation `f ⟹ g` in `[Proset P, Proset Q]`
   iff `f ≤ g` pointwise, and any two such are `≈`-equal. Conclude that
   `[Proset P, Proset Q]` is itself thin, and is the thin category of the
   exponential poset `Q^P`.
3. Define the inclusion `Pos ⟶ Cat` (this is one clause of the embeddings issue
   listed under Dependencies; consume it rather than duplicating it).
4. Prove `TerminalFunctor`, `CartesianFunctor` and `ClosedFunctor` for the
   inclusion, i.e. that `1`, `P × Q` and `Q^P` computed in `Pos` are carried to
   the terminal category, the product category and the functor category — the
   exponential clause being step 2.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Instance/Fun.v`,
`Instance/Cat/Cartesian.v`, `Instance/Cat/Cartesian/Closed.v`,
`Instance/One.v`, `Functor/Structure/Cartesian.v`,
`Functor/Structure/Cartesian/Closed.v`, `Construction/Enriched/Two.v`
(for the enriched-versus-ordinary bridge, if it is worth proving).

## Definition of Done

- [ ] Functors between thin categories are proved to be exactly monotone maps.
- [ ] The subsingleton property of `[Proset P, Proset Q]` hom-setoids and the
      "exists iff pointwise ≤" criterion are proved, matching Awodey §7.7
      Example 7.19 (printed p. 174).
- [ ] `TerminalFunctor`, `CartesianFunctor` and `ClosedFunctor` instances are
      proved for the inclusion `Pos ⟶ Cat`, matching Proposition 7.20 (printed
      p. 175).
- [ ] All morphism equations use `≈`; the thinness argument goes through the
      hom-setoid, never through `=` on morphisms.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for the thin-functor-category results and
      the three structured-functor instances.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if this becomes the canonical
      "structure preservation into Cat" statement.

## Verification

```bash
coqc -R . Category Instance/Pos/Cat.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Pos.Cat.
Print Assumptions thin_functor_monotone.
Print Assumptions thin_fun_thin.
Print Assumptions Pos_to_Cat_Closed.
```

Review item: the criterion for existence of a natural transformation between
monotone maps and the three preservation clauses match Awodey §7.7, printed
pp. 174–175.

## Dependencies

Depends on: #641 (Awodey 1.4: Pos, the category of posets and monotone maps)
Depends on: #680 (Awodey 6.2: Pos is cartesian closed — the componentwise
product and the pointwise-ordered monotone function space)
Depends on: `awodey:7.1:example2` — the full and faithful inclusion `Pos ⟶ Cat`

<!-- catalog: {"ids":["awodey:7.7:example19","awodey:7.7:prop20"],"deps":["#641","#680","awodey:7.1:example2"]} -->

---8<---

```yaml
title: "Awodey 7.7: The category Grpd of groupoids is cartesian closed and its inclusion into Cat preserves the structure"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.7:prop22]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.7, Proposition 7.22, printed page 175,
PDF page 184. Item covered: `awodey:7.7:prop22`.

## Background

[Grpd](https://ncatlab.org/nlab/show/Grpd), the category of
[groupoids](https://ncatlab.org/nlab/show/groupoid) and functors between them,
is cartesian closed, with the exponential given by the functor category: if `G`
and `H` are groupoids then every natural transformation between functors
`G → H` is invertible componentwise, so `H^G` is a groupoid again. The
inclusion into `Cat` therefore preserves the cartesian closed structure on the
nose. Awodey leaves the detailed proof as an exercise.

## Current state in the library

No category of groupoids exists: `rg -n '\bGrpd\b'` yields exactly one hit, the
prose line `Construction/Groupoid.v:23`, and that file's closing paragraph
concedes the point ("no standalone category of groupoids exists in-tree, so the
adjunction remark in the header above remains prose rather than a theorem").

What exists is one construction that *produces* a groupoid:
`Construction/Groupoid.v:103`,
`Program Definition Groupoid (C : Category) : Category := {| obj := @obj C; hom := @Isomorphism C; homset := @iso_setoid C; id := @iso_id C; compose := @iso_compose C |}`
— the core of `C`. There is no predicate expressing that every arrow of a given
category is invertible (see the groupoid-definition issue under Dependencies),
so "`H^G` is a groupoid" is not currently statable, and nothing in the tree
proves that a functor category into a groupoid is a groupoid.

The preservation vocabulary is available and should be reused:
`Functor/Structure/Cartesian.v:49` `Class CartesianFunctor` and
`Functor/Structure/Cartesian/Closed.v:49` `Class ClosedFunctor`, together with
`Instance/Cat/Cartesian.v:39`, `Instance/One.v:54` and
`Instance/Cat/Cartesian/Closed.v:47` (`Cat_Closed`, `exponent_obj := @Fun`).

## Work to be done

Suggested modules: `Instance/Grpd.v` (the category), `Instance/Grpd/Closed.v`
(the cartesian closed structure and the preservation result).

1. Define `Grpd` as the full subcategory of `Cat` cut out by the groupoid
   predicate (use `Construction/Subcategory.v`, whose `Full` at `:69` and
   `Full_Implies_Full_Functor` at `:74` give the inclusion for free).
2. Prove the key lemma: if `D` is a groupoid then `[C, D]` is a groupoid, i.e.
   every natural transformation with invertible components is invertible — this
   is `Instance/Fun.v:255`'s
   `Theorem Functor_Setoid_Nat_Iso : F ≅[Fun] G ↔ F ≈ G` read in the direction
   that constructs the inverse transformation, combined with `iso_sym`
   (`Theory/Isomorphism.v`).
3. Prove `Grpd` has a terminal object and binary products (computed as in
   `Cat`), and that `H^G := [G, H]` is the exponential in `Grpd`.
4. Prove `TerminalFunctor`, `CartesianFunctor` and `ClosedFunctor` for the
   inclusion `Grpd ⟶ Cat`.
5. Optionally record the companion fact that `Construction/Groupoid.v:103`'s
   core construction lands in `Grpd` and is right adjoint to the inclusion,
   which the file header currently states only as prose.

In-tree donors: `Construction/Groupoid.v`, `Construction/Subcategory.v`,
`Instance/Fun.v`, `Instance/Cat/Cartesian.v`,
`Instance/Cat/Cartesian/Closed.v`, `Theory/Isomorphism.v`,
`Functor/Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] `Grpd` is defined as a category, with the inclusion into `Cat` proved
      full and faithful.
- [ ] "A functor category into a groupoid is a groupoid" is proved.
- [ ] `Grpd` is proved cartesian closed, with the exponential the functor
      category, matching Awodey Proposition 7.22 (printed p. 175).
- [ ] `TerminalFunctor`, `CartesianFunctor` and `ClosedFunctor` instances for
      the inclusion are proved.
- [ ] All morphism equations use `≈`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for `Grpd`, the closure instance and the
      three structured-functor instances; closed under the global context as
      required for `Construction/`-level results by docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated, and the prose disclaimer at
      `Construction/Groupoid.v:23` (and the file's closing paragraph) corrected
      once `Grpd` exists.

## Verification

```bash
coqc -R . Category Instance/Grpd.v
coqc -R . Category Instance/Grpd/Closed.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Grpd.Closed.
Print Assumptions Fun_Groupoid.
Print Assumptions Grpd_Closed.
Print Assumptions Grpd_to_Cat_ClosedFunctor.
```

Review item: the exponential clause and the preservation claim match Awodey
Proposition 7.22, printed p. 175.

## Dependencies

Depends on: #248 (MacLane I.5: Groupoids and the structure of connected
groupoids) — which must first supply the groupoid *predicate* ("every arrow is
an isomorphism"); without it `Grpd` cannot be cut out, since the in-tree name
`Groupoid` is bound to the core construction at `Construction/Groupoid.v:103`

<!-- catalog: {"ids":["awodey:7.7:prop22"],"deps":["#248"]} -->

---8<---

```yaml
title: "Awodey 7.9: The category of partial maps is equivalent to the category of pointed sets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.9:prop27]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.9, Example 7.26 and Proposition 7.27,
printed page 181, PDF pages 190–191. Item covered: `awodey:7.9:prop27`.

## Background

Adjoining a fresh point turns a set into a
[pointed set](https://ncatlab.org/nlab/show/pointed+set) and a
[partial function](https://ncatlab.org/nlab/show/partial+function) into a
total point-preserving one; discarding the base point goes back. The two
constructions are mutually pseudo-inverse but not inverse — one round trip is
the identity, the other only naturally isomorphic — which is exactly why the
comparison is an equivalence of categories rather than an isomorphism.

## Current state in the library

The source category exists twice over; the target does not, and the comparison
is absent.

- `Instance/Sets/Par.v:27` defines
  `Program Definition Part : Category := {| obj := Sets; hom := fun x y => SetoidMorphism x (option y); ... |}`
  and `Instance/Coq/Par.v:53` defines the `Type`-level
  `Program Definition Par : Category := {| obj := Type; hom := fun A B => A ~> option B; id := λ _, Some; compose := ... option ... |}`.
  Both use the Kleisli-of-`option` encoding rather than the subset-domain
  presentation, and both discharge the category laws.
- The category of pointed sets is never constructed. `Construction/Slice.v:169`
  defines `Coslice `(C : Category) `(c : C) : Category`, and the file's header
  essay says in prose (line 82) that "pointed sets are the coslice of Set under
  the one-point set" — but no such instantiation exists anywhere in the tree.
  `rg -in 'Pointed'` finds only `Instance/Fun.v:230`/`:240` (pointed and
  well-pointed *endofunctors*) plus header prose.
- No comparison functor, no natural isomorphism, no `EquivalenceOfCategories`
  instance involving `Par`. `rg -n 'CategoryEquivalence'` finds only the generic
  apparatus in `Theory/Equivalence/Bundled.v` plus prose.

## Work to be done

Suggested module: `Instance/Sets/Par/Equivalence.v` (with `Sets_*` itself in
`Instance/Sets/Pointed.v` if the coslice instantiation is not delivered by the
pointed-sets issue under Dependencies).

1. Construct `Sets_*` — either directly (a setoid with a chosen point;
   morphisms the point-preserving setoid maps) or as
   `Coslice Sets 1` via `Construction/Slice.v:169`, and prove the two agree if
   both are wanted.
2. Define `F : Par ⟶ Sets_*` on objects by `A ↦ (A + 1, ⋆)` and on a partial
   map `f` by the total map that sends the undefined part to `⋆`, and prove
   functoriality (`≈`-respecting, identity, composition).
3. Define `G : Sets_* ⟶ Par` on objects by `(A, a) ↦ A ∖ {a}` (constructively:
   the sub-setoid of elements not `≈`-equal to the base point — state clearly
   what decidability, if any, this needs, and if it needs any, restrict the
   construction or carry the hypothesis explicitly) and on arrows by the
   partial map defined where `f(x) ≉ b`; prove functoriality.
4. Prove `F ∘ G ≈ Id` on `Par` and construct the natural isomorphism
   `G ∘ F ≅ Id` on `Sets_*` with components
   `(A, a) ≅ ((A ∖ {a}) + 1, ⋆)`; prove naturality.
5. Assemble `EquivalenceOfCategories F` (`Theory/Equivalence.v:151`) and record
   in the header why this is not an isomorphism of categories.
6. Secondary (from Example 7.26): connect the `option`-encoding of `Par` to the
   book's subset-domain presentation by exhibiting the composite's domain as
   the pullback of the inclusion `U_g ↪ B` along `|f|`, using
   `Structure/Pullback.v`; the tree currently has no lemma linking
   `Instance/Sets/Par.v` to pullbacks.

In-tree donors: `Instance/Sets/Par.v`, `Instance/Coq/Par.v`,
`Construction/Slice.v` (`Coslice`), `Theory/Equivalence.v`,
`Theory/Equivalence/FullFaithful.v`, `Structure/Pullback.v`,
`Theory/Coq/Maybe.v`.

## Definition of Done

- [ ] `Sets_*` is constructed (or obtained from the coslice) with its category
      laws proved.
- [ ] `F` and `G` are defined with proved functoriality.
- [ ] One round trip is proved equal to the identity and the other is proved
      naturally isomorphic to it, matching Awodey Proposition 7.27 (printed
      p. 181).
- [ ] An `EquivalenceOfCategories` instance is produced, and the header states
      why an isomorphism of categories is unavailable.
- [ ] Any decidability or choice hypothesis needed for `A ∖ {a}` is stated
      explicitly as a hypothesis, never a global `Axiom`.
- [ ] All morphism equations use `≈`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for `F`, `G`, the natural isomorphism and
      the equivalence; reconciled against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated, and docs/INHABITATION.md if the
      equivalence carries a hypothesis with no in-tree witness.

## Verification

```bash
coqc -R . Category Instance/Sets/Pointed.v
coqc -R . Category Instance/Sets/Par/Equivalence.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Sets.Par.Equivalence.
Print Assumptions Par_to_Pointed.
Print Assumptions Pointed_to_Par.
Print Assumptions Par_Pointed_Equivalence.
```

Review item: the two functors, the asymmetry of the round trips, and the
conclusion match Awodey §7.9, printed p. 181.

## Dependencies

Depends on: #261 (MacLane I.7: Set_*, the category of pointed sets)
Depends on: #678 (Awodey 5.7 Ex 4: The category of partial maps Par(C) over a
category with pullbacks) — the subset-domain/pullback presentation of `Par`

<!-- catalog: {"ids":["awodey:7.9:prop27"],"deps":["#261","#678"]} -->

---8<---

```yaml
title: "Awodey 7.9: The equivalence Sets^I ≃ Sets/I and reindexing as pullback"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:7.9:example28, awodey:7:ex13]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.9, Example 7.28, printed page 182, PDF
pages 191–192; §7.10 Exercise 13, printed page 188, PDF pages 197–198. Items
covered: `awodey:7.9:example28`, `awodey:7:ex13`.

## Background

For a set `I` regarded as a discrete category, the functor category `Sets^I` is
the category of `I`-indexed families, and it is equivalent — not isomorphic — to
the [slice category](https://ncatlab.org/nlab/show/slice+category) `Sets/I`, via
the total-space/indexing-projection functor one way and the fibre functor the
other. Exercise 13 adds that reindexing along `f : J → I` corresponds, under
this equivalence, to [base change](https://ncatlab.org/nlab/show/base+change),
i.e. to the pullback functor `f^*` — the square of categories commuting up to
natural isomorphism.

## Current state in the library

The two categories exist; the comparison does not.

- `Construction/Slice.v:123` defines
  `Program Definition Slice `(C : Category) `(c : C) : Category := {| obj := ∃ a : C, a ~> c; hom := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x; ... |}`,
  and `Instance/Discrete.v:37` plus `Instance/Fun.v:108` (`Fun`, with the
  `[C, D]` notation) give the functor-category side.
- `Construction/Slice/Pullback.v:67` defines
  `Star_Functor `(f : c ~> a) : @Slice C a ⟶ @Slice C c` under
  `Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g`
  — the `f^*` leg, stated more generally than the book asks (any `C` with the
  assumed pullbacks).
- Missing: neither comparison functor exists. There is no
  coproduct-of-an-`I`-indexed-family construction with its indexing projection
  (Φ) and no fibre functor `α ↦ (α^{-1}{i})_i` (Ψ), hence no unit/counit
  natural isomorphisms and no `EquivalenceOfCategories` instance. The claim
  appears only as header prose at `Construction/Slice.v:73-77` ("an object of
  Set/I is the same data as an I-indexed family of sets … an equivalence
  Set/I ≃ Set^I").
- Missing: the Exercise 13 square. There is no reindexing functor
  `Sets^f : Sets^I ⟶ Sets^J` (precomposition with `f` viewed as a functor of
  discrete categories) and no comparison of it with `Star_Functor` up to
  natural isomorphism; the accompanying `Σ_f ⊣ f^*` adjunction is a commented
  stub, not a theorem.

## Work to be done

Suggested module: `Instance/Sets/Indexed.v`.

1. Define `Φ : [DiscreteCat I, Sets] ⟶ Slice Sets I` sending a family to the
   coproduct of its members together with the indexing projection, and on
   arrows to the induced map over `I`. This needs `I`-indexed coproducts in
   `Sets`; if the tree lacks them, build them here (a setoid of dependent pairs)
   and say so in the header.
2. Define `Ψ : Slice Sets I ⟶ [DiscreteCat I, Sets]` sending `α : A → I` to the
   fibre family `(α^{-1}{i})_i` (as sub-setoids), and on arrows to the induced
   family of restrictions.
3. Prove the two natural isomorphisms `Ψ ∘ Φ ≅ Id` and `Φ ∘ Ψ ≅ Id` — completing
   the proof Awodey leaves as an exercise — and assemble
   `EquivalenceOfCategories Φ` (`Theory/Equivalence.v:151`). Record why they are
   pseudo-inverse but not inverse.
4. Define reindexing `Sets^f : [DiscreteCat I, Sets] ⟶ [DiscreteCat J, Sets]` as
   precomposition with the discrete functor induced by `f : J → I`.
5. Prove the Exercise 13 square commutes up to natural isomorphism:
   `Φ_J ∘ Sets^f ≅ Star_Functor f ∘ Φ_I`, reusing
   `Construction/Slice/Pullback.v:67` for `f^*` (instantiating its `pullbacks`
   hypothesis at `Sets`, or at `FinSet` where `FinSet_Pullbacks` already exists
   at `Instance/FinSet/Classifier.v:264`).

In-tree donors: `Construction/Slice.v`, `Construction/Slice/Pullback.v`,
`Instance/Discrete.v`, `Instance/Fun.v`, `Instance/Sets.v`,
`Structure/Pullback.v`, `Theory/Equivalence.v`,
`Structure/Limit/Product.v` (`iprod`, for indexed (co)products in the
diagram-shaped presentation).

## Definition of Done

- [ ] Φ and Ψ are defined with proved functoriality.
- [ ] Both natural isomorphisms are proved and assembled into an
      `EquivalenceOfCategories`, matching Awodey Example 7.28 (printed p. 182)
      and completing Exercise 13's first half (printed p. 188).
- [ ] The reindexing functor is defined and the pullback square is proved to
      commute up to natural isomorphism (Exercise 13's second half).
- [ ] The header states which side supplies the pullbacks hypothesis and
      whether the result is stated at `Sets`, at `FinSet`, or generically.
- [ ] All morphism equations use `≈`; fibres are sub-setoids, never subsets by
      `=`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for Φ, Ψ, the equivalence and the square;
      reconciled against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated, and the prose claim at
      `Construction/Slice.v:73-77` upgraded to a cross-reference to the proved
      theorem.

## Verification

```bash
coqc -R . Category Instance/Sets/Indexed.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Sets.Indexed.
Print Assumptions Family_to_Slice.
Print Assumptions Slice_to_Family.
Print Assumptions Indexed_Slice_Equivalence.
Print Assumptions reindex_is_pullback.
```

Review item: Φ, Ψ and the reindexing square match Awodey §7.9 Example 7.28
(printed p. 182) and §7.10 Exercise 13 (printed p. 188).

## Dependencies

Depends on: #673 (Awodey 5.3/5.5: Slices of Sets as indexed families —
reindexing as pullback, and its preservation of coproducts) — the object-level
correspondence and the reindexing-as-pullback statement, which this issue
upgrades to an equivalence of categories and a commuting square of functors

<!-- catalog: {"ids":["awodey:7.9:example28","awodey:7:ex13"],"deps":["#673"]} -->

---8<---

```yaml
title: "Awodey 7.10 Ex 3: The forgetful functors Grp ⟶ Mon ⟶ Sets — fullness, faithfulness and (non-)surjectivity"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:7:ex3]
deps_item_ids: [awodey:7.1:def1]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.10 Exercise 3, printed page 186, PDF
page 195. Item covered: `awodey:7:ex3`.

## Background

The exercise asks for twelve determinations: for each of the two standard
[forgetful functors](https://ncatlab.org/nlab/show/forgetful+functor)
`U : Grp ⟶ Mon` and `V : Mon ⟶ Sets`, decide faithfulness, fullness,
injectivity and surjectivity on arrows, and injectivity and surjectivity on
objects. The mathematically interesting answers are that `U` is
[full](https://ncatlab.org/nlab/show/full+and+faithful+functor) — a monoid
homomorphism between groups automatically preserves inverses — while `V` is
faithful but not full.

## Current state in the library

Exactly one of the twelve determinations exists.

- `Theory/Algebra/Monoid/Hom.v:83` builds
  `Program Definition Mon : Category := {| obj := { x : C & Monoid x }; hom := fun X Y => { f : `1 X ~> `1 Y & MonoidHom `2 X `2 Y f }; ... |}`
  — internal monoids in a monoidal `C` — with `Mon_Forget : Mon ⟶ C` at `:93`
  and `#[export] Instance Mon_Forget_Faithful : Faithful Mon_Forget` at `:101`.
  That is the single settled answer, and it is settled in greater generality
  than the exercise asks (any monoidal `C`, not just `Sets`).
- There is no category of groups. `Structure/Group.v:109` gives
  `Class GroupObject` (with a coercion `GroupObject >-> MonoidObject`, which is
  `U` on objects only) but no `Grp` and no functor `Grp ⟶ Mon`, so none of
  `U`'s six properties is stated — in particular not the fullness answer.
- Four of the six properties have no vocabulary: `Theory/Functor.v:331` defines
  `Full` and `:342` `Faithful`; `Theory/Equivalence.v:141` defines
  `EssentiallySurjective`; `Lib/Setoid.v:117`/`:121` define `injective` and
  `surjective` for setoid *functions*, not for functors. There is no predicate
  for a functor being injective or surjective on objects or on arrows.
- The library never proves any functor *not* full, so the negative answers have
  no precedent to copy.

## Work to be done

Suggested module: `Instance/Grp/Forget.v`.

1. Consume the object/arrow injectivity and surjectivity predicates from the
   functor-properties issue listed under Dependencies; do not redefine them.
2. Define `U : Grp ⟶ Mon` and `V : Mon ⟶ Sets` (the categories themselves come
   from the issues under Dependencies).
3. Prove the positive answers: `U` full (a monoid homomorphism between groups
   preserves inverses — the group inverse is determined by the monoid
   structure), `U` faithful, `V` faithful.
4. Prove the negative answers as genuine refutations, each with an explicit
   witness: `V` not full (a non-homomorphic function between the underlying
   sets of two monoids), `V` not surjective on objects, `V` not surjective on
   arrows, and the injectivity answers for both functors on objects and on
   arrows. Small concrete monoids and groups suffice; keep the witnesses
   computable where possible so the refutations are checked by `eq_refl`-style
   evaluation rather than by classical reasoning.
5. Tabulate all twelve answers in the file header so a reader can check the
   exercise at a glance.

In-tree donors: `Theory/Algebra/Monoid/Hom.v` (`Mon`, `Mon_Forget`,
`Mon_Forget_Faithful`), `Structure/Group.v` (`GroupObject` and the coercion to
`MonoidObject`), `Theory/Functor.v` (`Full`, `Faithful`), `Instance/CMon.v`
(a worked category of algebraic structures over setoids to copy).

## Definition of Done

- [ ] All twelve determinations of Awodey §7.10 Exercise 3 (printed p. 186) are
      settled, each as a proved statement (positive) or a proved refutation
      (negative) with an explicit witness — none left as prose.
- [ ] `U : Grp ⟶ Mon` is proved full, with the inverse-preservation argument
      spelled out.
- [ ] All morphism-level equations use `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for each of the twelve results; the
      refutations must not silently depend on classical axioms — if one does,
      it is stated as a hypothesis and recorded against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated only if `Instance/Grp/` becomes a
      documented development.

## Verification

```bash
coqc -R . Category Instance/Grp/Forget.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Grp.Forget.
Print Assumptions Grp_Forget_Full.
Print Assumptions Mon_Forget_not_Full.
Print Assumptions Mon_Forget_not_SurjectiveOnObjects.
```

Review item: the twelve answers match Awodey §7.10 Exercise 3, printed p. 186.

## Dependencies

Depends on: #255 (MacLane I.6: Grp, the category of groups)
Depends on: #503 (MacLane VII.3: Finite products in the category of monoids) —
for a category of monoids over `Sets`
Depends on: `awodey:7.1:def1` — the injectivity/surjectivity-on-objects-and-
arrows vocabulary, without which eight of the twelve answers are unstatable

<!-- catalog: {"ids":["awodey:7:ex3"],"deps":["#255","#503","awodey:7.1:def1"]} -->

---8<---

```yaml
title: "Awodey 7.10 Ex 4: The Alexandroff topology as a functor Pos ⟶ Top"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:7:ex4]
deps_item_ids: [awodey:7.1:def1]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.10 Exercise 4 (starred), printed page
187, PDF page 196. Item covered: `awodey:7:ex4`.

## Background

Declaring the upward-closed subsets of a poset to be the open sets gives the
Alexandroff (specialization) topology — see the nLab's
[specialization topology](https://ncatlab.org/nlab/show/specialization+topology)
and Wikipedia's
[Alexandrov topology](https://en.wikipedia.org/wiki/Alexandrov_topology). Every
monotone map is then continuous, so the assignment is a functor from posets to
spaces; the exercise asks whether it is faithful and whether it is full, and how
the answers change if the downward-closed subsets are taken as the opens
instead.

## Current state in the library

Absent, and both endpoints are missing.

- There is no category of topological spaces: `rg -n 'continuous|OpenSet|Topology|TopSpace'`
  over `*.v` finds only "continuous functor" (limit-preserving) prose in
  `Adjunction/GAFT.v`, `Theory/Adjunction.v:446` and
  `Structure/Factorization.v:79`; `rg -in 'Instance Top\b|Definition Top\b'`
  finds nothing.
- There is no category `Pos` (`Instance/Poset.v:116` and `Instance/Proset.v:33`
  turn a *single* order into a thin category; `Instance/Poset.v:22` mentions
  `Pos` only in prose), and no notion of a monotone map outside
  `Construction/Enriched/Two.v:175`'s `MonotoneMap`, which lives in the enriched
  framework.
- `rg -il 'alexandroff'` returns zero hits; `rg -il 'topolog'` returns roughly
  23 files and every hit is a header essay or citation (Grothendieck topologies
  in `Theory/Sheaf.v`, Lawvere–Tierney in `Structure/Topos.v`, TQFT
  citations).

## Work to be done

Suggested module: `Instance/Top/Alexandroff.v`, on top of a category `Top`
supplied by the topological-spaces issue under Dependencies.

1. Define the Alexandroff topology on a poset: opens are the upward-closed
   subsets (as `≈`-closed predicates, closed under arbitrary unions and
   intersections — note this topology is closed under *arbitrary*
   intersections, which is the defining Alexandroff property and worth stating).
2. Prove that a monotone map is continuous for these topologies, i.e. the
   inverse image of an upward-closed set is upward-closed.
3. Package the assignment as a functor `A : Pos ⟶ Top` and discharge the
   functor laws.
4. Prove `A` is faithful, and settle fullness: exhibit either a `Full` instance
   (with the chosen `prefmap` recovering a monotone map from a continuous one
   via the specialization order) or an explicit counterexample, per the
   exercise's "decide whether" phrasing.
5. Do the downward-closed variant and state the relationship between the two
   (one is the other precomposed with the order-reversal functor
   `Pos ⟶ Pos`), which is the exercise's closing discussion.

In-tree donors: `Instance/Poset.v`, `Instance/Proset.v`, `Theory/Functor.v`
(`Full`, `Faithful`), `Construction/Opposite.v` (for the order-reversal
functor), and the object/arrow surjectivity vocabulary from the
functor-properties issue.

## Definition of Done

- [ ] The Alexandroff topology is defined and proved a topology (including
      closure under arbitrary intersections).
- [ ] Continuity of monotone maps is proved, and `A : Pos ⟶ Top` is a functor
      with proved laws, matching Awodey §7.10 Exercise 4 (printed p. 187).
- [ ] Faithfulness is proved and fullness is settled either way, with a proof
      or an explicit counterexample.
- [ ] The downward-closed variant and its relation to the upward-closed one are
      stated and proved.
- [ ] All morphism equations use `≈`; opens are `≈`-closed predicates, never
      raw subsets by `=`.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` reported for the functor and the faithful/full
      results; any classical principle used for the counterexample is a
      hypothesis, recorded against docs/AXIOMS.md.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if this becomes part of a documented
      `Top` development.

## Verification

```bash
coqc -R . Category Instance/Top/Alexandroff.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Instance.Top.Alexandroff.
Print Assumptions Alexandroff.
Print Assumptions Alexandroff_Faithful.
Print Assumptions Alexandroff_Full_or_counterexample.
```

Review item: the topology, the continuity claim and the faithful/full verdicts
match Awodey §7.10 Exercise 4, printed p. 187.

## Dependencies

Depends on: #259 (MacLane I.7: Top, the category of topological spaces)
Depends on: #641 (Awodey 1.4: Pos, the category of posets and monotone maps)
Depends on: `awodey:7.1:def1` — the functor-property vocabulary used to phrase
the faithful/full verdicts uniformly

<!-- catalog: {"ids":["awodey:7:ex4"],"deps":["#259","#641","awodey:7.1:def1"]} -->

---8<---

```yaml
title: "Awodey 7.10 Ex 5: The full-image factorization of a functor, and its comparison with the bijective-on-objects factorization"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:7:ex5]
deps_item_ids: [awodey:7.1:def1]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd ed.), §7.10 Exercise 5 (starred), printed page
187, PDF page 196. Item covered: `awodey:7:ex5`.

## Background

Exercise 5 asks for two factorizations of an arbitrary functor: one through a
category on the same objects (the
[(bo, ff) factorization system](https://ncatlab.org/nlab/show/bo-ff+factorization+system)
variant with a full first factor and a faithful second), and one through the
[essential image](https://ncatlab.org/nlab/show/essential+image)-style
construction whose first factor is surjective on objects and whose second is
injective on objects, full and faithful. The final part asks when the two
agree.

## Current state in the library

Absent. `rg -in 'bijective on objects|surjective on objects|injective on objects'`
finds seven hits, all prose about one specific functor
(`Construction/Funny/Comparison.v:24`/`:62`,
`Structure/Premonoidal/Freyd.v:181`/`:369`,
`Construction/Cospan/Corelation.v:286`,
`Construction/Grothendieck/RoundTrip.v:55`), and
`rg -in 'essential image|full image|image of a functor'` finds nothing (the
"image" hits — `Structure/Abelian.v:260`, `Instance/Sets/Image.v:74` — are all
morphism-level).

The generic factorization machinery exists and should be reused rather than
re-invented: `Structure/Factorization.v:125` `Record Factorization`,
`Theory/Orthogonality.v` (orthogonal lifting `e ⫫ m`),
`Theory/Morphisms/Classes.v` (`MorphismClass`), together with the uniqueness-up-
to-unique-iso results in `Structure/Factorization.v`. What is missing is any
factorization of *functors* in `Cat`, and the object-level predicates needed to
state the two classes.

The intermediate category of factorization (b) is naturally built with
`Construction/Subcategory.v` — `Record Subcategory` at `:31`, `Sub` at `:50`,
`Incl` at `:59`, plus `Full` at `:69` and `Full_Implies_Full_Functor` at `:74`.

## Work to be done

Suggested module: `Construction/Functor/FullImage.v`.

1. Consume the object/arrow injectivity and surjectivity predicates from the
   functor-properties issue listed under Dependencies.
2. Build factorization (b): given `F : C ⟶ D`, let `E` be the full subcategory
   of `D` spanned by the objects in the image of `F` (via
   `Construction/Subcategory.v`), with `E : C ⟶ E` surjective on objects and
   `M : E ⟶ D` injective on objects, full and faithful; prove all four
   properties and `M ∘ E ≈ F`.
3. State factorization (a) — `E` bijective on objects and full, `M` faithful —
   as a corollary of the already-filed bijective-on-objects/faithful
   factorization (see Dependencies), adding only the fullness clause of the
   first factor.
4. Prove the comparison: characterize exactly when the two factorizations agree
   (they agree precisely when `F` is injective on objects and full on the
   relevant homs — state and prove the correct criterion; this is the "determine
   when" half of the exercise and must not be left as prose).
5. Optionally, phrase the two as orthogonal factorization systems on `Cat` using
   `Theory/Morphisms/Classes.v` and `Structure/Factorization.v`, if the lifting
   conditions can be discharged; otherwise say in the header why not.

**Library defect to fix in this issue** (surfaced by the Chapter 7 coverage
pass): `Construction/Subcategory.v` never states that the inclusion
`Incl : Sub ⟶ C` is faithful. The header remarks it at
`Construction/Subcategory.v:26-28` ("that inclusion is always faithful, since on
each hom-set it is the first projection out of a sigma type"), and the sole
proved instance is `Sheaves_Faithful` at `Theory/Sheaf/Category.v:103`, which
re-proves the generic one-liner ad hoc. Since factorization (b)'s `M` *is* such
an inclusion, prove the generic `#[export] Instance Incl_Faithful : Faithful Incl`
in `Construction/Subcategory.v` and re-route `Theory/Sheaf/Category.v:103` to it.
While there, consider adding the missing full-subcategory *constructor* (turning
a predicate on objects into a `Subcategory` with `scomp`/`sid` automatic), which
`Theory/Sheaf/Category.v:74` and `Theory/Lawvere/Model.v:68` each supply by hand.

In-tree donors: `Construction/Subcategory.v`, `Structure/Factorization.v`,
`Theory/Morphisms/Classes.v`, `Theory/Orthogonality.v`, `Instance/Cat.v`,
`Theory/Functor.v`.

## Definition of Done

- [ ] Factorization (b) is constructed and all four properties of its two legs
      are proved, with `M ∘ E ≈ F` as functors, matching Awodey §7.10
      Exercise 5 (printed p. 187).
- [ ] Factorization (a) is stated, with the fullness clause of its first factor
      proved on top of the already-filed bijective-on-objects/faithful
      factorization.
- [ ] The agreement criterion is stated and proved (not left as prose).
- [ ] `Faithful Incl` is proved generically in `Construction/Subcategory.v`,
      and `Theory/Sheaf/Category.v:103` is re-routed to the generic lemma
      instead of re-proving it. (Library defect, folded in here.)
- [ ] All morphism/functor equations use `≈`, never `=`; equality of functors
      is `Functor_Setoid` (`Theory/Functor.v:148`), not propositional equality.
- [ ] No `Admitted`, `admit`, or `Axiom`.
- [ ] `Print Assumptions` closed under the global context for the factorization
      artifacts and for `Incl_Faithful` (both live in
      `Construction/`, which docs/AXIOMS.md scopes as axiom-free).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the functor factorizations become a
      documented development.

## Verification

```bash
coqc -R . Category Construction/Subcategory.v
coqc -R . Category Construction/Functor/FullImage.v
coqc -R . Category Theory/Sheaf/Category.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```

```coq
Require Import Category.Construction.Subcategory.
Print Assumptions Incl_Faithful.
Require Import Category.Construction.Functor.FullImage.
Print Assumptions full_image_factorization.
Print Assumptions factorizations_agree_iff.
```

Review item: both factorizations and the agreement criterion match Awodey
§7.10 Exercise 5, printed p. 187.

## Dependencies

Depends on: #663 (Awodey 4.3: The homomorphism theorem for categories — kernel
congruence, kernel category, and the bijective-on-objects/faithful
factorization of a functor) — supplies factorization (a)'s backbone
Depends on: `awodey:7.1:def1` — the injectivity/surjectivity-on-objects
predicates in which both factorizations are stated

<!-- catalog: {"ids":["awodey:7:ex5"],"deps":["#663","awodey:7.1:def1"]} -->

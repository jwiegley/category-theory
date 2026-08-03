```yaml
title: "Riehl 4.1: Naturality of adjoint transposition as a bijection of commuting squares"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.1:lem3, riehl:4.1:exi]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition, author's recompiled copy — **not** Dover pagination), §4.1 "Adjoint functors": Lemma 4.1.3 with its display (4.1.4), and Exercise 4.1.i which asks for its proof. Printed pp. 133 and 138; PDF pp. 153 and 158. Items: `riehl:4.1:lem3`, `riehl:4.1:exi`.

Paraphrase: given functors `F : C ⟶ D`, `U : D ⟶ C` and a family of bijections `D(F c, d) ≅ C(c, U d)` that is *not* assumed natural, naturality of the family is *equivalent* to the assertion that a square in `D` built from `F h`, two transposes and `k` commutes if and only if the transposed square in `C` commutes.

## Background

An adjunction is usually presented as a hom-set bijection natural in both variables; Riehl's lemma repackages that naturality as a correspondence between commuting squares, which is the form used later to identify the two comma categories of an adjunction. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The *unpacked* naturality equations are in-tree as class fields, but the biconditional is not.

- `Theory/Adjunction.v:141` — `to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) : ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g` (Riehl's "the transpose of `f♯ ∘ F h` is `f♭ ∘ h`").
- `Theory/Adjunction.v:144` — `to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) : ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋` (the other variable), with the two `from_adj_nat_*` duals.
- `Theory/Adjunction.v:156` — `Build_Adjunction'` accepts an **arbitrary, not-assumed-natural** family of hom-setoid isomorphisms plus only the two to-side naturality conditions and derives the full `Adjunction` (the from-side conditions follow by monicity of the isomorphism). This is the closest in-tree approach to the exercise's "these bijections define an adjunction iff …", but it is a strictly weaker sufficiency statement, not the square biconditional.
- `Adjunction/Hom.v:72` — `Class Adjunction_Hom` states the bifunctor form (a natural isomorphism in `[D^op ∏ C, Sets]`), and `Adjunction/Hom.v:223` / `:259` (`Adjunction_Hom_to_Universal` / `Adjunction_Universal_to_Hom`) prove it interderivable with the two-condition form. This is the *naturality* half of the lemma as the library states it, and it is the right donor for the forward direction.

Gap: (a) nothing formulates the commuting-square correspondence of display (4.1.4) as a predicate; (b) nothing states the biconditional "square commutes in `D` ⟺ transposed square commutes in `C`" for a family not assumed natural; (c) the converse direction (square correspondence ⇒ naturality) is absent, so Exercise 4.1.i has no in-tree discharge.

Verifier sharpening, which the Phase-C text did not carry: the two biconditionals that *do* exist in `Theory/Adjunction.v` — `adj_univ` at `:196` (`f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g`) and `adj_univ_impl` at `:249` — are about the transposition bijection itself and must **not** be mistaken for this lemma. Separately, `Construction/Comma/Adjunction.v:904` `Adjunction_Comma : F ⊣ G ↔ @lawvere_equiv _ _ F G` does supply a converse, but `lawvere_equiv` (`Construction/Comma/Adjunction.v:83`) demands strictly more than a square-respecting bijection: besides the comma isomorphism it carries `projF`, `projG` (the isomorphism lies over `D ∏ C`) and the extra `whisker_equiv` coherence field `σ`. The morphism obligations of the two comparison functors (`Construction/Comma/Adjunction.v:840-845`, `:857-862`) are literally the square transport, which is why that file is the natural donor for the forward leg.

## Work to be done

Suggested module: extend `Theory/Adjunction.v`, or a new `Theory/Adjunction/Squares.v` imported by it (keep `Theory/Adjunction.v` free of new dependencies).

1. Define, for a family `adj : ∀ x y, @Isomorphism Sets {| carrier := F x ~> y |} {| carrier := x ~> U y |}` with no naturality assumed, the square predicate: for `h : c' ~> c`, `k : d ~> d'`, `f♯ : F c ~> d`, `g♯ : F c' ~> d'`, `SquareD := (k ∘ f♯ ≈ g♯ ∘ fmap[F] h)` and `SquareC := (fmap[U] k ∘ ⌊f♯⌋ ≈ ⌊g♯⌋ ∘ h)`.
2. Prove the forward leg: from the four `*_adj_nat_*` conditions, `SquareD ↔ SquareC`. Record the two-variable normal form `⌊k ∘ f ∘ fmap[F] h⌋ ≈ fmap[U] k ∘ ⌊f⌋ ∘ h` as a named lemma — it is the workhorse and is currently unavailable.
3. Prove the converse: from `∀ …, SquareD ↔ SquareC`, derive `to_adj_nat_l` and `to_adj_nat_r` (instantiate with `g♯ := k ∘ f♯ ∘ fmap[F] h` and use the identity square), then feed `Build_Adjunction'` (`Theory/Adjunction.v:156`) to obtain the full `Adjunction`. This is the content of Exercise 4.1.i and closes the biconditional.
4. State the packaged result as `adj_squares_iff_natural` and re-derive `Build_Adjunction'`-style smart constructor `Build_Adjunction_from_squares`.

In-tree donors: `Theory/Adjunction.v` (`⌊−⌋`/`⌈−⌉` notation, `Build_Adjunction'`), `Adjunction/Hom.v` (bifunctor form and its interderivability lemmas), `Construction/Comma/Adjunction.v:840-862` (the square transport already carried out inside the comma comparison).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Lemma 4.1.3 and Exercise 4.1.i, with `≈` used for every morphism equality (never `=`).
- [ ] The square predicate is stated for a family of hom-setoid bijections **not** assumed natural.
- [ ] Both directions of the biconditional are proved; the converse produces a full `Adjunction` for the *given* `F` and `U`.
- [ ] The two-variable normal form `⌊k ∘ f ∘ fmap[F] h⌋ ≈ fmap[U] k ∘ ⌊f⌋ ∘ h` is a named, reusable lemma.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reports "Closed under the global context" for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level.

## Verification

```sh
nix develop --command coqc -R . Category Theory/Adjunction/Squares.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Adjunction.Squares. Print Assumptions adj_squares_iff_natural." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: the square predicate matches Riehl's display (4.1.4) up to paraphrase; the converse direction is genuinely proved (not assumed via `lawvere_equiv`'s extra `projF`/`projG`/`σ` data); `Build_Adjunction'` is reused rather than duplicated.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:4.1:lem3","riehl:4.1:exi"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 4.1: Chains of adjoint functors between the ordinal categories"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.1:example14]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.1, Example 4.1.14; printed p. 137, PDF p. 157. Item: `riehl:4.1:example14`.

Paraphrase: for each `n ≥ 0` write `n+1` for the ordinal category freely generated by the linear quiver `0 → 1 → … → n`. For `0 ≤ i ≤ n` there is an injective functor `d^i : n ⟶ n+1` omitting the object `i` from its image, and for `0 ≤ i < n` a surjective functor `s^i : n+1 ⟶ n` for which `i` is the unique object with two preimages. These assemble into a chain of `2n+1` adjunctions `d^n ⊣ s^{n-1} ⊣ d^{n-1} ⊣ … ⊣ s^0 ⊣ d^0`, so arbitrarily long finite chains of adjoints exist.

## Background

These are the coface and codegeneracy maps of the simplex category; the alternating adjoint chain is the standard 2-categorical structure of `Δ` viewed as a locally posetal 2-category. See [nLab: simplex category](https://ncatlab.org/nlab/show/simplex+category), whose "Δ and Δ_a as 2-categories" section records exactly this string of adjunctions and notes that half the units and counits are identities.

## Current state in the library

Nothing of the family exists. The verifier's independent pass reproduced the Phase-C negative log:

- The only order-shaped categories in-tree are `Instance/One.v` (`_1`), `Instance/Two.v:134` (`_2`), and `Instance/Omega.v` (the ordinal `ω`, over a `Type`-valued `le_t`). There is no indexed family `n ↦ n` of finite ordinal categories.
- `Theory/Metacategory.v:413` `Definition Three : Category := FromArrows ThreeArrows` is an arrows-only metacategory demonstration with **no** functors relating it to `_2` or `_1`; it is not a usable third ordinal.
- Searches for `simplex`, `simplicial`, `ordinal`, `face map`, `degeneracy`, `adjoint chain`, `string of adjoint` return nothing at declaration level.
- The longest adjoint run anywhere in the library is a single composite (`Adjunction/Compose.v:173` `Adjunction_Compose`).

## Work to be done

Suggested module: `Instance/Ordinal.v` for the family and its functors, `Instance/Ordinal/Adjunctions.v` for the chain (or a single file if it stays small).

1. Define `Ord (n : nat) : Category` — the finite ordinal `{0 < … < n-1}` as a thin category. Reuse the `Type`-valued order idiom of `Instance/Omega.v` (`le_t`) rather than stdlib `le`, so elimination into `Type` stays available; `Instance/Proset.v:33` `Proset` is the generic donor if a `PreOrder` presentation is preferred.
2. Define the coface `d^i : Ord n ⟶ Ord (S n)` and codegeneracy `s^i : Ord (S n) ⟶ Ord n` on objects, with the monotonicity obligations discharged by decision on `i`.
3. Prove the adjunctions. In a thin category the hom-setoid identifies all proofs (as `Instance/Proset.v:33-43` does with `Setoid.equiv := fun _ _ => True`), so each adjunction reduces to the order biconditional and both triangle identities are vacuous; state that reduction once as a reusable lemma so all `2n+1` instances are one-liners.
4. Assemble the chain `d^n ⊣ s^{n-1} ⊣ … ⊣ s^0 ⊣ d^0`, indexed uniformly in `n`, and note which units/counits are identities.
5. Optional but cheap: state the simplicial identities that the cofaces and codegeneracies satisfy, so the family is usable by a later `Δ` development.

In-tree donors: `Instance/Omega.v` (`le_t` and its `Cochain` duality), `Instance/Proset.v`, `Adjunction/Compose.v` (for composing the chain), `Theory/Adjunction.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Example 4.1.14, with `≈` used for every morphism equality.
- [ ] The ordinal family `Ord n` is defined uniformly in `n`, not as a handful of hand-built small categories.
- [ ] `d^i` and `s^i` are functors, with monotonicity proved rather than assumed.
- [ ] The full `2n+1`-long adjoint chain is proved for every `n`, with the thin-category reduction factored out as a named lemma.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the ordinal family, the two functor families, and the chain.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Ordinal.v
nix develop --command coqc -R . Category Instance/Ordinal/Adjunctions.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Ordinal.Adjunctions. Print Assumptions ordinal_adjoint_chain." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20
```

Review items: the chain really is `2n+1` adjunctions long and alternates cofaces and codegeneracies as in §4.1; the ordinal category is freely generated by the linear quiver (thin, with a unique arrow `i ~> j` exactly when `i ≤ j`).

## Dependencies

Depends on: #224 (MacLane I.2: Finite ordinals as categories and the chain ω) — supplies the ordinal-category family this example indexes over.
Depends on: #225 (MacLane I.2: The simplicial category Delta) — the cofaces and codegeneracies are `Δ`'s generating maps; build them once.

<!-- catalog: {"ids":["riehl:4.1:example14"],"deps":["#224","#225"]} -->

---8<---

```yaml
title: "Riehl 4.1: The forgetful functors out of the category of fields admit no adjoints"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.1:example12]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.1, Example 4.1.12; printed p. 137, PDF p. 157. Item: `riehl:4.1:example12`.

Paraphrase: none of the structure-forgetting functors out of the category of fields — into rings, into abelian groups (additively or via the multiplicative group of units), or into sets — admits a left or a right adjoint. The obstruction given is characteristic: the target categories receive maps from the integers into fields of every characteristic, while there are no field homomorphisms between fields of differing characteristic, so no value for a hypothetical left adjoint can be chosen; a symmetric argument blocks the right adjoint.

## Background

This is the standard example that "forgetful functors have left adjoints" is a heuristic, not a theorem: the category of fields fails the solution-set condition badly enough that no adjoint exists on either side. See [nLab: field](https://ncatlab.org/nlab/show/field), whose "properties of the category of fields" discussion records the absence of most limits and colimits, and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Absent in every ingredient, confirmed by an independent verifier pass:

- There is no category of fields, rings, abelian groups or groups. `rg -nw 'Ring'` over `*.v` returns **0** hits; every occurrence of "field" is the record-field sense or bibliography prose. The complete instance roster (`ls Instance/*.v`) is Adj, Adjoints, AST, Cat, CMon, Comp, Cones, Coq, Discrete, Ens, Fact, FinSet, Fun, Lambda, Omega, One, Parallel, Poset, Props, Proset, Rel, Roof, Sets, Shapes, StrictCat, Two, Zero, ZX — the only algebraic instance is `Instance/CMon.v` (commutative monoids over setoids).
- `Structure/Group.v:109` `Class GroupObject (grp : C)` is a group *object* internal to a cartesian monoidal category, not the category `Grp`.
- Nothing about characteristic, field homomorphisms, or the prime subring exists.
- Decisively for the shape of the claim: the library proves **no** non-existence-of-adjoint result at all. The single near-hit, `Construction/ColouredPROP/LNL.v:53`, is prose noting that `Comon_Forget` has no in-tree right adjoint — an unrelated functor and not a proof of non-existence.

## Work to be done

Suggested modules: `Instance/Field.v` for the category, `Instance/Field/NoAdjoint.v` for the obstruction. The prerequisite algebraic categories should come from their own issues (see Dependencies), not be re-created here.

1. Define `Field` as a category of setoid-based fields and field homomorphisms (homomorphisms preserve `0`, `1`, `+`, `·` and are automatically injective). Follow the `Instance/CMon.v` pattern: a `Record` of carrier + operations + laws over a `Setoid`, with a hom record and a proof-irrelevant hom-setoid.
2. Define the characteristic as a function `Field → nat` (or a `Type`-valued predicate `HasChar k p`) and prove the two facts the argument needs: (i) a field homomorphism preserves characteristic; (ii) fields of every prime characteristic exist (`Z/p` for `p` prime, plus `Q` in characteristic 0) — enough witnesses to run the argument.
3. State the non-existence results as `¬ { F : Sets ⟶ Field & F ⊣ U }` and dually, for each of the four forgetful functors Riehl lists that the ambient categories support. The cleanest formulation is via `Theory/Universal/Arrow.v`: a left adjoint would supply a `UniversalArrow` at the relevant object, whose arrow into fields of two different characteristics cannot both factor.
4. If only `Sets` is available as a target (i.e. if `Ring`/`Ab` land in later issues), scope this issue to `U : Field ⟶ Sets` and record the other three clauses as follow-up checkboxes.

In-tree donors: `Instance/CMon.v` (the algebraic-category-over-setoids template, plus `CMon_Forget` at `:169`), `Theory/Universal/Arrow.v:127` (`UniversalArrow` as an initial object of `=(c) ↓ F`) for the obstruction, `Theory/Adjunction.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Example 4.1.12, with `≈` used for morphism equalities.
- [ ] `Field` is a genuine `Category` instance, with the hom-setoid respecting the field laws.
- [ ] Characteristic is defined and proved preserved by field homomorphisms.
- [ ] At least one non-existence theorem is proved (not assumed), for `U : Field ⟶ Sets` on both sides.
- [ ] Any clause deferred for want of `Ring` / `Ab` is recorded explicitly in the file header, not silently dropped.
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond the documented `Instance/` layer allowances of docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for the category and each non-existence theorem.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Field.v
nix develop --command coqc -R . Category Instance/Field/NoAdjoint.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Field.NoAdjoint. Print Assumptions field_forget_no_left_adjoint." | coqtop -R . Category'
nix develop --command make
```

Review items: the argument really is the characteristic obstruction of §4.1 (not a smallness dodge); the non-existence statement quantifies over *all* candidate adjoints, not just a chosen one.

## Dependencies

Depends on: #226 (MacLane I.2: The roster of standard large categories) — supplies the ambient algebraic categories the other three clauses forget into.
Depends on: #232 (MacLane I.3: The field of quotients as a functor) — the first place a category of fields is required.

<!-- catalog: {"ids":["riehl:4.1:example12"],"deps":["#226","#232"]} -->

---8<---

```yaml
title: "Riehl 4.1: Groupoids in Cat — the core and the category of fractions as adjoints to the inclusion"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.1:example15]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.1, Example 4.1.15; printed p. 137, PDF pp. 157–158. Item: `riehl:4.1:example15`.

Paraphrase: the inclusion of groupoids into categories admits both adjoints. The right adjoint sends a category to its maximal subgroupoid — because functors preserve isomorphisms, any functor out of a groupoid factors uniquely through it. The left adjoint formally inverts every morphism, producing the category of fractions, built as a quotient of the free category on the quiver of `C` glued to the quiver of `C^op`, modulo the two cancellation relations.

## Background

The core (maximal subgroupoid) is right adjoint to the inclusion `Grpd ↪ Cat`, and the localization at all morphisms is left adjoint to it — the two-sided universal property that makes `Grpd` both reflective and coreflective in `Cat`. See [nLab: core groupoid](https://ncatlab.org/nlab/show/core), which states and proves the right-adjoint half, and [nLab: calculus of fractions](https://ncatlab.org/nlab/show/calculus+of+fractions) for the construction of `C[W⁻¹]` by generators and relations.

## Current state in the library

Only the object-level right-adjoint construction exists, and the library says so itself.

- `Construction/Groupoid.v:103` — `Program Definition Groupoid (C : Category) : Category := {| obj := @obj C; hom := @Isomorphism C; homset := @iso_setoid C; id := @iso_id C; compose := @iso_compose C |}`. This is the core, as a map `Category → Category`.
- `Construction/Groupoid.v:93-95` discloses the shortfall verbatim: "The file constructs the core of a given C; no standalone category of groupoids exists in-tree, so the adjunction remark in the header above remains prose rather than a theorem." (The definitional header at `:22-24` does assert the adjunction flatly; `:93-95` retracts it — disclosed, not a defect.)

Missing: (1) a category `Grpd` of groupoids and the inclusion into `Cat`/`StrictCat`; (2) functoriality of `Groupoid` in `C`, i.e. a core functor `Cat ⟶ Grpd`; (3) the right-adjoint statement (unique factorization of a functor out of a groupoid through the core); (4) the **entire** left adjoint — no category of fractions, no zig-zag morphisms, no gluing of the quiver of `C` to that of `C^op`, no quotient by the two cancellation relations.

`Construction/Localization.v` is a *different* construction and must not be mistaken for this one: it is reflective orthogonal-subcategory localization, with `WLocal` at `:129`, the full subcategory `C_W` at `:164`, and `Theorem reflector_inverts_W` at `:241` sitting under `Context (R : Reflective (C_W W))` — it lands in the full subcategory of `W`-local objects rather than constructing `C[W⁻¹]` by generators and relations.

## Work to be done

Suggested modules: `Instance/Grpd.v` (the category of groupoids and the inclusion), `Construction/Groupoid/Core.v` (functoriality plus the right adjunction), `Construction/Fractions.v` (the left adjoint).

1. Define `Grpd` — either as a full subcategory of `StrictCat` cut out by "every morphism is an isomorphism" (donor: `Construction/Subcategory.v`, whose `Full` field at `:69` and `Full_Implies_Full_Functor` at `:74` give the fullness plumbing), or as a bundled record. Provide the inclusion `Incl : Grpd ⟶ Cat`.
2. Upgrade `Construction/Groupoid.v`'s object-level core to a functor `Core : Cat ⟶ Grpd`: a functor `F : C ⟶ D` carries isomorphisms to isomorphisms, so `fmap[Core] F` is `F` restricted to isos.
3. Prove `Incl ⊣ Core` by the universal property: for a groupoid `G`, every functor `G ⟶ C` factors uniquely through `Core C`. Route through `Theory/Universal/Arrow.v:214` `AdjunctionFromUniversalArrows` (the pattern `Construction/Free/Quiver.v:550` already uses for `FreeForgetfulAdjunction`), or build the hom-setoid isomorphism directly with `Build_Adjunction'`.
4. Build the category of fractions `C[C⁻¹]`: take the free category on the quiver of `C` disjointly glued to the quiver of `C^op` (donor: `Construction/Free/Quiver.v`, `QuiverCategory` at `:358`, `FreeCatFunctor` at `:546`), then quotient by the congruence generated by the composition relations of `C` and the two cancellation relations `f⁻¹ f = id`, `f f⁻¹ = id`. Donor for the quotient: `Construction/Quotient.v` (generic hom-congruence quotients).
5. Prove the resulting category is a groupoid and that `Fractions ⊣ Incl`, again through the universal property (a functor out of `C` inverting every morphism factors uniquely).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Example 4.1.15, with `≈` for morphism equality throughout.
- [ ] `Grpd` exists as a category with an inclusion functor into `Cat`/`StrictCat`.
- [ ] `Core : Cat ⟶ Grpd` is a functor, and `Incl ⊣ Core` is a proved `Adjunction`, replacing the retracted prose at `Construction/Groupoid.v:93-95` (update that header).
- [ ] The category of fractions is constructed by generators and relations and proved to be a groupoid.
- [ ] `Fractions ⊣ Incl` is proved, so the adjoint triple `Fractions ⊣ Incl ⊣ Core` is exhibited.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for `Core`, both adjunctions, and the fractions construction.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is flagship-level.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Grpd.v
nix develop --command coqc -R . Category Construction/Groupoid/Core.v
nix develop --command coqc -R . Category Construction/Fractions.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Fractions. Print Assumptions Fractions_Incl_Adjunction." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_19
```

Review items: the core adjunction is stated for the *category* `Grpd`, not just as a per-object factorization; the fractions construction inverts **all** morphisms (not a chosen class), matching §4.1 rather than `Construction/Localization.v`'s orthogonality-based localization.

## Dependencies
- Depends on: #707 — its **Work item 1** defines `Grpd` as the full subcategory of `Cat` cut out by the groupoid predicate, in the same `Instance/Grpd.v` this issue targets. Only that definition is the prerequisite here; this issue does **not** need #707's cartesian-closure result. Whichever lands first creates the file and the other extends it.

Depends on: #907 (Riehl 1.1: The maximal subgroupoid of a category as a wide subcategory) — the core as a subcategory; this issue makes it functorial and adjoint.
Depends on: #248 (MacLane I.5: Groupoids and the structure of connected groupoids) — the groupoid vocabulary the category `Grpd` is built over.
Depends on: #299 (MacLane II.8: The least congruence and presented categories) — the quotient-by-relations machinery the category of fractions needs.

<!-- catalog: {"ids":["riehl:4.1:example15"],"deps":["#707","#907","#248","#299"]} -->

---8<---

```yaml
title: "Riehl 4.3: Uniqueness of adjoints up to a unique compatible natural isomorphism"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.3:prop1]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.3, Proposition 4.3.1; printed p. 144, PDF pp. 164–165. Item: `riehl:4.3:prop1`.

Paraphrase: if `F` and `F'` are both left adjoint to the same `G`, then they are naturally isomorphic, and moreover there is a **unique** natural isomorphism `θ : F ⇒ F'` compatible with the two adjunctions — i.e. making `(G θ) ∘ η ≈ η'` and `ε' ∘ (θ G) ≈ ε` commute. Riehl gives two proofs, one "syntactic" (define `θ` as the transpose of the other unit and check the triangles) and one via Yoneda.

## Background

Uniqueness up to natural isomorphism is the standard consequence of representability; the sharpening Riehl adds is that the comparison isomorphism is itself *unique* subject to compatibility with units and counits, which is what makes "the" left adjoint well defined as structure and not merely as a property. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor), whose "In terms of representable functors" section records the uniqueness proposition.

## Current state in the library

Three fragments exist; none is the proposition.

- `Theory/Adjunction.v:404` — `Theorem left_adjoint_iso `(G : D ⟶ C) (F F' : C ⟶ D) : F ⊣ G → F' ⊣ G → F ≈ F'`, with the dual `right_adjoint_iso` at `:364`. Here `≈` on functors is `Functor_Setoid` (`Theory/Functor.v:148`), which *is* a natural isomorphism, so the bare conclusion is faithful — but nothing says the isomorphism commutes with the units and counits, and nothing says it is unique.
- `Theory/Bicategory/Adjunction.v:708` — `Theorem adjoint_unique {a b : bicat y x} (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) : a ≅[bicat y x] b`, built from `matecell Aa Ab` / `matecell Ab Aa`; with `mate_unit_compat` at `:636` (the comparison 2-cell commutes with the two units) and `mate_charac` at `:347` (any unit-compatible 2-cell equals the mate — the uniqueness clause).
- That package is stated for two **right** adjoints `a, b` of a fixed 1-cell `f`, i.e. Riehl's dual statement, and only the **unit** half of the compatibility is proved: an exhaustive enumeration of the top-level assertions of `Theory/Bicategory/Adjunction.v` shows there is no counit-compatibility lemma. It can be read in `Cat` through `Instance/Cat/Bicategory/Adjunction.v:163` `Cat_BicatAdjunction_Adjunction_iff`, but no in-tree lemma dualizes it back to the left-adjoint statement — there is no opposite-bicategory construction, and `Adjunction/Opposite.v` only dualizes hom-set adjunctions in `Cat`.

Gap, precisely: (1) on the book's own side (two left adjoints of a fixed `G` in `Cat`), no unit/counit compatibility and no uniqueness; (2) no transport of the bicategorical package to the left-adjoint side; (3) even bicategorically, counit compatibility `ε' ∘ (θ ⊳ G) ≈ ε` is unstated.

## Work to be done

Suggested module: extend `Theory/Adjunction.v` (or a new `Theory/Adjunction/Uniqueness.v` if `Theory/Adjunction.v` should stay dependency-free).

1. Given `A : F ⊣ G` and `A' : F' ⊣ G`, define `θ : F ⟹ F'` componentwise as the transpose (under `A`) of `η'`, and `θ⁻¹` symmetrically; prove naturality from `to_adj_nat_l` / `to_adj_nat_r` and mutual inverseness from the triangle identities. Package as `left_adjoint_comparison : F ≅[[C,D]] F'`.
2. Prove the two compatibility equations as separate named lemmas: `left_adjoint_comparison_unit : fmap[G] (θ x) ∘ η x ≈ η' x` and `left_adjoint_comparison_counit : ε' y ∘ θ (G y) ≈ ε y`. Note that clause (2) is the one currently missing even in the bicategorical development.
3. Prove uniqueness: any natural transformation `γ : F ⟹ F'` satisfying the unit equation equals `θ` (mirror `mate_charac`, `Theory/Bicategory/Adjunction.v:347`). Conclude `∃! θ`.
4. Dualize to two right adjoints of a fixed `F`, either directly or by `Adjunction/Opposite.v:34` `Opposite_Adjunction`.
5. Optionally strengthen the bicategorical file with the missing counit-compatibility lemma, so the `Cat` statement and the internal one agree.

In-tree donors: `Theory/Adjunction.v` (`to_adj_unit` at `:264`, `adj_univ` at `:196`, `left_adjoint_iso` at `:404`), `Theory/Bicategory/Adjunction.v` (`matecell` `:330`, `mate_unit_compat` `:636`, `mate_charac` `:347`, `adjoint_unique` `:708`), `Instance/Cat/Bicategory/Adjunction.v:163`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.3 Proposition 4.3.1, with `≈` for all morphism and 2-cell equalities.
- [ ] The comparison isomorphism is constructed explicitly (not merely asserted to exist) and shown natural.
- [ ] **Both** compatibility equations — unit and counit — are proved.
- [ ] Uniqueness of the compatible isomorphism is proved, not just existence.
- [ ] The dual statement for two right adjoints of a fixed left adjoint is available.
- [ ] `left_adjoint_iso` / `right_adjoint_iso` are refactored to be corollaries of the new result rather than left as independent weaker statements.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the comparison, both compatibility lemmas, and the uniqueness theorem.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Theory/Adjunction/Uniqueness.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Adjunction.Uniqueness. Print Assumptions left_adjoint_unique_compatible." | coqtop -R . Category'
nix develop --command make
```

Review items: the uniqueness clause quantifies over all compatible isomorphisms; the counit compatibility is genuinely proved (this is the clause absent even from `Theory/Bicategory/Adjunction.v`).

## Dependencies

None.

<!-- catalog: {"ids":["riehl:4.3:prop1"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 4.3: The adjunction calculus internal to a bicategory — composition, adjoint equivalences, and the representable characterization"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.3:remark8]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.3, Remark 4.3.8; printed p. 148, PDF p. 168. Item: `riehl:4.3:remark8`.

Paraphrase: the "syntactic" proofs of Propositions 4.3.1, 4.3.4, 4.3.5, 4.3.6 and 4.3.7 apply verbatim to adjunctions defined internally to *any* 2-category, not only to `Cat` — which is Riehl's reason for preferring them to the Yoneda-style arguments. Conversely, the Yoneda-style arguments can be bootstrapped from `Cat` to a general 2-category, because internal adjunctions are characterized representably.

## Background

An adjunction in a 2-category is a pair of 1-cells with unit and counit 2-cells satisfying the triangle identities; every construction on `Cat`-adjunctions that uses only pasting therefore transports. See [nLab: adjunction](https://ncatlab.org/nlab/show/adjunction), which is explicitly "about adjunctions in general 2-categories".

## Current state in the library

Two of the five cited results are internalized — at *bicategory* generality, which is weaker than the strict 2-categories Riehl speaks of and therefore stronger as a theorem — and three are not.

Present:
- `Theory/Bicategory/Adjunction.v:708` `adjoint_unique` — Proposition 4.3.1's content, under `Context {B : Bicategory}` at `:318`.
- `Theory/Bicategory/Mates.v:515` `mate_iso` — Proposition 4.3.7 (the mates correspondence), under `Context {B : Bicategory}` at `:469`.
- `Theory/Bicategory/Mates.v:245` `precomp_left`, `:306` `precomp_right`, `:390` `postcomp_left`, `:450` `postcomp_right` — an internal adjunction `f ⊣ u` induces bijections `bicat(f ∘ c, d) ≅ bicat(c, u ∘ d)` and `bicat(c, e ∘ f) ≅ bicat(c ∘ u, e)`, each reduced to `adj_triangle_left`/`adj_triangle_right`.

Missing:
- **Composition of internal adjunctions** (Proposition 4.3.4 internalized): the class `BicatAdjunction` (`Theory/Bicategory/Adjunction.v:270`) has no companion `Compose_BicatAdjunction`; a whole-tree grep confines `BicatAdjunction` to three files and finds no composition operation.
- **Promotion of an internal equivalence to an internal adjoint equivalence** (Proposition 4.3.5 internalized): there is no internal-equivalence class at all.
- **The induced hom-category adjunctions** (Proposition 4.3.6 internalized).
- The converse half of the remark: the `precomp_*`/`postcomp_*` lemmas go *from* an internal adjunction *to* the hom bijections, and nothing goes back — nothing states that a coherent family of hom-level bijections yields an internal adjunction.

## Work to be done

Suggested module: `Theory/Bicategory/Adjunction/Calculus.v`, alongside the existing `Theory/Bicategory/Adjunction.v`.

1. `Compose_BicatAdjunction`: given `f ⊣ u` in `bicat x y` and `f' ⊣ u'` in `bicat y z`, build `f' ∘∘∘ f ⊣ u ∘∘∘ u'`. The unit and counit are the whiskered composites; the triangle identities follow by pasting with the associator and unitors. Mirror `Adjunction/Compose.v` (`Adjunction_Compose` at `:173`, `Adjunction_Compose_unit`/`_counit`) at the 2-cell level.
2. `BicatEquivalence`: a 1-cell `f` with `u`, and invertible 2-cells `bi1id ≅ u ∘∘∘ f`, `f ∘∘∘ u ≅ bi1id`. Prove the internal analogue of Proposition 4.3.5: replace one of the two invertible 2-cells so that the triangle identities hold, yielding a `BicatAdjunction` whose unit and counit are invertible. Donor for the replacement trick: `Theory/Equivalence/Adjoint.v`.
3. Internalize Proposition 4.3.6: for a fixed object `w`, postcomposition and precomposition are functors between hom-categories (`bicat w x ⟶ bicat w y` etc.), and the `precomp_*`/`postcomp_*` round trips upgrade to an `Adjunction` once naturality in the hom variable is added. This is the internal counterpart of the `Cat`-level statement filed as #431.
4. The representable converse: state that a family of bijections `bicat(f ∘ c, d) ≅ bicat(c, u ∘ d)`, natural in `c` and `d` and coherent in `w`, determines an internal adjunction `f ⊣ u` (take `c := bi1id`, `d := f` and read off the unit). This closes the "bootstrap from `Cat`" direction the remark asserts.

In-tree donors: `Theory/Bicategory.v` (`Build_Bicategory'`), `Theory/Bicategory/Adjunction.v`, `Theory/Bicategory/Mates.v` (`preΘ` `:176`, `preΞ` `:180`, `postΛ` `:323`, `postΠ` `:327` and the four round trips), `Adjunction/Compose.v`, `Instance/Cat/Bicategory.v` (where `bicat C D ≡ [C, D]` definitionally, so each internal result reads back as the `Cat` statement).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.3 Remark 4.3.8, with `≈` used for all 2-cell equalities.
- [ ] `Compose_BicatAdjunction` is proved, with both triangle identities discharged.
- [ ] An internal-equivalence class exists and the promotion to an internal adjoint equivalence is proved.
- [ ] The internal hom-category adjunctions of Proposition 4.3.6 are proved as `Adjunction` terms, not merely as hom-level bijections.
- [ ] The representable converse (coherent hom bijections ⇒ internal adjunction) is proved, closing the remark's second half.
- [ ] Each internalized result is checked to specialize correctly in `Instance/Cat/Bicategory.v`.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for every principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Bicategory entry should record the completed internal calculus.

## Verification

```sh
nix develop --command coqc -R . Category Theory/Bicategory/Adjunction/Calculus.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Bicategory.Adjunction.Calculus. Print Assumptions Compose_BicatAdjunction." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20
```

Review items: every new result is stated under `Context {B : Bicategory}` (not specialized to `Cat`); the specializations in `Instance/Cat/Bicategory.v` really do reproduce the `Cat`-level statements.

## Dependencies

Depends on: #431 (MacLane V.5: Adjunctions and limits in functor categories) — the `Cat`-level Proposition 4.3.6 that step 3 internalizes.

<!-- catalog: {"ids":["riehl:4.3:remark8"],"deps":["#431"]} -->

---8<---

```yaml
title: "Riehl 4.3: The double category of categories, functors, adjunctions and mates"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.3:exvi]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.3, Exercise 4.3.vi (with its footnote 7); printed p. 148, PDF p. 168. Item: `riehl:4.3:exvi`.

Paraphrase: interpret the pasting-functoriality results of Exercise 4.3.v by exhibiting a double category whose objects are categories, whose horizontal morphisms are functors, whose vertical morphisms are adjunctions, and whose squares are mates. Footnote 7 offers an alternative reading: those results define an isomorphism between a pair of double categories sharing the same objects and horizontal morphisms.

## Background

Mates are the canonical 2-cells filling a square of adjunctions; their compatibility with horizontal and vertical pasting is exactly the interchange law of a double category. See [nLab: mate](https://ncatlab.org/nlab/show/mate) and [nLab: double category](https://ncatlab.org/nlab/show/double+category).

## Current state in the library

The **framework exists; the instance does not** — the verifier stressed that this makes the item buildable rather than foundational.

- `Theory/DoubleCategory.v` supplies the pseudo double category class (strict vertical category, weak horizontal composition, squares `dsq h u v k` as setoids with the `dsq_coerce` boundary calculus, horizontal pasting with `dinterchange`, and the globular `dassoc`/`dunit_left`/`dunit_right`), with companions and conjoints in `Theory/DoubleCategory/Companion.v`.
- `rg ': DoubleCategory'` finds exactly two instances tree-wide: `Construction/Sq.v:47` (`Sq`, commuting squares) and `Construction/Cospan/Double.v:929` (`Cospan_Double`). Neither has adjunctions as vertical morphisms.
- `Adj_Double`, `Double_Adj`, `AdjDouble` and `DoubleFunctor` all return **0** hits, so footnote 7's alternative (an isomorphism of two double categories) has no vehicle either.
- `Instance/Adjoints.v:133` `Adjoints` does make categories-and-adjunctions a 1-category, with no squares.
- `Instance/Adj.v:43` `Adj (C D : Category)` takes as a morphism an arbitrary **pair** `(σ : F ⟹ F', τ : U ⟹ U')` with no conjugacy condition; its own header (`:29-41`) records this as a known coarsening whose tightening to mate pairs is future work — so this issue is the place that tightening lands.
- The mates calculus itself is in `Theory/Bicategory/Mates.v` (`mate` `:476`, `mate_inv` `:480`, `mate_iso` `:515`, the two round trips `:489-505`), but `mate_compose`, `mate_functorial`, `mate_hcomp`, `mate_vcomp`, `mate_paste` all return **0** hits, and the file's own header descope at `:52-55` names pasting functoriality as ledger entry 10 — that gap is the prerequisite recorded under Dependencies.

## Work to be done

Suggested module: `Instance/Cat/Double/Adjunction.v` (or `Construction/AdjDouble.v` if it should not sit under `Instance/Cat/`).

1. Fix the data: objects are categories; horizontal morphisms are functors (the strict vertical/horizontal split must be chosen to match `Theory/DoubleCategory.v`'s convention, in which the *vertical* category is strict — so adjunctions, which compose strictly up to the associativity of functor composition, go vertically).
2. Vertical composition of adjunctions is `Adjunction/Compose.v:173` `Adjunction_Compose`; the vertical identity is `adj_id`. Discharge the strict vertical laws through `dsq_coerce`.
3. A square with horizontal boundary `H : C' ⟶ C`, `K : D' ⟶ D` and vertical boundary two adjunctions is a mate pair; define the square setoid by equality of the 2-cell (the mate of the other is then determined, by `mate_iso`).
4. Prove horizontal pasting (`dinterchange`) and the globular unitors/associator, using the pasting functoriality of mates.
5. Footnote 7's alternative: build the two double categories (squares = 2-cells between left adjoints; squares = 2-cells between right adjoints) and exhibit the mates bijection as an isomorphism between them, with the same objects and horizontal morphisms.
6. Tighten `Instance/Adj.v` to use conjugate pairs, retiring the caveat at its `:29-41`.

In-tree donors: `Theory/DoubleCategory.v`, `Construction/Sq.v` (the worked commuting-squares model to imitate), `Theory/Bicategory/Mates.v`, `Adjunction/Compose.v`, `Instance/Adjoints.v`, `Instance/Adj.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.3 Exercise 4.3.vi, with `≈` for all 2-cell equalities.
- [ ] A `DoubleCategory` instance is produced whose vertical morphisms are adjunctions and whose squares are mate pairs.
- [ ] `dinterchange` and the globular coherence cells are proved, not admitted.
- [ ] Footnote 7's isomorphism of two double categories is either proved or explicitly scoped out in the file header with a reason.
- [ ] `Instance/Adj.v`'s hom is tightened to conjugate pairs, and its `:29-41` caveat is updated to reflect the new state.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the double-category instance.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the DoubleCategory entry gains a third model.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Cat/Double/Adjunction.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Cat.Double.Adjunction. Print Assumptions Adj_Double." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20
```

Review items: the square setoid really is mate pairs (not the coarse product setoid `Instance/Adj.v` currently uses); interchange is proved from mate pasting functoriality rather than assumed.

## Dependencies

Depends on: #398 (MacLane IV.7: Adjoint squares and the Palmquist mates bijection) — supplies the mates bijection and, with the Riehl §4.3 increment recorded there, its pasting functoriality, which is the interchange law of this double category.
Depends on: #283 (MacLane II.5: Strict 2-categories, double categories, and Cat) — the ambient double-category vocabulary.
Depends on: #399 (MacLane IV.8: Horizontal composition of conjugate pairs makes Adj two-dimensional) — the 2-dimensional structure on `Adj` this issue upgrades to squares.

<!-- catalog: {"ids":["riehl:4.3:exvi"],"deps":["#398","#283","#399"]} -->

---8<---

```yaml
title: "Riehl 4.4: Two-variable adjunctions, left and right closures, and closed monoidal categories"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.4:def7, riehl:4.4:def-closures, riehl:4.4:def-closed-monoidal, riehl:4.4:def-n-variable-adjunction, riehl:4.6:exviii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.4 "Adjoint functors and duality": Definition 4.4.7 (two-variable adjunction), the unnumbered definitions of left closure, right closure, biclosed and closed immediately following it, the unnumbered gloss defining a closed monoidal category, and the unnumbered generalization to `n`-variable adjunctions; plus §4.6 Exercise 4.6.viii. Printed pp. 152, 155 and 172; PDF pp. 172, 175 and 192. Items: `riehl:4.4:def7`, `riehl:4.4:def-closures`, `riehl:4.4:def-closed-monoidal`, `riehl:4.4:def-n-variable-adjunction`, `riehl:4.6:exviii`.

Paraphrase: a two-variable adjunction is a triple of bifunctors `F : A ∏ B ⟶ C`, `G : A^op ∏ C ⟶ B`, `H : B^op ∏ C ⟶ A` together with a natural isomorphism `C(F(a,b), c) ≅ B(b, G(a,c)) ≅ A(a, H(b,c))`. When `F` is a monoidal product, `G` and `H` are its left and right closures; when both exist `F` is biclosed (often simply "closed", especially when `F` is naturally symmetric); a closed monoidal category is a monoidal category whose tensor is closed in that sense, generalizing cartesian closure away from the categorical product. Exercise 4.6.viii asks for the preservation consequence: the left adjoint `F` preserves colimits in each variable separately (with a counterexample showing it need not preserve colimits in the product category `A ∏ B`), together with the corresponding statements for the two right adjoints.

## Background

Two-variable adjunctions package tensor–hom situations in which the three categories are distinct, and are the correct setting for enriched and homotopical "pushout-product / pullback-hom" arguments. See [nLab: two-variable adjunction](https://ncatlab.org/nlab/show/two-variable+adjunction) and [nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category), which states the left-closed / right-closed / biclosed terminology this issue formalizes.

## Current state in the library

There is no notion of a two-variable adjunction anywhere: `rg` over the tree for "two-variable" / "two variable" finds only `Functor/Bifunctor.v`'s phrase "functors of two variables", and there is no class, record or lemma with this content.

What exists is a family of *single-leg, single-category* closed classes, none of which carries naturality:

- `Structure/Cartesian/Closed.v` — the live cartesian-closed development (`Class Closed`), with `flip {x y z} (f : x ~> z^y) : y ~> z^x := curry (uncurry f ∘ swap)` at `:117`; naturality of the transpose is recovered only piecemeal as `curry_comp_l` (`:165`), `curry_comp` (`:177`), `uncurry_comp_r` (`:185`), `uncurry_comp` (`:193`).
- `Structure/Monoidal/Closed.v:46` — `Class ClosedMonoidal`, whose **first field** is `closed_is_cartesian : @CartesianMonoidal C`. The library's headline "closed monoidal category" therefore hard-requires the tensor to be the cartesian one — precisely the special case Riehl's gloss generalizes away from. `Construction/Funny/Closed.v:30-34` records this as a structural no-go for non-cartesian tensors.
- `Structure/Monoidal/StarAutonomous.v:109` — `Class SymMonClosed`, the genuine general class, but it bundles `smc_is_symmetric : @SymmetricMonoidal C`, an extra hypothesis Riehl does not impose; and it has **no in-tree instance** (its own SCOPE paragraph at `:67` says "No concrete instance is constructed here", and `rg 'SymMonClosed'` returns only the class declaration and header prose).
- `Structure/Closed.v:166`'s Eilenberg–Kelly `Class Closed` sits **inside** the comment block opened at `:154` and closed at `:195`, so it is not in force and cannot supply the missing typing. Its live `Curry` (`:124`) and `Flip` (`:144`) do supply partial-application plumbing an `n`-variable definition would want.
- `Functor/Hom/Internal.v:40` — `InternalHomFunctor` builds `C^op ∏ C ⟶ C` by hand for the cartesian case only; neither `ClosedMonoidal` nor `SymMonClosed` derives an internal-hom bifunctor from its `exp_iso`.
- All three `exp_iso` fields are of the shape `exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z` — a bare per-triple isomorphism of hom-setoids with **no naturality field at all**, so Riehl's single natural isomorphism relating three hom-setoids cannot even be phrased against them.
- No `Adjunction` instance anywhere realizes `(− ⨂ y) ⊣ (y ⇒ −)` or `(− × y) ⊣ (−)^y`; the only product-related adjunction is `Adjunction/Diagonal/Product.v:37` (`Diagonal_Product C ⊣ ×(C)`), a different statement. This is why Exercise 4.6.viii's one-variable consequence "`(− ⨂ y)` is cocontinuous" cannot be obtained by applying `Adjunction/Continuity.v:223` `left_adjoint_preserves_colimits` — there is no adjunction to apply it to.
- `biclosed` appears 12 times, every one inside a comment (`Structure/Closed.v`, `Instance/Two.v`, `Instance/StrictCat/Funny.v`, `Construction/Funny*.v`, `Construction/Product.v`, `Construction/Day.v`).
- No lemma says the two closures agree for a symmetric tensor. Verifier sharpening: the gap is smaller than Phase C suggested — `Structure/Cartesian.v:298` proves `swap_invol` and `:480` packages a genuine isomorphism `x × y ≅ y × x`; composing that with `exp_iso` yields the missing second transposition `(x × y ~> z) ≊ (y ~> z^x)` in one step. Build the symmetry clause that way rather than from scratch.
- Verifier sharpening on the one existing non-cartesian closure witness: `Construction/Funny/Closed.v:350` `Funny_exponential_law : (⟦A □ B, E⟧) ≅[Cat] (⟦A, ⟦B, E⟧⟧)` should be cited as a *non-interface* witness only. Its own header (`:25-56`) discloses that this closed structure cannot be expressed by either library interface and that the hom-setoid adjunction `(− □ B) ⊣ ⟦B, −⟧` is "unprovable in this metatheory"; what is proved is an isomorphism of hom-*categories* plus strict beta/eta laws.

## Work to be done

Suggested modules: `Structure/Adjunction/TwoVariable.v` for the class and its calculus; `Structure/Monoidal/Biclosed.v` for the monoidal specialization; extend `Adjunction/Continuity.v` (or a new `Structure/Adjunction/TwoVariable/Continuity.v`) for the preservation half.

1. Define `Class TwoVariableAdjunction {A B C : Category} (F : A ∏ B ⟶ C) (G : A^op ∏ C ⟶ B) (H : B^op ∏ C ⟶ A)` carrying the two hom-setoid isomorphisms **plus their naturality in all three variables**, stated as isomorphisms of trifunctors into `Sets` (the existing `Adjunction/Hom.v:72` `Adjunction_Hom` is the one-variable template for "naturality as a natural isomorphism of hom-functors"). Do not repeat the mistake of the existing `exp_iso` fields, which omit naturality.
2. Derive the two one-variable adjunctions `F(a,−) ⊣ G(a,−)` and `F(−,b) ⊣ H(b,−)` as `Adjunction` terms, so the whole existing adjunction calculus applies.
3. Define left closure, right closure and `Biclosed` over a **bare** `Monoidal` base — not `CartesianMonoidal`, not `SymmetricMonoidal`. `Structure/Monoidal/StarAutonomous.v`'s `SymMonClosed` should then become the symmetric specialization of the new class rather than an independent copy.
4. Prove that for a braided/symmetric tensor the two closures are naturally isomorphic, using `Structure/Cartesian.v:480` (or the braiding) composed with `exp_iso`; supply the missing `flip_flip` involution lemma for `Structure/Cartesian/Closed.v:117` and `Structure/Monoidal/Closed.v:129` while you are there.
5. Define the `n`-variable generalization (`F : A_1 ∏ … ∏ A_n ⟶ B` admitting pointwise right adjoints when any `n−1` variables are fixed) at least to the extent of stating it; `Structure/Closed.v`'s live `Curry`/`Flip` are the partial-application donors.
6. Exercise 4.6.viii: prove that the left adjoint of a two-variable adjunction preserves colimits in each variable (immediate from step 2 plus `Adjunction/Continuity.v:223`), formulate the dual preservation statements for `G` and `H`, and exhibit the counterexample showing `F` need not preserve colimits computed in `A ∏ B` (in `Sets`, `× : Sets ∏ Sets ⟶ Sets` on the initial object of the product category is the standard witness).

In-tree donors: `Functor/Bifunctor.v`, `Construction/Product.v`, `Adjunction/Hom.v`, `Structure/Cartesian/Closed.v`, `Structure/Monoidal/Closed.v`, `Structure/Monoidal/StarAutonomous.v`, `Functor/Hom/Internal.v`, `Adjunction/Continuity.v`, `Structure/Limit/Preservation.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.4 Definition 4.4.7 and the surrounding closure definitions, with `≈` used for every morphism equality.
- [ ] `TwoVariableAdjunction` is typed over **three possibly distinct categories**, not an endo-tensor on one.
- [ ] Naturality in all three variables is a field (or an immediate consequence of a field), not recovered piecemeal by derived lemmas.
- [ ] Both transpositions are present, so the triple `(F, G, H)` is genuinely formed.
- [ ] `Biclosed` is defined over a bare `Monoidal` base; `SymMonClosed` and `ClosedMonoidal` are related to it rather than left as unconnected copies, and the cartesian bundling of `ClosedMonoidal` is documented or removed.
- [ ] The symmetric case is proved: the two closures are naturally isomorphic (with `flip_flip` supplied).
- [ ] The `n`-variable definition is stated.
- [ ] Exercise 4.6.viii is discharged: per-variable colimit preservation for `F`, the dual statements for `G` and `H`, and a concrete counterexample for the product category.
- [ ] At least one concrete instance of `TwoVariableAdjunction` is exhibited (currying in `Sets` is the cheapest), so the class is not left uninhabited the way `SymMonClosed` is.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the class, the derived one-variable adjunctions, the symmetry lemma and the preservation theorems.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this reshapes the Monoidal/Closed entries.

## Verification

```sh
nix develop --command coqc -R . Category Structure/Adjunction/TwoVariable.v
nix develop --command coqc -R . Category Structure/Monoidal/Biclosed.v
nix develop --command bash -c 'echo "Require Import Category.Structure.Adjunction.TwoVariable. Print Assumptions TwoVariableAdjunction_left_adjoint_left." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: the class matches Riehl's Definition 4.4.7 including the three-variable naturality; `Biclosed` does **not** require symmetry or cartesianness; the Exercise 4.6.viii counterexample really distinguishes per-variable from joint colimit preservation.

## Dependencies

Depends on: #396 (MacLane IV.7: Adjunctions with a parameter) — supplies the assembly of pointwise right adjoints into a bifunctor, which is the input to Definition 4.4.7.

<!-- catalog: {"ids":["riehl:4.4:def7","riehl:4.4:def-closures","riehl:4.4:def-closed-monoidal","riehl:4.4:def-n-variable-adjunction","riehl:4.6:exviii"],"deps":["#396"]} -->

---8<---

```yaml
title: "Riehl 4.4: Two antitone Galois connections — zero sets versus ideals, and axioms versus models"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.4:example2, riehl:4.4:example3]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.4, Examples 4.4.2 and 4.4.3; printed pp. 149–150, PDF pp. 169–170. Items: `riehl:4.4:example2`, `riehl:4.4:example3`.

Paraphrase, Example 4.4.2: over an algebraically closed field and a fixed number of variables, the operations "common zero locus of a set of polynomials" and "set of polynomials vanishing on a set of points" are contravariant functors between the inclusion-ordered powersets of the polynomial ring and of affine space; they are *mutually right adjoint*, because a point set is contained in the zero locus of `S` exactly when `S` is contained in the vanishing ideal of that point set. The Nullstellensatz identifies the fixed points on one side with the radical ideals.

Paraphrase, Example 4.4.3: fix a first-order signature. Between the inclusion-ordered powerset of sentences and the inclusion-ordered powerset of structures, the operations "the structures satisfying every axiom in `A`" and "the sentences satisfied by every structure in `M`" are again mutually right adjoint, the transposition being the two readings of the satisfaction relation. The fixed points are the deductively closed theories and the elementary classes.

## Background

Both are instances of the antitone (dual) Galois connection induced by a relation, the original setting Galois theory was named for. See [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection), which distinguishes the monotone and antitone senses, and [Wikipedia: Hilbert's Nullstellensatz](https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz), which records the zero-set/ideal correspondence as a Galois connection with Zariski closure and radical as the two closure operators.

## Current state in the library

Both examples are absent in every ingredient, and both blocked by the same missing vocabulary.

- The notion the examples instantiate — mutually right adjoint contravariant functors — has no in-tree definition (`rg -in 'mutually (left|right) adjoint|contravariant adjunction|dual adjunction'` returns **0** hits). The word "antitone" occurs exactly twice in the library, both in background essays: `Theory/Adjunction.v:79` and `Instance/Poset.v:59`. "Galois" occurs only in background essays (`Theory/Adjunction.v:78`, `Instance/Poset.v:37-100`, `Instance/Adjoints.v:280`, `Structure/Limit.v:53`, `Structure/Factorization.v:69`, `Adjunction/GAFT.v:136`) — not one is a `Definition`, `Class` or `Lemma`.
- For Example 4.4.2: `nullstellensatz` → 0 hits; `zariski` → 1 hit, a prose aside at `Theory/Sheaf.v:76`; `radical ideal`, `algebraically closed`, `common zero` → 0 hits. There is no ring, no field, no polynomial ring and no ideal anywhere; the full `Instance/` roster contains exactly one algebraic category, `Instance/CMon.v`. Two hosts were checked and ruled out: `Instance/Ens.v:56` `EnsT` is not the inclusion poset of subsets, and `Structure/Topos.v`'s `Pow a := Ω ^ a` carries no `V`/`I` pair.
- For Example 4.4.3: `satisfaction`, `model theory` → 0 hits; "first-order" occurs only in prose. `Theory/Lawvere/Model.v`'s `Model`/`Models` is "product-preserving functor out of a Lawvere theory" — no poset of axiom sets, no poset of structures, no adjoint pair between them. `Instance/Comp.v`'s `OpSignature`/`Algs` gives algebras for an operation signature but asserts no Galois connection between equation sets and algebra classes. No `⊨` relation exists in the tree.
- Formalizable in principle throughout — hence ABSENT rather than out of scope. The poset-as-thin-category machinery is already there (`Instance/Proset.v:33`, `Instance/Poset.v:116`).

## Work to be done

Suggested modules: `Construction/GaloisFromRelation.v` for the shared engine; `Instance/Poset/Nullstellensatz.v` and `Instance/Poset/Satisfaction.v` (or `Theory/Lawvere/Satisfaction.v`) for the two instances.

1. Build the shared engine first, since both examples are the same theorem: given sets `X`, `Y` and a relation `R ⊆ X × Y`, the maps `S ↦ {y | ∀ x ∈ S, R x y}` and `T ↦ {x | ∀ y ∈ T, R x y}` between the inclusion-ordered powersets are mutually right adjoint, with `T ⊆ F S ↔ S ⊆ G T`. In a thin category the naturality and triangle obligations are vacuous (`Instance/Proset.v:33-43` sets `Setoid.equiv := fun _ _ => True`), so this is short — but state that vacuity once as a named lemma rather than re-deriving it.
2. Derive the closure operators `G F` and `F G`, their idempotence, and the fixed-point correspondence (the "closed" elements on each side biject), so both examples get their fixed-point statement for free.
3. Example 4.4.2 instance: this needs the powerset poset over a polynomial ring's underlying set and over affine `n`-space. Scope honestly — if commutative algebra is not being built, instantiate the engine at the abstract relation "`p` vanishes at `x`" over an arbitrary commutative ring and point set, prove the Galois connection and the closure operators, and record the Nullstellensatz identification of the fixed points as a deliberate non-goal in the file header (it is a genuine theorem of algebra, not of category theory).
4. Example 4.4.3 instance: define a first-order signature (function/constant/relation symbols with arities), `σ`-structures, sentences, and the satisfaction relation `⊨`; instantiate the engine. `Instance/Comp.v`'s `OpSignature` is the nearest donor for the signature layer, and `Theory/Lawvere/Model.v` for the models-as-functors reading.
5. Connect both to the general notion once it exists: each is an instance of mutual right adjointness in the sense of Riehl's Definition 4.4.1.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Instance/Ens.v` (subsets of a type), `Instance/Comp.v` (`OpSignature`, `Algs`), `Theory/Lawvere/Model.v`, `Adjunction/Opposite.v:34` (`Opposite_Adjunction`, for reading a mutual right adjunction as `F^op ⊣ G`).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.4 Examples 4.4.2 and 4.4.3, with `≈` for all morphism equalities.
- [ ] The relation-induced antitone Galois connection is proved once, generically, and both examples are instances of it.
- [ ] The transposition is stated as the biconditional `T ⊆ F S ↔ S ⊆ G T` (Riehl's mutual right adjointness), not as two unrelated monotone maps.
- [ ] The induced closure operators and the fixed-point bijection are proved.
- [ ] The satisfaction relation `⊨` is defined and the syntax/semantics connection instantiated.
- [ ] Any algebraic content deliberately not formalized (the Nullstellensatz itself) is declared in the file header, not silently elided.
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond documented `Instance/`-layer allowances.
- [ ] `Print Assumptions` reported for the generic engine and each instance.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Construction/GaloisFromRelation.v
nix develop --command coqc -R . Category Instance/Poset/Satisfaction.v
nix develop --command bash -c 'echo "Require Import Category.Construction.GaloisFromRelation. Print Assumptions relation_galois_mutual_right." | coqtop -R . Category'
nix develop --command make
```

Review items: the connection is **antitone** (contravariant on both sides), matching §4.4 rather than the monotone connections of §4.1; the fixed-point statements are proved rather than asserted.

## Dependencies

Depends on: #358 (MacLane IV.2: Functors adjoint on the right) — the definition of mutually right adjoint contravariant functors, which both examples instantiate.
Depends on: #380 (MacLane IV.5: Galois connections are adjunctions between preorders) — the preorder/adjunction dictionary these connections live in.
Depends on: #223 (MacLane I.2: Preorders as thin categories, with partial and linear orders) — the ordered powersets both examples are stated over.

<!-- catalog: {"ids":["riehl:4.4:example2","riehl:4.4:example3"],"deps":["#358","#380","#223"]} -->

---8<---

```yaml
title: "Riehl 4.5: Sets and injections — slices as predicate posets, and local cartesian closure without a terminal object"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.5:construction-setmono-slice, riehl:4.5:example5, riehl:4.5:remark8]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.5 "Contravariant adjunctions" / locally cartesian closed material: the unnumbered construction identifying slices of the category of sets and injections with predicate posets (printed p. 157, PDF p. 177), Example 4.5.5 (printed p. 158, PDF p. 178), and Remark 4.5.8 (printed p. 160, PDF p. 180). Items: `riehl:4.5:construction-setmono-slice`, `riehl:4.5:example5`, `riehl:4.5:remark8`.

Paraphrase: let `Set_mono` be the category of sets and injections. Its slice over `X` is (equivalent to) the poset of predicates on `X`, a subobject of `X` corresponding to the monomorphism onto its truth set; under that identification the cartesian closed structure of the predicate poset is exactly `(q ⇒ r) = ∀_i Δ_i r` and `(p ∧ q) = ∃_i Δ_i r` for the mono `i` of a predicate's truth set. `Set_mono` is locally cartesian closed yet has neither binary products nor a terminal object — a witness that local cartesian closure does not imply cartesian closure in the absence of a terminal object — though it does have the pullbacks that local cartesian closure guarantees. Remark 4.5.8 compares the two triples: for a monomorphism `f`, the `Set`-level triple `Σ_f ⊣ Δ_f ⊣ Π_f` restricted to `Set_mono` coincides with the quantifier triple `∃_f ⊣ Δ_f ⊣ ∀_f`; for a general `f` they differ, `∃_f` being defined by image-factorizing the restricted `Σ_f`.

## Background

`Set_mono` is the standard counterexample separating "each slice is cartesian closed" from "the category is cartesian closed", and the identification of its slices with predicate posets is the elementary face of the subobject fibration. See [nLab: locally cartesian closed category](https://ncatlab.org/nlab/show/locally+cartesian+closed+category) and [nLab: subobject](https://ncatlab.org/nlab/show/subobject).

## Current state in the library

The subobject-side half exists; the category `Set_mono` and everything about its slices does not.

Present:
- `Theory/Subobject.v:93` — `Theorem sub_equiv_iff_mutual (u v : SubObj x) : (u ≈ v) ↔ (sub_le u v * sub_le v u)`, over `Record SubObj x := { sub_dom : C; sub_mono : sub_dom ~> x; sub_is_monic : Monic sub_mono }` with the factorization preorder `sub_le`.
- `Structure/SubobjectClassifier.v:187` — `Theorem classifier_classifies (x : C) : @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}` (`Defined`), the object-level half of "subobjects are predicates". It is stated only for a category already equipped with a `SubobjectClassifier` (Terminal + `HasPullbacks` + `Ω`), and the only concrete carrier in-tree is FinSet (`Instance/FinSet/Topos.v`); `Sets` itself is cross-universe theorems only (`Instance/Sets/Classifier.v`).

Missing:
- `Set_mono` does not exist: `rg -i 'Set_mono|SetMono|sets and mono'` returns **0** hits, and `Construction/Subcategory.v` is never instantiated at the monomorphism class (`rg 'Monic' | grep -iE 'subcategory|wide|Category :='` → 0 hits).
- No slice carries any structure: `@Slice` occurs only in `Construction/Slice.v` and `Construction/Slice/Pullback.v`, and is never given a `Cartesian`, `Terminal` or `Closed` instance — so "each slice is cartesian closed" is currently unstatable.
- The correspondence subobjects ↔ predicates is an isomorphism of **setoids in `Sets`**, not an equivalence of preorder **categories**; `SubObj x` is the mono-quotient preorder and is never presented as a category.
- Remark 4.5.8 compares two operations (`∃_f` and `Σ_f`) neither of which is defined, over a category that does not exist. Deliberately not counted as partial coverage: `Instance/Sets/Image.v` does supply the (Epi, Mono) factorization (`Sets_Image_epi_epic:113`, `Sets_Image_mono_monic`, `Sets_Image_Factorization`) and `Structure/Regular/Factorization.v` supplies `Regular_OFS` — these are an *ingredient* of the remark's construction, not a clause of its claim, and will be the donor for defining `∃_f`.

## Work to be done

Suggested modules: `Instance/SetMono.v` (the category), `Instance/SetMono/Slice.v` (slices as predicate posets and local cartesian closure), and a short section of the same file for Remark 4.5.8.

1. Define `Set_mono` as the wide subcategory of `Sets` on the monomorphisms. Use `Construction/Subcategory.v` with `sobj := fun _ => True` and `shom f := Monic f`, discharging closure under identity and composition from `Theory/Morphisms.v:212` `monic_compose`.
2. Present the poset of predicates on `X` as a category (the pointwise order on `X → Ω`), and prove `Set_mono/X ≃ Ω^X` as an **equivalence of categories**, upgrading `classifier_classifies` from a setoid isomorphism. `Theory/Subobject.v`'s `sub_le` gives the order and `sub_equiv_iff_mutual` the antisymmetry-up-to-`≈`.
3. Prove each slice `Set_mono/X` is cartesian closed, with the closed structure exhibited in the form Riehl gives: `∧` as `∃_i Δ_i` and `⇒` as `∀_i Δ_i` along the mono of a predicate's truth set.
4. Prove the negative half of Example 4.5.5: `Set_mono` has **no** terminal object and **no** binary products, while it does have pullbacks. These are the statements that make the example a witness, so they must be proved, not asserted.
5. Remark 4.5.8: define `∃_f` by image-factorizing `Σ_f` (donor: `Instance/Sets/Image.v`, `Structure/Regular/Factorization.v`), prove it agrees with `Σ_f` when `f` is monic, and exhibit a non-monic `f` where they differ.

In-tree donors: `Construction/Subcategory.v`, `Theory/Morphisms.v`, `Theory/Subobject.v`, `Structure/SubobjectClassifier.v`, `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Instance/Sets/Image.v`, `Structure/Regular/Factorization.v`, `Instance/Props.v` (the truth-value poset).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.5 (the `Set_mono` construction, Example 4.5.5 and Remark 4.5.8), with `≈` for all morphism equalities.
- [ ] `Set_mono` exists as a category and its pullbacks are constructed.
- [ ] `Set_mono/X ≃ Ω^X` is proved as an equivalence of categories, not only as a setoid bijection.
- [ ] Each slice is proved cartesian closed, with `∧` and `⇒` exhibited as `∃_i Δ_i` and `∀_i Δ_i`.
- [ ] The absence of a terminal object and of binary products in `Set_mono` is **proved**.
- [ ] `∃_f` is defined by image factorization; agreement with `Σ_f` for monic `f` and a concrete disagreement for non-monic `f` are both proved.
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond documented `Instance/`-layer allowances.
- [ ] `Print Assumptions` reported for the category, the slice equivalence and the closure structure.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Instance/SetMono.v
nix develop --command coqc -R . Category Instance/SetMono/Slice.v
nix develop --command bash -c 'echo "Require Import Category.Instance.SetMono.Slice. Print Assumptions SetMono_slice_predicates." | coqtop -R . Category'
nix develop --command make
```

Review items: local cartesian closure is established **without** using a terminal object anywhere; the two negative statements (no terminal, no binary products) are theorems.

## Dependencies

Depends on: #732 (Awodey 9.7: Locally cartesian closed categories, and the equivalence with slicewise cartesian closure) — the predicate this example is a witness for.
Depends on: #384 (MacLane IV.5: Quantifiers as adjoints to substitution) — supplies `∃_i ⊣ Δ_i ⊣ ∀_i`, in terms of which the slice closure is described.
Depends on: #389 (MacLane IV.6: Powerset lattices and Boolean algebras are cartesian closed) — the predicate poset whose closed structure the slices inherit.

<!-- catalog: {"ids":["riehl:4.5:construction-setmono-slice","riehl:4.5:example5","riehl:4.5:remark8"],"deps":["#732","#384","#389"]} -->

---8<---

```yaml
title: "Riehl 4.5: The composition-pullback-pushforward triple on slices of quivers over the walking arrow"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.5:example11, riehl:4.5:exiv]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.5, Example 4.5.11 and Exercise 4.5.iv; printed pp. 161 and 165, PDF pp. 181–182 and 185. Items: `riehl:4.5:example11`, `riehl:4.5:exiv`.

Paraphrase: quivers form a presheaf category and are therefore locally cartesian closed. Let `A` be the walking arrow (two vertices and one arrow between them), `dA` its discrete subquiver on the same two vertices, and `δ : dA → A` the inclusion. Slicing gives an adjoint triple `Σ_δ ⊣ Δ_δ ⊣ Π_δ` between the slice over `dA` and the slice over `A`; objects of the slice over `A` are "bipartite quivers" (two vertex sets with edges between them), and the three functors compute recognisable operations on them. Exercise 4.5.iv asks for the same computation in the category of *reflexive* quivers, where every vertex carries a specified endoarrow.

## Background

This is the smallest non-trivial worked example of dependent sum, substitution and dependent product in a presheaf topos: `Σ` is composition, `Δ` is pullback, `Π` is the dependent product. See [nLab: quiver](https://ncatlab.org/nlab/show/quiver) and [nLab: dependent product](https://ncatlab.org/nlab/show/dependent+product).

## Current state in the library

Neither the ambient theorem nor the instance exists.

- `Construction/Free/Quiver.v` does exist and is registered (`_CoqProject:72`): `Class Quiver`, `QuiverHomomorphism` at `:205`, `#[export] Instance QuiverCategory : Category` at `:358`, `Forgetful` at `:412`, `FreeCatFunctor` at `:546`, `FreeForgetfulAdjunction` at `:550`. So the category of quivers is in-tree — but it is built from node/edge class data and is **never** identified with a presheaf category, and no slice of it is ever formed (`rg -n 'Quiver.*Slice|Slice.*Quiver'` → 0).
- Additional in-tree material that strengthens rather than weakens the gap: `Instance/Parallel.v:155-166` explicitly identifies presheaves on the walking parallel pair with quivers and builds one such presheaf, `Presheaf_Graph : Parallel^op ⟶ Sets` — but that is a single hand-built presheaf with `nat`/`nat*nat` carriers, not the category of quivers as presheaves, and it carries no slices and no adjoint triple.
- The `Σ_f ⊣ Δ_f` adjunction is a **commented-out** stub at `Construction/Slice/Pullback.v:121-127`, and the stub even states the adjunction backwards (`Star_Functor f ⊣ Bang_Functor f`), which the file's own header flags at `:38-40`. The two functors themselves exist: `Bang_Functor` at `:50`, `Star_Functor` at `:67`.
- No `Π` functor exists anywhere: `rg -in 'Pi_f|Π_f|dependent product|pushforward'` over `*.v` returns only prose (`Construction/Slice/Pullback.v:37`, `Structure/Pullback.v:128`, `Theory/Adjunction.v:77`, `Construction/Slice.v:96`) plus `Construction/Grothendieck/RoundTrip.v`'s unrelated opcartesian-lift "pushforward" vocabulary.
- For the exercise: `rg -in 'rQuiver|reflexive quiver'` → **0** hits. `Construction/Free/Quiver.v`'s `Quiver` class has no reflexivity/degeneracy field. A plausible alias trap was correctly avoided by the coverage pass and is worth repeating here: `Structure/Coequalizer/Reflexive.v` is about reflexive *pairs* of parallel morphisms (a common section), an entirely different notion.

## Work to be done

Suggested modules: `Instance/Quiver/Presheaf.v` (quivers as presheaves on the walking parallel pair), `Instance/Quiver/Slice.v` (the triple over `δ`), `Instance/RQuiver.v` (reflexive quivers) and a section of `Instance/Quiver/Slice.v` for the exercise.

1. Identify `QuiverCategory` with `[Parallel^op, Sets]` as an equivalence (or an isomorphism) of categories, using the identification already sketched in prose at `Instance/Parallel.v:155-166`. This is what makes the local cartesian closure of presheaf categories applicable.
2. Construct the walking arrow `A`, the discrete subquiver `dA` and the inclusion `δ` as quivers and a quiver homomorphism.
3. Build the three functors between `Quiver/dA` and `Quiver/A`: `Σ_δ` by postcomposition (`Bang_Functor`), `Δ_δ` by pullback (`Star_Functor`), and `Π_δ` from the presheaf-level dependent product. Prove `Σ_δ ⊣ Δ_δ ⊣ Π_δ`.
4. Compute each functor explicitly on bipartite quivers and state the computation as lemmas — that is the content of the example, and it is what makes the abstract triple legible.
5. Exercise 4.5.iv: define `rQuiver` (a quiver with a chosen endoarrow at each vertex, morphisms preserving it), redo steps 2–4 there, and record where the answers differ from the plain-quiver case.

In-tree donors: `Construction/Free/Quiver.v`, `Instance/Parallel.v`, `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Instance/Fun.v`, `Construction/Displayed/Codomain.v:204` (`codomain_cleaving`, the base-change cleaving), `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.5 Example 4.5.11 and Exercise 4.5.iv, with `≈` for all morphism equalities.
- [ ] Quivers are identified with presheaves on the walking parallel pair, as a proved equivalence.
- [ ] All three functors `Σ_δ`, `Δ_δ`, `Π_δ` are constructed and both adjunctions proved.
- [ ] The explicit computation on bipartite quivers is stated and proved for each of the three functors.
- [ ] `rQuiver` is defined and the whole computation redone there.
- [ ] The commented-out, backwards `Base_Functor_Adjunction` stub at `Construction/Slice/Pullback.v:121-127` is replaced by the live, correctly-oriented adjunction (or that file's header note at `:38-40` is updated to point at the new home).
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond documented `Instance/`-layer allowances.
- [ ] `Print Assumptions` reported for the equivalence, the three functors and the two adjunctions.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Quiver/Presheaf.v
nix develop --command coqc -R . Category Instance/Quiver/Slice.v
nix develop --command coqc -R . Category Instance/RQuiver.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Quiver.Slice. Print Assumptions quiver_delta_triple." | coqtop -R . Category'
nix develop --command make
```

Review items: the adjunctions are oriented as `Σ ⊣ Δ ⊣ Π` (not the reversed order of the commented-out stub); the explicit bipartite-quiver computations match §4.5.

## Dependencies

Depends on: #730 (Awodey 9.7: The dependent product — the right adjoint to base change on slices) — supplies `Π_f`, without which the triple cannot be typed.
Depends on: #734 (Awodey 9.7: Presheaf categories are locally cartesian closed) — the ambient theorem that makes quivers locally cartesian closed.
Depends on: #906 (Riehl 1.1: Reflexive quivers and the underlying reflexive quiver of a category) — supplies `rQuiver` for the exercise.
Depends on: #962 (Riehl 3.6: Completeness and cocompleteness of Quiver and rQuiver, and the failure for Graph) — supplies the limits (in particular the pullbacks) the base-change functor needs.

<!-- catalog: {"ids":["riehl:4.5:example11","riehl:4.5:exiv"],"deps":["#730","#734","#906","#962"]} -->

---8<---

```yaml
title: "Riehl 4.5: The Beck-Chevalley transformations and their invertibility over a pullback square"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.5:def-beck-chevalley, riehl:4.5:lem12, riehl:4.5:cor13]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.5: the unnumbered definition of the Beck–Chevalley isomorphisms, Lemma 4.5.12 and Corollary 4.5.13; printed pp. 162–163, PDF pp. 182–183. Items: `riehl:4.5:def-beck-chevalley`, `riehl:4.5:lem12`, `riehl:4.5:cor13`.

Paraphrase: a commuting square `f h = g k` in a locally cartesian closed category induces canonical natural transformations `β : Σ_h Δ_k ⇒ Δ_f Σ_g` (between functors on the slice over one corner) and `γ : Δ_g Π_f ⇒ Π_k Δ_h`, and **both are invertible when the square is a pullback**; these are the Beck–Chevalley isomorphisms. Corollary 4.5.13: consequently base change along any morphism preserves the cartesian closed structure of the slices — forming a product (respectively an exponential) with an object and then pulling back is naturally isomorphic to pulling back and then forming the product (respectively exponential) with the pulled-back object.

## Background

Beck–Chevalley is the "commutation of adjoints" property underlying substitution in dependent type theory and base change in geometry; `β` and `γ` are mates of identity 2-cells, which is why the mates calculus is the right tool. See [nLab: Beck-Chevalley condition](https://ncatlab.org/nlab/show/Beck-Chevalley+condition).

## Current state in the library

Absent; the two ingredient adjunctions are absent as well, so neither transformation can currently be typed.

- `rg -in 'beck.?chevalley'` over the tree returns exactly two `.v` hits, both background prose that cite the condition without claiming it is formalized: `Theory/Bicategory.v:104` ("the 2-categorical toolkit for lifts, transports, and Beck–Chevalley squares (Kelly, Street 1974)") and `Comonad/Coalgebra.v:94` ("a bifibration satisfying the Beck–Chevalley condition").
- `β` and `γ` are natural transformations between **composites of slice functors**, and none of the four ingredients exists: no `Σ_f ⊣ Δ_f` adjunction (the stub at `Construction/Slice/Pullback.v:121-127` is commented out and states the adjunction backwards, as the file's header admits at `:38-40`); no `Π_f` at all; no locally-cartesian-closed hypothesis to assume; and no transformation of any kind between composites of `Bang_Functor`/`Star_Functor` — the only non-comment occurrences of those two identifiers in the whole tree are their definitions (`:50`, `:67`) and the `f !` notation at `:60`.
- The *general* machinery is present and is the intended donor, not partial coverage: `Theory/Bicategory/Mates.v` supplies the Kelly–Street mates calculus (`mate`, `mate_iso` at `:515`, `mate_roundtrip_left/right`), which is exactly how the book defines `β`; and the pullback toolkit is complete and verified at `Theory/Morphisms/Stability.v` — `pullback_paste:106`, `pullback_unpaste:160`, `monic_pullback_stable:226`, `pullback_transport:329`.
- For Corollary 4.5.13, the two functor-structure classes exist but are never instantiated at a slice functor: `Functor/Structure/Cartesian.v:49` `Class CartesianFunctor` and `Functor/Structure/Cartesian/Closed.v:49` `Class ClosedFunctor` (the latter inside `Section ClosedFunctor` over a `@CartesianFunctor` context at `:45`). No lemma anywhere states what base change preserves, and no slice category is given cartesian or cartesian closed structure.

## Work to be done

Suggested module: `Construction/Slice/BeckChevalley.v`.

1. With `Σ_f ⊣ Δ_f` and `Δ_f ⊣ Π_f` available (see Dependencies), define `β` as the mate of the identity 2-cell on `Δ_k Δ_f = Δ_g Δ_h` (equivalently, transpose `Σ_h Δ_k ⇒ Δ_f Σ_g` across `Σ_h ⊣ Δ_h`). Use `Theory/Bicategory/Mates.v` rather than building the transposition by hand — that is the point of Riehl's remark that these proofs internalize.
2. Define `γ : Δ_g Π_f ⇒ Π_k Δ_h` dually.
3. Prove both are isomorphisms when the square is a pullback. The essential input is the pasting calculus: `pullback_paste` / `pullback_unpaste` at `Theory/Morphisms/Stability.v:106,160` identify `Δ_k Δ_f` with `Δ_g Δ_h` up to the canonical comparison, and `pullback_transport` at `:329` moves along it.
4. Prove Corollary 4.5.13 as a consequence: `Δ_f : C/X ⟶ C/Y` is a `CartesianFunctor` and a `ClosedFunctor` for every `f`. This requires the slices to carry cartesian closed structure first (from the locally-cartesian-closed hypothesis), so state that instantiation explicitly.
5. State the Beck–Chevalley condition as a reusable predicate (a square plus the assertion that `β` and `γ` are invertible), so that later fibration work — `Comonad/Coalgebra.v:94` already refers to it — can consume it.

In-tree donors: `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Theory/Morphisms/Stability.v`, `Theory/Bicategory/Mates.v`, `Functor/Structure/Cartesian.v`, `Functor/Structure/Cartesian/Closed.v`, `Construction/Displayed/Codomain.v` (`codomain_cleaving` at `:204`, `codomain_cleaving_pullbacks` at `:232`).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.5 Lemma 4.5.12 and Corollary 4.5.13, with `≈` for all morphism and natural-transformation equalities.
- [ ] `β` and `γ` are **constructed** (as mates), not postulated.
- [ ] Both are proved invertible under the pullback hypothesis, and the hypothesis is genuinely used.
- [ ] A reusable `BeckChevalley` predicate is exposed for downstream fibration work.
- [ ] Corollary 4.5.13 is proved: base change is a `CartesianFunctor` and a `ClosedFunctor` between slices.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for `β`, `γ`, both invertibility theorems and the corollary.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Slice/BeckChevalley.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Slice.BeckChevalley. Print Assumptions beck_chevalley_beta_iso." | coqtop -R . Category'
nix develop --command bash -c 'echo "Require Import Category.Construction.Slice.BeckChevalley. Print Assumptions base_change_ClosedFunctor." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20
```

Review items: `β` is obtained as a mate (matching §4.5's derivation) rather than by an ad hoc transposition; the invertibility proof uses the pullback hypothesis and not a stronger assumption.

## Dependencies

Depends on: #387 (MacLane IV.5: Base change is right adjoint to composition on slices) — supplies `Σ_f ⊣ Δ_f`, one of the two adjunctions `β` is a mate over.
Depends on: #730 (Awodey 9.7: The dependent product — the right adjoint to base change on slices) — supplies `Π_f`, without which `γ` cannot be typed.
Depends on: #732 (Awodey 9.7: Locally cartesian closed categories, and the equivalence with slicewise cartesian closure) — the ambient hypothesis and the slice closed structure Corollary 4.5.13 speaks about.
Depends on: #398 (MacLane IV.7: Adjoint squares and the Palmquist mates bijection) — the mates calculus used to define both transformations.

<!-- catalog: {"ids":["riehl:4.5:def-beck-chevalley","riehl:4.5:lem12","riehl:4.5:cor13"],"deps":["#387","#730","#732","#398"]} -->

---8<---

```yaml
title: "Riehl 4.5: Distributivity of the dependent product over the dependent sum, and the type-theoretic axiom of choice"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.5:lem14, riehl:4.5:construction-type-theoretic-ac]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.5, Lemma 4.5.14 and the unnumbered specialization that follows it; printed pp. 163–164, PDF pp. 183–184. Items: `riehl:4.5:lem14`, `riehl:4.5:construction-type-theoretic-ac`.

Paraphrase: for a composable pair `a : A → X`, `b : B → A` in a locally cartesian closed category, form `Δ_a Π_a b` with the counit component `ε : Δ_a Π_a b → b` of `Δ_a ⊣ Π_a` at `b`, and let `e` be the induced map over `Π_a b`. Then there is a natural isomorphism `Π_a Σ_b ≅ Σ_{Π_a b} Π_e ε^*` between functors on the slice over `B`, proved by Yoneda. Specializing to the evaluation diagram over `A → 1` yields, for a family `(C_{a,b})`, the natural isomorphism `Π_{a∈A} Σ_{b∈B} C_{a,b} ≅ Σ_{f ∈ B^A} Π_{a∈A} C_{a, f(a)}` — the type-theoretic axiom of choice, whose right-hand side names a Skolem function.

## Background

This is the categorical form of the distributivity of dependent products over dependent sums; its evaluation-diagram specialization is the "axiom of choice" that is *provable* in dependent type theory from the rules for `Π`, `Σ` and identity types. See [nLab: dependent product](https://ncatlab.org/nlab/show/dependent+product) and [nLab: type theoretic axiom of choice](https://ncatlab.org/nlab/show/type-theoretic+axiom+of+choice).

## Current state in the library

Absent, and unstatable as things stand.

- `rg -in 'skolem'` returns **0** hits tree-wide.
- No `Π` functor between slices exists (see the negative evidence recorded for the Beck–Chevalley item), so neither side of the isomorphism can be formed; and with the `Σ_f ⊣ Δ_f` adjunction commented out at `Construction/Slice/Pullback.v:121-127` there is no counit `ε` to build the statement from.
- Slices of slices are never constructed.
- A distinguishing check worth repeating, because an alias-only search would misfire: `Structure/Distributive.v:44-48` defines `Class Distributive` with exactly `distr_prod_coprod {x y z} : @Isomorphism C (x × (y + z)) (x × y + x × z)` and `distr_zero {x} : x × 0 ≅ 0` — distributivity of **product over coproduct**, an unrelated law. There is no `Π`-over-`Σ` statement anywhere.
- There is no polynomial-functor or container development in-tree, the usual alternative home for this result.
- The Skolem-shaped Coq lemma `(∀ a, {b & C a b}) → {f & ∀ a, C a (f a)}` is likewise nowhere stated, even in the `Instance/Coq` or `Instance/Sets` layers where it would be axiom-free. Note that `docs/AXIOMS.md:173-174` lists `dependent_choice` and `unique_choice` as **stdlib axioms enumerated by the audit**, not as anything the library proves or uses in the certified core — do not cite them as coverage.

## Work to be done

Suggested module: `Construction/Slice/Distributivity.v`, with the specialization in the same file or in `Instance/Sets/Choice.v`.

1. With `Σ`, `Δ`, `Π` and the two adjunctions available (see Dependencies), construct `ε : Δ_a Π_a b → b` and the induced `e : Δ_a Π_a b → Π_a B` over `Π_a b`.
2. State and prove `Π_a Σ_b ≅ Σ_{Π_a b} Π_e ε^*` as a natural isomorphism of functors `C/B ⟶ C/X`. Follow Riehl's Yoneda argument: compare the two sides by their representable characterizations, i.e. by the induced bijections on hom-sets out of an arbitrary object of `C/X`, each unfolded through the adjunctions. The in-tree donor for that style is `Theory/Coend/Yoneda.v` / `Theory/Hom/Yoneda.v` plus `Theory/Adjunction.v`'s transposition lemmas.
3. Specialize to the evaluation diagram `A × B ← A × B^A → B^A` over `A → 1`, where the evaluation map is the counit of `Δ_A ⊣ Π_A` at the projection, and derive the type-theoretic axiom of choice isomorphism.
4. Instantiate in `Sets` (or `Coq`) and check that the resulting statement really is `(∀ a, Σ b, C a b) ≅ (Σ f, ∀ a, C a (f a))` — and that the proof is **axiom-free**, since the choice function is constructed rather than chosen. Record the `Print Assumptions` output in the file header, as the library does for other axiom-sensitive results.

In-tree donors: `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Theory/Adjunction.v`, `Theory/Hom/Yoneda.v`, `Structure/Limit/Product.v` (`iprod`, `iprod_ump` at `:105`) for the indexed-product reading, `Instance/Sets.v`, `Instance/Coq.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.5 Lemma 4.5.14 and its specialization, with `≈` for all morphism equalities.
- [ ] The counit `ε` and the induced map `e` are constructed explicitly.
- [ ] The distributivity isomorphism is proved **natural**, not merely pointwise.
- [ ] The type-theoretic axiom of choice isomorphism is derived as a specialization, not proved independently.
- [ ] The `Sets` (or `Coq`) instantiation is exhibited and confirmed axiom-free by `Print Assumptions`, with the output quoted in the file header.
- [ ] The file header states explicitly that this is `Π`-over-`Σ` distributivity, distinct from `Structure/Distributive.v`'s product-over-coproduct law.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the distributivity isomorphism and the choice corollary.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Slice/Distributivity.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Slice.Distributivity. Print Assumptions pi_sigma_distributive." | coqtop -R . Category'
nix develop --command bash -c 'echo "Require Import Category.Construction.Slice.Distributivity. Print Assumptions type_theoretic_choice." | coqtop -R . Category'
nix develop --command make
```

Review items: the choice statement is derived from the lemma (not proved directly); the `Sets` instantiation uses no stdlib choice axiom.

## Dependencies
- Related (NOT blocking): **#657** also proposes to create `Instance/Sets/Choice.v`. It states the **categorical** axiom of choice (every epi in `Sets` splits) and projective objects; this issue states the **type-theoretic** axiom of choice, as the distributivity of the dependent product over the dependent sum in a locally cartesian closed category. Neither statement is derived from the other in tree and their dependency sets are disjoint, so no edge is asserted — but they target one file and must not be worked in the same parallel wave.

Depends on: #387 (MacLane IV.5: Base change is right adjoint to composition on slices) — supplies `Σ_a ⊣ Δ_a` and hence one side of the comparison.
Depends on: #730 (Awodey 9.7: The dependent product — the right adjoint to base change on slices) — supplies `Π_a` and the counit `ε` the statement is built from.
Depends on: #732 (Awodey 9.7: Locally cartesian closed categories, and the equivalence with slicewise cartesian closure) — the ambient hypothesis.

<!-- catalog: {"ids":["riehl:4.5:lem14","riehl:4.5:construction-type-theoretic-ac"],"deps":["#387","#730","#732"]} -->

---8<---

```yaml
title: "Riehl 4.6: Distributive laws for sets, and the corresponding cardinal arithmetic"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.6:cor5]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.6, Corollary 4.6.5; printed p. 167, PDF p. 187. Item: `riehl:4.6:cor5`.

Paraphrase, six clauses. For any sets there are natural isomorphisms `A × (B + C) ≅ (A × B) + (A × C)`, `(B × C)^A ≅ B^A × C^A` and `A^{B+C} ≅ A^B × A^C`; consequently, for any cardinals, `α × (β + γ) = (α × β) + (α × γ)`, `(β × γ)^α = β^α × γ^α` and `α^{β+γ} = α^β × α^γ`. The three set-level clauses are drawn as consequences of adjointness — `A × −` is a left adjoint, `(−)^A` is a right adjoint, and `A^{(−)} : Set^op ⟶ Set` is mutually right adjoint to itself — rather than proved from the universal properties directly.

## Background

The distributive and exponential laws of cardinal arithmetic are the decategorification of preservation properties of adjoints; the categorical proof is uniform where the set-theoretic one is case-by-case. See [Wikipedia: Cardinal number](https://en.wikipedia.org/wiki/Cardinal_number), whose "Cardinal arithmetic" section defines addition, multiplication and exponentiation exactly as the operations these isomorphisms decategorify, and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

The three set-level clauses are in-tree and in fact stronger than the book's (they hold in any bicartesian closed category); the three cardinal clauses and the derivation-from-adjointness are absent.

- `Structure/BiCCC.v:90` — `#[export] Program Instance prod_coprod_r {x y z : C} : x × (y + z) ≅ x × y + x × z`.
- `Structure/BiCCC.v:134` — `#[export] Program Instance exp_coprod {x y z : C} : x^(y + z) ≅ x^y × x^z`.
- `Structure/Cartesian/Closed.v:310` — `#[export] Program Instance exp_prod_r {x y z : C} : (y × z)^x ≅ y^x × z^x`.
- These land at `Sets` and `Coq`: `Instance/Sets/Cartesian.v:32`, `Instance/Sets/Cocartesian.v:28`, `Instance/Sets/Cartesian/Closed.v:38`, and `Instance/Coq.v:141/167/199`.
- `Theory/Algebra.v:79-87` carries the same three statements as **anonymous** `Goal … auto. Qed.` blocks — compiled corroboration, but not named reusable constants; use the `BiCCC`/`CCC` instances instead.

Missing: (1) the three cardinal-level equations entirely — there is no category of cardinals, no cardinality functor, and no machinery for converting a natural isomorphism in `Sets` into an identity in a discrete (skeletal) category; `rg -i 'cardinal|cardinality'` finds nothing but prose. (2) The isomorphisms are proved directly from the product/coproduct/exponential universal properties rather than derived from adjointness, so the third clause is **not** exhibited as "a mutual right adjoint carries coproducts to products"; the mutual self-adjointness of `A^{(−)}` on `Set^op` is nowhere stated.

## Work to be done

Suggested modules: `Instance/Cardinal.v` for the skeletal target and the cardinality functor; a short `Structure/BiCCC/Adjoint.v` (or additions to `Adjunction/Continuity.v`) for the derivation.

1. Re-derive the three set-level isomorphisms **from adjointness**, so that the corollary reads as Riehl states it: exhibit `A × − ⊣ (−)^A` as an `Adjunction` (currently only `exp_iso` exists as a bare field — see the two-variable-adjunction issue), then apply `Adjunction/Continuity.v:223` `left_adjoint_preserves_colimits` and `:202` `right_adjoint_preserves_limits`. Keep the existing direct instances and prove they agree with the adjoint-derived ones.
2. State and prove that `A^{(−)} : Sets^op ⟶ Sets` is mutually right adjoint to itself, giving the third clause as "carries coproducts to products".
3. Build the cardinal layer: define `Card` as the skeleton of `Sets` restricted to isomorphisms (a discrete category whose objects are isomorphism classes), with a cardinality functor `|−| : Sets_iso ⟶ Card`. The skeleton machinery is the donor here; `Instance/FinSet.v` is the finite model to sanity-check against, where the three equations should compute.
4. Transport each of the three natural isomorphisms along `|−|` to obtain the three cardinal identities, stated as equalities of objects in the discrete category `Card` (this is where "natural isomorphism becomes identity" is discharged, and it is the only genuinely new proof obligation).
5. Sanity examples: check the finite instances compute by `eq_refl` in `Instance/FinSet.v`, in the spirit of `Instance/FinSet/Topos.v`'s `Pow 2 = 4`.

In-tree donors: `Structure/BiCCC.v`, `Structure/Cartesian/Closed.v`, `Adjunction/Continuity.v`, `Instance/Sets*.v`, `Instance/FinSet.v`, `Adjunction/Opposite.v` (for the self-adjointness on `Sets^op`).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.6 Corollary 4.6.5 (all six clauses), with `≈` for morphism equalities.
- [ ] Each of the three set-level isomorphisms is derived from an adjunction, and shown to agree with the existing direct `BiCCC`/`CCC` instance.
- [ ] `A^{(−)}` is proved mutually right adjoint to itself on `Sets^op`.
- [ ] A category of cardinals and a cardinality functor exist, and the three cardinal identities are proved.
- [ ] Finite instances compute (sanity `Example`s in the `Instance/FinSet` layer).
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond documented `Instance/`-layer allowances; the cardinal layer's axiom usage, if any, is recorded in docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for the three adjoint-derived isomorphisms and the three cardinal identities.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Cardinal.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Cardinal. Print Assumptions cardinal_exp_sum." | coqtop -R . Category'
nix develop --command make
```

Review items: the derivation really goes through adjointness (matching §4.6's proof) rather than re-proving the isomorphisms; the cardinal statements are equalities in a discrete category, not isomorphisms in disguise.

## Dependencies

Depends on: #374 (MacLane IV.4: Skeletons and skeletal categories) — supplies the skeleton construction the category of cardinals is built from.
Depends on: #238 (MacLane I.4: The skeleton equivalence between finite sets and finite ordinals) — the finite model against which the cardinal identities are sanity-checked.

<!-- catalog: {"ids":["riehl:4.6:cor5"],"deps":["#374","#238"]} -->

---8<---

```yaml
title: "Riehl 4.6: Adjoints preserve monomorphisms and epimorphisms, via the pullback characterization of a monomorphism"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.6:exvi]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.6, Exercise 4.6.vi; printed p. 172, PDF p. 192. Item: `riehl:4.6:exvi`.

Paraphrase: show that a morphism `f : x → y` is a monomorphism exactly when the square whose two parallel legs are the identity on `x` and whose other two legs are `f` is a pullback; conclude that right adjoints preserve monomorphisms and, dually, that left adjoints preserve epimorphisms.

## Background

Monicity is a limit condition, which is why it is inherited by any limit-preserving functor; the pullback square in question is the kernel pair of `f` being trivial. See [nLab: monomorphism](https://ncatlab.org/nlab/show/monomorphism), whose Properties section states exactly this pullback characterization, and [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Every ingredient is present; neither the characterization nor the conclusion is stated.

- `Theory/Morphisms.v:116` `Monic`, `:104` `Epic` — the morphism classes.
- `Theory/Morphisms/Stability.v:53` `IsPullback` — the apex-pinned pullback predicate the characterization needs.
- `Structure/Regular.v:46` `kernel_pair` — the kernel pair, whose triviality is the content of the square.
- `Adjunction/Continuity.v:202` `right_adjoint_preserves_limits : PreservesAllLimits U` and `:223` `left_adjoint_preserves_colimits` — RAPL/LAPC, the second half of the exercise's conclusion.

Three near-misses that are **not** the exercise, each verified at its cited line:
- `Theory/Morphisms/Stability.v:226` `monic_pullback_stable` says monos are *stable under* pullback — a different fact.
- `Theory/Subobject/Functor.v:127` `is_pullback_along_id` is the pullback of an *identity* along a mono `m`, with no monicity hypothesis or conclusion.
- `Theory/Adjunction.v:311` `adj_monic` is a claim about the *transpose* under a faithful `F`.

No lemma anywhere says a right adjoint (or any limit-preserving functor) preserves monomorphisms, or that a left adjoint preserves epimorphisms.

## Work to be done

Suggested module: extend `Theory/Morphisms/Stability.v` with the characterization, and `Adjunction/Continuity.v` with the preservation corollaries.

1. Prove `monic_iff_pullback : Monic f ↔ IsPullback f f id id x` (with the orientation matching `Theory/Morphisms/Stability.v:53`'s apex-pinned form). Forward: monicity gives uniqueness of the mediating map; backward: two maps equalized by `f` induce a cone, and the mediator's two triangles force them equal.
2. Dualize to `epic_iff_pushout` (via `Construction/Opposite.v`, since `IsPullback` in `C^op` is the pushout condition — check whether a pushout predicate exists or must be introduced; if it must, state it as the `C^op` reading rather than duplicating the definition).
3. Conclude `right_adjoint_preserves_monic : Monic f → Monic (fmap[U] f)` from `right_adjoint_preserves_limits`, and dually `left_adjoint_preserves_epic`. Prefer the cone-level preservation vocabulary of `Structure/Limit/Preservation.v` if the apex-only `PreservesLimit` proves too weak — `Adjunction/Continuity.v` already works at the honest cone level.
4. State the more general corollary the argument actually gives: **any** limit-preserving functor preserves monomorphisms. That is the reusable form, and it is what `Structure/Limit/Preservation.v` consumers will want.

In-tree donors: `Theory/Morphisms.v`, `Theory/Morphisms/Stability.v`, `Structure/Regular.v`, `Adjunction/Continuity.v`, `Structure/Limit/Preservation.v`, `Construction/Opposite.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.6 Exercise 4.6.vi, with `≈` for all morphism equalities.
- [ ] The biconditional `Monic f ↔ IsPullback …` is proved in **both** directions.
- [ ] The dual statement for epimorphisms is available (by `C^op`, without duplicating the definition).
- [ ] Both preservation corollaries are proved from the characterization plus RAPL/LAPC, not re-proved from scratch.
- [ ] The general form ("a limit-preserving functor preserves monomorphisms") is stated as the reusable lemma.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the characterization and both corollaries.
- [ ] New files registered in `_CoqProject` (if any are added).
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Theory/Morphisms/Stability.v
nix develop --command coqc -R . Category Adjunction/Continuity.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Morphisms.Stability. Print Assumptions monic_iff_pullback." | coqtop -R . Category'
nix develop --command bash -c 'echo "Require Import Category.Adjunction.Continuity. Print Assumptions right_adjoint_preserves_monic." | coqtop -R . Category'
nix develop --command make
```

Review items: the new lemma is distinguished in its comment from the existing `monic_pullback_stable` (stability, not characterization); the preservation results are corollaries of RAPL/LAPC.

## Dependencies

Depends on: #427 (MacLane V.4: Cone-level preservation of limits and continuous functors) — the preservation vocabulary the corollaries are stated over.

<!-- catalog: {"ids":["riehl:4.6:exvi"],"deps":["#427"]} -->

---8<---

```yaml
title: "Riehl 4.6: Cat is not locally cartesian closed"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.6:exvii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.6, Exercise 4.6.vii; printed p. 172, PDF p. 192. Item: `riehl:4.6:exvii`.

Paraphrase: show that the category of small categories is not locally cartesian closed, by exhibiting a base-change functor that fails to preserve colimits. Concretely, pull back along the functor from the walking arrow into the free composable pair that picks out the composite arrow, and show the resulting functor between slices does not preserve the displayed pushout of the two inclusions of the terminal category into the walking arrow.

## Background

`Cat` is cartesian closed (exponentials are functor categories) but **not** locally cartesian closed; pullback along a functor need not have a right adjoint. See [Wikipedia: Category of small categories](https://en.wikipedia.org/wiki/Category_of_small_categories), which states this among the 1-categorical properties, and [nLab: locally cartesian closed category](https://ncatlab.org/nlab/show/locally+cartesian+closed+category).

## Current state in the library

Neither the statement nor the machinery for the counterexample exists.

- There is no locally-cartesian-closed class, predicate or instance anywhere; `rg 'LCCC'` → 0 hits, and every occurrence of the phrase is a comment. One of them is directly relevant and is currently the library's only record of this fact: `Instance/Cat.v:129` reads "though Cat is not locally cartesian closed (Wikipedia, 'Category of small categories')" — a comment, hence not an assertion. (It is line-wrapped in the source, so a naive `rg` for the whole phrase misses it.)
- No dependent product `Π_f` exists (prose only at `Structure/Pullback.v:128`, `Construction/Slice.v:91`, `Construction/Slice/Pullback.v:37`).
- `Cat` is never given `HasPullbacks`, so `Star_Functor` cannot even be instantiated there.
- The counterexample's shapes are missing: there is no three-object category in the `Instance/` layer (`Theory/Metacategory.v:413` `Three` is an arrows-only metacategory demonstration with no functors relating it to `_2`), and no `d^1 : 2 ⟶ 3`.
- What `Cat` does have is the finite (co)limit fragment: `Instance/Cat/Cartesian.v:39` `Cat_Cartesian`, `Instance/Cat/Cocartesian.v:40` `Cat_Cocartesian`, `Instance/One.v:54` `Cat_Terminal`, `Instance/Zero.v:44` `Cat_Initial` — and nothing else: `rg -n -i 'limit|colimit|equalizer' Instance/Cat.v Instance/Cat/*.v` → 0 hits.

## Work to be done

Suggested module: `Instance/Cat/NotLCC.v`.

1. Build the ordinal categories `2` (the walking arrow) and `3` (the free composable pair) in the `Instance/` layer, and the functor `d^1 : 2 ⟶ 3` picking out the composite. If the ordinal family from the Riehl §4.1 chain-of-adjoints issue lands first, reuse it rather than hand-building; otherwise build just these two.
2. Give `Cat` pullbacks (at least along `d^1`), so that base change `Δ_{d^1} : Cat/3 ⟶ Cat/2` can be defined via `Construction/Slice/Pullback.v:67` `Star_Functor`.
3. Construct the pushout in `Cat/3` of the two inclusions `1 ↣ 2` (the legs `0` and `1`), computed in `Cat` and lifted to the slice.
4. Show `Δ_{d^1}` does not preserve it: compute both sides explicitly and exhibit a concrete difference (an object or morphism present in one and not the other). This is the mathematical content — an inequality of categories up to isomorphism — so it must be a proof, not an `Example`.
5. Conclude: since a left adjoint preserves all colimits (`Adjunction/Continuity.v:223`), `Δ_{d^1}` has no right adjoint, hence `Cat/3` is not cartesian closed and `Cat` is not locally cartesian closed. Update the comment at `Instance/Cat.v:129` to cite the theorem instead of Wikipedia.

In-tree donors: `Instance/Cat.v`, `Instance/Cat/Cartesian.v`, `Instance/Cat/Cocartesian.v`, `Instance/Two.v`, `Instance/One.v`, `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Adjunction/Continuity.v`, `Construction/Free/Quiver.v` (free categories on the linear quivers).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.6 Exercise 4.6.vii, with `≈` for all morphism equalities.
- [ ] The categories `2`, `3` and the functor `d^1` are constructed.
- [ ] `Cat` is given the pullbacks the base-change functor needs.
- [ ] The pushout in the slice is constructed and the failure of preservation is **proved**, with the concrete witness of the difference named.
- [ ] The conclusion "`Δ_{d^1}` has no right adjoint, so `Cat` is not locally cartesian closed" is a theorem.
- [ ] The Wikipedia-citing comment at `Instance/Cat.v:129` is replaced by a pointer to the theorem.
- [ ] No `Admitted` / `admit` / `Axiom` introduced beyond documented `Instance/`-layer allowances.
- [ ] `Print Assumptions` reported for the non-preservation theorem and the conclusion.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Cat/NotLCC.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Cat.NotLCC. Print Assumptions Cat_not_locally_cartesian_closed." | coqtop -R . Category'
nix develop --command make
```

Review items: the counterexample is the one §4.6 describes (pullback along the composite-picking functor `2 ⟶ 3`); the failure is proved rather than asserted from the literature.

## Dependencies

Depends on: #732 (Awodey 9.7: Locally cartesian closed categories, and the equivalence with slicewise cartesian closure) — supplies the predicate this issue refutes for `Cat`.
Depends on: #414 (MacLane V.1: Cat is small-complete) — supplies the pullbacks in `Cat` that base change requires.
Depends on: #338 (MacLane III.5: Cat has small coproducts) — the colimit side of the counterexample.
Depends on: #666 (Awodey 4.4: Finitely presented example categories — the walking isomorphism, Z/2Z, cyclic groups, and presentations of the category 3) — supplies the category `3` the counterexample is stated over.

<!-- catalog: {"ids":["riehl:4.6:exvii"],"deps":["#732","#414","#338","#666"]} -->

---8<---

```yaml
title: "Riehl 4.6: The essential image of a reflective subcategory, and its local objects"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.6:exx]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.6, Exercise 4.6.x; printed p. 173, PDF p. 193. Item: `riehl:4.6:exx`.

Paraphrase, three clauses. For a reflective subcategory inclusion with reflector `L` and unit `η`: (i) `η L = L η`, and these natural transformations are isomorphisms; (ii) an object `c` lies in the essential image of the inclusion — i.e. is isomorphic to an object of the subcategory — exactly when `η_c` is an isomorphism; (iii) the essential image consists precisely of the objects that are **local** for the class of morphisms inverted by `L`.

## Background

These three facts are what make a reflective subcategory the same thing as an idempotent monad and identify it with a localization: the essential image is the class of local objects, and the unit detects membership. See [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and [nLab: essential image](https://ncatlab.org/nlab/show/essential+image).

## Current state in the library

Fragments of all three clauses exist, none in the exercise's form.

- `Construction/Reflective/Idempotent.v:139` — `Definition join_iso_fmap_ret (x : C) (Hj : IsIsomorphism (@join C M _ x)) : fmap[M] (@ret C M _ x) ≈ @ret C M _ (M x)`. For the reflection monad `M := Incl ◯ reflector R`, this **is** `L η = η L` — but object-wise, under the hypothesis `IsIsomorphism (join x)`, never as an equality or invertibility of natural transformations.
- `Construction/Reflective/Idempotent.v:103` — `join_iso_ret_iso`, whose hypothesis is discharged for a reflection by `Reflective_IdempotentMonad` at `:198`.
- `Construction/Localization.v:184` — `Lemma unit_at_local_iso … : IsIsomorphism (unit …)`, the reflection unit at a `W`-local object.
- `Construction/Localization.v:241` — `Theorem reflector_inverts_W {a b : C} (w : a ~> b) (Hw : W a b w) : IsIsomorphism (fmap[Refl] w)`.

Gaps:
- (a) `rg -i 'essential image'` → **0** hits: the notion does not exist, so clause (ii) is not statable. The closest object is `MLocal_Subcategory` (`Construction/Reflective/Idempotent.v:224`), which *defines* the subcategory of an idempotent monad as `{x | IsIsomorphism (ret x)}` and shows it full reflective (`Idempotent_Reflective` at `:345`) — but nothing identifies that subcategory with a **given** reflective `D`, which is exactly the content of (ii).
- (b) Neither converse is proved: "`η_c` invertible ⇒ `c` is isomorphic to an object of `D`", and "`c` local ⇒ `c` in the essential image".
- (c) Clause (i) has no transformation-level form: no `η L ≈ L η` as an equation of natural transformations and no bundled `Isomorphism` witness.
- (d) Clause (iii) is **inverted** relative to the book: `Construction/Localization.v` *defines* `C_W W` by the `W`-locality condition (`WLocal` at `:129`) and then *hypothesizes* its reflectivity (`Context (R : Reflective (C_W W))` at `:231`), so the essential-image = local-objects identification is assumed rather than proved. `reflector_inverts_W` gives "`L` inverts `W`" but not the converse "`L f` invertible ⇒ `f ∈ W`", which the book's phrase "the class of morphisms inverted by `L`" requires.

Verifier observation, worth acting on inside this issue: `unit_at_local_iso` is headed "the reflection unit at a `W`-local object is an isomorphism", yet its proof never uses `W`-locality — it needs only fullness and the two triangle identities, so it holds verbatim for **any** full reflective subcategory. Generalizing it into `Construction/Reflective.v` would give the tree the unit-side companion of `reflective_counit_iso` for free, which is precisely the shape clauses (i) and (ii) need.

## Work to be done

Suggested modules: `Theory/EssentialImage.v` for the notion (if the Riehl §1.5 issue has not already landed it), and `Construction/Reflective/EssentialImage.v` for the three clauses.

1. Define the essential image of a functor as a full subcategory of the codomain spanned by the objects isomorphic to some `F c`. Reuse `Construction/Subcategory.v`.
2. Generalize `unit_at_local_iso` (`Construction/Localization.v:184`) to an arbitrary full reflective subcategory and move it to `Construction/Reflective.v`, next to `reflective_counit_iso` (`:92`). Update the two misleading comments flagged below.
3. Clause (i): state `η L ≈ L η` as an equation of natural transformations `L ⟹ L L` and prove both are isomorphisms, deriving the object-wise `join_iso_fmap_ret` as a corollary rather than the other way round.
4. Clause (ii): prove the biconditional `c ∈ essential image ↔ IsIsomorphism (η c)`. The `⇐` direction is where the work is; `MLocal_Subcategory` gives the shape of the argument but must be re-anchored to a given reflective subcategory.
5. Clause (iii): define the class `W_L` of morphisms inverted by `L`, prove the missing converse (`L f` invertible ⇒ `f ∈ W_L` — trivial for `W_L` so defined, so the real content is that `W_L` agrees with the class `Construction/Localization.v` takes as given), and prove that the essential image is exactly the class of `W_L`-local objects, thereby *proving* what `Construction/Localization.v:231` currently assumes.

In-tree donors: `Construction/Reflective.v` (`Reflective` at `:60`, `reflective_counit_iso` at `:92`), `Construction/Reflective/Idempotent.v`, `Construction/Localization.v`, `Construction/Localization/Universal.v` (`reflection_retract` at `:126`), `Construction/Subcategory.v`, `Theory/Equivalence.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.6 Exercise 4.6.x (all three clauses), with `≈` for all morphism equalities.
- [ ] The essential image is defined and used, not worked around.
- [ ] Clause (i) is stated at the level of natural transformations, with the object-wise lemma derived from it.
- [ ] Clause (ii) is proved in both directions.
- [ ] Clause (iii) is **proved** for a given reflective subcategory, replacing the hypothesis currently carried at `Construction/Localization.v:231`.
- [ ] `unit_at_local_iso` is generalized to any full reflective subcategory and relocated beside `reflective_counit_iso`.
- [ ] LIBRARY-DEFECT fixed while here: `Construction/Localization.v:179-180` (repeated in the file header at `:42`) calls `unit_at_local_iso` "the dual, for the unit, of `reflective_counit_iso`". It is **not** a dual — duality in this library is `C^op`-based and the unit-side dual would be the statement for a *coreflective* subcategory; both statements here concern the same reflective subcategory, and the proof literally derives this one from the counit, taking `fmap[Incl] (counit s)` as the inverse. Reword to "consequence of" / "companion to".
- [ ] LIBRARY-DEFECT fixed while here: `Construction/Localization/Universal.v:64` — the header's PROOF SHAPE bullet claims `reflection_counit_is_iso` is "reproved transparently so its inverse is available to later coherence proofs", but the lemma at `:110` ends with `Qed.` at `:121`, i.e. **opaque**; the inline comment at `:108-109` says the opposite (the inverse is recovered by destructing the opaque record). Correct the header.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for all three clauses.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Reflective/EssentialImage.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Reflective.EssentialImage. Print Assumptions essential_image_iff_unit_iso." | coqtop -R . Category'
nix develop --command grep -n 'dual' Construction/Localization.v
nix develop --command make
```

Review items: clause (iii) is proved rather than assumed; the two header corrections are applied; the generalized unit lemma no longer mentions `W`-locality in its hypotheses.

## Dependencies

Depends on: #918 (Riehl 1.5: The essential image of a functor, and a fully faithful functor as an equivalence onto it) — supplies the essential-image notion clause (ii) is stated with.
Depends on: #370 (MacLane IV.3: Concrete reflective and coreflective subcategories) — the reflective-subcategory setting.

<!-- catalog: {"ids":["riehl:4.6:exx"],"deps":["#918","#370"]} -->

---8<---

```yaml
title: "Riehl 4.7: Locally presentable categories, accessible functors, and their adjoint functor theorem"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.7:def16, riehl:4.7:thm17]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd ed.), §4.7, Definition 4.7.16 and Theorem 4.7.17; printed p. 179, PDF p. 199. Items: `riehl:4.7:def16`, `riehl:4.7:thm17`.

Paraphrase: for a regular cardinal `κ` (an infinite cardinal such that a union of fewer than `κ` sets each of cardinality less than `κ` again has cardinality less than `κ`), a locally small category is **locally κ-presentable** when it is cocomplete and has a *set* of objects such that every object is a colimit of a diagram valued in the full subcategory they span, and each of those objects is κ-presentable (its covariant hom-functor preserves κ-filtered colimits); a functor is **accessible** when it preserves κ-filtered colimits for some regular `κ`. Theorem 4.7.17: a functor between locally presentable categories admits a right adjoint if and only if it is cocontinuous, and admits a left adjoint if and only if it is continuous and accessible. Riehl gives only a proof sketch, deferring to Adámek–Rosický: the second clause follows from the General Adjoint Functor Theorem because an accessible functor satisfies the solution-set condition, and the first is dual.

## Background

Local presentability is the standard smallness hypothesis under which adjoint existence becomes a purely (co)continuity condition — the practical form of the adjoint functor theorems. See [nLab: locally presentable category](https://ncatlab.org/nlab/show/locally+presentable+category), [nLab: accessible functor](https://ncatlab.org/nlab/show/accessible+functor), and the "For locally presentable categories" section of [nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library

Absent; and the vocabulary the definition needs does not exist.

- Blind searches for *presentable*, *locally finitely presentable*, *accessible*, *filtered*, *κ-filtered*, *directed colimit*, *regular cardinal*, *compact object*, *Ind-completion* and *dense generator* found no definition anywhere. `rg -i filtered` returns a single unrelated hit (`Comonad/CoKleisli.v:81`, a filtered *stream*), and there is no notion of cardinal beyond `Theory/Metacategory.v`'s finite counter.
- **Correction to the Phase-C negative log, which an implementer must not copy**: `rg -i 'presentable'` **does** hit `Adjunction/GAFT.v:124` ("a biconditional between locally presentable categories") and `rg -i 'accessible'` **does** hit `Adjunction/GAFT.v:125` ("has a left adjoint exactly when it is accessible and preserves small limits"). Both are header-essay prose in `Adjunction/GAFT.v:122-127` — the only in-tree trace of the Adámek–Rosický sharpening — not definitions. The verdict is unaffected, but the log lines claiming zero hits are false as written. (`Construction/Free.v:88` says "finitely presented category", a different phrase.)
- Disambiguation, verified: `Theory/Adamek.v` is the **initial-algebra** Adámek theorem (`adamek : AdamekData → Initial (FAlg F)`), unrelated to the presentable adjoint functor theorem. `Structure/Limit/Preservation.v` names cocontinuity vocabulary but proves no adjoint-existence result.
- The consuming end is in good shape and is the intended donor: `Adjunction/GAFT.v:241` `Theorem GAFT (U : C ⟶ D) (comp : @Complete C) (cont : @PreservesImageLimit C D U) (sols : ∀ d, SolutionSet U d) : { F : D ⟶ C & F ⊣ U }` with `Record SolutionSet` at `:159`. Clause (ii) of Theorem 4.7.17 is exactly "accessible ⇒ `SolutionSet`" plus this theorem.

## Work to be done

Suggested modules: `Theory/Presentable.v` (regular cardinals, κ-filtered categories, κ-presentable objects, `LocallyPresentable`, `AccessibleFunctor`), `Adjunction/Presentable.v` (the theorem).

1. Define regular cardinals in whatever form the library can support. The honest options are (a) a `Type`-level "κ-small" predicate on index types closed under the required unions, taken as data — matching how `Adjunction/SAFT.v` packages well-poweredness as `SubobjectIndex` data rather than deriving it; or (b) restricting to `κ = ω` (locally finitely presentable) as a first, fully constructive instalment. Whichever is chosen, say so in the file header, as `Adjunction/SAFT.v:52-90` does for its own hypothesis packaging.
2. Define κ-filtered categories and κ-filtered colimits.
3. Define a κ-presentable object (`C(x, −)` preserves κ-filtered colimits) and `LocallyPresentable C` (cocomplete + a set of κ-presentable objects generating every object as a κ-filtered colimit).
4. Define `AccessibleFunctor F` (preserves κ-filtered colimits for some regular κ).
5. Prove `accessible_SolutionSet : LocallyPresentable C → AccessibleFunctor U → ∀ d, SolutionSet U d`, then obtain clause (ii) by feeding `Adjunction/GAFT.v:241` `GAFT` — note that GAFT's continuity hypothesis is the cone-level `PreservesImageLimit`, which is the correct (leaner) reading and should be used rather than the apex-only `PreservesLimit`.
6. Clause (i) (cocontinuous ⇒ right adjoint) is the dual; obtain it through `Adjunction/Opposite.v:34` `Opposite_Adjunction` if the dual of GAFT is available, otherwise state it over `C^op` directly.
7. Record honestly in the header which of the two clauses is proved and which (if either) remains conditional, and update `docs/INHABITATION.md` if the theorem ships without a concrete in-tree locally presentable category. `Adjunction/GAFT.v:122-127`'s prose paragraph should be replaced by a cross-reference to the new theorem.

In-tree donors: `Adjunction/GAFT.v`, `Adjunction/SAFT.v` (for the "package smallness as data" idiom), `Structure/Limit/Preservation.v`, `Structure/Colimit.v`, `Theory/WeaklyInitial.v`, `Construction/Comma/Limit.v`, `Adjunction/Opposite.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.7 Definition 4.7.16 and Theorem 4.7.17, with `≈` for all morphism equalities.
- [ ] Regular cardinals / κ-smallness are defined, with the chosen encoding and its limitations disclosed in the file header.
- [ ] κ-filtered categories, κ-presentable objects, `LocallyPresentable` and `AccessibleFunctor` are all defined.
- [ ] `accessible ⇒ SolutionSet` is **proved**, not assumed — this is the mathematical content of clause (ii).
- [ ] Clause (ii) is obtained by applying the in-tree `GAFT` rather than re-proving it.
- [ ] Clause (i) is proved or explicitly scoped out with a reason.
- [ ] The header essay at `Adjunction/GAFT.v:122-127` is updated to cross-reference the theorem instead of describing it as external.
- [ ] `docs/INHABITATION.md` records whether a concrete locally presentable category is exhibited in-tree.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` closed for the definitions and the theorem.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this extends the adjoint-functor-theorem entry.

## Verification

```sh
nix develop --command coqc -R . Category Theory/Presentable.v
nix develop --command coqc -R . Category Adjunction/Presentable.v
nix develop --command bash -c 'echo "Require Import Category.Adjunction.Presentable. Print Assumptions presentable_left_adjoint." | coqtop -R . Category'
nix develop --command make && nix build .#category-theory_8_20
```

Review items: the accessibility ⇒ solution-set step is proved rather than hypothesized; the continuity hypothesis is the cone-level `PreservesImageLimit`; the header discloses the encoding of regular cardinals.

## Dependencies

Depends on: #559 (MacLane IX.1: Filtered categories and filtered colimits) — supplies the filtered-colimit vocabulary the κ-filtered notion generalizes.
Depends on: #437 (MacLane V.6: The representability theorem) — the representability face of the same adjoint-existence machinery, which this theorem's sketch invokes.

<!-- catalog: {"ids":["riehl:4.7:def16","riehl:4.7:thm17"],"deps":["#559","#437"]} -->

---8<---

```yaml
title: "Riehl 4.1: Induction, restriction and coinduction along a group homomorphism"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.1:example11]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition, author's recompiled copy — **not** Dover pagination), §4.1 "Adjoint functors", Example 4.1.11. Printed p. 136; PDF p. 156. Item: `riehl:4.1:example11`.

Paraphrase: for a group homomorphism `φ : H → G` and a complete and cocomplete category `C`, restriction along `φ` between the two functor categories `C^{BG} ⟶ C^{BH}` (deloopings of the groups regarded as one-object categories) admits both a left adjoint, called induction, and a right adjoint, called coinduction — an adjoint triple `ind ⊣ res ⊣ coind`. Taken over vector spaces this is the classical Frobenius reciprocity between representations of a subgroup and of the ambient group.

## Background

Restriction of a group action along a homomorphism is precomposition with a functor between one-object categories, so its two adjoints are the left and right Kan extensions along that functor; the `ind ⊣ res` half is the categorical form of Frobenius reciprocity. See [nLab: Frobenius reciprocity](https://ncatlab.org/nlab/show/Frobenius+reciprocity) and [nLab: induced representation](https://ncatlab.org/nlab/show/induced+representation).

## Current state in the library

The general shape is stated but never inhabited, and the concrete setting does not exist.

- `Theory/Kan/Extension.v:127` — `Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {| fobj := fun G => G ◯ F; … |}`. This **is** restriction along a functor, at full generality.
- `Theory/Kan/Extension.v:222` — `Class LeftKan := { Lan : [A, C] ⟶ [B, C]; lan_adjoint : Lan ⊣ Induced }`, and `:140` `Class RightKan := { Ran; ran_adjoint : Induced ⊣ Ran }`. These say exactly "restriction has a left adjoint" and "restriction has a right adjoint" over the same middle functor — but they are **hypothesis classes**: no theorem derives either from (co)completeness of `C`, no file assumes both at once, and neither has a concrete instance anywhere in the tree.
- No delooping of a group or monoid as a one-object category exists: the only delooping in the tree is `Theory/Bicategory/OneObject.v` (a monoidal category as a one-object bicategory). `Structure/Group.v:109`'s `GroupObject` is a group internal to a cartesian category, not a group presented as a category.
- No category of vector spaces or modules exists, so the representation-theoretic reading of the example is not expressible today.

Gap: the example's actual assertion — that restriction along a group homomorphism *admits* both adjoints — is nowhere proved, and its subject (a delooping) is nowhere constructed.

## Work to be done

Suggested modules: `Instance/Delooping/Restriction.v` (the functor `Bφ` and the triple) and `Instance/Sets/GSet.v` (the concrete instance).

1. Over the delooping of a group as a one-object category (#220), define `Bφ : BH ⟶ BG` for a group homomorphism `φ : H → G`, and `res φ := Induced Bφ : [BG, C] ⟶ [BH, C]`.
2. Supply `LeftKan`/`RightKan` instances at this shape from cocompleteness/completeness of `C` — the general existence result is #590; this issue's obligation is the instantiation, plus the observation that the index categories here are small and connected, so the pointwise formulas are coproduct/product-and-equalizer computations.
3. Assemble the triple `ind ⊣ res ⊣ coind` and, if #743 has landed, package it as an `AdjointTriple`.
4. Instantiate at `C := Sets`, giving `G`-sets and `H`-sets: induction is the quotient of `G × A` by the `H`-action and coinduction the set of `H`-equivariant maps `G → A`. This is the first concrete inhabitant of `LeftKan`/`RightKan` in the tree and should be flagged as such in the header.
5. State the `ind ⊣ res` half under the name Frobenius reciprocity, and record in the header that the `Vect_k` reading (representations) awaits a category of vector spaces (#258/#305) and is deliberately out of scope here — the categorical content is complete without it.

In-tree donors: `Theory/Kan/Extension.v` (`Induced`, `LeftKan`, `RightKan`), `Adjunction/Compose.v`, `Structure/Limit/Product.v` (indexed products for the pointwise formulas), `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Example 4.1.11 (paraphrased), with `≈` used for every morphism equality (never `=`).
- [ ] `Bφ` and `res φ` defined for an arbitrary group homomorphism, with functoriality proved.
- [ ] Both adjoints constructed, not assumed: `LeftKan`/`RightKan` instances at this shape, so the tree gains its first inhabitants of those classes.
- [ ] The triple exhibited as one datum, and the `ind ⊣ res` half named as Frobenius reciprocity.
- [ ] The concrete `G`-set instance built and shown to compute the expected induction/coinduction.
- [ ] The header states the `Vect_k` scope exclusion and why.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reports "Closed under the global context" for each principal artifact (or, for the `Sets` instance, enumerates the `Instance/`-layer stdlib axioms per docs/AXIOMS.md).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] docs/INHABITATION.md updated: the Kan-extension classes acquire their first witness.

## Verification

```sh
nix develop --command coqc -R . Category Instance/Delooping/Restriction.v
nix develop --command coqc -R . Category Instance/Sets/GSet.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Sets.GSet. Print Assumptions frobenius_reciprocity." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: the statement matches Riehl §4.1 Example 4.1.11 up to paraphrase; both adjoints are *constructed* from (co)completeness rather than assumed as class hypotheses; the `G`-set instance really inhabits `LeftKan`/`RightKan` and is not a bespoke re-derivation.

## Dependencies

Depends on: #590 (existence of Kan extensions from (co)completeness, and the global adjoint to precomposition — the source of both adjoints)
Depends on: #220 (delooping monoids and groups into one-object categories — the index categories `BH`, `BG`)

<!-- catalog: {"ids":["riehl:4.1:example11"],"deps":["#590","#220"]} -->

---8<---

```yaml
title: "Riehl 4.1: Adjoints to the vertex functor of quivers, and the question for graphs"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.1:exiii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition), §4.1 "Adjoint functors", Exercise 4.1.iii, clause (ii) and its trailing question. Printed p. 138; PDF p. 158. Item: `riehl:4.1:exiii` (clause (i) of the same exercise, on the objects functor of `Cat`, is recorded against #357).

Paraphrase: exhibit a left and a right adjoint to the vertex functor from quivers to sets, and decide whether the corresponding functor for undirected graphs admits a left or a right adjoint.

## Background

A quiver is a directed graph allowing loops and parallel edges; the vertex functor forgets all edges, and its adjoints are the edgeless and the codiscrete quiver on a set — the quiver analogue of the discrete/codiscrete adjoints of the objects functor on categories. See [nLab: quiver](https://ncatlab.org/nlab/show/quiver) and [nLab: free category](https://ncatlab.org/nlab/show/free+category).

## Current state in the library

Quivers are a first-class in-tree structure, but nothing forgets them to sets.

- `Construction/Free/Quiver.v:54` — `Class Quiver := { nodes : Type; edges : nodes → nodes → uedges; edgeset : ∀ X Y, Setoid (edges X Y) }`.
- `Construction/Free/Quiver.v:358` — `Instance QuiverCategory : Category` (the `Quiv` of the literature), with quiver homomorphisms at `:205` and their equivalence at `:219`.
- `Construction/Free/Quiver.v:412` — `Definition Forgetful : @Functor StrictCat QuiverCategory`, `:546` `FreeCatFunctor`, `:550` `FreeForgetfulAdjunction`. So the *free category on a quiver* adjunction is in place; the vertex functor `QuiverCategory ⟶ Sets` is not defined anywhere, and neither is any edgeless or codiscrete quiver construction.
- There is no category of undirected graphs in the tree at all (the `Graph` occurrences under `Instance/Parallel.v` and `Structure/Monoidal/*` are the parallel-pair shape and hypergraph vocabulary, not a graph category).

Gap: no functor `QuiverCategory ⟶ Sets`, no adjoint on either side, and no subject for the graph question.

## Work to be done

Suggested module: `Construction/Free/Quiver/Vertices.v` (a satellite of the existing quiver file).

1. Define the vertex functor `V : QuiverCategory ⟶ Sets`, sending a quiver to its nodes. `nodes` is a bare `Type`, so state in the header whether it is shipped to `Sets` with the equality setoid or the functor is instead built into `Coq`, and why the choice keeps the adjunctions honest.
2. Left adjoint: the **edgeless** quiver on a setoid (every edge setoid empty), with the transposition bijection — a quiver homomorphism out of it is exactly a function on vertices.
3. Right adjoint: the **codiscrete** quiver (exactly one edge for each ordered pair of vertices), with its transposition bijection.
4. Prove both adjunctions, giving the adjoint string `E ⊣ V ⊣ K`, and cross-reference #357: this is the quiver analogue of the discrete/codiscrete adjoints of the objects functor on categories, and the two developments should share vocabulary rather than duplicate it.
5. Settle the graph clause. Either construct a category of undirected graphs (symmetric, loop-permitting) and determine which of the two adjoints survives, or scope it out in the header with the concrete obstruction stated — but the file must answer Riehl's question rather than pass over it.

In-tree donors: `Construction/Free/Quiver.v`, `Instance/Sets.v`, `Theory/Adjunction.v`, `Theory/Universal/Arrow.v`, `Instance/Discrete.v` (the analogous discrete construction for categories).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.1 Exercise 4.1.iii clause (ii), with `≈` for every morphism equality (never `=`).
- [ ] `V : QuiverCategory ⟶ Sets` defined with its functor laws, and the codomain choice justified in the header.
- [ ] Both adjunctions proved as `Adjunction` instances (not merely as bijections of underlying sets).
- [ ] The graph question answered — either a proof or an explicit, argued obstruction recorded in the header.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reports closure for each adjunction (stdlib axioms of the `Instance/` layer enumerated per docs/AXIOMS.md if they appear).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Free/Quiver/Vertices.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Free.Quiver.Vertices. Print Assumptions edgeless_vertex_adjunction. Print Assumptions vertex_codiscrete_adjunction." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: the two adjunctions are stated over `QuiverCategory` as it already exists (no re-definition of quivers); the transposition bijections are proved, not assumed; the header answers the graph question.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:4.1:exiii"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 4.2: The six equivalent presentations of an adjunction, closed as one theorem"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.2:thm7]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition), §4.2 "The unit and counit as universal arrows", Theorem 4.2.7 with its displays (4.2.8) and (4.2.9). Printed pp. 140–142; PDF pp. 160–162. Item: `riehl:4.2:thm7`.

Paraphrase: for a **fixed** pair of functors in opposite directions, the data of a fully specified adjunction is encoded equivalently by any one of six things — a natural family of hom-set bijections; a unit and counit satisfying the triangle identities; a unit alone, provided a specified composite of maps of hom-sets is bijective; a counit alone, dually; initial objects in the comma categories under each object of the domain; terminal objects in the comma categories over each object of the codomain.

## Background

The equivalence of these presentations is what licenses moving freely between the hom-set, unit/counit and universal-arrow descriptions of an adjunction; the crucial subtlety is that all six are stated for the *same given pair* of functors, so no clause is allowed to construct its own adjoint. See [nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and [Wikipedia: adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors).

## Current state in the library

One leg is closed in both directions; three exist only forwards; and the two comma-category legs exist only in a form that builds a *new* left adjoint.

- Closed both ways, clauses (i) ⟺ (ii): `Adjunction/Natural/Transformation/Universal.v:42` `Adjunction_from_Transform (A : F ∹ U) : F ⊣ U` and `:84` `Adjunction_to_Transform {A : F ⊣ U} : F ∹ U`.
- Forward only, clauses (iii)/(iv): `Theory/Adjunction.v:264` `to_adj_unit {x y} (f : F x ~> y) : ⌊f⌋ ≈ fmap[U] f ∘ η` — display (4.2.8) as the transposition formula — and `:248` `adj_univ_impl {x y} (f : F x ~> y) (g : x ~> U y) : f ≈ ε ∘ fmap[F] g ↔ ⌊f⌋ ≈ g`. Both start from an existing `F ⊣ U`. There is **no** lemma taking a bare `η : Id ⟹ U ◯ F` with `F` and `U` both given, plus bijectivity of the induced map of hom-sets, and producing `F ⊣ U`.
- Clauses (v)/(vi): `Theory/Universal/Arrow.v:185` `LeftAdjointFunctorFromUniversalArrows` and `:214` `AdjunctionFromUniversalArrows` build the adjunction from comma-initial data — but they **construct their own left adjoint** rather than accepting the given `F`, so they do not close the cycle for a fixed pair. `Adjunction/GAFT.v:180` `GAFT_from_initials` has the same shape. The couniversal (terminal-arrow) form is entirely absent: `rg 'couniversal|RightAdjointFunctor|TerminalArrow'` returns 0 hits.
- `Theory/Adjunction.v:156` `Build_Adjunction'` accepts a family of hom-setoid isomorphisms not assumed natural plus the two to-side naturality conditions — a strictly weaker sufficiency statement, not one of the six clauses.

Gap: the theorem is nowhere stated as a single equivalence; three of the six presentations have no route back to `F ⊣ U` for a *given* `F`, and one has no in-tree formulation at all.

## Work to be done

Suggested module: `Adjunction/Presentations.v`.

1. Fix `F : C ⟶ D` and `U : D ⟶ C` and define the six presentations as predicates/records over that fixed pair, reusing what exists: the hom-set form is `Theory/Adjunction.v:130`'s class, the unit/counit form is `Adjunction/Natural/Transformation.v`'s `F ∹ U`.
2. Supply the two missing converses: from a bare unit `η` whose induced map `D(F c, d) → C(c, U d)` is bijective for all `c`, `d`, build the counit and the triangle identities — and dually from a bare counit. These are the load-bearing new lemmas; they must **not** route through `AdjunctionFromUniversalArrows`, whose left adjoint is constructed rather than given.
3. Give the comma-category clauses in the fixed-`F` form: `∀ c, Initial (=(c) ↓ U)` **whose initial object is `(F c, η_c)`**, and the dual `∀ d, Terminal (F ↓ =(d))`; introduce the couniversal-arrow vocabulary the tree lacks, preferably as `UniversalArrow` in the opposite category so that `Adjunction/Opposite.v` supplies the duality for free.
4. Close the cycle (i) ⇒ (ii) ⇒ (iii) ⇒ (v) ⇒ (i) and the dual cycle, and package the result as named round-trip theorems, so that consumers can move between presentations by a single lemma call.
5. Re-derive the existing constructors as corollaries — in particular check that `AdjunctionFromUniversalArrows`' left adjoint agrees with the given `F` up to natural isomorphism when both are present.

In-tree donors: `Theory/Adjunction.v`, `Adjunction/Natural/Transformation/Universal.v`, `Theory/Universal/Arrow.v`, `Construction/Comma.v`, `Adjunction/Opposite.v`, `Adjunction/Hom.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.2 Theorem 4.2.7 (paraphrased), with `≈` for every morphism equality (never `=`).
- [ ] All six presentations stated for a **fixed** pair `(F, U)`; no clause constructs its own adjoint.
- [ ] The two missing converses (bare unit with bijectivity ⇒ adjunction; bare counit dually) proved.
- [ ] The couniversal/terminal-arrow presentation introduced, with duality obtained through `Adjunction/Opposite.v` rather than by a parallel development.
- [ ] The equivalences delivered as named theorems, and the pre-existing constructors re-derived as corollaries.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reports "Closed under the global context" for each equivalence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (this is the reference statement of what an adjunction *is* in the library).

## Verification

```sh
nix develop --command coqc -R . Category Adjunction/Presentations.v
nix develop --command bash -c 'echo "Require Import Category.Adjunction.Presentations. Print Assumptions adjunction_presentations_equiv." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: every clause quantifies over the same given `F` and `U`; the unit-only and counit-only clauses are genuine converses, not restatements of `to_adj_unit`; the comma clauses identify the initial object as the unit component rather than merely asserting initiality of something.

## Dependencies

Depends on: #347 (determination of an adjunction by its counit and by couniversal arrows)
Depends on: #726 (each unit component is initial in the comma category — the direction the tree lacks)
Depends on: #348 (a left adjoint exists exactly when the hom-functors are representable — the packaging equivalence between the two universal-arrow presentations)

<!-- catalog: {"ids":["riehl:4.2:thm7"],"deps":["#347","#726","#348"]} -->

---8<---

```yaml
title: "Riehl 4.5: The composition laws of the slice adjoint triple, and the pushforward on morphisms"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:4.5:exii, riehl:4.5:exiii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition), §4.5 "Dependent products and sums", Exercises 4.5.ii and 4.5.iii. Printed pp. 164–165; PDF pp. 184–185. Items: `riehl:4.5:exii`, `riehl:4.5:exiii`.

Paraphrase: for a composable pair of morphisms in a locally cartesian closed category, show that composition of the dependent-sum functors holds on the nose, while the base-change functors and the dependent-product functors compose only up to canonical isomorphism (in the reversed order for base change). Then show that the dependent product of a morphism of the source slice — an object of a slice over the pushforward — agrees with the object obtained by regarding that morphism as an object of a slice, pulling back along the counit of the base-change/pushforward adjunction, and pushing forward.

## Background

These are the coherence laws that make the assignment of a slice to each object, with base change along each morphism, a pseudofunctor — the fibration-theoretic content behind the `Σ ⊣ Δ ⊣ Π` triple. See [nLab: base change](https://ncatlab.org/nlab/show/base+change) and [nLab: dependent product](https://ncatlab.org/nlab/show/dependent+product).

## Current state in the library

Two of the three functors exist and are never used; the third does not exist; no composition law is stated.

- `Construction/Slice/Pullback.v:50` — `Program Definition Bang_Functor (f : a ~> b) : @Slice C a ⟶ @Slice C b` (postcomposition, the `Σ_f`).
- `Construction/Slice/Pullback.v:67` — `Program Definition Star_Functor (f : c ~> a) : @Slice C a ⟶ @Slice C c` (pullback, the `Δ_f`), under a section-level `Hypothesis pullbacks`.
- Neither functor is consumed anywhere in the library: across the whole tree `Bang_Functor|Star_Functor` occurs only at those two definitions, the `f !` notation at `:60`, the commented-out adjunction stub at `:121-127`, and header prose. No composition law (`Σ_{gf} ≈ Σ_g ◯ Σ_f`, `Δ_{gf} ≅ Δ_f ◯ Δ_g`) is stated.
- There is no pushforward at all: `rg -i 'pushforward|dependent product|Π_f'` finds only prose and the commented `Production` stub, so Exercise 4.5.iii has no subject — there is no counit `ε : Δ_f Π_f b ⟶ b` to pull back along.
- `Construction/Displayed/Codomain.v:204` `codomain_cleaving` (with `:232` `codomain_cleaving_pullbacks`) gives base change in cloven-fibration form, and `Construction/Indexed.v` supplies the coherence pack an indexed-category presentation would need — but neither is instantiated at the codomain fibration, so the pseudofunctoriality these exercises ask for is nowhere available.

Gap: no composition law for any of the three functors, and no description of the pushforward's action on morphisms.

## Work to be done

Suggested module: `Construction/Slice/Composition.v` (beside the base-change and dependent-product files created by #730).

1. Prove `Σ_{g ∘ f} ≈ Σ_g ◯ Σ_f` as an equality of functors up to the library's functor equivalence — Riehl notes this one holds strictly, and the proof is associativity of composition, so state precisely in which sense "on the nose" survives the setoid presentation.
2. Prove `Δ_{g ∘ f} ≅ Δ_f ◯ Δ_g` (note the reversal) as a natural isomorphism, obtained from the pasting lemma for pullbacks — `Theory/Morphisms/Stability.v` already has the two-way pasting toolkit, so this should consume it rather than re-chase the squares.
3. Prove `Π_{g ∘ f} ≅ Π_g ◯ Π_f` by uniqueness of right adjoints, using the previous item and the adjunction of #730 — this is the cheap proof and it should be visible as such.
4. Prove Exercise 4.5.iii: for `u` a morphism of the source slice, identify `Π_f u` with the pullback of `u`, viewed as an object of the slice over its codomain, along the counit component of `Δ_f ⊣ Π_f`, pushed forward along the induced map. State the identification as an isomorphism in the appropriate slice, and derive from it the action of `Π_f` on morphisms (which is otherwise only implicit in the functor definition).
5. Record, in the header, the fibration reading: items 1–3 are exactly the pseudofunctor coherence for the codomain fibration, and note whether `Construction/Indexed.v`'s `IndexedCat` can be instantiated with them (if not, say what is missing — that note is itself useful).

In-tree donors: `Construction/Slice/Pullback.v`, `Theory/Morphisms/Stability.v` (pullback pasting), `Construction/Displayed/Codomain.v`, `Construction/Indexed.v`, `Theory/Adjunction.v` (uniqueness of adjoints).

## Definition of Done

- [ ] Statement fidelity to Riehl §4.5 Exercises 4.5.ii and 4.5.iii (paraphrased), with `≈` for every morphism equality (never `=`).
- [ ] All three composition laws proved, each in the strength Riehl claims (strict for `Σ`, canonical isomorphism for `Δ` and `Π`), with the reversal for `Δ` explicit.
- [ ] The `Π` law obtained from uniqueness of adjoints rather than by an independent construction.
- [ ] Exercise 4.5.iii proved as a stated isomorphism, and the action of `Π_f` on morphisms recorded as a usable lemma.
- [ ] The header records the pseudofunctor/indexed-category reading and the status of an `IndexedCat` instantiation.
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reports "Closed under the global context" for each composition law.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Slice/Composition.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Slice.Composition. Print Assumptions Pi_compose_iso. Print Assumptions Star_compose_iso." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: the `Δ` law composes in the reversed order and is proved from pullback pasting, not re-derived; the `Π` law cites uniqueness of adjoints; Exercise 4.5.iii is an isomorphism in a named slice, not a diagram sketch in a comment.

## Dependencies

Depends on: #730 (the dependent product and the two slice adjunctions `Σ_f ⊣ Δ_f ⊣ Π_f` — without them none of these statements has a subject)
Depends on: #732 (locally cartesian closed categories — the ambient hypothesis of both exercises)

<!-- catalog: {"ids":["riehl:4.5:exii","riehl:4.5:exiii"],"deps":["#730","#732"]} -->

---8<---

```yaml
title: "Riehl 4.6: The nerve and the homotopy category — Cat as a reflective subcategory of simplicial sets, and the cocompleteness of Cat"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:4.6:example13, riehl:4.6:cor15]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context* (2nd edition), §4.6 "Adjoint functors and limits", Example 4.6.13 clause (vi) (printed pp. 170–171; PDF pp. 190–191) and Corollary 4.6.15 (printed p. 171; PDF p. 191), the cocompleteness half. Items: `riehl:4.6:example13`, `riehl:4.6:cor15`.

Paraphrase: the nerve — the restricted Yoneda embedding along the inclusion of the simplex category into categories, whose `n`-simplices are the functors from the `n`-th ordinal — is fully faithful and has a left adjoint, the homotopy-category functor, computed as the free category on the underlying reflexive quiver of the 1-truncation modulo the relations imposed by the 2-simplices; the counit is an isomorphism, so categories form a reflective subcategory of simplicial sets. Since simplicial sets are complete and cocomplete with (co)limits computed pointwise, categories inherit limits and acquire colimits by applying the reflector.

## Background

The nerve/homotopy-category adjunction is the standard bridge between category theory and simplicial homotopy theory, and it is the cheapest route to cocompleteness of the category of small categories — colimits of categories are hard to build directly but easy to obtain by reflecting a pointwise colimit of simplicial sets. See [nLab: nerve](https://ncatlab.org/nlab/show/nerve) and [nLab: simplicial set](https://ncatlab.org/nlab/show/simplicial+set).

## Current state in the library

Neither the simplicial side nor the conclusion exists; the two ingredients of the reflector do.

- No simplex category and no simplicial sets exist in the tree (both are filed obligations: #225, #515), and no nerve functor (#621 owns it).
- `Cat` carries only the four finite (co)limits: `Instance/Cat/Cartesian.v:39` `Cat_Cartesian`, `Instance/Cat/Cocartesian.v:40` `Cat_Cocartesian`, `Instance/One.v:54` `Cat_Terminal`, `Instance/Zero.v:44` `Cat_Initial`. Neither `Complete Cat` nor `Cocomplete Cat` is ever asserted — `rg 'Complete|Cocomplete'` finds those predicates (`Structure/Complete.v:115,119`) only as **hypotheses**, in `Adjunction/GAFT.v`, `Adjunction/SAFT.v`, `Construction/Comma/Limit.v` and `Theory/Adamek/Corollaries.v`. There are no equalizers, coequalizers or small (co)products in `Cat`.
- The reflector's two ingredients are in place and unused for this purpose: `Construction/Free/Quiver.v` builds the free category on a quiver with its universal property (`:518`, `:546`, `:550`), and `Construction/Quotient.v` provides generic hom-congruence quotients — exactly "free category on the 1-truncation, modulo relations from the 2-simplices".
- No reflective subcategory in the tree has a concrete witness, and no transfer of colimits along a reflection exists (`rg -i 'reflective.*colimit'` → 0 hits).

Gap: the adjunction, the reflectivity, and both halves of the corollary are absent; the completeness half is separately filed (#414).

## Work to be done

Suggested modules: `Construction/Nerve/Homotopy.v` (the left adjoint and the adjunction) and `Instance/Cat/Cocomplete.v` (the corollary).

1. Over the nerve of #621, define the homotopy-category functor: take the free category on the reflexive quiver given by the 0- and 1-simplices (donor `Construction/Free/Quiver.v`), then quotient by the congruence generated by the 2-simplices (donor `Construction/Quotient.v`), and prove functoriality.
2. Prove `ho ⊣ N` — the transposition bijection between simplicial maps into a nerve and functors out of the homotopy category — preferably through the universal properties of the free category and the quotient, so the proof is two universal properties composed rather than a simplicial computation.
3. Prove `N` fully faithful and the counit `ho N C ≅ C` an isomorphism, hence `Cat` reflective in simplicial sets (packaged with `Construction/Reflective.v`'s `Reflective`, giving the tree its first concrete reflective subcategory — coordinate with #370, which supplies others).
4. Derive the corollary: with simplicial sets cocomplete pointwise (from cocompleteness of `Sets`, #329, via pointwise colimits in a functor category, #715), transfer along the reflection (#434) to obtain `Cocomplete Cat`; state it in the `Structure/Complete.v` vocabulary so it discharges the hypotheses that `Adjunction/GAFT.v` and friends currently demand of their callers.
5. Record in the header how this relates to the direct route: `Complete Cat` is #414's products-and-equalizers construction, and this issue supplies the colimit half by reflection, as Riehl does. Note the universe discipline the same way `Structure/Complete.v:30-40` does.

In-tree donors: `Construction/Free/Quiver.v`, `Construction/Quotient.v`, `Construction/Reflective.v`, `Instance/Cat.v`, `Instance/Fun.v`, `Structure/Complete.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §4.6 Example 4.6.13(vi) and Corollary 4.6.15 (paraphrased), with `≈` for every morphism equality (never `=`).
- [ ] `ho` constructed from the free category on the 1-truncation modulo the 2-simplex relations, with functoriality proved.
- [ ] `ho ⊣ N` proved as an `Adjunction`, with the transposition derived from the two universal properties.
- [ ] `N` proved fully faithful and the counit proved invertible; the reflection packaged as a `Reflective` instance (the library's first concrete one, or coordinated with #370's).
- [ ] `Cocomplete Cat` proved by transfer along the reflection, in the `Structure/Complete.v` vocabulary, with the universe constraint documented in the header.
- [ ] The header states the division of labour with #414 (completeness) and #434 (the transfer principle).
- [ ] No `Admitted` / `admit` / `Axiom` introduced.
- [ ] `Print Assumptions` reported for `ho`, the adjunction, and `Cocomplete Cat` (stdlib axioms of the `Instance/` layer enumerated per docs/AXIOMS.md if they appear).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 and 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and docs/INHABITATION.md updated — flagship-level: the first nerve/homotopy-category bridge and the first cocompleteness result for `Cat`.

## Verification

```sh
nix develop --command coqc -R . Category Construction/Nerve/Homotopy.v
nix develop --command coqc -R . Category Instance/Cat/Cocomplete.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Cat.Cocomplete. Print Assumptions Cat_Cocomplete." | coqtop -R . Category'
nix develop --command make
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
nix develop --command make todo
```

Review items: `ho` is built from the existing free-category and quotient machinery rather than re-implemented; the counit isomorphism is proved, not assumed; the cocompleteness proof really goes through the reflection (so it is Riehl's argument) and not through an unrelated direct construction.

## Dependencies

Depends on: #621 (the nerve of a category as a simplicial set — the right adjoint)
Depends on: #515 (simplicial sets and simplicial objects — the ambient category)
Depends on: #434 (a full reflective subcategory of a cocomplete category is cocomplete — the transfer principle)
Depends on: #414 (`Cat` is small-complete — the other half of Corollary 4.6.15)

<!-- catalog: {"ids":["riehl:4.6:example13","riehl:4.6:cor15"],"deps":["#621","#515","#434","#414"]} -->

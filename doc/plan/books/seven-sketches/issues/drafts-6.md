```yaml
title: "Seven Sketches 6.2.1: Deciding initiality in small concrete categories"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:6.2.1:ex6.3, 7sketches:6.2.1:example6.5, 7sketches:6.2.1:ex6.6]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.1, printed p. 185 (PDF p. 197). Items `7sketches:6.2.1:ex6.3` (the zero- and two-initial-object cases only; the one-initial-object case is already filed), `7sketches:6.2.1:example6.5`, `7sketches:6.2.1:ex6.6`.

## Background

An initial object admits exactly one morphism to every object; whether one exists is a genuine question about a category, and the book's three probes — two-element preorders, a two-object category with a parallel pair of arrows, and free categories on small graphs — exhibit categories with none, with one, and with two. See the nLab on [initial object](https://ncatlab.org/nlab/show/initial+object) and Wikipedia on [initial and terminal objects](https://en.wikipedia.org/wiki/Initial_and_terminal_objects).

## Current state in the library

The carriers are all in-tree; the verdicts are not, and the library has never once written down a *negative* initiality claim.

- `Instance/Parallel.v:80` builds exactly the book's two-object category — `Parallel : Category` over `Inductive ParObj := ParX | ParY` with `hom x y := ∃ b : bool, ParHom b x y` and `equiv f g := ``f = ``g``, i.e. two tag-distinguished parallel non-identity arrows. One of the book's two argument halves is already a named lemma: `ParHom_Y_X_absurd` (`Instance/Parallel.v:61`) says the hom-set `ParY ~> ParX` is empty. The other half — that the two arrows `ParX ~> ParY` are inequivalent, which is decidable definitionally because hom equivalence is equality of the boolean tag — is not recorded, and the file never mentions `Initial` or `Terminal` at all.
- `Instance/Two/Discrete.v` contains `Two_Discrete` plus `TwoDHom_X_Y_absurd` / `TwoDHom_Y_X_absurd` and nothing else; `Instance/Two/Monoidal.v:98` has `Two_Terminal` but there is no `Two_Initial`. The codiscrete (indiscrete) two-element preorder — the carrier for the two-initial-objects case — has no in-tree home at all: `Structure/Discrete.v:23-24` promises "the dual (codiscrete / indiscrete) construction is the further right adjoint" and no construction follows.
- `Construction/Free/Quiver.v:54` (`Quiver`), `:431` (`FreeOnQuiver : Category`) and `:550` (`FreeForgetfulAdjunction`) give the free-category-on-a-graph construction in full, but nothing anywhere concerns initial objects of `FreeOnQuiver`. **Phase-D correction to the coverage record:** Phase C wrote that the free category on the one-vertex-one-loop graph "is not built as a category anywhere"; that is wrong — `Test/Issue138.v:87-96` builds exactly it (`B138_loop`, `FreeOnQuiver B138_loop`, and an `eq_refl` `Example` on its object type), so that graph already has a carrier to reason about.
- There are thirteen `Initial` instances in the tree and every one is a positive existence result. **Phase-D correction:** the coverage record's original wording, that "the library has no way to state that a category has no initial object", overreached — `@Initial C → False` is perfectly expressible; the library simply never writes it. `Structure/Initial.v:36` states the uniqueness fact only as background prose.

## Work to be done

Introduce the negative idiom once and use it three times.

1. In `Instance/Parallel.v` (extend): `ParOne_neq_ParTwo` — the two arrows `ParX ~> ParY` are not `≈` (immediate from the boolean tag) — and `Parallel_no_Initial : @Initial Parallel → False`, discharging the `ParX` case from the first lemma and the `ParY` case from the existing `ParHom_Y_X_absurd`.
2. In `Instance/Two/Discrete.v` (extend): `Two_Discrete_no_Initial : @Initial Two_Discrete → False`, from the two hom-emptiness lemmas already there.
3. New `Instance/Two/Codiscrete.v`: the two-element codiscrete preorder (a thin category on two objects with a unique arrow in each direction), filling the construction `Structure/Discrete.v:23-24` announces; prove that *both* objects are initial, giving the two-initial-objects case. This is the natural place to also give the general codiscrete construction on any type, since the header already advertises it.
4. New `Construction/Free/Quiver/Initial.v`: the four verdicts of the exercise for `FreeOnQuiver` — the one-vertex graph (initial), the three-vertex path `a → b → c` (initial, the source), two isolated vertices (none), and one vertex with a loop (none, because the endo-hom-set is the path monoid on one generator and so is not a singleton). Reuse `Test/Issue138.v`'s `B138_loop` for the fourth.

In-tree donors: `Instance/Parallel.v`, `Instance/Two/Discrete.v`, `Instance/Two/Monoidal.v` (`Two_Terminal` as the shape template), `Structure/Initial.v`, `Construction/Free/Quiver.v`, `Test/Issue138.v`, `Instance/One.v` (`_1`, for the one-vertex case).

## Definition of Done

- [ ] A reusable `@Initial C → False` idiom is established, with `Parallel`, `Two_Discrete`, and two of the four free categories as instances.
- [ ] `ParOne_neq_ParTwo` proved, so both halves of the book's argument for `Parallel` are recorded.
- [ ] The codiscrete two-element preorder is constructed and both of its objects are shown initial, closing the promise at `Structure/Discrete.v:23-24`.
- [ ] All four free-category verdicts of Exercise 6.6 proved.
- [ ] Statement fidelity to Seven Sketches §6.2.1 (printed p. 185); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Two/Codiscrete.v
coqc -R . Category Construction/Free/Quiver/Initial.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Parallel_no_Initial.
Print Assumptions Two_Discrete_no_Initial.
```
Reviewer: statement matches Seven Sketches §6.2.1 (printed p. 185) — in particular that Example 6.5's argument uses *both* failure reasons (two arrows one way, none the other), not just the empty hom-set.

## Dependencies

Depends on: #756 — the remaining case of Exercise 6.3, the two-element linear order `_2` with exactly one initial object, is that issue's `Initial` structure on `_2`.

<!-- catalog: {"ids":["7sketches:6.2.1:ex6.3","7sketches:6.2.1:example6.5","7sketches:6.2.1:ex6.6"],"deps":["#756"]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.3: Elementary pushout calculus — pushouts along isomorphisms, discrete categories, and a collapsing pushout in Set"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.3:example6.23, 7sketches:6.2.3:ex6.24, 7sketches:6.2.3:example6.29]
deps_item_ids: [7sketches:6.2.1:example6.5]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.3, printed pp. 189–190 (PDF pp. 201–203). Items `7sketches:6.2.3:example6.23`, `7sketches:6.2.3:ex6.24`, `7sketches:6.2.3:example6.29`.

## Background

A pushout glues two objects along a common sub-object; three basic facts about the construction are that it is invariant under replacing the span's legs by isomorphisms, that it exists trivially in a discrete category, and that in Set it can collapse an infinite diagram to a single point. See the nLab on [pushout](https://ncatlab.org/nlab/show/pushout) and Wikipedia on [pushouts in category theory](https://en.wikipedia.org/wiki/Pushout_(category_theory)).

## Current state in the library

`Structure/Pushout.v` (174 lines) supplies the whole elementary API — `IsPushout` (defined as `@Pullback (C^op) …` at `:47`), `pushout_apex`, `pushout_in1`, `pushout_in2`, `pushout_commutes`, `pushout_ump`, `pushout_med`, `pushout_med_in1`, `pushout_med_in2`, `pushout_med_unique`, `pushout_med_eq`, and `HasPushouts`. None of the three items is stated.

- **Pushout along isomorphisms.** No in-tree lemma builds a pushout square out of two isomorphisms. The two nearest results are both strictly weaker and in the wrong direction. `Construction/Cospan/Double.v:275-288` and `:327` (with the right-hand mirror at `:347`/`:389`) prove `pushout_apex PL ≅ cospan_apex h` where `PL : IsPushout (cospan_in2 h) (cospan_in1 (cospan_id b))` — i.e. only the degenerate `i = id` case, only for spans whose legs are cospan legs, and derived from an *assumed* chosen pushout rather than constructing one. `Theory/Morphisms/Stability.v:264` `iso_pullback_stable` instantiated at `C^op` yields only that a pushout of an isomorphism is an isomorphism — invertibility of a leg, not universality of a square (Example 6.23 implies it, not conversely). Searching `iso_pushout|pushout_iso|pushout along|isomorphism.*pushout square` over the tree returns 0 hits, and none of the 40 `IsPushout` occurrences builds a pushout out of isomorphisms.
- **Discrete categories.** `Instance/Discrete.v` contains exactly three items — `DiscreteCat` (`:37`), `DiscreteCat_Functor` (`:52`), `DiscreteCat_Discrete` (`:65`) — with no `Initial`, no `Terminal`, and no pushouts; `Structure/Discrete.v` is the single predicate at `:28`. Every in-tree use of `DiscreteCat` is as a *diagram shape* for indexed (co)products (`Structure/Limit/Product.v`, `Theory/WeaklyInitial.v`, `Adjunction/GAFT.v:249`, `Adjunction/SAFT.v:146`); nothing asks about its own pushouts or initial object. There are only two `HasPushouts` instances in the whole tree, `Instance/FinSet/Pushout.v:513` and `Instance/Sets/Pushout.v:185`.
- **The collapsing pushout.** The *general* Sets pushout is there — `Instance/Sets/Pushout.v:51` `Inductive pushout_eq` with the single non-structural constructor `po_glue` at `:63`, apex `(carrier B + carrier C)` under that relation, `Sets_HasPushouts` at `:185` — but no instance is ever evaluated: neither `Instance/Sets/Pushout.v` nor `Instance/FinSet/Pushout.v` contains a single `Example` or `Compute`, and no lemma anywhere asserts that a pushout apex is a singleton or terminal. The two halving functions the example uses do not occur in the tree (`div2|Nat.div|floor` — 0 hits).

## Work to be done

1. New `Structure/Pushout/Iso.v`: for `f : a ~> x` and isomorphisms `i : a ≅ a'`, `j : x ≅ x'`, *construct* `IsPushout f (to i)` with apex `x'`, legs `to j` and `from i ∘ f ∘ to j`, deriving the mediator as `from j ∘ k` and its uniqueness from invertibility — with **no** ambient `HasPushouts` hypothesis, since the book's point is that such a square is a pushout outright. State the pullback dual in the same file (or obtain it by `C^op`, given `IsPushout` is definitionally a pullback there). Then re-derive the `i = id` case of `Construction/Cospan/Double.v` from it, so the unitor section stops re-proving a special case.
2. New `Instance/Discrete/Pushout.v`: `HasPushouts (DiscreteCat S)` for every `S` — in a discrete category the only spans are `x ← x → x`, so the apex is `x` with identity legs and the mediator is forced. Then the initial-object clause: `DiscreteCat S` has an initial object exactly when `S` has exactly one element, using the negative idiom introduced by the §6.2.1 initiality issue for the other cases.
3. Extend `Instance/Sets/Pushout.v` (or a new `Instance/Sets/Pushout/Examples.v`) with the book's worked instance: with `f a := a / 2` and `g a := (a + 1) / 2` on `nat`, prove `pushout_apex (pushout f g)` is terminal in `Sets`. The argument is the book's induction — chase `po_glue` along `f 0 = g 0 = 0`, `f 1 = 0`, `g 1 = 1`, `f 2 = 1`, `g 2 = 1`, … — carried out on the inductive `pushout_eq` relation directly, which keeps it funext-free like the rest of the file.

In-tree donors: `Structure/Pushout.v` (the UMP accessors), `Theory/Morphisms/Stability.v` (`pullback_transport`, `iso_pullback_stable`, the pasting lemmas), `Construction/Cospan/Double.v:275-327` (the identity case to be subsumed), `Instance/Discrete.v`, `Instance/Sets/Pushout.v`, `Instance/Sets.v` (`Sets_Terminal`).

## Definition of Done

- [ ] A pushout square is *constructed* from `f` and two isomorphisms, with no ambient pushout hypothesis; the pullback dual is stated.
- [ ] The `i = id` case in `Construction/Cospan/Double.v` is re-derived from the new lemma rather than re-proved.
- [ ] `HasPushouts (DiscreteCat S)` for arbitrary `S`, and the initial-object characterisation of `DiscreteCat S`.
- [ ] The `nat` halving pushout is evaluated and its apex proved terminal in `Sets` — the tree's first worked colimit computation in a concrete category.
- [ ] Statement fidelity to Seven Sketches §6.2.3 (printed pp. 189–190); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Structure/Pushout/Iso.v
coqc -R . Category Instance/Discrete/Pushout.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions iso_is_pushout.
Print Assumptions DiscreteCat_HasPushouts.
Print Assumptions halving_pushout_terminal.
```
Reviewer: statement matches Seven Sketches §6.2.3 — in particular the isomorphism lemma must *produce* a pushout, not compare an assumed one.

## Dependencies

Depends on: 7sketches:6.2.1:example6.5 — the `@Initial C → False` idiom, needed for the discrete categories that have no initial object.

<!-- catalog: {"ids":["7sketches:6.2.3:example6.23","7sketches:6.2.3:ex6.24","7sketches:6.2.3:example6.29"],"deps":["7sketches:6.2.1:example6.5"]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.3: The pushout over the initial object is the binary coproduct"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.3:example6.27, 7sketches:6.2.3:ex6.28]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.3, printed p. 190 (PDF p. 202). Items `7sketches:6.2.3:example6.27` (the statement and both directions of its proof) and `7sketches:6.2.3:ex6.28` (the three steps the example leaves as "why?").

## Background

In a category with an initial object, every pair of objects sits in a canonical span with apex the initial object, and the pushout of that span is precisely the binary coproduct — one direction because the coproduct square commutes by uniqueness of maps out of the initial object and its universal property supplies the pushout mediator, the other because a pushout over the initial object satisfies the coproduct universal property. See the nLab on [pushout](https://ncatlab.org/nlab/show/pushout) and on [coproduct](https://ncatlab.org/nlab/show/coproduct).

## Current state in the library

Absent in both directions, and the dual is absent too.

- `Structure/Pushout.v` never mentions `Initial` or `Cocartesian` and does not even `Require` them; past the class its content is only the UMP accessors and `HasPushouts`. Everything linking pushouts to coproducts in the tree is prose: `Construction/Cospan/Bridging.v:34` ("the binary coproduct `+`, i.e. the pushout over the initial object"), `Construction/Cospan/Symmetric.v:30`, `Construction/DecoratedCospan.v:31`. The one substantive-looking hit, `Construction/Cospan/Hypergraph.v:489-707`, proves a *different* statement — that the pushout of two covers is isomorphic to the coproduct of pushouts, a compatibility of the tensor bifunctor — and no `IsPushout` occurrence anywhere instantiates a span whose apex is the initial object.
- The dual is in the same state, and worse: `Structure/Pullback.v`'s only lemma-level content past the class is `pullback_unique` (`:182`) and `Pullback_to_WeakPullback` (`:239`); the reduction "a product is a pullback over the terminal object" lives at `:255-274` as a **quoted Wikipedia paragraph under a stale `(* jww (2017-06-02): *)` marker at `:267`** — an acknowledged, still-open TODO rather than a proof.

## Work to be done

New `Structure/Pushout/Coproduct.v`.

- Under `Context {C : Category} {I : @Initial C}`: given `Cocartesian C`, exhibit the coproduct square `x ← 0 → y` with injections `inl`/`inr` as an `IsPushout` — commutativity is `zero_unique`, and the mediator is the copairing `▽`, its uniqueness the coproduct's.
- Conversely, from `IsPushout (zero : 0 ~> x) (zero : 0 ~> y)` construct the binary coproduct of `x` and `y` (injections the pushout legs, copairing the pushout mediator), so the two universal properties agree; conclude the isomorphism `x +_0 y ≅ x + y` when both exist.
- Record the three "why?" steps of Exercise 6.28 as the three named lemmas the two constructions decompose into, so each is separately citable rather than buried inside a single `Program` obligation.
- Prove the pullback/terminal dual in the same pass and **replace the stale `jww (2017-06-02)` Wikipedia-quote block at `Structure/Pullback.v:255-274` with the proved statement** — the block is a known un-formalised TODO and this issue closes exactly it.

In-tree donors: `Structure/Pushout.v` (UMP accessors), `Structure/Cocartesian.v` (`▽`, `inl`, `inr`, `coprod_zero_l`/`coprod_zero_r`), `Structure/Initial.v` (`zero`, `zero_unique`, `zero_comp`), `Structure/Pullback.v`, `Structure/Cartesian.v`.

## Definition of Done

- [ ] Both directions proved: a coproduct square is a pushout over the initial object, and a pushout over the initial object is a coproduct.
- [ ] The three steps of Exercise 6.28 exist as separately named lemmas.
- [ ] The pullback/terminal dual is proved and the stale `jww (2017-06-02)` TODO block at `Structure/Pullback.v:255-274` is removed in favour of it *(library defect surfaced by Phase-D verification of §6.2.3)*.
- [ ] Statement fidelity to Seven Sketches §6.2.3 (printed p. 190); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits (in particular the removed `jww` marker must not be replaced by another).
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Structure/Pushout/Coproduct.v
coqc -R . Category Structure/Pullback.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions coproduct_is_pushout_over_initial.
Print Assumptions pushout_over_initial_is_coproduct.
```
Reviewer: statement matches Seven Sketches §6.2.3 (printed p. 190); confirm `Structure/Pullback.v` no longer carries the stale TODO quote.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.2.3:example6.27","7sketches:6.2.3:ex6.28"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.4: Generators for finite colimits — initial object with pushouts, and coequalizers with finite coproducts"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.4:prop6.32, 7sketches:6.2.4:example6.33, 7sketches:6.2.4:ex6.35]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.4, printed pp. 192–193 (PDF pp. 204–205). Items `7sketches:6.2.4:prop6.32` (the three-way equivalence), `7sketches:6.2.4:example6.33` (a finite colimit computed as an iterated pushout) and `7sketches:6.2.4:ex6.35` (the verification of that computation). The book gives no proof, citing Borceux, *Handbook of Categorical Algebra* 1, Prop. 2.8.2.

## Background

For a category the following are equivalent: it has all finite colimits; it has an initial object and all pushouts; it has all coequalizers and all finite coproducts. The proof is an induction that assembles an arbitrary finite diagram from the generating shapes. See the nLab on [finitely cocomplete category](https://ncatlab.org/nlab/show/finitely+cocomplete+category) and on [colimit](https://ncatlab.org/nlab/show/colimit).

## Current state in the library

Entirely absent — this is the single largest gap in Chapter 6 — and there is no dual either.

- No generation theorem in either direction exists. The "existence theorem for limits" appears only as header prose (`Structure/Limit.v:94`, `:103`, `Structure/Pullback.v:272`), and `Structure/Pullback.v:267` carries a stale `(* jww (2017-06-02): *)` marker directly above a Wikipedia quote of it — an acknowledged un-formalised TODO.
- The library discloses the same gap from the other side: `Structure/Topos.v:22-23` states that "the reduction of pullbacks to products and equalizers (and conversely) is not [formalized]", which is precisely why `ElementaryTopos` carries terminal object, products and pullbacks as three separate fields.
- Clause (3) has no consumer either: `HasCoequalizers` (`Structure/Coequalizer.v:68`) has exactly one derivation, `HasCoequalizers_HasReflexiveCoequalizers` (`Structure/Coequalizer/Reflexive.v:76`), and no instance anywhere in the tree.
- The near misses are genuinely near misses. `Terminal_Limit` (`Structure/Limit/Terminal.v:33`) and `Cartesian_Limit` (`Structure/Limit/Cartesian.v:39`, verbatim `(∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C`) are single-shape correspondences, not inductive generation; `Adjunction/GAFT.v:193` `Complete_HasEqualizers` is the trivial direction from an unrestricted hypothesis. `Construction/Cospan/Hypergraph.v:41` calls the package "initial object, binary coproducts, binary pushouts" *finite colimits* in its header without the notion existing — a true statement of Borceux 2.8.2, so evidence for this gap rather than a defect.
- For the worked iterated pushout there is nothing: `pushout_pasting_med` is *named* at `Construction/Cospan/Category.v:310-326` as a lemma that "should shrink this proof" but does not exist anywhere in the tree (the same comment says the deferral is deliberate and the present proof self-contained, so it is an honest deferral, not a stale pointer). `Construction/Cospan/Category.v:327` `cospan_compose_assoc` only asserts `cospan_equiv` of two iterated-pushout apexes, never a colimit UMP over the underlying diagram. `Theory/Morphisms/Stability.v:106,160` carry `pullback_paste`/`pullback_unpaste` for pullbacks with no pushout dual.
- The generic cocone-level vocabulary the proof needs *is* available: `Structure/Limit/Preservation.v:130` `IsAColimit`, with `colimit_inj` (`:135`), `ump_colimit` (`:147`), `colimit_med` (`:152`), `colimit_med_commutes` (`:156`), `colimit_med_unique` (`:160`), `colimit_med_eq` (`:166`). Its only instantiation at a concrete shape is `Structure/Coequalizer.v:275` `is_coequalizer_colimit`, at the walking parallel pair.

## Work to be done

Suggested module: `Structure/Colimit/Finite.v`, dual to the finite-limit module that #417 creates.

1. Consume #417's finiteness predicate on an index category and its `FinitelyComplete`; define `FinitelyCocomplete C := FinitelyComplete (C^op)` and expose covariant accessors (the library's duality architecture makes this a one-liner plus re-exports, but the accessors matter for readability downstream).
2. Prove (2) ⇒ (1): by induction on the enumeration of the index category's arrows, building the colimit of a finite diagram from the initial object (empty diagram) and iterated pushouts. Introduce the missing `pushout_paste`/`pushout_unpaste` lemmas as the dual of `Theory/Morphisms/Stability.v:106,160` — they are the workhorses of the induction and are wanted independently (`Construction/Cospan/Category.v:310-326` asks for exactly one of them).
3. Prove (3) ⇒ (1) by the coequalizer-of-coproducts construction, and (1) ⇒ (2), (1) ⇒ (3) trivially by exhibiting the generating shapes as finite diagrams.
4. Discharge Example 6.33 and Exercise 6.35 as the worked instance of step 2: for the four-object diagram of display (6.34), build the apex by two pushouts followed by a third and prove the resulting cocone satisfies `IsAColimit` for the original diagram. This is the concrete witness that the induction is not vacuous.
5. Update the header disclosures at `Structure/Topos.v:20-26` and `Construction/Cospan/Hypergraph.v:41` to point at the now-proved reduction.

In-tree donors: `Structure/Limit/Preservation.v:130-166` (the `IsAColimit` API), `Structure/Coequalizer.v` (`IsCoequalizer`, `is_coequalizer_colimit`), `Structure/Pushout.v`, `Structure/Cocartesian.v`, `Structure/Initial.v`, `Theory/Morphisms/Stability.v` (the pullback pasting lemmas to dualize), `Instance/Cones.v` (`Cocones`).

## Definition of Done

- [ ] `FinitelyCocomplete` defined over #417's finiteness predicate, with covariant accessors.
- [ ] All three implications of Proposition 6.32 proved, in a form that quantifies over *every* finite index category, not a fixed list of shapes.
- [ ] `pushout_paste` / `pushout_unpaste` proved as the dual of the existing pullback pasting lemmas.
- [ ] Example 6.33's iterated-pushout object is proved to satisfy `IsAColimit` for the diagram of display (6.34) — Exercise 6.35 discharged, not asserted.
- [ ] The header disclosures at `Structure/Topos.v:20-26` and `Construction/Cospan/Hypergraph.v:41` are updated to cite the proved reduction.
- [ ] Statement fidelity to Seven Sketches §6.2.4 (printed pp. 192–193); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is flagship-level.

## Verification

```bash
coqc -R . Category Structure/Colimit/Finite.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions FinitelyCocomplete.
Print Assumptions finite_colimits_from_initial_and_pushouts.
Print Assumptions finite_colimits_from_coequalizers_and_coproducts.
Print Assumptions example_6_33_is_colimit.
```
Reviewer: statement matches Seven Sketches Proposition 6.32 (printed p. 192) and Borceux 2.8.2; confirm the induction actually consumes the finiteness datum rather than treating it as a placeholder.

## Dependencies

Depends on: #417 — the finiteness predicate on an index category and `FinitelyComplete`, whose dual this issue defines and uses.

<!-- catalog: {"ids":["7sketches:6.2.4:prop6.32","7sketches:6.2.4:example6.33","7sketches:6.2.4:ex6.35"],"deps":["#417"]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.4: FinSet and Set have all finite colimits"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.4:cor6.36]
deps_item_ids: [7sketches:6.2.4:prop6.32]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.4, printed p. 193 (PDF p. 205). Item `7sketches:6.2.4:cor6.36`.

## Background

Since both the category of finite sets and the category of sets have an empty set as initial object and admit all pushouts (quotients of disjoint unions), the generating criterion for finite colimits applies to each. See the nLab on [finitely cocomplete category](https://ncatlab.org/nlab/show/finitely+cocomplete+category).

## Current state in the library

Exactly the *hypotheses* of the book's proof are in place, for both categories, and by exactly the book's construction — but the conclusion is stated for neither.

- Pushouts: `Instance/Sets/Pushout.v:185` `Sets_HasPushouts`, whose apex is the sum carrier quotiented by the inductive relation of `:51` whose only non-structural constructor is `po_glue : pushout_eq (inl (f a)) (inr (g a))` (`:63`) — literally "the disjoint union modulo the equivalence generated by `f a ~ g a`", the book's recipe; and `Instance/FinSet/Pushout.v:513` `FinSet_HasPushouts`, the counted quotient of `Fin.t (y + z)`.
- Initial objects: `Instance/Sets.v:265` `Sets_Initial` (carrier `False`) and `Instance/FinSet.v:223` `FinSet_Initial` (the object `0`).
- Binary coproducts: `Instance/Sets/Cocartesian.v:28` `Sets_Cocartesian` and `Instance/FinSet.v:250` `FinSet_Cocartesian`.

What is missing is the conclusion and the inference. There is no `Cocomplete` instance anywhere — `Cocomplete` (`Structure/Complete.v:119`) occurs only as its own definition and as a *hypothesis* in `Theory/Adamek/Corollaries.v:61` — and `HasCoequalizers` is likewise instantiated nowhere, so the clause-(3) route is closed as well. The decisive check: the identifier `Colimit` does not occur anywhere under `Instance/` at all, so no colimit is ever constructed in a concrete category in this library.

## Work to be done

Suggested modules: `Instance/Sets/Colimit.v` and `Instance/FinSet/Colimit.v`.

- Apply the clause-(2) implication of the finite-colimit generators (Proposition 6.32, §6.2.4) to `Sets` and to `FinSet`, obtaining `FinitelyCocomplete Sets` and `FinitelyCocomplete FinSet` from the six instances above. Both are short once the generating theorem exists — this issue is the concrete witness that the theorem is not vacuous, and would be the first colimit ever constructed in an `Instance/` category.
- Supply `HasCoequalizers Sets` and `HasCoequalizers FinSet` as well, so the clause-(3) route is also witnessed and the equivalence of the three clauses is exercised in both directions on a real category. For `Sets` this is the parallel-pair specialisation of the `pushout_eq` idiom already in `Instance/Sets/Pushout.v`; for `FinSet` it is the union-find quotient already used by `Instance/FinSet/Pushout.v`.
- Record the results in `docs/INHABITATION.md`, which currently has no entry for finite cocompleteness of any concrete category.

In-tree donors: `Instance/Sets/Pushout.v`, `Instance/FinSet/Pushout.v`, `Instance/Sets.v`, `Instance/FinSet.v`, `Instance/Sets/Cocartesian.v`, `Structure/Coequalizer.v` (the `IsCoequalizer` API and `is_coequalizer_colimit`).

## Definition of Done

- [ ] `FinitelyCocomplete Sets` and `FinitelyCocomplete FinSet` proved via the clause-(2) route, not re-derived by hand.
- [ ] `HasCoequalizers Sets` (coordinate with #315, which owns the `Sets` quotient construction) and `HasCoequalizers FinSet` supplied, giving the first instances of a class that currently has none.
- [ ] `docs/INHABITATION.md` records the two witnesses.
- [ ] Statement fidelity to Seven Sketches Corollary 6.36 (printed p. 193); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what the `Instance/` layer already sanctions per docs/AXIOMS.md; any new stdlib axiom dependency is disclosed there.
- [ ] `Print Assumptions` reported for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Sets/Colimit.v && coqc -R . Category Instance/FinSet/Colimit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_FinitelyCocomplete.
Print Assumptions FinSet_FinitelyCocomplete.
Print Assumptions Sets_HasCoequalizers.
```
Reviewer: statement matches Seven Sketches Corollary 6.36 (printed p. 193), and the proof goes through the generating criterion rather than around it.

## Dependencies

Depends on: 7sketches:6.2.4:prop6.32
Depends on: #417 — the finiteness predicate the conclusion is stated over.
Depends on: #315 — the quotient-setoid construction of coequalizers in `Sets`, which this issue's `HasCoequalizers Sets` instance should reuse rather than duplicate.

<!-- catalog: {"ids":["7sketches:6.2.4:cor6.36"],"deps":["7sketches:6.2.4:prop6.32","#417","#315"]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.4: Colimits at the small shapes by duality — the empty, discrete two-object, and one-object diagrams"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.4:example6.31, 7sketches:6.2.4:example6.39, 7sketches:6.2.4:example6.40]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.4, printed pp. 192–194 (PDF pp. 204–206). Items `7sketches:6.2.4:example6.31` (an initial object is the colimit of the empty diagram), `7sketches:6.2.4:example6.39` (a coproduct is the colimit over the two-vertex discrete graph) and `7sketches:6.2.4:example6.40` (the colimit of a one-object diagram is the object).

## Background

The smallest diagram shapes name the smallest colimits: the empty diagram's colimit is an initial object, a two-object discrete diagram's colimit is a binary coproduct, and a one-object diagram's colimit is the object itself. Each is dual to a limit statement of the same shape. See the nLab on [colimit](https://ncatlab.org/nlab/show/colimit) and on [discrete category](https://ncatlab.org/nlab/show/discrete+category).

## Current state in the library

All three are asserted only in their *limit* form, and the obstruction to reading them off by duality is the same in each case and is not addressed anywhere.

- `Structure/Limit/Terminal.v:33` proves `Terminal_Limit (C : Category) (F : 0 ⟶ C) : Limit F ↔ @Terminal C` over `Instance/Zero.v`'s empty category (`obj := Empty_set`). The colimit half is only header prose (`Structure/Limit/Terminal.v:29-31`, `Structure/Initial.v:33-34`). `Terminal_Limit` occurs exactly three times in the tree — the theorem and two comments — so nothing consumes it and nothing dualizes it.
- `Structure/Limit/Cartesian.v:39` proves `Cartesian_Limit (C : Category) : (∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C`. There is no coproduct counterpart: `Cocartesian_Colimit`, `IsIndexedCoproduct` and `HasIndexedCoproducts` all return 0 hits, and `Structure/Limit/Product.v` develops only the product side (`IsIndexedProduct`, `iprod`, `limit_is_indexed_product`, `HasIndexedProducts`) with no dual file.
- For shape `1` there is nothing at all: no `Limit_One`/`One_Limit`; `[1, C] ≃ C` appears only as comments at `Instance/One.v:22` and `Instance/One/Diagonal.v:30`; `Instance/One.v` contains exactly `_1` (`:25`), `Erase` (`:47`) and `Cat_Terminal` (`:54`); `Instance/One/Diagonal.v`'s sole assertion is `Diagonal_Unique` (`:33`), about constant diagrams *out of* an arbitrary `J`, not about a diagram whose shape is `1`. `Structure/Limit/Kan/Extension.v:46` `Kan_Limit` uses `Erase J : J ⟶ 1` as the functor one extends *along* — the opposite direction.

**The crux, established by Phase-D verification and not obvious from the statements.** `Initial C` is literally `Notation` for `@Terminal (C^op)` (`Structure/Initial.v:96`) and `Colimit F := Limit (F^op)` (`Structure/Limit.v:158`, the last line of the file), so `Terminal_Limit` applied at `C^op` *would* give Example 6.31 — but only after identifying `0^op` with `0`, and the tree contains no `0^op = 0` lemma, no opposite-of-`Instance/Zero.v` instance, and no application of `Terminal_Limit` at any opposite category. The same identification of `Two_Discrete^op` with `Two_Discrete` is what blocks reading Example 6.39 off `Cartesian_Limit`. Phase D considered overturning these to PRESENT on the grounds that the duality architecture makes them definitional re-readings, and rejected it for exactly this reason: the shape self-dualities are missing, so the derivations do not typecheck today.

## Work to be done

Suggested module: `Structure/Colimit/Shapes.v`, plus small additions to `Instance/Zero.v`, `Instance/Two/Discrete.v` and `Instance/One.v`.

1. Supply the three shape self-dualities as isomorphisms in `Cat`: `_0^op ≅ _0`, `Two_Discrete^op ≅ Two_Discrete`, `_1^op ≅ _1`. These are the reusable pieces — every dualization of a fixed-shape (co)limit statement in the library will want them, and none exists today.
2. `Initial_Colimit (C : Category) (F : 0 ⟶ C) : Colimit F ↔ @Initial C`, obtained from `Terminal_Limit` at `C^op` through the first self-duality, together with the remark that the initial object is therefore a *finite* colimit (the empty category being finite).
3. `Cocartesian_Colimit (C : Category) : (∀ F : Two_Discrete ⟶ C, Colimit F) ↔ @Cocartesian C`, dual to `Cartesian_Limit`; and, for parity with `Structure/Limit/Product.v`, the indexed-coproduct file (`IsIndexedCoproduct`, `icoprod`, `colimit_is_indexed_coproduct`, `HasIndexedCoproducts`) over `Instance/Discrete.v`'s `DiscreteCat`.
4. `One_Limit` / `One_Colimit`: for `F : 1 ⟶ C`, both the limit and the colimit of `F` are `F tt`, so a diagram of shape `1` is its own (co)limit.

In-tree donors: `Structure/Limit/Terminal.v`, `Structure/Limit/Cartesian.v`, `Structure/Limit/Product.v` (the template to dualize), `Structure/Limit.v` (`Colimit`), `Structure/Initial.v`, `Instance/Zero.v`, `Instance/One.v`, `Instance/Two/Discrete.v`, `Construction/Opposite.v`.

## Definition of Done

- [ ] The three shape self-dualities `_0^op ≅ _0`, `Two_Discrete^op ≅ Two_Discrete`, `_1^op ≅ _1` proved and exported.
- [ ] `Initial_Colimit` proved *through* `Terminal_Limit` at `C^op` rather than re-proved from scratch, so the duality architecture does the work.
- [ ] `Cocartesian_Colimit` proved, and the indexed-coproduct dual of `Structure/Limit/Product.v` supplied.
- [ ] The shape-`1` (co)limit proved in both directions.
- [ ] Statement fidelity to Seven Sketches §6.2.4 (printed pp. 192–194); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Structure/Colimit/Shapes.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Initial_Colimit.
Print Assumptions Cocartesian_Colimit.
Print Assumptions One_Colimit.
```
Reviewer: statement matches Seven Sketches §6.2.4 (printed pp. 192–194); confirm the opposite-shape identifications are proved rather than assumed by `Set Printing All` sleight of hand.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.2.4:example6.31","7sketches:6.2.4:example6.39","7sketches:6.2.4:example6.40"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.2.4: The colimit formula in Set — a finite colimit is a quotient of a coproduct"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.2.4:thm6.37]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.2.4, printed p. 193 (PDF p. 205). Item `7sketches:6.2.4:thm6.37`.

## Background

For a diagram of sets indexed by a category presented by a finite graph with equations, the colimit is the set of pairs (vertex, element of that vertex's set) quotiented by the equivalence relation generated by the diagram's arrows — dually to the finite-limit formula, which realises a limit as a subset of a product. See the nLab on [colimit](https://ncatlab.org/nlab/show/colimit) and on [coequalizer](https://ncatlab.org/nlab/show/coequalizer).

## Current state in the library

The recipe is realised shape by shape and never in general.

- `Instance/Sets/Pushout.v:185` `Sets_HasPushouts` builds the pushout apex as `(carrier B + carrier C)` modulo the inductively generated relation `pushout_eq` (`:51`) whose only non-structural constructor is `po_glue : pushout_eq (inl (f a)) (inr (g a))` (`:63`) — the sum of the fibres quotiented by exactly the relation the diagram's arrows generate, realised as an inductive setoid so the construction stays funext-free. That is the book's formula, at the span shape.
- `Instance/Sets/Coend.v:163` `SetsCoend` builds `Σ x : C, F (x, x)` (the inductive `coend_sum`, `:68`) modulo `coend_eq` (`:75`). Note this quotients by the **two-sided** dinaturality relation (`ce_glue`), so it is *not* an instance of the book's one-sided formula, only its closest general-shape analogue.
- No theorem quantifies over a general `D : J ⟶ Sets`, and consequently there is no `Cocomplete Sets`; `Cocomplete` is instantiated nowhere in the tree.
- The theorem's index also has no in-tree home: there is no notion of a category *presented by a finite graph with equations*. `Construction/Free/Quiver.v:431` `FreeOnQuiver` gives the free category on a graph but carries no equations and no finiteness, and it is never used as a diagram shape — its only uses outside its own file are `Check` commands at `Test/Issue138.v:90,96`.
- The dual half the book appeals to — "a finite limit is a subset of a product" — is likewise only instantiated (`Instance/Sets/End.v` builds the end as the sub-setoid of compatible families) and never proved as a general formula.

## Work to be done

Suggested modules: `Construction/Free/Quiver/Presented.v` (the index) and `Instance/Sets/Colimit/Formula.v` (the theorem).

1. Define a category presented by a finite graph together with equations: a `Quiver` with finite node and edge types, plus a set of pairs of parallel paths, and the quotient of `FreeOnQuiver` by the congruence they generate. `Construction/Quotient.v` (generic hom-congruence quotients) is the donor and is exactly the machinery `Construction/PROP/Presentation.v` already uses one level up; `Construction/Free/Quiver.v:550`'s free/forgetful adjunction gives the universal property to lift.
2. Construct the colimit of an arbitrary `D : J ⟶ Sets` for such a `J`: carrier `Σ v : V, D v` as an inductive sum setoid, quotiented by the inductively generated relation with the single non-structural constructor `(v, d) ~ (w, D a d)` for each edge `a : v → w` — deliberately mirroring `pushout_eq`/`po_glue` so the whole development stays funext-free — with the injections `D v → colim` and the mediating map from any cocone, plus its uniqueness.
3. Derive the shape instances as corollaries and *replace* the ad hoc constructions where they coincide: the pushout apex of `Instance/Sets/Pushout.v` and the coproduct of `Instance/Sets/Cocartesian.v` should both be exhibited as instances of the formula (or proved isomorphic to it), so the tree has one construction rather than several.
4. State the dual formula for finite limits in `Sets` (a subset of a product) and connect it to `Instance/Sets/End.v`, since the book cites it as the counterpart.

In-tree donors: `Instance/Sets/Pushout.v` (`pushout_eq`, `po_glue`, `pushout_apex_setoid`), `Instance/Sets/Coend.v` (the same idiom at a harder quotient), `Instance/Sets/End.v`, `Construction/Free/Quiver.v`, `Construction/Quotient.v`, `Structure/Limit/Preservation.v:130-166` (the `IsAColimit` API to conclude against).

## Definition of Done

- [ ] A finite-graph-with-equations presentation of an index category exists, with its universal property.
- [ ] The colimit of an arbitrary `Sets`-valued diagram on such an index is constructed as the quotient of the sum of the fibres, with the full cocone universal property proved.
- [ ] The construction is funext-free, in the style of `Instance/Sets/Pushout.v` (the header must say so explicitly).
- [ ] The existing `Sets` pushout and coproduct are exhibited as instances of the formula, or proved isomorphic to it.
- [ ] The dual finite-limit formula is stated and related to `Instance/Sets/End.v`.
- [ ] Statement fidelity to Seven Sketches Theorem 6.37 (printed p. 193); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what the `Instance/` layer already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is flagship-level.

## Verification

```bash
coqc -R . Category Construction/Free/Quiver/Presented.v
coqc -R . Category Instance/Sets/Colimit/Formula.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions sets_colimit_formula.
Print Assumptions sets_pushout_is_formula_instance.
```
Reviewer: statement matches Seven Sketches Theorem 6.37 (printed p. 193) — the quotient must be by the relation *generated* by the arrows, and the injections must be the class maps.

## Dependencies

Depends on: #315 — quotient setoids and coequalizers in `Sets`, the quotient machinery this formula generalises.
Depends on: #417 — the finiteness predicate on an index category.
Depends on: #299 (MacLane II.8: The least congruence and presented categories) — it targets the same new module `Construction/Free/Quiver/Presented.v` and owns the least-congruence/quotient machinery this colimit formula quotients by. Land it first rather than building a second congruence construction.

<!-- catalog: {"ids": ["7sketches:6.2.4:thm6.37"], "deps": ["#315", "#417", "#299"]} -->

---8<---

```yaml
title: "Seven Sketches 6.3.1: The spider of a single Frobenius monoid"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.3.1:def6.54]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.3.1, printed p. 199 (PDF p. 211). Item `7sketches:6.3.1:def6.54`.

## Background

Given a Frobenius monoid on an object of a monoidal category, the spider of type (m, n) folds m input wires into one by iterated multiplication and splits that wire into n outputs by iterated comultiplication, with the unit and counit covering the zero-arity cases. See the nLab on [Frobenius algebra](https://ncatlab.org/nlab/show/Frobenius+algebra) and on [symmetric monoidal category](https://ncatlab.org/nlab/show/symmetric+monoidal+category).

## Current state in the library

The morphism itself is built, faithfully, but only under a much stronger hypothesis than the book's.

`Structure/Monoidal/Hypergraph/Spider.v:274-280` defines `canonical_spider (X : C) (m n : nat) : tpower X m ~> tpower X n`, case-splitting on `m` and `n` exactly as the book does: `fold_mu X m'` (`:236`, iterated `scfa_mu`), `unfold_delta X n'` (`:242`), `fold_eta` (`:252`) and `fold_eps` (`:259`) at arity zero, over `tpower` (`:217`). The small cases are pinned down by `canonical_spider_0_0`/`_0_1`/`_1_0`/`_1_1`/`_2_1`/`_1_2`/`_2_2` (`:288-333`), all by `reflexivity`, plus `canonical_spider_1_1_id` (`:310`).

The gap is the hypothesis. `Section SpiderConstructions` opens at `:228-230` with `Context {Sym : @SymmetricMonoidal C}` and `Context {H : @Hypergraph C Sym}`, and every definition reads its operations out of `scfa X` — where `Class Hypergraph` (`Structure/Monoidal/Hypergraph.v:144-173`) demands a chosen `SpecialCommutativeFrobenius` on **every** object of `C` plus four `scfa_tensor_*` and four `scfa_unit_*` coherence axioms. So writing down the spider of one Frobenius monoid currently requires equipping the whole category and discharging eight coherences.

Phase-D verification sharpened this in three ways that change how the work should be done:

- The generalisation is **mechanical**: none of the six definitions (`tpower`, `fold_mu`, `unfold_delta`, `fold_eta`, `fold_eps`, `canonical_spider`) touches a coherence field. The only item in the section that uses one is the *lemma* `fold_eps_eta_I` (`:385`), which consumes `scfa_unit_eta`/`scfa_unit_epsilon`.
- Two further hypothesis differences run the same way and are not recorded in the coverage record: the book defines the spider in a plain **monoidal** category, whereas the section requires `SymmetricMonoidal`; and the book needs only a Frobenius monoid, not a **special** one.

## Work to be done

Suggested module: keep `Structure/Monoidal/Hypergraph/Spider.v` and reparameterise its constructions section, or split the constructions into `Structure/Monoidal/Frobenius/Spider.v` and leave the hypergraph-facing lemmas where they are.

1. Open a section over `Context {C : Category} {M : @Monoidal C} (X : C) (F : SpecialCommutativeFrobenius X)` and re-express `tpower`, `fold_mu`, `unfold_delta`, `fold_eta`, `fold_eps` and `canonical_spider` against `F` rather than `scfa X`. Weaken `SymmetricMonoidal` to `Monoidal` wherever the definitions permit, and record in the header exactly which downstream lemmas genuinely need symmetry (`spider_mu_commutative`, `:149`, is the obvious one) and which need specialness (`fold_mu_unfold_delta_id`, `:613`).
2. Keep the existing names as thin wrappers — `canonical_spider X m n := canonical_spider_of (scfa X) m n` and similarly for the folds — so `Structure/Monoidal/Hypergraph/Tactics.v` and every other consumer keeps compiling unchanged, and re-derive the seven small-case lemmas as instances rather than duplicating them.
3. Where the book's definition asks only for a Frobenius monoid, state which of the constructions survive without specialness and package that as a second, weaker section if it is cheap; otherwise disclose in the header why specialness is retained.

In-tree donors: `Theory/Algebra/Frobenius.v`, `Theory/Algebra/SpecialCommutativeFrobenius.v`, `Structure/Monoidal/Hypergraph.v` (the class whose `scfa` field the wrappers project), `Structure/Monoidal/Hypergraph/Spider.v` (everything above, to be re-sited).

## Definition of Done

- [ ] The spider `s_{m,n}` is defined from a single `SpecialCommutativeFrobenius X` with no `Hypergraph` hypothesis, and in a plain `Monoidal` category wherever the definitions allow.
- [ ] The existing `Hypergraph`-parameterised names survive as wrappers; no downstream file changes behaviour.
- [ ] The seven small-case lemmas and `canonical_spider_1_1_id` are re-derived at the weaker hypothesis, still by `reflexivity` where they were.
- [ ] The header states precisely which results need symmetry and which need specialness.
- [ ] Statement fidelity to Seven Sketches Definition 6.54 (printed p. 199); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] Any new file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Spider entry currently describes the hypergraph-only form.

## Verification

```bash
coqc -R . Category Structure/Monoidal/Hypergraph/Spider.v
coqc -R . Category Structure/Monoidal/Hypergraph/Tactics.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions canonical_spider_of.
```
Reviewer: statement matches Seven Sketches Definition 6.54 (printed p. 199) — the spider must be definable from one Frobenius monoid on one object, with no category-wide supply.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.3.1:def6.54"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.3.1: The spider normal-form theorem — connected Frobenius diagrams are spiders"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.3.1:thm6.55, 7sketches:6.3.1:example6.56, 7sketches:6.3.1:ex6.57]
deps_item_ids: [7sketches:6.3.1:def6.54]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.3.1, printed pp. 199 and 199–200 (PDF pp. 211–212). Items `7sketches:6.3.1:thm6.55` (the theorem), `7sketches:6.3.1:example6.56` (two connected diagrams shown equal by it) and `7sketches:6.3.1:ex6.57` (which of six displayed diagrams `X ⊗ X → X ⊗ X ⊗ X` are necessarily equal — the *positive*, equality half; the separation half is scoped to the free-Frobenius-prop issue).

## Background

If a morphism between tensor powers of a Frobenius object is built only from the Frobenius generators and the symmetry, and its string diagram is connected, then it equals the spider of the corresponding arity — connectivity is the only invariant. See the nLab on [Frobenius algebra](https://ncatlab.org/nlab/show/Frobenius+algebra) and on [PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

Everything except the theorem, and the file says so itself three times (`Structure/Monoidal/Hypergraph/Spider.v:43-45`, `:414-445`, `:687-701`).

- The syntax and semantics exist: `SpiderExpr` (`:470-481`) and `denote_spider` (`:524-549`), with the target normal form `canonical_spider` (`:274`).
- The hardest ingredient is proved: `fold_mu_unfold_delta_id (X : C) (k : nat) : fold_mu X k ∘ unfold_delta X k ≈ id[X]` (`:613-628`), the k-ary specialness crux, by induction from `spider_collapse`. Alongside it are `spider_2_to_1_then_1_to_2` (`:356`), `canonical_spider_1_1_id` (`:310`), `spider_1_to_3` (`:179`), `spider_2_to_2` (`:188`) and `spider_mu_commutative` (`:149`, braid absorption).
- The theorem itself is not stated, and the two helper inductions the file names — `spider_compose_canonical` (for `SE_seq`) and `spider_par_canonical` (for `SE_par`) — do not exist anywhere in the tree.
- `SpiderExpr` carries **no connectivity predicate**, so the book's essential hypothesis cannot even be written down. This is the crux: the induction cannot be run until the syntax is indexed by connectivity (or `SE_par` is restricted to a connected-gluing constructor).
- The equality half of Exercise 6.57 is not reachable either: there is no lemma anywhere relating any expression to `canonical_spider X 2 3`, and the only `denote_spider` results in the tree are three smoke tests at `:661`, `:666`, `:674`.

**Two false claims in the library's own status comments, both found by Phase-D verification and both load-bearing for whoever takes this on.** They must be corrected as part of this work, not merely worked around:

1. The unconditional statement sketched at `:414-445`, `spider_normal_form : ∀ X m n (f : tpower X m ~> tpower X n), … f ≈ canonical_spider X m n`, is **false as written**. `SE_par_X SE_id_X SE_id_X : SpiderExpr X 2 2` denotes `to (tpower_add_iso) ∘ bimap id id ∘ from (tpower_add_iso) ≈ id`, whereas `canonical_spider X 2 2` unfolds (`:329-333`) to `unfold_delta X 1 ∘ fold_mu X 1`, i.e. δ ∘ μ up to `unit_right` casts — in Cospan(FinSet) at `X = 1` that is the cospan 2 → 1 ← 2 (all four ports joined), not the identity cospan. *(Note: the Phase-C record wrote `unfold_delta X 0` here; the correct unfolding is `unfold_delta X 1`, since n = 2 gives n' = 1. Phase D corrected this.)*
2. The helper sketched at `:565-567`, `spider_compose_canonical : canonical_spider X k n ∘ canonical_spider X m k ≈ canonical_spider X m n`, is **false at k = 0**: it would require the extraspecial law `ε ∘ η ≈ id` that `Theory/Algebra/SpecialCommutativeFrobenius.v:30-33` explicitly declines to impose. In Cospan(FinSet) the k = 0 composite is 1 → 2 ← 1, not the identity.

## Work to be done

Suggested module: `Structure/Monoidal/Hypergraph/Spider.v` (extend) plus `Structure/Monoidal/Hypergraph/Spider/NormalForm.v` for the induction.

1. Give `SpiderExpr` a connectivity index — either an extra `bool`/`Prop` parameter tracking whether the denoted diagram is connected, or a separate `ConnectedSpiderExpr` whose `SE_par` constructor is replaced by a gluing constructor that shares at least one wire. Whichever is chosen, the header must justify it against the book's hypothesis.
2. Prove `spider_compose_canonical` **with the correct side condition** (`k > 0`, or with the k = 0 case treated separately), and `spider_par_canonical` for connected gluings only.
3. Prove `spider_normal_form` for connected expressions: `denote_spider e ≈ canonical_spider X m n` for every connected `e : SpiderExpr X m n`, by structural induction using the two helpers and `fold_mu_unfold_delta_id`.
4. Discharge Example 6.56 and the equality half of Exercise 6.57 as one-line consequences of the criterion — the point of the theorem is that they *should* be one-liners, so a hand proof of either is not acceptable evidence.
5. **Correct the two false status comments** at `:414-445` and `:565-567`, replacing the unconditional sketches with the true statements and recording the two counterexamples above in the file so the error cannot recur.

In-tree donors: `Structure/Monoidal/Hypergraph/Spider.v` (all of the above), `Structure/Monoidal/Hypergraph/Tactics.v`, `Theory/Algebra/SpecialCommutativeFrobenius.v` (which laws are and are not imposed), `Construction/Cospan/Hypergraph.v` (the model in which the counterexamples live).

## Definition of Done

- [ ] `SpiderExpr` carries a connectivity index (or a connected variant exists), so the book's hypothesis is statable.
- [ ] `spider_compose_canonical` proved with its correct side condition, and `spider_par_canonical` proved for connected gluings.
- [ ] `spider_normal_form` proved for connected expressions.
- [ ] Example 6.56 and the equality half of Exercise 6.57 discharged *by* the criterion, in a line each.
- [ ] The two false status comments at `Structure/Monoidal/Hypergraph/Spider.v:414-445` and `:565-567` are corrected, with the `SE_par_X SE_id_X SE_id_X` and `k = 0` counterexamples recorded in the file *(library defect surfaced by Phase-D verification of §6.3.1)*.
- [ ] Statement fidelity to Seven Sketches Theorem 6.55 (printed p. 199); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this closes the milestone the Spider file defers.

## Verification

```bash
coqc -R . Category Structure/Monoidal/Hypergraph/Spider/NormalForm.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions spider_normal_form.
Print Assumptions spider_compose_canonical.
Print Assumptions spider_par_canonical.
```
Reviewer: statement matches Seven Sketches Theorem 6.55 (printed p. 199); check that the connectivity hypothesis is *used*, and that neither helper has been stated in the unconditional form the file's old comments proposed.

## Dependencies

Depends on: 7sketches:6.3.1:def6.54

<!-- catalog: {"ids":["7sketches:6.3.1:thm6.55","7sketches:6.3.1:example6.56","7sketches:6.3.1:ex6.57"],"deps":["7sketches:6.3.1:def6.54"]} -->

---8<---

```yaml
title: "Seven Sketches 6.3.1: The free prop on the Frobenius presentation is Cospan(FinSet)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.3.1:thm6.58]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.3.1, printed p. 200 (PDF p. 212). Item `7sketches:6.3.1:thm6.58`.

## Background

Take the four-element generating set {μ, η, δ, ε} with arities (2;1), (0;1), (1;2), (1;0) and impose the Frobenius axioms; the prop presented by that data is equivalent, as a symmetric monoidal category, to the prop of cospans of finite sets. See the nLab on [PROP](https://ncatlab.org/nlab/show/PROP), on [Frobenius algebra](https://ncatlab.org/nlab/show/Frobenius+algebra) and on [cospan](https://ncatlab.org/nlab/show/cospan).

## Current state in the library

The equivalence has no in-tree counterpart of any strength, but both sides of it are already constructible, and the amount of missing machinery is smaller than a naive search suggests.

- The claim itself appears only as prose: `Construction/PROP/Presentation.v:51` ("the theory of special commutative Frobenius algebras presents the PROP of cospans of finite sets") and `Construction/PROP/Signature.v:29-32` ("the free *hypergraph* PROP on no generators … is the PROP of cospans of finite sets; that extra structure is **not** imposed by the `FreePROP` of this development, which quotients only by the strict-SMC axioms"). Neither is a `Definition` or `Theorem`.
- The **left** side is available: `PresentedPROP` exists at `Construction/PROP/Presentation.v:312`, with its universal property at `Construction/PROP/Presentation/Universal.v:340` (`Presented_factor`) and `:435` (`Presented_unique`). No in-tree `Signature`/`EqSystem` names the four Frobenius generators or the nine axioms.
- The **right** side is available too: `Cospan_SymmetricMonoidal` (`Construction/Cospan/Symmetric.v:398`) over `Cospan_Monoidal` (`Construction/Cospan/Hypergraph.v:1973`), with `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v:513`), `FinSet_Initial` (`Instance/FinSet.v:223`) and `FinSet_Cocartesian` (`:250`) supplying the base — though no `.v` file ever forms `CospanCat FinSet`.

**Phase-D correction — this materially shrinks the work and contradicts the Phase-C search log, which must not be used as drafted.** The log asserted that "the library has no notion of equivalence of (symmetric) monoidal categories". That is literally true only of the exact strings searched. The library **does** have strong monoidal functors, under the name `MonoidalFunctor` (`Functor/Structure/Monoidal.v:77`, comparison morphisms invertible), plus `BraidedMonoidalFunctor` (`Functor/Structure/Monoidal/Braided.v:67`) and `SymmetricMonoidalFunctor` (`Functor/Structure/Monoidal/Braided.v:99`). What is genuinely missing is only the **equivalence** notion — a symmetric monoidal functor that is an equivalence of the underlying categories — which is one short definition on top of `Theory/Equivalence.v`, not a from-scratch development.

## Work to be done

Suggested modules: `Functor/Structure/Monoidal/Equivalence.v` (the missing notion) and `Construction/PROP/Frobenius.v` (the theorem).

1. Define symmetric monoidal equivalence: a `SymmetricMonoidalFunctor` whose underlying functor carries an `Equivalence` structure (`Theory/Equivalence.v`), with the quasi-inverse shown symmetric monoidal. Keep it small and general — it is wanted independently by every "equivalent as a symmetric monoidal category" claim in the book.
2. Give the Frobenius signature as a `Signature` (`Construction/PROP/Signature.v:50`) with the four generators at their stated arities, and the nine equations of Definition 6.52 as the equation system; form the presented prop.
3. Build the interpretation into Cospan(FinSet) by sending each generator to the corresponding cospan — `cospan_scfa_mu`/`eta`/`delta`/`epsilon` are already available from `Construction/Cospan/Hypergraph.v` — checking the nine equations there, and obtain the induced prop functor from `Presented_factor`.
4. Prove it an equivalence. The spider normal form (§6.3.1, Theorem 6.55) is the natural route to fullness and faithfulness once it exists; if this issue lands first, the direct combinatorial argument on cospans is acceptable provided the header records which route was taken.
5. Form `CospanCat FinSet` explicitly as a named in-tree term while you are here — nothing in the tree currently does, and this issue needs it (see the note in the operad-Cospan issue for why that matters).

In-tree donors: `Construction/PROP/Presentation.v`, `Construction/PROP/Presentation/Universal.v`, `Construction/PROP/Signature.v`, `Construction/Cospan/Symmetric.v`, `Construction/Cospan/Hypergraph.v`, `Functor/Structure/Monoidal/Braided.v`, `Theory/Equivalence.v`, `Instance/FinSet/Pushout.v`.

## Definition of Done

- [ ] Symmetric monoidal equivalence defined, with the quasi-inverse's monoidal structure proved rather than assumed.
- [ ] The Frobenius signature and its nine equations exist as a prop presentation.
- [ ] The interpretation into Cospan(FinSet) is built and shown to be a symmetric monoidal equivalence.
- [ ] `CospanCat FinSet` exists as a named in-tree term.
- [ ] The separation half of Exercise 6.57 is discharged here: the free Frobenius prop distinguishes the displayed diagrams that are *not* connected in the same way, so "which of the six are necessarily equal" has both a positive and a negative answer in-tree.
- [ ] Statement fidelity to Seven Sketches Theorem 6.58 (printed p. 200); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — this is flagship-level and supplies a long-promised witness.

## Verification

```bash
coqc -R . Category Functor/Structure/Monoidal/Equivalence.v
coqc -R . Category Construction/PROP/Frobenius.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions frobenius_prop_equiv_cospan_finset.
```
Reviewer: statement matches Seven Sketches Theorem 6.58 (printed p. 200); confirm the equivalence is of *symmetric monoidal* categories, not merely of underlying categories.

## Dependencies

Depends on: #827 — FinSet as a prop, the skeletal base the cospan prop is built over.
Depends on: 7sketches:6.3.1:thm6.55 — the spider normal form, the intended route to fullness and faithfulness.

<!-- catalog: {"ids":["7sketches:6.3.1:thm6.58"],"deps":["#827","7sketches:6.3.1:thm6.55"]} -->

---8<---

```yaml
title: "Seven Sketches 6.3.3: Two distinct hypergraph structures on linear relations"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.3.3:example6.65]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.3.3, printed p. 203 (PDF p. 215). Item `7sketches:6.3.3:example6.65`.

## Background

The prop of linear relations carries two different hypergraph structures on one and the same underlying symmetric monoidal category — one built from the copy/discard generators, one from the add/zero generators — which is what shows that a hypergraph structure is extra data rather than a property of a category. See the nLab on [hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category) and on [PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

Absent, and both the carrier and the phenomenon are missing.

- There is no linear algebra in the tree at all: `LinRel`, `LinearRelation`, "linear relation", `VectorSpace` and `Matrix` each return zero files; every `Vect` hit is a `Coq.Vectors.Vector`/`Fin` import or a prose mention (`Theory/Algebra/Frobenius.v:64`, `Theory/Algebra/CommutativeFrobenius.v:34`). There is no category of vector spaces and nothing under `Instance/` named `Vect`, `FdVect` or `Mat`.
- Nothing in-tree carries **two distinct `Hypergraph` instances on one symmetric monoidal category**, so the example's actual point has no counterpart of any strength.
- The nearest neighbour is instructive rather than helpful: `Instance/ZX.v` has both spider colours, `zx_z_self_fuse` (`:517`) and `zx_x_self_fuse` (`:524`) on `ZX_Cat` (`:348`), but only as *syntax* — the file states at `:383-398` and `:438-466` that lifting `ZX_Cat` to a PROP with a `Hypergraph` structure is not done, so the two colours are never two Frobenius structures. `Instance/Rel.v:38-39` explicitly declines to build the dagger-compact structure ("None of that extra"), so there is no Frobenius data there either.

## Work to be done

Suggested module: `Instance/Rel/Linear/Hypergraph.v`, over the `LinRel R` prop that #857 builds.

1. Construct the **black** supply: for each object, the copy comultiplication and the discard counit, with their adjoint multiplication and unit, and prove the special commutative Frobenius laws in `LinRel R`.
2. Construct the **white** supply: the addition multiplication and the zero unit, with their adjoints, and the same laws.
3. Assemble two `@Hypergraph (LinRel R) _` instances on the *same* `SymmetricMonoidal` structure, discharging the eight tensor/unit coherences for each.
4. Prove they are genuinely different — exhibit an object and a morphism on which the two multiplications disagree — and state the moral as a named lemma: a hypergraph structure is data, not a property. That lemma is the reusable output; it is the first in-tree evidence for a distinction the `Hypergraph` class's design depends on.
5. Optionally connect to `Instance/ZX.v`: the two colours there are the syntactic shadow of exactly these two supplies, so a note (or a functor, if cheap) linking them keeps the two developments from drifting.

In-tree donors: `Structure/Monoidal/Hypergraph.v` (the class and its eight coherences), `Structure/Monoidal/Hypergraph/Spider.v`, `Theory/Algebra/SpecialCommutativeFrobenius.v`, `Structure/Monoidal/CopyDiscard.v` (the copy/discard half is already a first-class in-tree notion), `Construction/Cospan/Hypergraph.v` (the worked instance to imitate), `Instance/ZX.v`.

## Definition of Done

- [ ] Both supplies constructed on `LinRel R` and each proved a special commutative Frobenius structure.
- [ ] Two `Hypergraph` instances on one and the same symmetric monoidal category.
- [ ] A proof that the two instances differ, with an explicit witness.
- [ ] A named lemma recording that a hypergraph structure is data rather than a property.
- [ ] Statement fidelity to Seven Sketches Example 6.65 (printed p. 203); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what the `Instance/` layer already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for both hypergraph instances and the distinctness lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated alongside the hypergraph entry.

## Verification

```bash
coqc -R . Category Instance/Rel/Linear/Hypergraph.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions LinRel_Hypergraph_black.
Print Assumptions LinRel_Hypergraph_white.
Print Assumptions LinRel_hypergraph_structures_differ.
```
Reviewer: statement matches Seven Sketches Example 6.65 (printed p. 203) — both structures must sit on the *same* symmetric monoidal category, not on two isomorphic copies.

## Dependencies

Depends on: #857 — `LinRel_R`, the prop of linear relations this equips.

<!-- catalog: {"ids":["7sketches:6.3.3:example6.65"],"deps":["#857"]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.1: The power-set functor is lax symmetric monoidal"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.4.1:example6.69, 7sketches:6.4.1:ex6.70]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.1, printed p. 204 (PDF p. 216). Items `7sketches:6.4.1:example6.69` (the coherence maps and the claim) and `7sketches:6.4.1:ex6.70` (naturality of the coherence maps).

## Background

The covariant power-set functor, with the cartesian monoidal structure on sets, becomes a symmetric monoidal functor via the unit map picking out the whole of a one-element set and the comparison map sending a pair of subsets to their product subset; the comparison is not invertible, so the functor is lax but not strong. See the nLab on [monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor) and on [power set](https://ncatlab.org/nlab/show/power+set).

## Current state in the library

No covariant power-set functor exists, so neither the coherence maps nor the naturality square can be written.

- The only `Pow` in the tree is `Structure/Topos.v:129`, `Pow {C} {H : ElementaryTopos C} (a : C) : C := Ω ^ a` — an internal power *object*, not a functor `Sets ⟶ Sets`, and carrying no monoidal comparison maps. `Theory/Subobject/Functor.v`'s `Sub : C^op ⟶ Sets` is contravariant and its object action is the subobject setoid. `Instance/Sets/Image.v`'s `Sets_Image` is the image of a single morphism, not the functorial direct image. `Instance/Ens.v` is the *category* of ensembles and `Instance/Rel.v` curries relations as `A ~> Ensemble B` — a hom type, not a functor. Enumerating the endofunctors on the set-like categories gives `StreamF`, `TracedF`, `StoreF`, `EnvF`, `ListF`, `NatF`, `option_Functor`, `ExcT` — no power set.
- Laxator naturality — Exercise 6.70's square — is available in the tree only *structurally*, as the field `ap_functor_nat : ((⨂) ◯ F ∏⟶ F) ~{[C ∏ C, D]}~> (F ◯ (⨂))` of `LaxMonoidalFunctor` (`Functor/Structure/Monoidal.v:114`). That is an obligation on whoever instantiates the class, not a proved fact about any particular functor.

**Phase-D correction to the coverage record, which changes the size of the job.** The Phase-C search log claimed that "the only inhabited lax/strong monoidal functors in the tree are `Id_*` and `Compose_*`". That is false. Concrete non-trivial strong (symmetric) monoidal functors *are* built in-tree — `BaseChangeF_Monoidal` / `BaseChangeF_Braided` / `BaseChangeF_Symmetric` (`Construction/ColouredPROP/BaseChange.v:352`), the `Relabel` functor (`Construction/ColouredPROP/Relabel.v:388`), `Lawvere_PROP_interp_Symmetric` (`Theory/Lawvere/PROP.v:242`) and the PROP `InterpF_*` tower (`Construction/PROP/Universal.v`). None of them is a power set, so the gap stands, but there are working templates for discharging the laxator obligations rather than a blank page.

## Work to be done

Suggested module: `Instance/Sets/Powerset/Monoidal.v`, over the power-set functor #227 builds in `Instance/Sets/Powerset.v`.

1. Define the coherence maps against the cartesian monoidal structure on `Sets` (`Structure/Monoidal/Cartesian.v:49` / `Structure/Monoidal/Internal/Product.v:314`): `φ_I : 1 → P 1` picking out the maximal subset, and `φ_{S,T} : P S × P T → P (S × T)` sending `(A, B)` to the product subset. Both must respect the predicate setoid `#227` adopts, and the same cross-universe discipline that file records applies here.
2. Discharge the `LaxMonoidalFunctor` obligations: associativity and both unit coherences, and `ap_functor_nat` — which *is* Exercise 6.70's commuting square, with edges `im f × im g`, `φ`, `im (f × g)` and `φ'`. Prove it as a naturality statement, not as a pointwise remark, so the exercise is genuinely discharged by the instance.
3. Upgrade to the symmetric case (`BraidedLaxMonoidalFunctor` / `SymmetricMonoidalFunctor`, `Functor/Structure/Monoidal/Braided.v:54,99`) — the book's Definition 6.68 asks for a *symmetric* monoidal functor, and it is this strengthened form that Theorem 6.77 consumes.
4. Record laxness explicitly: exhibit sets `S`, `T` and a subset of `S × T` that is not a product of subsets, and conclude `φ_{S,T}` is not invertible — so the tree gains its first proved example of a functor that is lax but not strong.

In-tree donors: `Functor/Structure/Monoidal.v` (`LaxMonoidalFunctor`, `ap_functor_nat`), `Functor/Structure/Monoidal/Braided.v`, `Construction/ColouredPROP/BaseChange.v:352` and `Construction/PROP/Universal.v` (worked laxator discharges to imitate), `Structure/Monoidal/Internal/Product.v`, `Instance/Sets.v`, `Instance/Sets/Image.v`.

## Definition of Done

- [ ] `φ_I` and `φ_{S,T}` defined for the covariant power-set functor over the cartesian structure on `Sets`.
- [ ] A `LaxMonoidalFunctor` instance with all coherences discharged, `ap_functor_nat` among them — this is Exercise 6.70 and must be a naturality proof.
- [ ] The symmetric strengthening supplied, matching Definition 6.68.
- [ ] Non-invertibility of `φ_{S,T}` proved with an explicit witness, so "lax but not strong" is a theorem rather than a remark.
- [ ] Statement fidelity to Seven Sketches Example 6.69 and Exercise 6.70 (printed p. 204); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md; any funext or classical dependency is disclosed in the header.
- [ ] `Print Assumptions` reported for the lax monoidal instance and the non-invertibility witness.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Sets/Powerset/Monoidal.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Powerset_LaxMonoidalFunctor.
Print Assumptions Powerset_lax_not_strong.
```
Reviewer: statement matches Seven Sketches Example 6.69 (printed p. 204), and Exercise 6.70's square is discharged as the instance's naturality field rather than restated.

## Dependencies

Depends on: #227 — the covariant power-set functor and its direct-image action, which this issue equips with monoidal structure.
Depends on: #227 (MacLane I.3: the covariant power-set functor) — it CREATES `Instance/Sets/Powerset.v`. NOTE this module is shared by four further issues (#466 the power-set monad, #704 the contravariant/double powerset, #750 the no-initial-algebra result, and this one); they are peers under #227 with no precedence among them, so they must not be worked in the same parallel wave.

<!-- catalog: {"ids": ["7sketches:6.4.1:example6.69", "7sketches:6.4.1:ex6.70"], "deps": ["#227", "#466", "#704", "#750"]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.2: Decorated cospans form a hypergraph category — deriving the coherences from the decoration functor"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.4.2:thm6.77]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.2, printed p. 207 (PDF p. 219). Item `7sketches:6.4.2:thm6.77`. The book states the theorem without proof.

## Background

Given a category with finite colimits and a symmetric monoidal functor from it (with the coproduct structure) into sets (with the product structure), the F-decorated cospans form a hypergraph category whose symmetric monoidal and Frobenius structure are induced by those of the plain cospan category. See the nLab on [decorated cospan](https://ncatlab.org/nlab/show/decorated+cospan) and on [hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category).

## Current state in the library

The entire tower is constructed — and every layer of it is conditional on a coherence class that nothing in the library instantiates, so the implication actually proved is "coherences ⇒ hypergraph category", not the book's "symmetric monoidal F ⇒ hypergraph category".

- `DecoratedCospanCat` (`Construction/DecoratedCospan/Category.v:264`), `DecoratedCospan_Monoidal` (`Construction/DecoratedCospan/Monoidal.v:237`, with `I := initial_obj` and `tensor := DecoratedCospan_Bifunctor`), `DecoratedCospan_BraidedMonoidal` (`Construction/DecoratedCospan/Braided.v:165`, `braid := fun X Y => Dlift (@paws C H_Coc X Y)`), `DecoratedCospan_SymmetricMonoidal` (`Braided.v:246`) and `DecoratedCospan_Hypergraph : @Hypergraph DC DCSMC` (`Construction/DecoratedCospan/Hypergraph.v:205`, all nine fields projected out of `Context {DCHGC : DecCospan_Hypergraph_Coherent}` opened at `:199`).
- Searching `DecCospan_.*Coherent` returns 66 hits across seven files, and **every one** is a `Class` declaration (`Category.v:113`, `Monoidal.v:118`, `Braided.v:110` and `:233`, `Symmetric.v:143`, `Hypergraph.v:155`), a `Context` assumption, or prose. There is no `Instance`, no `Build_`, no `:=` witness anywhere in the tree. The file says so itself at `Hypergraph.v:91-105`: "NONE of these classes is instantiated anywhere in the library … This construction is therefore a CONDITIONAL result … Even the 'trivial decoration' (`F = Δ I_D`) witness is NOT supplied here." Two independent in-tree corroborations exist: `docs/AXIOMS.md:93-105` makes exactly this point, and `Makefile:211` audits `DecoratedCospan_Hypergraph` precisely because the parametric `Print Assumptions` certifies nothing concrete.
- The hypotheses also differ from the book's. The library needs a chosen `HasPushouts C` plus `Cocartesian C` and `Initial C` rather than "finite colimits"; an abstract `MC : @Monoidal C` with a `cospan_merge : N ⊗ M ~> N + M` bridge; and, for the hypergraph layer, the lax-*symmetric* strengthening of F, which the book's Definition 6.68 supplies but which the library encodes only indirectly through the braided/symmetric coherence classes — every file takes a bare `LM : @LaxMonoidalFunctor C D MC MD F` (`Category.v:88`, `Monoidal.v:83`, `Braided.v:78`, `Hypergraph.v:117`, `Symmetric.v:80`) and none assumes `BraidedLaxMonoidalFunctor` (`Functor/Structure/Monoidal/Braided.v:54`).
- The target notion is in-tree at full strength: `Hypergraph` (`Structure/Monoidal/Hypergraph.v:144`) with a per-object special commutative Frobenius supply plus eight tensor/unit coherences.
- One further consequence: `dec_cospan_scfa` is supplied as *data* by the coherence class rather than constructed from `Cospan_Hypergraph`'s Frobenius supply, so the book's clause "the hypergraph structure is induced by that of Cospan_C" is stated but not proved.

## Work to be done

Suggested modules: extend the existing `Construction/DecoratedCospan/*.v` files rather than adding new ones, since the point is to *discharge* what they currently assume.

1. Strengthen the ambient hypothesis from `LaxMonoidalFunctor` to `BraidedLaxMonoidalFunctor` (and its symmetric refinement) wherever the book's Definition 6.68 does, and record in each header which coherence field the strengthening pays for.
2. Derive `DecCospan_Coherent` (`Category.v:113`) from that data: its four fields are the decoration-side identity and associativity equations, and each should follow from the laxator's unit and associativity coherences composed with the pushout copairings.
3. Derive `DecCospan_Bifunctor_Coherent`, `DecCospan_Monoidal_Coherent` (`Monoidal.v:118`), `DecCospan_Braided_Coherent` (`Braided.v:110`), `DecCospan_Symmetric_Coherent` (`Braided.v:233`) and `DecCospan_Hypergraph_Coherent` (`Hypergraph.v:155`) in the same way, each as an `Instance` so that the six `Context` assumptions become theorems.
4. Replace the `dec_cospan_scfa` *datum* by a construction: transport `Cospan_Hypergraph`'s per-object Frobenius supply along the decoration, so the book's "induced by those of Cospan_C" clause is proved rather than assumed.
5. Update `docs/AXIOMS.md:93-105`, `docs/INHABITATION.md` and the `Makefile:211` audit note once the construction is unconditional.

In-tree donors: the six `Construction/DecoratedCospan/*.v` files, `Construction/Cospan/Hypergraph.v` (the undecorated Frobenius supply to transport), `Functor/Structure/Monoidal.v` and `Functor/Structure/Monoidal/Braided.v` (the laxator coherences that must do the work), `Structure/Monoidal/Hypergraph.v`.

## Definition of Done

- [ ] All six `DecCospan_*_Coherent` classes have `Instance`s derived from `(Braided)LaxMonoidalFunctor` data — none remains a bare `Context` assumption.
- [ ] The hypothesis on F matches Definition 6.68 (lax symmetric monoidal), with the strengthening justified in the headers.
- [ ] `dec_cospan_scfa` is constructed by transport from `Cospan_Hypergraph` rather than supplied as data.
- [ ] `DecoratedCospan_Hypergraph` is an unconditional consequence of "F is lax symmetric monoidal", so `Print Assumptions` on it certifies something concrete.
- [ ] `docs/AXIOMS.md:93-105`, `docs/INHABITATION.md` and the `Makefile:211` audit note are updated to reflect the new status.
- [ ] Statement fidelity to Seven Sketches Theorem 6.77 (printed p. 207); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] All files remain registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is flagship-level and changes a headline conditional result into a theorem.

## Verification

```bash
coqc -R . Category Construction/DecoratedCospan/Hypergraph.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions DecoratedCospan_Hypergraph.
Print Assumptions DecCospan_Coherent_from_lax.
```
Reviewer: statement matches Seven Sketches Theorem 6.77 (printed p. 207); confirm that no `DecCospan_*_Coherent` survives as a section hypothesis and that the Frobenius supply is transported, not posited.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.4.2:thm6.77"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.2: The constant decoration recovers the plain cospan category"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:6.4.2:ex6.78]
deps_item_ids: [7sketches:6.4.2:thm6.77]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.2, printed p. 207 (PDF p. 219). Item `7sketches:6.4.2:ex6.78`.

## Background

Taking the decoration functor to be constant at a one-element set gives every apex exactly one decoration, so the decorated-cospan category collapses to the plain cospan category and the decorated-cospan theorem specialises to the plain cospan example. See the nLab on [decorated cospan](https://ncatlab.org/nlab/show/decorated+cospan) and on [cospan](https://ncatlab.org/nlab/show/cospan).

## Current state in the library

Only the forgetful half exists, and the constant decoration itself does not exist at all.

- `Construction/Cospan/BlackBox.v:178` defines `forget_decoration : DecoratedCospanCat HP LM id_decoration cospan_merge ⟶ CospanCat C HP`, identity on objects, discarding the decoration, with functoriality from `forget_decoration_correct_id` (`:127`) and `forget_decoration_correct_compose` (`:133`) — proved for an *arbitrary* lax monoidal decoration. Nothing asserts it is an isomorphism or an equivalence in any case, nothing goes the other way, and it is never shown full, faithful or essentially surjective.
- There is no constant functor `C ⟶ D` in the tree at all. `Functor/Diagonal.v:33` gives `Diagonal {C} (J : Category) : C ⟶ [J, C]`, whose object action yields the constant *diagram* but which carries no `LaxMonoidalFunctor` structure; `Construction/Grothendieck/Strict.v:264`'s `Constant_IndexedCat` is a different construction entirely.
- Even with the functor, `DecoratedCospanCat` cannot be formed at it, because no `DecCospan_Coherent` instance exists (see the decorated-cospan theorem issue for §6.4.2).
- The library names this case as intended work twice: `Construction/DecoratedCospan/Category.v:368` ("A concrete instance — for the trivial decoration `F = const(I_D)` — is the canonical 'no-decoration' case") and `Construction/DecoratedCospan/Hypergraph.v:103` ("Even the 'trivial decoration' (`F = Δ I_D`) witness is NOT supplied here").

*Phase-D correction to the coverage record: its gap text repeated the claim that the only lax/strong monoidal functor instances in the tree are `Id_*` and `Compose_*`. That is false — `BaseChangeF_Symmetric`, `Relabel`, `Lawvere_PROP_interp_Symmetric` and the PROP `InterpF_*` tower are all concrete. The surviving and correct point is that none of them is a constant functor.*

## Work to be done

Suggested modules: `Functor/Constant.v` (new) and `Construction/DecoratedCospan/Trivial.v` (new).

1. Define the constant functor `Const d : C ⟶ D` for a fixed `d : D` (object action constantly `d`, morphism action constantly `id[d]`), and equip `Const I_D` with a `LaxMonoidalFunctor` — indeed a strong symmetric monoidal — structure, using the unitor of `D` for both coherence maps. This is small, general and long overdue in the tree.
2. Instantiate the decorated-cospan tower at it: discharge `DecCospan_Coherent` and its five siblings for the constant decoration (they should follow from the unit coherences alone), so the library finally has *one* concrete decorated-cospan category.
3. Prove the exercise's content: `forget_decoration` at the constant decoration is fully faithful and essentially surjective, hence an equivalence `DecoratedCospanCat (Const I_D) … ≃ CospanCat C HP`; strengthen to an isomorphism of categories if the decoration setoid is a singleton on the nose. Then show the equivalence is symmetric monoidal and carries the hypergraph structure across, so Theorem 6.77 specialises to the plain-cospan statement of §6.3.3.

In-tree donors: `Construction/Cospan/BlackBox.v` (`forget_decoration` and its two correctness lemmas), `Construction/DecoratedCospan/*.v`, `Functor/Diagonal.v`, `Functor/Structure/Monoidal/Id.v` (the shape of a trivially-lax instance), `Theory/Equivalence.v`, `Theory/Equivalence/FullFaithful.v`.

## Definition of Done

- [ ] A general constant functor exists, with its strong symmetric monoidal structure at the unit.
- [ ] The decorated-cospan tower is instantiated at the constant decoration — the library's first concrete decorated-cospan category, closing the promises at `Construction/DecoratedCospan/Category.v:368` and `Hypergraph.v:103`.
- [ ] `forget_decoration` at the constant decoration is proved full, faithful and essentially surjective, and the resulting equivalence is shown symmetric monoidal.
- [ ] The hypergraph structure is shown to transport across the equivalence, so Theorem 6.77 visibly specialises to the plain-cospan case.
- [ ] Statement fidelity to Seven Sketches Exercise 6.78 (printed p. 207); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — this supplies the decorated-cospan witness both currently record as missing.

## Verification

```bash
coqc -R . Category Functor/Constant.v
coqc -R . Category Construction/DecoratedCospan/Trivial.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Const_SymmetricMonoidalFunctor.
Print Assumptions trivial_decoration_equivalence.
```
Reviewer: statement matches Seven Sketches Exercise 6.78 (printed p. 207) — the comparison must be shown invertible, not merely defined.

## Dependencies

Depends on: 7sketches:6.4.2:thm6.77

<!-- catalog: {"ids":["7sketches:6.4.2:ex6.78"],"deps":["7sketches:6.4.2:thm6.77"]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.3: C-circuits — edge-labelled graphs over a component set"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.4.3:def-c-circuit, 7sketches:6.4.3:ex6.79]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.3, printed pp. 207–208 (PDF pp. 219–220). Items `7sketches:6.4.3:def-c-circuit` (an unnumbered definition made in running prose under the lead "Let's build some circuits") and `7sketches:6.4.3:ex6.79` (encode the displayed bridge circuit as a tuple).

## Background

Fixing a set of circuit components, a C-circuit is a directed graph — vertices, edges, source and target — together with a labelling assigning a component to each edge, so a circuit is a five-tuple; the encoding is not unique, since reversing an edge represents the same physical circuit. See the nLab on [quiver](https://ncatlab.org/nlab/show/quiver) and Wikipedia on [electrical networks](https://en.wikipedia.org/wiki/Electrical_network).

## Current state in the library

The graph half is present in indexed form; the labelling, the component set, and therefore the circuit itself are not.

- `Construction/Free/Quiver.v:54` gives `Class Quiver@{o h p} := { nodes : Type@{o}; uedges := Type@{h} : Type@{h+1}; edges : nodes → nodes → uedges; edgeset : ∀ X Y, Setoid@{h p} (edges X Y) }`, glossed in the header (`:21`, `:57`) as a directed multigraph with arrows indexed by source and target. The indexed form and the book's span form are interchangeable (the edge set is `Σ_{x,y} edges x y`), and the in-tree version is if anything stronger, since each edge set is a setoid.
- Nothing carries a labelling. There is no `Circuit` type, no edge-labelled graph, and no record of the book's five-tuple.
- The component set cannot be written either: `Coq.Reals`, `Rdefinitions` and `R0` return zero hits across the tree, so ℝ⁺ — and hence the resistance labels — has no carrier. The nearest analogue for "a set of components" is `Definition Signature : Type := nat → nat → Type` (`Construction/PROP/Signature.v:50`), whose comment at `:39-41` even sketches battery/resistor/Y-junction as `Sig 0 1`/`Sig 1 1`/`Sig 2 1` — but that is an *arity-graded* generator set for string diagrams, not the book's ungraded label set, and no labelling of a graph by it is defined.
- There is no in-tree remark that distinct tuples may denote the same circuit, and no quotient by edge reversal.

*Phase-D correction to the coverage record: its negative log claimed that a grep for `labelled graph|labeled graph|labelling|labeling|edge label|vertex|vertices|C-circuit` returns **zero** hits. It does not — `vertex_obj` occurs 27 times (cone apices, in `Theory/Equivalence/Limit.v`, `Instance/Cones*.v`, `Structure/Limit/*.v`, `Construction/Comma/Limit.v`), `labeling` 13 times in `Instance/FinSet/Pushout.v` (the union-find labelling), and `labelled` in `Instance/ZX.v:172`, `Instance/Shapes.v:29`, `Instance/Coq/Comonad/Env.v:69`, `Construction/PROP/Signature.v:45`. None of these is an edge-labelled graph or the vertex/edge set of one, so the classification is unaffected — but the log's absoluteness is wrong and should not be repeated. The companion claim about `Coq.Reals` **is** correct.*

## Work to be done

Suggested modules: `Construction/Graph/Labelled.v` (the general notion) and `Instance/Circuit.v` (the component set and the worked circuit).

1. Define an edge-labelled graph over a label type: either a `Quiver` together with `label : ∀ x y, edges x y → L`, or a standalone record in the book's span form with `V`, `A`, `s`, `t`, `l`. Prefer extending `Quiver`, so the free-category machinery of `Construction/Free/Quiver.v` remains available and the two presentations do not drift; if the span form is chosen, prove the two equivalent.
2. Define the component set: an inductive `{light; switch; battery}` plus a numeric-resistance constructor. **Do not import `Coq.Reals`** — nothing in the tree does, and pulling in its axioms for a label set would be a poor trade; use ℚ, `nat`, or an abstract ordered carrier parameter, and disclose the choice and its consequence (the book's ℝ⁺ is replaced) in the header.
3. Record the non-uniqueness the book points out as an explicit statement — two distinct labelled graphs, differing by the reversal of one edge, denoting the same physical circuit — rather than silently quotienting. A quotient is *not* wanted here: the decoration functor of the next section is defined on the tuples.
4. Discharge Exercise 6.79: the four-node bridge circuit of display (6.71) — a 2-ohm resistor and a 3-farad capacitor in parallel across the top, a 1-ohm resistor on each side, a 1-henry inductor across the bottom — as a closed term of the circuit type, with a `Compute`-checkable sanity `Example` on its edge count.

In-tree donors: `Construction/Free/Quiver.v` (`Quiver`, `QuiverHomomorphism`), `Construction/PROP/Signature.v` (the component-set sketch at `:39-41`), `Instance/FinSet.v` (finite vertex sets), `Instance/Shapes.v`.

## Definition of Done

- [ ] An edge-labelled graph type exists over an arbitrary label type, related to the existing `Quiver` rather than duplicating it.
- [ ] A concrete component set exists, with the choice of numeric carrier and its divergence from the book's ℝ⁺ disclosed in the header; no `Coq.Reals` dependency is introduced.
- [ ] The non-uniqueness of the encoding is recorded as an explicit statement, and no quotient is imposed.
- [ ] Exercise 6.79's bridge circuit exists as a closed term with a computing sanity `Example`.
- [ ] Statement fidelity to Seven Sketches §6.4.3 (printed pp. 207–208); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Construction/Graph/Labelled.v
coqc -R . Category Instance/Circuit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions LabelledGraph.
Compute (* edge count of the Exercise 6.79 bridge circuit *).
```
Reviewer: statement matches Seven Sketches §6.4.3 (printed pp. 207–208) — the labelling is part of the data, and the header discloses the numeric-carrier substitution.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.4.3:def-c-circuit","7sketches:6.4.3:ex6.79"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.3: The circuit decoration functor from finite sets to sets"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.4.3:construction-circ, 7sketches:6.4.3:ex6.80, 7sketches:6.4.3:ex6.82]
deps_item_ids: [7sketches:6.4.3:def-c-circuit]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.3, printed p. 208 (PDF p. 220). Items `7sketches:6.4.3:construction-circ` (an unnumbered construction developed in prose under the lead "A decoration functor for circuits", including the coherence map of display (6.81)), `7sketches:6.4.3:ex6.80` (compute the functor's action on a node-merging function) and `7sketches:6.4.3:ex6.82` (compute the coherence map on two two-node circuits).

## Background

Sending a finite set to the set of circuits with that vertex set, and a function to the relabelling of endpoints along it, gives a functor from finite sets to sets; putting two circuits side by side on the disjoint union of their vertex sets makes it symmetric monoidal from the coproduct structure to the product structure — exactly the input the decorated-cospan theorem consumes. See the nLab on [monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor) and on [decorated cospan](https://ncatlab.org/nlab/show/decorated+cospan).

## Current state in the library

Absent. Nothing named `Circ` exists: the only two occurrences of the token in the tree are comments in `Construction/Cospan/BlackBox.v:19,64` citing Baez–Fong's black-box functor as motivation, and all 26 further "circuit" hits are prose or the unrelated "short-circuits" of `Theory/Coq/Either.v` and `Theory/Coq/Maybe.v`.

- The *source* of the functor is fully present: `FinSet_Initial` (`Instance/FinSet.v:223`), `FinSet_Cocartesian` (`:250`) and `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v:513`) give `(FinSet, +)`. The *target* is `Sets`. But no functor out of `FinSet` into `Sets` of any kind exists — enumerating `Instance/FinSet/` (`Classifier.v`, `Closed.v`, `Lawvere.v`, `Product.v`, `Pushout.v`, `Topos.v`) turns up none.
- The object action has nothing to range over, since no edge-labelled graph type exists (see the §6.4.3 C-circuit issue).
- The nearest in-tree operation is `QuiverHomomorphism` (`Construction/Free/Quiver.v:205`, `fnodes : nodes G → nodes G'` plus a fibrewise `fedgemap`), which is a map *between* quivers, not a pushforward of one quiver along a bare function on nodes — which is what the morphism action is — and it carries no labels.
- `Construction/DecoratedCospan/Hypergraph.v:66-67` states plainly that "this library does not yet provide any such instance".
- `lax_ap` is never applied to a concrete functor: outside `Functor/Structure/Monoidal.v` (the field), `Functor/Structure/Monoidal/Braided.v` (the compatibility square) and `Construction/DecoratedCospan.v:295` (the composition formula), it does not occur.

*Phase-D correction: the coverage record's log claimed the only inhabited lax/strong monoidal functors in the tree are `Id_*` and `Compose_*`. That is false — `BaseChangeF_Monoidal`/`Braided`/`Symmetric` (`Construction/ColouredPROP/BaseChange.v:352`), `Relabel` (`Construction/ColouredPROP/Relabel.v:388`), `Lawvere_PROP_interp_Symmetric` (`Theory/Lawvere/PROP.v:242`) and the PROP `InterpF_*` tower are concrete strong symmetric monoidal functors. None is a circuit decoration, so the gap stands, but there are worked laxator discharges to copy.*

## Work to be done

Suggested module: `Instance/Circuit/Decoration.v`.

1. Object action: `Circ V` := the setoid of circuits with vertex set `V` — over the edge-labelled graph type of the §6.4.3 C-circuit issue, with an appropriate equivalence on the edge data. Choosing that setoid carefully is the design decision of this issue; the header must say what it is and why (in particular whether edge sets are compared up to bijection).
2. Morphism action: for `f : V → V'`, `Circ f` keeps the edges and their labels and relabels endpoints by post-composition with `f` — note this may merge nodes, which is the point of Exercise 6.80. Prove `fmap_id`, `fmap_comp` and respectfulness.
3. Coherence maps: `ψ_{V,V'} : Circ V × Circ V' → Circ (V + V')` placing two circuits side by side (edge set the disjoint union, labelling the copairing), and the unit map at the empty vertex set. Discharge the `LaxMonoidalFunctor` obligations from `(FinSet, +)` to `(Sets, ×)` — in fact `ψ` is invertible here, so the *strong* symmetric monoidal structure should be proved, and the header should note that this is stronger than Definition 6.75 requires.
4. Discharge Exercises 6.80 and 6.82 as computations on closed terms: `Circ f` applied to the lightbulb-and-resistor circuit on four nodes along the merging function into three nodes, and `ψ_{2,2}` applied to the battery and switch circuits — both with `Compute`/`eq_refl` sanity `Example`s wherever the chosen setoid makes that possible, and with an explicit `≈` proof otherwise.

In-tree donors: `Instance/FinSet.v`, `Instance/FinSet/Pushout.v`, `Instance/Sets.v`, `Functor/Structure/Monoidal.v` and `Functor/Structure/Monoidal/Braided.v`, `Construction/ColouredPROP/BaseChange.v:352` and `Construction/PROP/Universal.v` (worked laxator discharges), `Construction/Free/Quiver.v`.

## Definition of Done

- [ ] `Circ : FinSet ⟶ Sets` defined with both functor laws and respectfulness; the choice of setoid on circuits is disclosed in the header.
- [ ] The coherence maps of display (6.81) defined and the lax symmetric monoidal obligations discharged; strongness proved if it holds, with a note that Definition 6.75 asks only for laxness.
- [ ] Exercise 6.80's node-merging computation carried out on a closed term.
- [ ] Exercise 6.82's side-by-side computation carried out on closed terms.
- [ ] Statement fidelity to Seven Sketches §6.4.3 (printed p. 208); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for the functor and its monoidal structure.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is the first concrete decoration functor in the tree.

## Verification

```bash
coqc -R . Category Instance/Circuit/Decoration.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Circ.
Print Assumptions Circ_LaxMonoidalFunctor.
```
Reviewer: statement matches Seven Sketches §6.4.3 (printed p. 208) — in particular the morphism action must relabel endpoints along `f` while keeping edges and labels, so node merging is possible.

## Dependencies

Depends on: 7sketches:6.4.3:def-c-circuit

<!-- catalog: {"ids":["7sketches:6.4.3:construction-circ","7sketches:6.4.3:ex6.80","7sketches:6.4.3:ex6.82"],"deps":["7sketches:6.4.3:def-c-circuit"]} -->

---8<---

```yaml
title: "Seven Sketches 6.4.3: Cospan_Circ, the hypergraph category of open electric circuits"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.4.3:construction-cospan-circ, 7sketches:6.4.3:ex6.84, 7sketches:6.4.3:ex6.86, 7sketches:6.4.3:ex6.88]
deps_item_ids: [7sketches:6.4.3:construction-circ, 7sketches:6.4.2:thm6.77]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.4.3, printed pp. 209–211 (PDF pp. 221–223). Items `7sketches:6.4.3:construction-cospan-circ` (an unnumbered construction developed under the leads "Open circuits using decorated cospans", "Composition in Cospan_Circ" and "Monoidal products in Cospan_Circ", with displays (6.83), (6.85) and (6.87)), `7sketches:6.4.3:ex6.84` (identify the decoration of the battery open circuit), `7sketches:6.4.3:ex6.86` (recompute the introductory composition) and `7sketches:6.4.3:ex6.88` (close off an open circuit with a cup and a cap).

## Background

Feeding the circuit decoration functor into the decorated-cospan theorem produces a hypergraph category whose objects are finite interface sets and whose morphisms are open circuits; composition glues along the shared interface by a pushout and pushes the combined decoration forward, and the monoidal product stacks circuits side by side. See the nLab on [decorated cospan](https://ncatlab.org/nlab/show/decorated+cospan), on [hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category) and Wikipedia on [electrical networks](https://en.wikipedia.org/wiki/Electrical_network).

## Current state in the library

Everything general is present and in fact stronger than the book asks; everything specific to circuits is missing.

- The composition rule the section applies is in-tree and general: `dec_cospan_compose` (`Construction/DecoratedCospan.v:303`) pairs `cospan_compose` with `dec_compose_decoration` (`:291`), the latter being `fmap[F] (pushout_in1 P ▽ pushout_in2 P) ∘ fmap[F] (cospan_merge N M) ∘ lax_ap[F] ∘ bimap (dc_decoration f) (dc_decoration g) ∘ from (unit_left)` — the book's rule verbatim. `cospan_compose` (`Construction/Cospan/Category.v:135`) takes the pushout of the shared foot, and `cospan_compose_apex` (`:535`, by `reflexivity`) makes the book's apex `N +_B M` definitional.
- The premise of Exercise 6.84 is likewise in-tree in full generality: `DecoratedCospanArrow` (`Construction/DecoratedCospan.v:120`) is exactly a cospan plus a decoration of its apex, presented as a generalized element `I ~> F (cospan_apex …)`.
- The cup/cap structure of Exercise 6.88 is in-tree and **stronger than the exercise asks**: `Hypergraph_CompactClosed` (`Structure/Monoidal/CompactClosed.v:303`) gives `dual X := X`, `cc_unit X : I ~> dual X ⨂ X` and `cc_counit X : X ⨂ dual X ~> I` built from the per-object Frobenius supply, and the class at `:139-160` carries **both** snake identities as fields — the book merely exhibits the two cospans. In the cospan category these unfold through `cospan_scfa_eta` and `cospan_scfa_delta` (`Construction/Cospan/Hypergraph.v:124-125,131-132`).
- What is missing: there is no `Circ` decoration functor (see the §6.4.3 decoration-functor issue), so no morphism of the intended category can be written; no `DecCospan_Coherent` instance exists at all (all twenty uses of the class are `Context` hypotheses; the only defining occurrence is `Construction/DecoratedCospan/Category.v:113`), so `DecoratedCospanCat` has no concrete decoration whatsoever; there is no worked composition of two decorated cospans at concrete data anywhere; the book's `η : 0 → 2` in its explicit `0 → 1 ← 2` singleton-apex form is never recorded, and no instantiation at the finite set `1` appears; and "closed circuit" — an endomorphism of the monoidal unit — has no in-tree name, since the tree has no scalar or `End(I)` vocabulary at all (every `scalar` hit is restriction/extension of scalars or unrelated).
- `Construction/Cospan/BlackBox.v:233-235` lists exactly this construction, and its black-box variants into `Vect_R` and `ZX_Cat`, as un-built.

Two notes for whoever takes this on. First, do **not** re-file the coverage of Definition 6.75 here: the decorated-cospan definition itself is already present, and Exercise 6.84's premise is that definition — only the identification of the particular decoration is missing. Second, the book has a typo in Exercise 6.88: the second cospan is called η in the prose but ε in the display; the formalisation should follow the display and note the discrepancy in the header.

## Work to be done

Suggested module: `Instance/Circuit/Cospan.v`.

1. Instantiate the decorated-cospan tower at `(Circ, ψ)` over `FinSet`: discharge the six `DecCospan_*_Coherent` obligations for this decoration (or consume them as theorems once the §6.4.2 decorated-cospan issue derives them from lax monoidality), obtaining `CospanCirc` as a symmetric monoidal, indeed hypergraph, category.
2. Discharge Exercise 6.84: exhibit the morphism of display (6.83) — the cospan `1 → 2 ← 1` decorated by the battery circuit on two vertices — as a closed term, and prove its decoration is the single-battery-edge circuit.
3. Discharge Exercise 6.86: express the two circuits of display (6.73) as morphisms, compute their composite with `dec_cospan_compose`, and prove the result equals the circuit of display (6.74) — using `cospan_compose_apex` so the apex is definitionally the pushout `N +_B M`.
4. Discharge Exercise 6.88: define `η : 0 → 2` and `ε : 2 → 0` as the singleton-apex cospans decorated by the empty circuit on one vertex, relate them to `cc_unit`/`cc_counit` at the finite set `1` (so the general compact-closed structure is visibly the same maps), and compute the composite `η ; x ; ε` for the stacked circuit of display (6.87).
5. Introduce the missing scalar vocabulary: `Scalar C := I ~> I` for a monoidal `C`, with its commutative-monoid structure, and define a closed circuit as a scalar of `CospanCirc`. This is small, general and wanted independently — the tree has no `End(I)` notion at all.

In-tree donors: `Construction/DecoratedCospan.v` and `Construction/DecoratedCospan/*.v`, `Construction/Cospan/Category.v`, `Construction/Cospan/Hypergraph.v`, `Structure/Monoidal/CompactClosed.v`, `Construction/Cospan/BlackBox.v`, `Instance/FinSet/Pushout.v`.

## Definition of Done

- [ ] `CospanCirc` exists as a concrete hypergraph category — the library's first inhabited decorated-cospan category.
- [ ] Exercise 6.84's morphism and its decoration are exhibited and identified.
- [ ] Exercise 6.86's composition is computed and proved equal to the book's answer, with the apex the pushout.
- [ ] Exercise 6.88's cup and cap are defined, related to `cc_unit`/`cc_counit`, and the closed composite computed; the book's prose/display naming discrepancy is noted in the header.
- [ ] A general `Scalar C := I ~> I` notion exists with its commutative-monoid structure, and "closed circuit" is defined in terms of it.
- [ ] Statement fidelity to Seven Sketches §6.4.3 (printed pp. 209–211); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for `CospanCirc` and each worked computation.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — this is flagship-level and closes the un-built variant list at `Construction/Cospan/BlackBox.v:233-235`.

## Verification

```bash
coqc -R . Category Instance/Circuit/Cospan.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CospanCirc.
Print Assumptions CospanCirc_Hypergraph.
Print Assumptions battery_switch_composite.
```
Reviewer: statement matches Seven Sketches §6.4.3 (printed pp. 209–211); confirm the composites are *computed* by the general rule rather than posited, and that Definition 6.75's own coverage is not re-filed here.

## Dependencies

Depends on: 7sketches:6.4.3:construction-circ
Depends on: 7sketches:6.4.2:thm6.77

<!-- catalog: {"ids":["7sketches:6.4.3:construction-cospan-circ","7sketches:6.4.3:ex6.84","7sketches:6.4.3:ex6.86","7sketches:6.4.3:ex6.88"],"deps":["7sketches:6.4.3:construction-circ","7sketches:6.4.2:thm6.77"]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.1: Context-free grammars present free operads"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.1:example6.92]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.1, printed p. 214 (PDF p. 226). Item `7sketches:6.5.1:example6.92`. The book states the correspondence in prose, attributing it to Hermida–Makkai–Power, and gives no construction.

## Background

Context-free grammars are to operads as graphs are to categories: the syntactic categories are the types and the production rules the generating operations, so a grammar presents a free operad in the same way a graph presents a free category. See the nLab on [context-free grammar](https://ncatlab.org/nlab/show/context-free+grammar) and on [operad](https://ncatlab.org/nlab/show/operad).

## Current state in the library

Absent on both sides of the correspondence.

- There is no context-free grammar anywhere. All nine hits for `context.?free|grammar|production rule|syntactic categor` are incidental prose: `Solver/Denote.v:21` ("the `Term` grammar"), `Instance/Lambda/Ty.v:10` and `Instance/Lambda/Value.v:15,21` (the object-language term grammar), `Instance/Lambda.v:94`, `Construction/Quotient.v:18,151,215` ("syntactic category" in the ordinary categorical sense) and `Structure/Monoidal/Symmetric.v:91` (Coecke's "grammar"). No alphabet, nonterminal or production rule is defined.
- There is **no free construction at the operad or multicategory level at all**: `free (operad|multicategor)|FreeOperad|FreeMulti` returns zero hits. The six `Theory/Multicategory*.v` files carry the structure but never a freeness result.
- Free props exist one level up — `Construction/PROP/Free.v` and `Construction/ColouredPROP/Free.v` — but those are symmetric monoidal categories, not operads, and are deliberately not credited here.
- The analogue the correspondence is stated against **is** in-tree and is the template: `Construction/Free/Quiver.v:431` `FreeOnQuiver` with the free/forgetful adjunction at `:550`.

## Work to be done

Suggested modules: `Theory/Multicategory/Free.v` (the free operad on a signature) and `Instance/Grammar.v` (grammars and the correspondence).

1. Define the free (coloured) operad on a multi-signature: a type of colours, and for each list of input colours and output colour a set of generating operations; the free operad's operations are the well-formed trees over those generators, quotiented by nothing beyond the operad axioms. `Construction/ColouredPROP/Free.v`'s term construction over list-of-colour boundaries is the closest in-tree pattern; `Theory/Multicategory.v`'s zipper `mcomp` signature and `mcast` boundary-coercion pack are what the trees must satisfy.
2. Prove the universal property: multifunctors out of the free operad correspond to interpretations of the generators, matching `Construction/PROP/Universal.v`'s shape one level up.
3. Define a context-free grammar as exactly that data — nonterminals as colours, terminals as nullary generators, production rules as generating operations — and prove the correspondence: the free operad on a grammar's rules is the operad whose types are the syntactic categories, with derivations as operations.
4. State the parallel with graphs and free categories explicitly, citing `Construction/Free/Quiver.v:550`, so the analogy the book draws is recorded rather than left to the reader.

In-tree donors: `Theory/Multicategory.v`, `Theory/Multicategory/Operad.v`, `Theory/Multicategory/Functor.v`, `Construction/ColouredPROP/Free.v` and `Construction/ColouredPROP/Interp.v`, `Construction/PROP/Universal.v`, `Construction/Free/Quiver.v`.

## Definition of Done

- [ ] A free (coloured) operad on a multi-signature exists, with its universal property proved.
- [ ] A context-free grammar type exists — alphabet, nonterminals, production rules — as first-class data.
- [ ] The correspondence is proved: the free operad on a grammar has the syntactic categories as types and the derivations as operations.
- [ ] The analogy with graphs and free categories is recorded, with a cross-reference to the quiver development.
- [ ] Statement fidelity to Seven Sketches Example 6.92 (printed p. 214); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping); any UIP-on-colour-lists discipline follows the axiom-free Hedberg pattern of `Theory/Multicategory/Representable.v` and is disclosed in the header.
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the first freeness result at the operad level.

## Verification

```bash
coqc -R . Category Theory/Multicategory/Free.v
coqc -R . Category Instance/Grammar.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions FreeOperad.
Print Assumptions grammar_presents_free_operad.
```
Reviewer: statement matches Seven Sketches Example 6.92 (printed p. 214); the free construction must be at the *operad* level, not the prop level.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.5.1:example6.92"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.2: The many-coloured operad of sets and multi-argument functions"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.2:example6.93]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.2, printed pp. 214–215 (PDF pp. 226–227). Item `7sketches:6.5.2:example6.93`.

## Background

The operad whose types are all sets and whose operations of arity (X₁, …, Xₙ; Y) are the functions from the product of the Xᵢ into Y, with substitution plugging one function into an argument slot of another, is the target operad in which algebras are taken. See the nLab on [operad](https://ncatlab.org/nlab/show/operad) and on [multicategory](https://ncatlab.org/nlab/show/multicategory).

## Current state in the library

The one-coloured shadow of the operad is in-tree and faithful; the many-coloured operad itself is not, and the obstruction is precise.

- `Theory/Multicategory/Endomorphism.v:1052` builds `EndOperad : Multicategory` with `mobj := poly_unit`, `End_hom Γ _ := pow (length Γ) ~{C}~> X` (`:420-421`), `End_mid a := exl` (`:427`) and `End_mcomp f g := f ∘ pow_cast _ ∘ graft (length Γ₁) (length Δ) (length Γ₂) g ∘ pow_cast _` (`:429-434`). Clauses (ii)–(iv) of the book's definition are realised verbatim — operations are multi-argument morphisms out of the n-fold cartesian power, substitution is grafting into the ith slot with identities elsewhere, and the identity is the projection out of the one-fold power. Clause (i) is where it is weaker: `mobj := poly_unit`, so there is exactly **one** type. `EndOperad` is therefore the classical End(X), the one-object full sub-operad of the book's operad at a chosen carrier — not the many-coloured operad in which algebras of a coloured operad must land.
- The generic recipe that would build the many-coloured version exists — `Fold_Multicategory` / `RepresentableMulticategory` (`Theory/Multicategory/Representable.v:763`) over a symmetric monoidal base — and `Sets` carries the required cartesian symmetric monoidal structure (`CC_SymmetricMonoidal`, `Structure/Monoidal/Internal/Product.v:314`). But the recipe additionally demands `luip : ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q` (taken as an explicit argument at `Representable.v:863-866`), and the file's only discharge route is `list_uip_of_dec` (`:879-882`) from an element **decider** — which `obj Sets` does not have, setoid objects carrying no decidable equality. Phase-D verification confirmed both ends of this: the base structure is not the blocker, `luip` is.
- No instance of any kind is built: `RepresentableMulticategory` and `Fold_Multicategory` have no use anywhere outside `Theory/Multicategory/Representable.v`.

This gap is what blocks the coloured-operad-algebra definition, the circuit algebra example and the hypergraph-prop proposition later in §6.5.

## Work to be done

Suggested module: `Instance/Sets/Operad.v`, with any weakening of the recipe landing in `Theory/Multicategory/Representable.v`.

Two routes; the header must record which was taken and why.

- **(a) Direct.** Build the operad with `mobj := obj Sets` and `mhom Γ c` the setoid of morphisms from the *heterogeneous* product of the Γ-fibres into `c`, indexing the product structurally over the list rather than by a cast on `length Γ`. This sidesteps list-UIP entirely, because no boundary equation is ever transported — the zipper `mcomp` signature of `Theory/Multicategory.v` already splices lists without needing them to be propositionally equal.
- **(b) Weaken the recipe.** Replace `Representable.v`'s `luip` hypothesis by the proof-irrelevant boundary coercion the multicategory class already supplies: `Theory/Multicategory.v`'s `mcast` groupoid pack with its any-proof law variants is designed exactly so that two proofs of the same boundary equation act identically. If that suffices, `Fold_Multicategory` becomes available over `Sets` and every other non-decidable base, which is a considerably larger win than this one instance.

Either way: prove the four clauses of Definition 6.91 against the book's reading — substitution `g ∘ᵢ f` must be *the* function plugging `f`'s value into the ith argument — and supply `EndOperad X` as the one-coloured full sub-operad at a chosen carrier, so the existing development is exhibited as a special case rather than left disconnected.

In-tree donors: `Theory/Multicategory.v` (the zipper `mcomp` and the `mcast` pack), `Theory/Multicategory/Representable.v`, `Theory/Multicategory/Endomorphism.v`, `Structure/Monoidal/Internal/Product.v`, `Instance/Sets.v`, `Instance/Sets/Cartesian.v`.

## Definition of Done

- [ ] A many-coloured operad of sets exists, with types all objects of `Sets` and operations the multi-argument functions.
- [ ] All four clauses of Definition 6.91 proved, substitution matching the book's slot-plugging formula.
- [ ] The route taken around the `luip` obstruction is disclosed in the header; if route (b), `Theory/Multicategory/Representable.v`'s hypothesis is genuinely weakened and the existing `ColouredPROP` consumer still compiles.
- [ ] `EndOperad X` is exhibited as the one-coloured sub-operad at a chosen carrier.
- [ ] Statement fidelity to Seven Sketches Example 6.93 (printed pp. 214–215); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for the operad and its comparison with `EndOperad`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the first inhabited many-coloured operad in the tree.

## Verification

```bash
coqc -R . Category Instance/Sets/Operad.v
coqc -R . Category Theory/Multicategory/Representable.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions SetsOperad.
Print Assumptions EndOperad_is_SetsOperad_at.
```
Reviewer: statement matches Seven Sketches Example 6.93 (printed pp. 214–215) — the types must be *all* sets and arities heterogeneous, not a single carrier.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.5.2:example6.93"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.2: The operad Cospan of finite-set cospans, and substitution as nesting"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.2:example6.94, 7sketches:6.5.2:ex6.96]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.2, printed pp. 215–216 (PDF pp. 227–228). Items `7sketches:6.5.2:example6.94` (the operad, with the wiring-diagram reading of display (6.95)) and `7sketches:6.5.2:ex6.96` (four parts: draw two given cospans as wiring diagrams, compute a substitution and state its arity, and observe that substitution is nesting).

## Background

Types are natural numbers, an operation of arity (a₁, …, aₙ; b) is a cospan from the sum of the aᵢ to an apex with b mapping in, substitution is pushout, and the identity is the identity cospan — the operadic analogue of the symmetric monoidal category of cospans of finite sets, read graphically as wiring diagrams whose substitution is the nesting of one diagram inside a circle of another. See the nLab on [operad](https://ncatlab.org/nlab/show/operad) and on [cospan](https://ncatlab.org/nlab/show/cospan).

## Current state in the library

The book's own gloss — "the operadic analogue of (Cospan_FinSet, 0, +)" — is in-tree at full strength, over an arbitrary base; the operad itself is never formed.

- `Cospan_SymmetricMonoidal` (`Construction/Cospan/Symmetric.v:398`) over `Cospan_Monoidal` (`Construction/Cospan/Hypergraph.v:1973`, `I := Cospan_unit_obj`, `tensor := Cospan_Bifunctor`), with morphisms the cospans of `Construction/Cospan/Category.v` composed by pushout (`cospan_compose`, `:135`) and `cospan_compose_apex` (`:535`) proved by `reflexivity`. Over `FinSet` the required base structure is all present: `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v:513`), `FinSet_Initial` (`Instance/FinSet.v:223`), `FinSet_Cocartesian` (`:250`).
- No multicategory whose operations of arity (a₁,…,aₙ; b) are cospans is ever formed: `RepresentableMulticategory` and `Fold_Multicategory` have no use outside `Theory/Multicategory/Representable.v`.

**Phase-D verification established the decisive point, which changes how big this job is:** this instance is **not** blocked by the `luip` hypothesis that blocks the many-coloured operad of sets. `obj (CospanCat FinSet) = obj FinSet = nat` (`Construction/Cospan/Category.v:560-561`, `Instance/FinSet.v:117`), which has decidable equality, so `list_uip_of_dec Nat.eq_dec` discharges `luip` outright. The shapes agree on the nose as well: a `Fold_Multicategory` multimorphism `Γ ⟶ c` over `(CospanCat FinSet, 0, +)` is a morphism `tfold Γ ~> c`, i.e. a cospan `(a₁ + … + aₙ) → p ← b`, and its `mcomp` is the book's substitution. The missing step is an instantiation, not new mathematics.

For Exercise 6.96, part (3)'s arity bookkeeping is exactly the library's zipper signature: `mcomp {Γ₁ Γ₂ Δ b c} : mhom (Γ₁ ++ b :: Γ₂) c → mhom Δ b → mhom (Γ₁ ++ Δ ++ Γ₂) c`, realised in `Fold_Multicategory` as `f ∘ msplice ob Γ₁ g`, so `g` of arity (2,2,2;0) with `f` of arity (2,2;2) substituted at the first slot has arity (2,2,2,2;0); and `cospan_compose_apex` computes the new apex. Parts (1), (2) and (4) are purely graphical — there is no wiring-diagram formalism in the tree (`wiring diagram`, zero hits) and none is required, since the cospan data *is* the diagram.

## Work to be done

Suggested module: `Instance/FinSet/Cospan/Operad.v`.

1. Form `CospanCat FinSet` as a named in-tree term. **Nothing in the tree does this today** — see the Definition of Done below for why that matters — and everything here needs it.
2. Instantiate `Fold_Multicategory` at `(CospanCat FinSet, Cospan_unit_obj, Cospan_Bifunctor)` with `ob := id` on `nat`, discharging `luip` by `list_uip_of_dec Nat.eq_dec`, and expose the result as `CospanOperad` with the four clauses of Definition 6.91 stated in the book's vocabulary (types are naturals; an operation of arity (a₁,…,aₙ;b) is a cospan; substitution is pushout; the identity is the identity cospan).
3. Discharge Exercise 6.96: the cospans of parts (1) and (2) as closed terms, the substitution of part (3) computed with its arity, and part (4)'s observation recorded as the statement that `mcomp` at these operations is the pushout gluing — i.e. that nesting *is* substitution. Make the arity a `Compute`-checkable fact.
4. Record in the header that the graphical parts of the exercise are discharged by the underlying cospan data, since no wiring-diagram language exists or is needed.

In-tree donors: `Theory/Multicategory/Representable.v` (`Fold_Multicategory`, `list_uip_of_dec`, `msplice`, `tfold`), `Construction/Cospan/Category.v`, `Construction/Cospan/Symmetric.v`, `Construction/Cospan/Hypergraph.v`, `Instance/FinSet.v`, `Instance/FinSet/Pushout.v`.

## Definition of Done

- [ ] `CospanCat FinSet` exists as a named in-tree term, and `CospanOperad` is built from it via `Fold_Multicategory` with `luip` discharged by decidability of equality on `nat`.
- [ ] The four clauses of Definition 6.91 are stated and proved in the book's vocabulary for this operad.
- [ ] Exercise 6.96's substitution is computed at the exercise's data, with its arity a checkable fact, and part (4)'s nesting observation stated.
- [ ] **Library defect, closed here:** the tree currently never forms `CospanCat FinSet` in code — the only evidence that it typechecks is prose at `docs/INHABITATION.md:73-78` — and this matters because the *same* construction is documented at `docs/INHABITATION.md:62-71` to be universe-**inconsistent** over `Sets`. The named term is the guard against that claim bit-rotting under `make`.
- [ ] **Library defect, corrected here:** `Construction/Cospan/Category.v:45` states that "cospans of monos in `Set` present corelations". That is wrong — corelations are jointly-**epic** cospans, per `Construction/Cospan/Corelation.v:22-27`. Fix the header sentence.
- [ ] Statement fidelity to Seven Sketches Example 6.94 and Exercise 6.96 (printed pp. 215–216); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for `CospanOperad`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — the first inhabited multicategory instance in the tree.

## Verification

```bash
coqc -R . Category Instance/FinSet/Cospan/Operad.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CospanOperad.
Compute (* the arity of the Exercise 6.96 substitution *).
```
Reviewer: statement matches Seven Sketches Example 6.94 (printed p. 215); confirm `CospanCat FinSet` is a real term that `make` compiles, and that `Construction/Cospan/Category.v:45` no longer says "monos".

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:6.5.2:example6.94","7sketches:6.5.2:ex6.96"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.3: Algebras for a coloured operad"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.3:def6.99]
deps_item_ids: [7sketches:6.5.2:example6.93]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.3, printed p. 217 (PDF p. 229). Item `7sketches:6.5.3:def6.99`.

## Background

An algebra for an operad is an operad functor into the operad of sets: each type becomes the set of fillers available for the corresponding box in a wiring diagram, and each operation becomes a function assembling n fillers with the given boundaries into one filler with the output boundary. See the nLab on [algebra over an operad](https://ncatlab.org/nlab/show/algebra+over+an+operad) and on [multicategory](https://ncatlab.org/nlab/show/multicategory).

## Current state in the library

The definition is in-tree in exactly the book's shape, and is restricted at *both* ends to a single colour.

`Theory/Multicategory/Algebra.v:112` defines `OperadAlgebra (O : Operad) {C : Category} `{@Cartesian C} `{@Terminal C} (X : C) : Type := MultiFunctor (operad_multi O) (EndOperad X)` — "an algebra is an operad functor into an endomorphism-style operad", the book's definition. The action reading is the book's too: `OperadAction` (`:152-170`) has `oact (n : nat) : ohom O n → (pow X n ~> X)`, i.e. an assembly of n fillers into one, with `oact_id`, `oact_comp` (substitution goes to grafting) and `oact_sym` as the functor laws; `Build_OperadAlgebra` (`:228-234`) constructs an algebra from an action; `OperadAlgebras` (`:417-424`) is the category of them; and `Comm_algebra_to_CMon` (`:523-527`) works out that algebras of the terminal operad in `Sets` are commutative monoids.

Both restrictions are structural rather than incidental:

- The **source** must be a one-coloured `Operad`. `Theory/Multicategory/Operad.v:72-78` defines `IsOperad M := @mobj M = poly_unit` and `Record Operad := { operad_multi; operad_one : IsOperad operad_multi }`, so a genuinely coloured operad — the cospan operad of §6.5.2, whose types are the naturals — has no in-tree algebras.
- The **target** is `EndOperad X`, the endomorphism operad of a single chosen object of a cartesian category, not the many-coloured operad of sets (which is itself absent — see the §6.5.2 operad-of-sets issue). So the book's "F(t) is the set of fillers for the box t", varying with t, collapses to one carrier.

This is precisely what makes the circuit algebra example and the hypergraph-prop proposition of §6.5.3 inexpressible.

## Work to be done

Suggested module: `Theory/Multicategory/Algebra/Coloured.v` (or generalise `Theory/Multicategory/Algebra.v` in place, keeping the one-coloured names as instances).

1. Define an algebra for an arbitrary `Multicategory` `M` as a `MultiFunctor` from `M` into the many-coloured operad of sets, so the carrier varies with the colour.
2. Recover the existing one-coloured notion as the special case at a one-object source and a one-object target, keeping `OperadAlgebra`, `OperadAction`, `Build_OperadAlgebra`, `OperadAlgebras` and `Comm_algebra_to_CMon` working unchanged — the commutative-monoid example is the sanity check that the generalisation is conservative.
3. Give the coloured analogue of `OperadAction` — a per-colour carrier plus an action of each operation, with the identity, substitution and symmetry laws — and its `Build_` convenience constructor, since discharging a `MultiFunctor` by hand is the ergonomic obstacle the one-coloured file already solves.
4. Build the category of algebras of a coloured operad and its forgetful functor to the colour-indexed families of sets.

In-tree donors: `Theory/Multicategory/Algebra.v` (everything above), `Theory/Multicategory/Functor.v` (the heterogeneous multifunctor setoid), `Theory/Multicategory/Operad.v`, `Theory/Multicategory/Endomorphism.v`, `Instance/CMon.v`.

## Definition of Done

- [ ] An algebra for an arbitrary (coloured) multicategory is defined as a multifunctor into the operad of sets, with a per-colour carrier.
- [ ] The one-coloured development is recovered as a special case; `Comm_algebra_to_CMon` still holds and is re-derived rather than duplicated.
- [ ] A coloured `OperadAction` and its convenience constructor exist, with a sanity lemma matching `alg_act_Build`.
- [ ] The category of coloured-operad algebras exists with its forgetful functor.
- [ ] Statement fidelity to Seven Sketches Definition 6.99 (printed p. 217); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Multicategory entry currently describes only the one-coloured algebra notion.

## Verification

```bash
coqc -R . Category Theory/Multicategory/Algebra/Coloured.v
coqc -R . Category Theory/Multicategory/Algebra.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions ColouredOperadAlgebra.
Print Assumptions Comm_algebra_to_CMon.
```
Reviewer: statement matches Seven Sketches Definition 6.99 (printed p. 217) — the carrier must vary with the type, which is the whole content of the definition.

## Dependencies

Depends on: 7sketches:6.5.2:example6.93

<!-- catalog: {"ids":["7sketches:6.5.3:def6.99"],"deps":["7sketches:6.5.2:example6.93"]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.3: Electric circuits as an algebra of the cospan operad"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.3:example6.100]
deps_item_ids: [7sketches:6.5.3:def6.99, 7sketches:6.5.2:example6.94, 7sketches:6.4.3:construction-circ]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.3, printed pp. 217–218 (PDF pp. 229–230). Item `7sketches:6.5.3:example6.100`.

## Background

Recasting the circuit story operadically: the types are finite sets (a set t being a cell with t ports), the fillers for t are the circuits with t marked terminals, and the assignment is an operad functor from the cospan operad into the operad of sets, sending a wiring diagram of arity (2,2,2;0) to a function assembling three two-terminal circuits into one closed circuit. See the nLab on [algebra over an operad](https://ncatlab.org/nlab/show/algebra+over+an+operad) and Wikipedia on [electrical networks](https://en.wikipedia.org/wiki/Electrical_network).

## Current state in the library

Absent, and every ingredient is absent with it. There is no `Circ` object, functor or type anywhere: the token occurs exactly twice, both times inside comments in `Construction/Cospan/BlackBox.v:19,64` naming Baez–Fong's black-box functor as motivation, and all 27 "circuit" hits are prose (`Construction/DecoratedCospan.v:89`, `Construction/DecoratedCospan/Category.v:104,340,371`, `Construction/DecoratedCospan/Hypergraph.v:151,242`, `Instance/ZX.v:120,151,171`, `Instance/Lambda.v:117`, `Construction/PROP/Signature.v:39`). Neither the source operad nor the target operad nor the notion of a coloured-operad algebra exists (see the three issues this depends on), and `RepresentableMulticategory`, `Fold_Multicategory`, `EndOperad` and `OperadAlgebra` have no use anywhere outside `Theory/Multicategory/`.

Note that the decorated-cospan route of §6.4 is deliberately **not** credited here: this example is the operadic recasting, a distinct obligation, and crediting the decorated-cospan machinery would double-count Definition 6.75's coverage.

## Work to be done

Suggested module: `Instance/Circuit/Algebra.v`.

1. Define the algebra: colours are the objects of `FinSet`, the carrier at `t` is `Circ t` (the set of circuits with `t` terminals, from the §6.4.3 decoration functor), and the action of an operation — a cospan `a₁ + … + aₙ → p ← b` — pushes the combined decoration `ψ(c₁, …, cₙ)` forward along the left leg and then reads off the result at `b`.
2. Prove the multifunctor laws: identity operations act as identities, substitution goes to composition of assembly maps, and the symmetric action is respected. The composition law is where the coherence of `ψ` is actually consumed, so it is the substantive obligation.
3. Discharge the example's computation: apply the algebra to the wiring diagram of arity (2,2,2;0) with a battery, a switch, and a lightbulb in series with a resistor, and prove the result is the closed circuit of the chapter's opening figure — closing the loop on §6.4.3's worked composites, which should be shown to agree with this operadic answer.
4. Record the relation to the decorated-cospan construction: the algebra and the decorated-cospan category are two presentations of the same data, and a lemma connecting them (even a partial one) is what makes the §6.5 material more than a restatement.

In-tree donors: everything the three dependencies build, plus `Theory/Multicategory/Functor.v`, `Instance/FinSet.v`, `Instance/Sets.v`, `Construction/Cospan/Category.v`.

## Definition of Done

- [ ] The circuit algebra of the cospan operad is defined, with a per-colour carrier `Circ t`.
- [ ] All multifunctor laws proved, the substitution law consuming the decoration functor's coherence.
- [ ] The example's (2,2,2;0) computation is carried out on closed terms and yields the chapter's opening closed circuit.
- [ ] A lemma relating the algebra to the decorated-cospan category of §6.4.3, so the two presentations are connected rather than parallel.
- [ ] Statement fidelity to Seven Sketches Example 6.100 (printed pp. 217–218); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond what `Instance/` already sanctions per docs/AXIOMS.md.
- [ ] `Print Assumptions` reported for the algebra and the worked computation.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — the first operad algebra over a genuinely coloured operad.

## Verification

```bash
coqc -R . Category Instance/Circuit/Algebra.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CircAlgebra.
Print Assumptions closed_circuit_example.
```
Reviewer: statement matches Seven Sketches Example 6.100 (printed pp. 217–218) — the algebra must be an operad functor into the operad of sets, not a restatement of the decorated-cospan category.

## Dependencies

Depends on: 7sketches:6.5.3:def6.99
Depends on: 7sketches:6.5.2:example6.94
Depends on: 7sketches:6.4.3:construction-circ

<!-- catalog: {"ids":["7sketches:6.5.3:example6.100"],"deps":["7sketches:6.5.3:def6.99","7sketches:6.5.2:example6.94","7sketches:6.4.3:construction-circ"]} -->

---8<---

```yaml
title: "Seven Sketches 6.5.3: Cospan-algebras are equivalent to hypergraph props"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:6.5.3:prop6.101]
deps_item_ids: [7sketches:6.5.3:def6.99, 7sketches:6.5.2:example6.94]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §6.5.3, printed p. 218 (PDF p. 230). Item `7sketches:6.5.3:prop6.101`. Stated without proof.

## Background

Algebras of the operad of finite-set cospans correspond to hypergraph props — hypergraph categories whose object monoid is the naturals under addition — which is the sense in which every hypergraph prop arises operadically, whereas the decorated-cospan construction produces only some of them. See the nLab on [hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category) and on [PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

One side of the claimed equivalence exists; the other is not merely missing but currently inexpressible.

- The **right-hand side** is defined: `Class HypergraphPROP` at `Construction/PROP.v:230-236`, bundling a `PROP` (`:68`) with a `Hypergraph` structure on its underlying symmetric monoidal category. It is uninhabited — `Test/HypergraphPROPResolution.v:89-92` records exactly that — but the notion is in force and correct.
- The **left-hand side** cannot be written: coloured-operad algebras are undefined in the tree (algebras exist only for one-coloured operads into a single-carrier endomorphism operad), and the operad of cospans is never built. The cospan operad's type collection is the naturals, so the coloured case is not a convenience here — it is the whole content.
- No theorem anywhere in the tree relates operad algebras to a categorical structure of any kind.

## Work to be done

Suggested module: `Theory/Multicategory/Algebra/Hypergraph.v`.

1. From a coloured algebra of the cospan operad, construct a hypergraph prop: the objects are the naturals (the operad's colours), the hom-sets come from the algebra's action on the arity-(a;b) operations, composition and the monoidal product from substitution, and the Frobenius supply on each object from the algebra's action on the cospan operad's own Frobenius operations (the cup, cap, copy and discard cospans are already available as `cospan_scfa_*` in `Construction/Cospan/Hypergraph.v`).
2. Conversely, from a hypergraph prop construct an algebra of the cospan operad: an operation of arity (a₁,…,aₙ;b) acts by the hypergraph structure's canonical interpretation of the cospan as a morphism, the spider normal form guaranteeing this is well defined.
3. Prove the two constructions mutually inverse up to the appropriate notion of sameness, and record explicitly which notion (isomorphism of categories, equivalence, or an equivalence of the categories of each) the proof establishes — the book does not say.
4. Record the significance the surrounding prose gives: the decorated-cospan construction of §6.4.2 produces only *some* hypergraph categories, whereas every hypergraph prop arises from a cospan-operad algebra. If the containment is not proved here, state it in the header with a pointer rather than dropping it.
5. Supply the witness: `HypergraphPROP` has no inhabitant in the tree, and an algebra built from the circuit development (or from the trivial algebra) closes that gap.

**Library defect to fix in passing.** `Test/HypergraphPROPResolution.v:90` justifies the no-witness claim by pointing at `docs/INHABITATION.md`, but that document never mentions `HypergraphPROP` — only `docs/AXIOMS.md:98` does. The cross-reference is dangling and should be repointed (or `docs/INHABITATION.md` given the entry), and if this issue supplies a witness both documents need updating anyway.

In-tree donors: `Construction/PROP.v` (`PROP`, `HypergraphPROP`), `Structure/Monoidal/Hypergraph.v`, `Structure/Monoidal/Hypergraph/Spider.v`, `Construction/Cospan/Hypergraph.v`, `Theory/Multicategory/Algebra.v`, `Test/HypergraphPROPResolution.v`.

## Definition of Done

- [ ] Both constructions are given — hypergraph prop from a cospan-operad algebra and back.
- [ ] They are proved mutually inverse, and the header states precisely which notion of sameness the equivalence is stated at.
- [ ] `HypergraphPROP` gains its first in-tree inhabitant.
- [ ] The prose claim that decorated cospans give only *some* hypergraph categories is either proved or recorded in the header with a pointer, not dropped.
- [ ] **Library defect, fixed here:** the dangling cross-reference at `Test/HypergraphPROPResolution.v:90` — it cites `docs/INHABITATION.md` for a `HypergraphPROP` claim that document does not make (`docs/AXIOMS.md:98` does) — is repaired, and both documents are updated to reflect the new witness.
- [ ] Statement fidelity to Seven Sketches Proposition 6.101 (printed p. 218); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and `docs/INHABITATION.md` updated — this is flagship-level.

## Verification

```bash
coqc -R . Category Theory/Multicategory/Algebra/Hypergraph.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions hypergraph_prop_of_cospan_algebra.
Print Assumptions cospan_algebra_of_hypergraph_prop.
Print Assumptions cospan_algebras_equiv_hypergraph_props.
```
Reviewer: statement matches Seven Sketches Proposition 6.101 (printed p. 218); confirm the equivalence is between algebras of the *cospan operad* and hypergraph props, and that `Test/HypergraphPROPResolution.v:90` no longer cites a document that does not discuss the class.

## Dependencies

Depends on: 7sketches:6.5.3:def6.99
Depends on: 7sketches:6.5.2:example6.94

<!-- catalog: {"ids":["7sketches:6.5.3:prop6.101"],"deps":["7sketches:6.5.3:def6.99","7sketches:6.5.2:example6.94"]} -->

```yaml
title: "Riehl 1.0: Group extensions, Ext(H,G), and the universal coefficient sequence"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.0:def-group-extension, riehl:1.0:eq1]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (locally recompiled author's copy — **not** Dover/AMS pagination).
- Section: 1.0 (the chapter's opening motivation), printed p. 1 (PDF p. 21).
- Items: `riehl:1.0:def-group-extension`, `riehl:1.0:eq1` (the numbered display (1.0.1)).

## Background

An extension of an abelian group `H` by an abelian group `G` is a short exact sequence `0 → G → E → H → 0`; the set of equivalence classes of such extensions carries an abelian group structure written `Ext(H,G)`, and the universal coefficient sequence relates singular cohomology with coefficients to homology through it. Riehl opens the book with this display precisely because its two outer maps are *natural* in the space — historically the first place naturality was isolated as a concept.

- nLab: <https://ncatlab.org/nlab/show/Ext>
- Wikipedia: <https://en.wikipedia.org/wiki/Ext_functor>, <https://en.wikipedia.org/wiki/Universal_coefficient_theorem>

## Current state in the library

Nothing of this is formalized, and the verifier's blind pass reproduced that independently.

- There is no category of abelian groups. `Structure/Abelian.v` axiomatizes an *abstract* abelian category (`Class Abelian`, with `Abelian_OFS` at line 441) and every additive file in the spine takes `ZeroObject` as a context hypothesis; the only concrete semiadditive witness is `Instance/CMon.v:140` (commutative monoids over setoids), which has no negation and no torsion theory.
- There is no exactness predicate anywhere: `rg -i 'exact sequence|short exact'` over `*.v` returns four files and every hit is background-essay prose (`Theory/Category.v:48` and `Theory/Functor.v:35` cite the *title* of the Eilenberg–Mac Lane 1942 paper; `Structure/Abelian.v:70` and `Structure/Coend.v:63` name exact sequences in essays). With no exactness predicate the sequence cannot even be written down.
- There is no `Ext`, no homology or cohomology functor, and no chain complexes of modules. `Construction/Chain.v`'s `Cochain` is the dual ω-chain used for final coalgebras and is unrelated.
- Verifier correction, folded in: the Phase-C note that "the only group notion in-tree is `Class GroupObject` (`Structure/Group.v:109`)" is inaccurate. `Instance/Comp.v:382` also defines `Definition Group := Algebra GroupOp GroupEq` — a group as an equational algebra over the in-tree universal-algebra development, with the worked witness `Definition Bool : Group` at line 405 and the ambient category `Program Definition Algs : Category` at `Instance/Comp.v:151`. That is the nearest existing foothold for a category of groups and should be examined before starting from scratch.

## Work to be done

This is the deepest single obligation Riehl's Chapter 1 raises; it sits on top of several already-filed prerequisites and should be attempted only once they land.

1. Over the category of abelian groups (issue #256) and the exact-sequence vocabulary (issue #545), define an **extension of `H` by `G`** as a short exact sequence together with the equivalence relation Riehl uses (an isomorphism of the middle terms commuting with the inclusion and the quotient). Suggested module: `Structure/Extension.v`.
2. Prove the equivalence relation is one, and construct the **Baer sum**, exhibiting `Ext(H,G)` as an abelian group (in-tree donor for the target: `Instance/CMon.v` plus whatever `Ab` instance #256 delivers).
3. Make `Ext(−,−)` a bifunctor `Ab^op ∏ Ab ⟶ Ab` and record the split extension as its zero element.
4. State the **universal coefficient sequence** for a chain complex of free modules, over the chain-complex/homology machinery of issue #557 and singular homology of issue #516, and prove the naturality of the two outer maps in the space — this naturality claim, not the exactness, is what Riehl's opening is actually about, and it is the part this library is best equipped to say something about.
5. Header essay recording the historical point (Eilenberg–Mac Lane isolated naturality from exactly this display) and cross-linking `Theory/Category.v:48` and `Theory/Functor.v:35`, which already cite the 1942 paper by title.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.0, printed p. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `Ext(H,G)` is constructed as an abelian group and proved functorial in both variables
- [ ] The universal coefficient sequence is stated, and the naturality of its two outer maps is proved
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Ext`, the Baer sum, and the naturality statement
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (this would be flagship-level)

## Verification

```
coqc -R . Category Structure/Extension.v
coqtop -R . Category -l Structure/Extension.v   # then: Print Assumptions Ext.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: the extension equivalence matches Riehl §1.0 (isomorphism commuting with *both* the inclusion of `G` and the quotient onto `H`); the naturality claim is stated for continuous maps of spaces, not merely for chain maps.

## Dependencies

- Depends on: #256 (Ab, the category of abelian groups)
- Depends on: #545 (exact sequences and short exact sequences)
- Depends on: #557 (chain complexes and homology objects)
- Depends on: #516 (homology of a simplicial object and singular homology)

<!-- catalog: {"ids":["riehl:1.0:def-group-extension","riehl:1.0:eq1"],"deps":["#256","#545","#557","#516"]} -->

---8<---

```yaml
title: "Riehl 1.1: Reflexive quivers and the underlying reflexive quiver of a category"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.1:def-quiver]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.1 ("Abstract and concrete categories"), printed p. 3 (PDF p. 23).
- Items: `riehl:1.1:def-quiver` (unnumbered, in running prose).

## Background

A quiver is a directed graph allowing parallel edges and loops; a *reflexive* quiver additionally names a distinguished endo-edge at each vertex. Riehl's framing sentence is that the objects and morphisms of a category form a reflexive quiver in which every finite path of composable arrows has a well-defined composite, unchanged by inserting or deleting identities.

- nLab: <https://ncatlab.org/nlab/show/reflexive+graph>, <https://ncatlab.org/nlab/show/quiver>

## Current state in the library

The bare-quiver half is fully present; the reflexive refinement is entirely absent.

- `Construction/Free/Quiver.v:54` — `Class Quiver@{o h p} := { nodes : Type@{o}; uedges := Type@{h} : Type@{h+1}; edges : nodes → nodes → uedges; edgeset : ∀ X Y, Setoid@{h p} (edges X Y) }`.
- `Construction/Free/Quiver.v:358` — `#[export] Instance QuiverCategory : Category` (objects quivers, morphisms quiver homomorphisms).
- `Construction/Free/Quiver.v:398` — `Program Definition QuiverOfCat (C : Category) : Quiver := {| nodes := obj; edges := hom |}` — this **forgets the identity selection**, so it lands in bare quivers, not reflexive ones.
- `Construction/Free/Quiver.v:412` — `Definition Forgetful : @Functor StrictCat QuiverCategory`; `:431` `FreeOnQuiver`; `:464` `InducedFunctor`; `:518` `UniversalArrowQuiverCat`; `:550` `FreeForgetfulAdjunction`. The verifier confirmed all of these forward pointers are live (no stale-pointer defect in that header).
- Gap: `rg -i 'reflexive quiver|reflexive graph'` over `*.v` returns **0 hits** (verifier re-ran this independently, exit 1). There is no class carrying a distinguished endo-edge at each vertex, no category of reflexive quivers, and no statement that the underlying quiver of a category is reflexive. Riehl's actual sentence is therefore unformalized; only its weaker shadow is.

## Work to be done

Suggested module: `Construction/Free/ReflexiveQuiver.v` (or a section added to `Construction/Free/Quiver.v`).

1. `Class ReflexiveQuiver` extending `Quiver` with `rid : ∀ x, edges x x`, and `ReflexiveQuiverHomomorphism` requiring `rid` to be preserved up to the edge setoid.
2. The category `ReflexiveQuiverCategory`, and the forgetful functor `ReflexiveQuiverCategory ⟶ QuiverCategory` that drops `rid`.
3. `ReflexiveQuiverOfCat (C : Category) : ReflexiveQuiver` with `rid x := id[x]`, and the functor `StrictCat ⟶ ReflexiveQuiverCategory` refining the existing `Forgetful` — i.e. show the existing `Forgetful` factors through the new one.
4. Riehl's composite clause as a corollary of the existing free-category machinery: the composite of a finite path in `QuiverOfCat C` (a `tlist` of `edges`, `Construction/Free/Quiver.v:431`) is well defined by associativity, and inserting or deleting `rid` edges does not change it. This is `fmap[InducedFunctor]` applied to the identity edge; state it as a named lemma rather than leaving it implicit.
5. Optional but cheap: the free category on a reflexive quiver (identity edges collapse to identities), which is the construction that makes the reflexive variant worth having.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.1, printed p. 3 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `ReflexiveQuiver`, its homomorphisms, and `ReflexiveQuiverCategory` are defined and proved lawful
- [ ] `ReflexiveQuiverOfCat` is constructed and the existing `Forgetful` is shown to factor through it
- [ ] The path-composite invariance under insertion/deletion of identity edges is a named lemma
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `ReflexiveQuiverOfCat` and the factorization
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Free/ReflexiveQuiver.v
coqtop -R . Category -l Construction/Free/ReflexiveQuiver.v
#   Print Assumptions ReflexiveQuiverOfCat.
grep -n ReflexiveQuiver _CoqProject
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.1 (printed p. 3)"; confirm the new forgetful functor really refines `Construction/Free/Quiver.v:412` rather than duplicating it.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:1.1:def-quiver"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 1.1: The maximal subgroupoid of a category as a wide subcategory"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.1:lem14, riehl:1.1:exii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.1 ("Abstract and concrete categories"), printed p. 8 (PDF p. 28).
- Items: `riehl:1.1:lem14` (Lemma 1.1.14), `riehl:1.1:exii` (Exercise 1.1.ii, the deferred proof of that lemma).

## Background

Every category contains a largest groupoid inside it: the wide subcategory whose morphisms are exactly the isomorphisms, often called the core. Riehl's illustration is the groupoid of finite sets and bijections sitting inside the category of finite sets.

- nLab: <https://ncatlab.org/nlab/show/core+groupoid>

## Current state in the library

The construction exists but is never related to the ambient category, and the subcategory/maximality content is missing.

- `Construction/Groupoid.v:103` — `Program Definition Groupoid (C : Category) : Category := {| obj := @obj C; hom := @Isomorphism C; homset := @iso_setoid C; id := @iso_id C; compose := @iso_compose C |}`. The verifier confirmed the file is 109 lines long and this is its *only* assertion: there is no functor `Groupoid C ⟶ C`, no `Subcategory` instance, and no maximality statement.
- The closure ingredients are all present: `Theory/Isomorphism.v:149` `#[export] Program Instance iso_id {x : C} : x ≅ x` (citation corrected by the verifier from the Phase-C `:152`, which is its closing brace) and `Theory/Isomorphism.v:166` `Program Definition iso_compose {x y z : C} (f : y ≅ z) (g : x ≅ y) : x ≅ z`.
- The target machinery is present and in routine use elsewhere: `Construction/Subcategory.v` `Record Subcategory` (line 31), `Sub` (50), `Incl` (59), `Full` (69), `Replete` (87), `Wide` (93); the pattern is applied at `Structure/Binoidal/Central.v:239` (`Lemma Centre_wide : Wide C CentralSub`) and `Structure/Monoidal/CopyDiscard/Deterministic.v:583` (`Lemma Det_wide : Wide C DeterministicSub`) — but **never to the isomorphisms**.
- Missing precisely: (a) a `Subcategory C` whose `sobj` is everything and whose `shom` selects the isomorphisms, with the `Wide` witness and the faithful inclusion; (b) the identification of that subcategory with `Groupoid C`; (c) the maximality clause; (d) the illustration `Fin_iso` — `Instance/FinSet.v` proves nothing about its isomorphisms.

## Work to be done

Suggested module: `Construction/Groupoid/Core.v` (extending `Construction/Groupoid.v`, which is `_CoqProject` line 53).

1. Build `IsoSub (C : Category) : Subcategory C` with `sobj _ := True`-style total object predicate and `shom ox oy f := IsIsomorphism f`, taking `sid` from `Theory/Isomorphism.v:149` and `scomp` from `:166`.
2. Prove `Wide C (IsoSub C)` and expose the faithful inclusion `Incl (IsoSub C) : Sub (IsoSub C) ⟶ C`.
3. Prove `Sub (IsoSub C) ≅[Cat] Groupoid C`, connecting the existing construction to the new subcategory packaging (this is the step that makes `Construction/Groupoid.v` a *sub*category rather than a free-standing category).
4. Maximality: for any `S : Subcategory C` all of whose selected morphisms are `C`-isomorphisms, the inclusion factors through `IsoSub C`. Once the groupoid predicate of issue #248 lands, restate this as "the largest wide subcategory satisfying `IsGroupoid`".
5. The illustration: `Fin_iso` as `IsoSub FinSet`, with a lemma identifying its morphisms with the bijections (`Instance/FinSet/Classifier.v:335` `finset_monic_iff_injective` is the nearest existing handle).
6. **Library defect, folded in here** (surfaced by the Chapter 1 coverage pass): `Construction/Subcategory.v:84-85` documents `Replete` as requiring only "both `y` and `f` are also in `D`", omitting the inverse, while the `Definition` at line 89 additionally demands `shom S oy ox (from f)`. The code, not the comment, matches the standard definition (and Riehl's footnote); fix the comment while working in this file.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.1 Lemma 1.1.14 and Exercise 1.1.ii, printed p. 8 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `IsoSub` is built, proved `Wide`, and its inclusion into `C` is available
- [ ] `Sub (IsoSub C) ≅[Cat] Groupoid C` is proved
- [ ] The maximality clause is proved (not left as prose)
- [ ] `Fin_iso` is exhibited and its morphisms identified with bijections
- [ ] The `Construction/Subcategory.v:84-85` `Replete` comment is corrected to mention the inverse
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `IsoSub`, the `Wide` witness, the comparison, and the maximality lemma
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Groupoid/Core.v
coqtop -R . Category -l Construction/Groupoid/Core.v
#   Print Assumptions IsoSub.  Print Assumptions IsoSub_wide.
sed -n '80,95p' Construction/Subcategory.v      # comment fix visible
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.1 (printed p. 8)"; the maximality clause must quantify over subcategories, not merely assert that isomorphisms compose.

## Dependencies

- Depends on: #248 (groupoids and the structure of connected groupoids — supplies the `IsGroupoid` predicate the maximality clause is best stated against)

<!-- catalog: {"ids":["riehl:1.1:lem14","riehl:1.1:exii"],"deps":["#248"]} -->

---8<---

```yaml
title: "Riehl 1.2: Representable characterizations of isomorphisms, split epimorphisms and split monomorphisms"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.2:lem3, riehl:1.2:remark4, riehl:1.2:exv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.2 ("Duality"), printed pp. 10–11 and p. 13 (PDF pp. 30–31, 33).
- Items: `riehl:1.2:lem3` (Lemma 1.2.3), `riehl:1.2:remark4` (Remark 1.2.4), `riehl:1.2:exv` (Exercise 1.2.v).

## Background

A morphism is an isomorphism exactly when post-composition with it is a bijection on every hom-set, and equivalently when pre-composition with it is; the same probing characterizes split epimorphisms (post-composition surjective) and split monomorphisms (pre-composition surjective). This is the first genuinely *representable* definition in the book: a property of an arrow expressed entirely through the functors it induces on hom-sets.

- nLab: <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/split+epimorphism>

## Current state in the library

None of the three biconditionals is stated. The verifier searched this record hardest (it is the one where a missed counterpart would have cost the most) and confirmed the negative from `rg -i 'postcompos|precompos'`, `rg -i 'biject'`, `rg -n 'hom .*≅|≅.*hom '` and a full read of the assertion lines of `Functor/Hom.v` and `Functor/Hom/Yoneda.v`.

- Present but *not* the criterion: `Theory/Functor.v:227` `#[export] Program Instance fobj_iso (F : C ⟶ D) : Proper (Isomorphism ==> Isomorphism) (fobj[F])` — preservation, one direction only, and never instantiated at the hom-functor.
- Present but *object-level*: `Theory/Functor.v:355` `Lemma FullyFaithful (F : C ⟶ D) ... : ∀ x y, F x ≅ F y → x ≅ y` and `Theory/Equivalence/Limit.v:335` `Definition ff_reflects_isos : ReflectsIsos F`; both assume a natural isomorphism rather than componentwise bijections.
- The hom-functor and its Yoneda properties exist and are simply never used for this: `Functor/Hom.v:49` `Program Definition Hom (C : Category) : C^op ∏ C ⟶ Sets`, `Functor/Hom.v:60` `Curried_Hom`, `:85` `Yoneda_Faithful`, `:96` `Yoneda_Full`.
- For the split case, only the `c = y` / `c = x` instance exists — as the *definitions* of the classes: `Theory/Morphisms.v:56` `Class Section (f : x ~> y) := { section : y ~> x; section_comp : section ∘ f ≈ id }`, `:70` `Class Retraction ... { retract : y ~> x; retract_comp : f ∘ retract ≈ id }`, with `SplitEpi := Retraction` (`:126`) and `SplitMono := Section` (`:127`).
- The nearest thing in the whole tree to the surjectivity form is `Construction/Localization.v:136` `WLocal_surj`, whose shape is `{ q : b ~> x & q ∘ w ≈ p }` — i.e. the right statement, stated only for the localizing class.
- Verifier note on classification, recorded for honesty: for `riehl:1.2:exv` the verifier's own blind pass reached ABSENT (the item *is* the characterization, and only the term being characterized is in tree) and deferred to the classifier's PARTIAL because `Retraction`/`Section` literally are the `c = y` / `c = x` instance of the book's condition. Either reading routes here.

## Work to be done

Suggested module: `Theory/Morphisms/Representable.v` (new), consuming `Functor/Hom.v` and `Theory/Morphisms.v`.

1. `iso_iff_postcomp_bijective : IsIsomorphism f ↔ ∀ c, IsIsomorphism (fmap[[Hom c,─]] f)` in `Sets`, and the pre-composition dual `iso_iff_precomp_bijective` via `C^op`. Riehl proves the first directly and gets the second by duality; the in-tree proof should do the same, so that the `C^op` translation is exercised rather than re-proved.
2. Derive the elementary corollary the book actually uses downstream: `f` is an isomorphism iff for every `c` the function `g ↦ f ∘ g` is a bijection of hom-setoids, stated with `≈` on both sides (never `=`).
3. `retraction_iff_postcomp_surjective : Retraction f ↔ ∀ c (g : c ~> y), { h : c ~> x & f ∘ h ≈ g }`, and the dual `section_iff_precomp_surjective`. Note that the library's `Lib/Setoid.v:121` `surjective` is *split* surjectivity (a chosen preimage, `{ x & f x ~~ y }`), which is exactly the data-carrying form these statements need and is why no choice principle is required.
4. Record Riehl's Remark 1.2.4 point in the header: the proof needs no local-smallness hypothesis, which in this library is automatic — `Functor/Hom.v:49` takes an arbitrary `C` with no side condition.
5. Instantiate at least one in-tree consumer to show the criterion earns its keep (e.g. re-derive `Theory/Isomorphism.v:392` `Monic_Retraction_Iso` or `:412` `Epic_Section_Iso` through it).

## Definition of Done

- [ ] Statement fidelity to Riehl §1.2 Lemma 1.2.3, Remark 1.2.4, Exercise 1.2.v (setoid `≈` discipline; never `=` on morphisms)
- [ ] Both directions of the isomorphism criterion are proved, and the pre-composition form is obtained by duality from the post-composition form
- [ ] Both split criteria are proved, with the split-mono form obtained by duality
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the four biconditionals
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Morphisms/Representable.v
coqtop -R . Category -l Theory/Morphisms/Representable.v
#   Print Assumptions iso_iff_postcomp_bijective.
#   Print Assumptions retraction_iff_postcomp_surjective.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.2 (printed pp. 10–11, 13)"; verify the dual statements are genuinely *derived* through `C^op` rather than copy-pasted proofs — that is the content of the section.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:1.2:lem3","riehl:1.2:remark4","riehl:1.2:exv"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 1.3: The Brouwer fixed-point theorem via the fundamental group"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.3:thm3]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.3 ("Functoriality"), printed pp. 16–17 (PDF pp. 36–37).
- Items: `riehl:1.3:thm3` (Theorem 1.3.3).

## Background

Every continuous endomorphism of the closed 2-disk has a fixed point. Riehl gives the standard functorial proof: a fixed-point-free map produces a retraction of the disk onto its boundary circle, and applying the fundamental group turns that retraction into an impossible retraction of the trivial group onto the integers. The theorem is in the book precisely as the showcase for "functors carry retractions to retractions".

- nLab: <https://ncatlab.org/nlab/show/Brouwer%27s+fixed+point+theorem>
- Wikipedia: <https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem>

## Current state in the library

Absent in every ingredient, verified independently.

- `rg -i 'brouwer'` over `*.v` → 0 hits. `rg -i 'fixed point|fixpoint'` returns only Coq's `Fixpoint` keyword and the Knaster–Tarski / Lambek citations in `Construction/FAlg.v`.
- There is no category of topological spaces (`rg -i 'topological space|open sets'` finds no construction), no pointed spaces, no fundamental group and no fundamental groupoid — the only occurrence of "fundamental group" in the tree is a prose line in the `Construction/Groupoid.v` background essay (line 58).
- The one categorical ingredient that *is* present is the general split-morphism transport used by the proof: `Theory/Morphisms.v:56/70` (`Section`/`Retraction`) and `Theory/Morphisms.v:162/179` (`retractions_are_epic`, `sections_are_monic`) — but there is still no lemma that an arbitrary functor preserves them (that is issue #656).
- The verifier deliberately kept this ABSENT rather than OUT_OF_SCOPE: the obstruction is a missing topology layer, not a foundational one, so the statement is formalizable in this library's setting.

## Work to be done

This issue is the *categorical spine* of the argument plus the concrete inputs; it should be opened only once the topology prerequisites land, and the categorical half can be landed first as a standalone abstract lemma.

1. **Abstract half (landable now, and useful independently):** in `Theory/Recursion.v`'s neighbourhood or a small `Theory/Retract.v`, state and prove "if `r ∘ i ≈ id` then `fmap[F] r ∘ fmap[F] i ≈ id` for any functor `F`, hence `F i` is a split mono and `F r` a split epi" — deferring the general statement to issue #656 and simply *consuming* it here.
2. Instantiate at `π₁ : Top_* ⟶ Grp` (issue #249's fundamental groupoid, restricted to a basepoint; issue #255's `Grp`) to obtain: a retraction of `D²` onto `S¹` induces a retraction of `π₁(D²) = 0` onto `π₁(S¹) ≅ ℤ`.
3. Supply the two computations as *inputs* (each is a substantial development in its own right; disclose in the header which are hypotheses and which are proved): `π₁(S¹) ≅ ℤ` and `π₁(D²)` trivial.
4. Assemble Riehl's contradiction: no group retraction `0 ↠ ℤ` exists, since a retraction is in particular an epimorphism of groups and `ℤ` is not trivial.
5. Record the geometric step (a fixed-point-free `f` yields the retraction by the ray construction) explicitly as the one analytic input, kept as a hypothesis if the analysis layer is not available.
6. Header: the footnote generalization to `Dⁿ` via `πₙ`, and a pointer to the Chapter-1 framing (this theorem is Riehl's motivating use of functoriality).

## Definition of Done

- [ ] Statement fidelity to Riehl §1.3 Theorem 1.3.3, printed pp. 16–17 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The functorial spine (retraction transport ⇒ contradiction) is proved unconditionally, with the analytic and homotopy-theoretic inputs isolated as explicitly named hypotheses or as proved lemmas
- [ ] Every hypothesis actually assumed is disclosed in the file header, per the library's conditional-theorem convention (see docs/INHABITATION.md)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the assembled theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship-level if the concrete instance lands)

## Verification

```
coqc -R . Category Theory/Topology/Brouwer.v
coqtop -R . Category -l Theory/Topology/Brouwer.v
#   Print Assumptions brouwer_fixed_point.
grep -n INHABITATION docs/INHABITATION.md      # entry added for the conditional form
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.3 (printed pp. 16–17)"; confirm docs/INHABITATION.md records whether the distinctive premises carry an in-tree witness.

## Dependencies

- Depends on: #259 (Top, the category of topological spaces)
- Depends on: #249 (the fundamental groupoid of a topological space)
- Depends on: #255 (Grp, the category of groups)
- Depends on: #656 (functors preserve split monomorphisms and split epimorphisms)

<!-- catalog: {"ids":["riehl:1.3:thm3"],"deps":["#259","#249","#255","#656"]} -->

---8<---

```yaml
title: "Riehl 1.3: Functorial clustering — FinMetric, Cluster, and persistent clusters"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.3:example4]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.3 ("Functoriality"), printed p. 17 (PDF p. 37).
- Items: `riehl:1.3:example4` (Example 1.3.4, "In search of a clustering functor").

## Background

Carlsson and Mémoli recast Kleinberg's impossibility result for clustering algorithms functorially: a clustering algorithm is a functor from finite metric spaces and distance-non-increasing maps to partitioned sets, and the only scale-invariant such functors are the two degenerate ones. Replacing single clusterings by *persistent* clusterings — functors out of the poset of scale parameters — restores a rich supply of examples, which is the categorical origin of persistent homology.

- nLab: <https://ncatlab.org/nlab/show/persistent+homology>
- Wikipedia: <https://en.wikipedia.org/wiki/Cluster_analysis>

## Current state in the library

Nothing of the example exists; the verifier reproduced every negative.

- `rg -i 'cluster'` → 3 hits, all the English word for a group of files (`Theory/Coq.v:5,87`, `Structure/Premonoidal.v:129`).
- `rg -i 'metric space'` → 5 files, every one citing Lawvere 1973 as *motivation* for enrichment (`Theory/Profunctor.v:46,100`; `Instance/Poset.v:39,75`; `Instance/Two.v:28`; `Construction/Enriched.v:40,49,75`); no metric space and no category of metric spaces is constructed.
- `Kleinberg`, `Carlsson`, `FinMetric`, `persistent`, `dendrogram` → 0 hits each.
- Verifier observation worth acting on: the `[0,∞)`-indexed persistence functor of the example is exactly a functor out of a `Proset` (`Instance/Proset.v:33`), which the tree *does* have — so the indexing half is free, and only the two categories and the impossibility theorem are missing.

## Work to be done

Suggested modules: `Instance/FinMetric.v` and `Instance/Cluster.v`, with the theory in `Theory/Clustering.v`.

1. `FinMetric`: finite metric spaces (a finite carrier with a distance function satisfying the metric axioms, over the library's setoid discipline) and distance-non-increasing maps. Build on the Lawvere-metric vocabulary already motivated in `Construction/Enriched.v` and on the Cost-enrichment issue #787, so the two presentations agree rather than diverging.
2. `Cluster`: sets equipped with a partition, and functions of underlying sets under which the domain partition refines the pullback of the codomain partition. The refinement preorder should reuse the partition machinery of issue #754 rather than being rebuilt.
3. The scale-invariance condition as a predicate on functors `FinMetric ⟶ Cluster`, and the classification: the only scale-invariant functors are the discrete and the indiscrete partitions, neither of which is surjective on objects.
4. Persistent clusters: functors `Proset ([0,∞), ≤) ⟶ (partitions of X, refinement)`, and the reformulation of a clustering algorithm as a functor `FinMetric ⟶ [Proset, Cluster]`; exhibit at least one non-degenerate example (single-linkage) to show the classification obstruction is genuinely lifted.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.3 Example 1.3.4, printed p. 17 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `FinMetric` and `Cluster` are constructed as categories with their laws proved
- [ ] The scale-invariance predicate is defined and the two-functor classification is proved (both that the two degenerate functors qualify and that nothing else does)
- [ ] At least one non-degenerate persistent clustering functor is exhibited
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the classification theorem and the persistent example
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/FinMetric.v Instance/Cluster.v Theory/Clustering.v
coqtop -R . Category -l Theory/Clustering.v
#   Print Assumptions scale_invariant_classification.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.3 (printed p. 17)"; confirm the `Cluster` morphism condition is the refinement condition Riehl states (domain partition refines the *pullback* of the codomain partition), not the naive partition-preservation condition.

## Dependencies

- Depends on: #787 (Lawvere metric spaces as Cost-categories, and short maps as Cost-functors)
- Depends on: #754 (partitions of a set and their correspondence with equivalence relations and surjections)

<!-- catalog: {"ids":["riehl:1.3:example4"],"deps":["#787","#754"]} -->

---8<---

```yaml
title: "Riehl 1.3: The fundamental theorem of Galois theory as an isomorphism of categories"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.3:example15]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.3 ("Functoriality"), printed p. 22 (PDF p. 42).
- Items: `riehl:1.3:example15` (Example 1.3.15).

## Background

For a finite Galois extension, the fundamental theorem of Galois theory upgrades from an inclusion-reversing bijection between subgroups and intermediate fields to an *isomorphism of categories* between the opposite of the orbit category of the Galois group and the category of intermediate fields with the `F`-fixing homomorphisms. Riehl uses it as the flagship example of a genuine (non-equivalence) isomorphism of categories.

- nLab: <https://ncatlab.org/nlab/show/Galois+theory>
- Wikipedia: <https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory>

## Current state in the library

Absent; the verifier reproduced every negative independently.

- `rg -i 'galois'` over `*.v` hits only Galois *connections* between posets (`Theory/Adjunction.v:78-79`, `Instance/Poset.v:37-100`, `Adjunction/GAFT.v:136`, `Structure/Factorization.v:69`, `Structure/Limit.v:53`), plus `Instance/Poset.v:58` citing the fundamental theorem purely as etymology. Nothing constructs a field extension, an automorphism group, or an orbit category.
- Case-sensitive `rg 'Automorphism'` → 0 hits (the ten lowercase "automorphism" occurrences are all prose about natural automorphisms and twists).
- There is no category of fields: the three `\bField\b` hits are `Structure/Premonoidal.v:188` ("Field orientations", record-field sense) and two bibliographic lines in `Theory/Algebra/Frobenius.v`; `\bRing\b` returns nothing at all. `Theory/Lawvere.v:91` observes in prose that the category of fields has no products.
- `rg -i 'subgroup'` → 3 prose hits only; no orbit category, no `G`-set.

## Work to be done

Suggested module: `Instance/Galois.v` with the orbit category in `Construction/Orbit.v`.

1. Over the category of groups (issue #255) and of `G`-sets (issue #234's part (c)), build the **orbit category** `O_G`: objects the subgroups of `G` (equivalently the transitive `G`-sets `G/H`), morphisms the `G`-equivariant maps, with the explicit description as cosets `gH ↦ g γ K` for `γ` with `γ⁻¹Hγ ⊆ K`.
2. Over the category of fields (issue #226's roster; see the Riehl §1.2 append there), build `Field_F^E`: the subcategory of the coslice under `F` spanned by intermediate fields `F ≤ K ≤ E`, with the `F`-fixing homomorphisms. Prove the automorphism group of the object `E` is the Galois group.
3. Define the Galois extension hypothesis as data (a finite-index subfield with automorphism-group order equal to the index), keeping the field-theoretic input explicit rather than hidden.
4. Construct `Φ : O_G^op ⟶ Field_F^E` (a subgroup to its fixed subfield) and prove it is an isomorphism of categories — i.e. an inverse functor on the nose, not merely an equivalence. Use `Instance/Cat.v:157` `Record Isomorphism_FullyFaithful` as the target packaging where useful, but note in the header that `≅[Cat]` is *equivalence* in this library (the hom-setoid of `Cat` is natural isomorphism), so the "isomorphism of categories" claim must be stated against strict functor equality (`Instance/StrictCat.v:56`), which is exactly Riehl's point.
5. Header essay distinguishing this from the Galois *connection* already in `Instance/Poset.v`, which the library currently cites only as etymology.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.3 Example 1.3.15, printed p. 22 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The orbit category and the intermediate-field category are constructed with their laws proved
- [ ] `Φ` is constructed and proved an isomorphism of categories in the *strict* sense, with the `Cat`-vs-`StrictCat` distinction disclosed in the header
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the orbit category, `Φ`, and the isomorphism
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship-level)

## Verification

```
coqc -R . Category Construction/Orbit.v Instance/Galois.v
coqtop -R . Category -l Instance/Galois.v
#   Print Assumptions galois_correspondence.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.3 (printed p. 22)"; confirm the conclusion is a strict isomorphism and not silently weakened to an equivalence by `≅[Cat]`.

## Dependencies

- Depends on: #255 (Grp, the category of groups)
- Depends on: #226 (the roster of standard large categories — the category of fields; see the Riehl §1.2 append there)
- Depends on: #234 (functors between preorders, groups, and representation categories — `G`-sets as functors out of a delooping)
- Depends on: #220 (delooping monoids and groups into one-object categories)

<!-- catalog: {"ids":["riehl:1.3:example15"],"deps":["#255","#226","#234","#220"]} -->

---8<---

```yaml
title: "Riehl 1.3/1.5: Counterexamples — functors need not reflect isomorphisms, and full or faithful alone does not suffice"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:1.3:exviii, riehl:1.5:exv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.3 ("Functoriality"), printed p. 24 (PDF p. 44); Section 1.5 ("Equivalence of categories"), printed p. 38 (PDF p. 58).
- Items: `riehl:1.3:exviii` (Exercise 1.3.viii), `riehl:1.5:exv` (Exercise 1.5.v).

## Background

Functors always preserve isomorphisms but need not reflect them; a functor that reflects isomorphisms is called conservative. Riehl asks for explicit counterexamples, and further for functors that are full-but-not-faithful or faithful-but-not-full which fail to reflect or create isomorphisms — showing that neither half of "fully faithful" suffices on its own.

- nLab: <https://ncatlab.org/nlab/show/conservative+functor>

## Current state in the library

Every `ReflectsIsos` occurrence in the tree is *positive*; not a single negative statement exists.

- `Structure/Limit/Preservation.v:243` — `Class ReflectsIsos {C D} (F : C ⟶ D) := { reflects_iso {x y} (f : x ~> y) : IsIsomorphism (fmap[F] f) → IsIsomorphism f }`. Its every use is a witness or a hypothesis: `Theory/Equivalence/Limit.v:335` `ff_reflects_isos`, `:456` `equivalence_reflects_isos`, `Monad/Monadicity/Beck.v:304`, `Monad/Lifting.v:497`, `Theory/Lawvere/Monad.v:89`, and `Context (refl : ReflectsIsos U)` in `Monad/Monadicity/Crude.v:115`. `rg 'ReflectsIsos F -> False'` → 0 hits; `rg -in 'does not reflect|need not reflect|fails to reflect|not conservative'` → 0 hits.
- One half of Riehl 1.5.v exists: `Construction/Funny/Comparison.v:69` `#[export] Program Instance FunnyToProduct_Full {C D} : Full (@FunnyToProduct C D)` together with `:154` `Corollary FunnyToProduct_not_faithful : Faithful (@FunnyToProduct _2 _2) → False` (resting on `:144` `funny_diagonals_distinct`) — a genuine full-but-not-faithful functor, and the tree's *only* negative statement about a functor.
- Missing: (a) any faithful-but-not-full functor proved not full (`rg 'Full .*-> False|not_full'` → 0 hits; every in-tree `Faithful` witness is either also `Full` or simply unclassified); (b) the exercises' actual conclusion, that such functors fail to reflect or to create isomorphisms — nothing is proved to fail either; (c) any "creates isomorphisms" predicate at all (the only creation notions in tree are `Monad/Monadicity/Beck.v:164` `CreatesUSplitCoequalizers` and `Theory/Equivalence/Limit.v:486/582`).
- **Verifier enrichment the Phase-C log undersells, and the shortest route to the whole issue:** the raw material for the 1.3.viii counterexample is already in tree. `Instance/Two.v:122` `Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False` says the walking arrow has no morphism back, and `Instance/One.v:47` gives the terminal category. The unique functor `_2 ⟶ _1` sends the non-identity arrow of `_2` (not an isomorphism, by `TwoHom_Y_X_absurd`) to an identity (an isomorphism) — that is Riehl's counterexample in two lines, and it does not need any new category.

## Work to be done

Suggested module: `Test/Conservative.v` or `Construction/Funny/Comparison.v` (extend), plus a small addition to `Structure/Limit/Preservation.v`.

1. Define `CreatesIsos` alongside the existing `ReflectsIsos` (`Structure/Limit/Preservation.v:243`), matching the shape of the in-tree creation predicates.
2. Riehl 1.3.viii: prove `ReflectsIsos (Erase : _2 ⟶ _1) → False`, using `Instance/Two.v:122` `TwoHom_Y_X_absurd` and `Instance/One.v:47`. State it as a named negative corollary so that the tree finally carries one.
3. Riehl 1.5.v, full-not-faithful leg: prove `ReflectsIsos (@FunnyToProduct _2 _2) → False` (or exhibit the failure of `CreatesIsos`), consuming the existing `FunnyToProduct_Full` and `FunnyToProduct_not_faithful`.
4. Riehl 1.5.v, faithful-not-full leg: exhibit a faithful functor and *prove it not full*, then show it fails to reflect isomorphisms. The cheapest in-tree candidate is a subcategory inclusion `Incl` for a non-full `Subcategory` (`Construction/Subcategory.v:59`); build a two-object toy subcategory rather than importing a new algebraic category.
5. Header note recording the general fact these counterexamples bound: fully faithful functors *do* reflect isomorphisms (`Theory/Equivalence/Limit.v:335`), so exactly one of the two halves cannot be dropped.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercises 1.3.viii and 1.5.v (setoid `≈` discipline; never `=` on morphisms)
- [ ] `CreatesIsos` is defined next to `ReflectsIsos`
- [ ] A functor is proved *not* to reflect isomorphisms (the tree's first negative `ReflectsIsos` statement)
- [ ] Both legs of Riehl 1.5.v are witnessed: a full-not-faithful functor and a faithful-not-full functor, each proved to fail reflection (or creation) of isomorphisms
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each negative result
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Test/Conservative.v
coqtop -R . Category -l Test/Conservative.v
#   Print Assumptions erase_not_conservative.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §§1.3, 1.5 (printed pp. 24, 38)"; confirm the faithful-not-full witness is genuinely proved not full, not merely left unproved.

## Dependencies

- Depends on: #231 (full and faithful functors, subcategories, and reflection of monics)

<!-- catalog: {"ids":["riehl:1.3:exviii","riehl:1.5:exv"],"deps":["#231"]} -->

---8<---

```yaml
title: "Riehl 1.3: Centre, commutator, automorphism and conjugacy-class functors on Grp and its wide subcategories"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:1.3:exix, riehl:1.3:exx]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.3 ("Functoriality"), printed p. 24 (PDF p. 44).
- Items: `riehl:1.3:exix` (Exercise 1.3.ix), `riehl:1.3:exx` (Exercise 1.3.x).

## Background

The centre, the commutator subgroup and the automorphism group are all assignments on groups; the exercise is to determine, for each, the largest wide subcategory of the category of groups along which it extends to a functor — isomorphisms only, epimorphisms, or all homomorphisms. Conjugacy classes give a functor to sets, and hence a cardinality invariant distinguishing non-isomorphic groups.

- nLab: <https://ncatlab.org/nlab/show/center+of+a+group>
- Wikipedia: <https://en.wikipedia.org/wiki/Conjugacy_class>

## Current state in the library

There is no category of groups, so none of the four assignments has a source category.

- `Structure/Group.v:109` — `Class GroupObject`, a group *object* in a cartesian monoidal category, with `Structure/Group/Proofs.v` for the derived laws. Not the category `Grp`.
- **The foothold both verifiers flagged and which a first implementer should not miss:** `Instance/Comp.v:382` `Definition Group := Algebra GroupOp GroupEq` presents groups as equational algebras over the in-tree universal-algebra development, and `Instance/Comp.v:151` `Program Definition Algs : Category := {| obj := OpAlgebra S; hom := AlgHom; ... |}` already gives them a category with homomorphisms (`OpAlgebra` at `:54`, `AlgHom` at `:64`, `EqSignature` at `:240`, `Record Algebra` at `:268`, witness `Definition Bool : Group` at `:405`). A category of groups is arguably a one-line instantiation of `Algs`; no such instantiation exists.
- `rg -in 'conjugacy'` over `*.v` → 0 hits (verifier re-ran it, exit 1). `rg -in 'commutator|automorphism group'` → prose only. Case-sensitive `rg 'Automorphism'` → 0 hits.
- Neither `Group_iso` nor `Group_epi` (wide subcategories on the isomorphisms, resp. the epimorphisms) exists, although the `Wide`/`Subcategory` machinery for building them does (`Construction/Subcategory.v:31/93`).
- The only positive general fact is `Theory/Functor.v:227` `#[export] Program Instance fobj_iso (F : C ⟶ D) : Proper (Isomorphism ==> Isomorphism) (fobj[F])` — Riehl's Lemma 1.3.8, which says nothing about conjugacy classes.

## Work to be done

Suggested module: `Instance/Grp/Functors.v`, over whatever `Grp` issue #255 delivers.

1. Build the two wide subcategories `Grp_iso` and `Grp_epi` using `Construction/Subcategory.v` (`sobj` total; `shom` selecting `IsIsomorphism`, resp. `Epic`), together with their `Wide` witnesses. Note that the isomorphism case is exactly the maximal-subgroupoid construction of the Riehl §1.1 issue, so reuse it rather than duplicating it.
2. Define `Z(−)`, `C(−)` (the commutator subgroup) and `Aut(−)` on objects, and settle each of the three variance questions with a proof or a counterexample:
   - `Z(−)`: functorial on `Grp_iso`, and **not** on `Grp` — issue #230 already schedules the `S₂ ↪ S₃ ↠ S₂` no-functor argument; consume it here rather than reproving it.
   - `C(−)`: functorial on all of `Grp` — issue #229 schedules the commutator/abelianization functors; consume them.
   - `Aut(−)`: functorial on `Grp_iso` only; a counterexample on `Grp_epi`.
3. Riehl 1.3.x: build `Conj : Grp ⟶ Sets` sending a group to its set of conjugacy classes, prove functoriality (a homomorphism carries conjugates to conjugates), and derive the corollary that groups whose conjugacy-class sets have different cardinalities are not isomorphic — the intended payoff, and a clean use of `Theory/Functor.v:227`.
4. Header note recording that all four assignments *are* trivially functorial out of the discrete category of groups, which is the exercise's baseline.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercises 1.3.ix and 1.3.x, printed p. 24 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `Grp_iso` and `Grp_epi` are built as wide subcategories with their `Wide` witnesses
- [ ] Each of `Z`, `C`, `Aut` is settled on each of the three domains, by a functor or by a proved counterexample — no clause left as prose
- [ ] `Conj : Grp ⟶ Sets` is constructed, proved functorial, and the cardinality corollary is proved
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Conj`, the cardinality corollary, and each counterexample
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Grp/Functors.v
coqtop -R . Category -l Instance/Grp/Functors.v
#   Print Assumptions Conj.  Print Assumptions conj_cardinality_invariant.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.3 (printed p. 24)"; confirm the epimorphisms of `Grp` used for `Grp_epi` are the categorical ones and that the identification with surjections is either proved (issue #251) or explicitly assumed.

## Dependencies

- Depends on: #255 (Grp, the category of groups)
- Depends on: #230 (the center of a group is not functorial)
- Depends on: #229 (commutator subgroup and abelianization functors)
- Depends on: #251 (epimorphisms of groups are surjective)
- Depends on: #643 (automorphism groups, permutation groups, and Cayley's theorem)

<!-- catalog: {"ids":["riehl:1.3:exix","riehl:1.3:exx"],"deps":["#255","#230","#229","#251","#643"]} -->

---8<---

```yaml
title: "Riehl 1.4: The torsion subgroup of a finitely generated abelian group and the non-naturality of its splitting"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.4:prop6, riehl:1.4:exv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.4 ("Naturality"), printed p. 28 and p. 30 (PDF pp. 48, 50).
- Items: `riehl:1.4:prop6` (Proposition 1.4.6), `riehl:1.4:exv` (Exercise 1.4.v).

## Background

Every finitely generated abelian group splits as its torsion subgroup plus a free part, but no such splitting can be chosen naturally in the group. Riehl's proof first computes that every natural endomorphism of the identity functor on finitely generated abelian groups is multiplication by a fixed integer, then derives a contradiction from the two test groups `ℤ` and `ℤ/2`. It is the book's cleanest demonstration that "isomorphic for each object" is strictly weaker than "naturally isomorphic".

- nLab: <https://ncatlab.org/nlab/show/torsion+subgroup>
- Wikipedia: <https://en.wikipedia.org/wiki/Structure_theorem_for_finitely_generated_modules_over_a_principal_ideal_domain>

## Current state in the library

Absent in both halves, verified independently.

- `rg -in 'torsion'` over `*.v` → **0 hits** (verifier re-ran it, exit 1). `rg -in 'finitely generated|abelian group'` → every hit is header prose in `Structure/{Abelian,Preadditive,Additive,Closed,Group,Monoid}.v` and `Theory/Adjunction.v`, citing `Ab` as motivation for the *abstract* abelian-category development.
- The only concrete additive witness is `Instance/CMon.v` (commutative monoids over setoids), which has no negation, no torsion and no finite-generation notion; so `Ab_fg`, `TA` and `A/TA` are all unavailable and the short exact sequence cannot be written.
- The more portable half is also missing: nothing in tree computes `End(Id)` for any category, and no statement of the form "every natural endomorphism of the identity is ..." exists anywhere. That computation is exactly the subject of issue #288 (the centre of a category), which is why this issue depends on it.
- `Structure/Abelian.v:441` `Abelian_OFS` and the rest of the additive spine take `ZeroObject` as a hypothesis and build no instance, so the ambient category has to come from issue #256.

## Work to be done

Suggested module: `Instance/Ab/Torsion.v`, over the `Ab` instance of issue #256.

1. Define the full subcategory `Ab_fg` of finitely generated abelian groups (`Construction/Subcategory.v` supplies the packaging).
2. Define the torsion subgroup `TA`, the quotient `A/TA`, and prove `ι_A : TA ↣ A` and `π_A : A ↠ A/TA` are the components of natural transformations between endofunctors of `Ab` — this is Riehl's Exercise 1.4.v, and it is the *positive* half, so it should be landed first and is independently useful.
3. Compute the centre of `Ab_fg`: every natural endomorphism of the identity functor is multiplication by a fixed integer, using that homomorphisms out of `ℤ` correspond to elements. State it against the `Nat(Id, Id)` monoid of issue #288 rather than inventing a second vocabulary.
4. Prove Proposition 1.4.6 as the corollary: there is no family of isomorphisms `A ≅ TA ⊕ (A/TA)` natural in `A`, by evaluating at `ℤ` (forcing `n = ±1`) and at `ℤ/2` (forcing `n` even).
5. Header note connecting this to `Theory/Equivalence.v`'s existing essay on pointwise-versus-natural isomorphism, which currently states the phenomenon only in prose.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.4 Proposition 1.4.6 and Exercise 1.4.v (setoid `≈` discipline; never `=` on morphisms)
- [ ] `Ab_fg`, `TA` and `A/TA` are constructed
- [ ] The naturality of `ι` and `π` is proved (Exercise 1.4.v)
- [ ] The centre computation for `Ab_fg` is proved, stated against issue #288's `Nat(Id, Id)` monoid
- [ ] The non-existence of a natural splitting is proved (a genuine negative statement, not a remark)
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the centre computation and the non-naturality theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Ab/Torsion.v
coqtop -R . Category -l Instance/Ab/Torsion.v
#   Print Assumptions torsion_splitting_not_natural.
#   Print Assumptions torsion_inclusion_natural.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.4 (printed pp. 28, 30)"; the negative statement must quantify over *all* natural families, not merely rule out the obvious candidate.

## Dependencies

- Depends on: #256 (Ab, the category of abelian groups)
- Depends on: #288 (the centre of a category)
- Depends on: #545 (exact sequences and short exact sequences)
- Depends on: #371 (torsion-free abelian groups form a reflective subcategory — its reflector is the quotient by the torsion subgroup, so the two developments must share one definition of `TA`)

<!-- catalog: {"ids":["riehl:1.4:prop6","riehl:1.4:exv"],"deps":["#256","#288","#545","#371"]} -->

---8<---

```yaml
title: "Riehl 1.4: The Riesz representation theorem as a natural isomorphism"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.4:example8]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.4 ("Naturality"), printed p. 28 (PDF p. 48).
- Items: `riehl:1.4:example8` (Example 1.4.8).

## Background

Riesz representation identifies the continuous dual of the space of continuous functions on a compact Hausdorff space with the space of signed measures on it. Riehl's point is that the identification is the assertion that a particular transformation — integration — is a natural *isomorphism* between two functors from compact Hausdorff spaces to Banach spaces, its naturality square being exactly the change-of-variables identity.

- nLab: <https://ncatlab.org/nlab/show/Riesz+representation+theorem>
- Wikipedia: <https://en.wikipedia.org/wiki/Riesz%E2%80%93Markov%E2%80%93Kakutani_representation_theorem>

## Current state in the library

Nothing exists; the verifier ran this one blind and reproduced the whole negative.

- `rg -i 'riesz'` over `*.v` → 0 hits. `rg -i 'banach'` → 1 hit, `Structure/Closed.v:67`, prose. `rg -i 'measure'` → 7 hits, all prose or Coq's `{measure ...}` recursion annotation. `rg -i 'compact.hausdorff|cHaus'` → nothing substantive.
- There is no category of topological spaces, no normed or Banach objects, no measures, and no integration.
- The verifier kept this ABSENT rather than OUT_OF_SCOPE: the obstruction is a missing analysis layer, not the library's foundations.
- Verifier correction to the Phase-C negative log, recorded so a later reader is not misled: the log's claim that "`rg -i 'compact'` returns only `CompactClosed`" is wrong in detail — `compact` also occurs in the compactly-generated-spaces prose — but the verdict is unaffected.

## Work to be done

This is a long-horizon issue whose value now is to record the obligation precisely; it should not be started before the topology layer (issue #259) and a normed-space layer exist.

1. Build `cHaus`, the category of compact Hausdorff spaces and continuous maps, as a full subcategory of `Top` (issue #259). Issue #489 (compact Hausdorff spaces are monadic over Set) and issue #413 already schedule adjacent material — align with whatever `cHaus` those deliver rather than building a second one.
2. Build `Ban`: Banach spaces and bounded linear maps (or short maps — fix the convention in the header, since it changes what "isomorphism" means).
3. `Σ : cHaus ⟶ Ban`, sending a space to the Banach space of signed Baire measures with pushforward as the action on maps; and `C* : cHaus ⟶ Ban`, the continuous dual of the space of continuous real-valued functions.
4. `η : Σ ⟹ C*` with components given by integration, proving the naturality square — which *is* the change-of-variables identity, and should be stated that way in the header.
5. The theorem itself: `η` is a natural isomorphism. Disclose in the header (per docs/INHABITATION.md) whether the analytic content is proved or assumed.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.4 Example 1.4.8, printed p. 28 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `cHaus` and `Ban` are constructed, or explicitly imported from the issues that build them
- [ ] `Σ`, `C*` and `η` are constructed and `η`'s naturality is proved
- [ ] The natural-isomorphism claim is either proved or stated as an explicitly disclosed hypothesis, with docs/INHABITATION.md updated
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `η` and its naturality
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship-level if the concrete instance lands)

## Verification

```
coqc -R . Category Instance/Ban.v Instance/CHaus.v Theory/Analysis/Riesz.v
coqtop -R . Category -l Theory/Analysis/Riesz.v
#   Print Assumptions riesz_natural.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.4 (printed p. 28)"; confirm the naturality square is stated for pushforward of measures against precomposition of functions, i.e. is genuinely the change-of-variables identity.

## Dependencies

- Depends on: #259 (Top, the category of topological spaces)
- Depends on: #489 (compact Hausdorff spaces are monadic over Set — the `cHaus` instance)

<!-- catalog: {"ids":["riehl:1.4:example8"],"deps":["#259","#489"]} -->

---8<---

```yaml
title: "Riehl 1.4: Natural transformations between the identity and the add-a-point endofunctor on Sets"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:1.4:exiv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.4 ("Naturality"), printed p. 30 (PDF p. 50).
- Items: `riehl:1.4:exiv` (Exercise 1.4.iv).

## Background

The add-a-point endofunctor on sets adjoins a fresh element to every set; the exercise asks for a complete classification of the natural transformations from the identity into it, and whether there are any in the other direction. It is a small, fully self-contained naturality computation of exactly the kind this library can do axiom-free.

- nLab: <https://ncatlab.org/nlab/show/maybe+monad>, <https://ncatlab.org/nlab/show/pointed+set>

## Current state in the library

The endofunctor exists twice; the classification does not exist at all.

- `Monad/Graded.v:287` — `Program Definition option_Functor : Coq ⟶ Coq := {| fobj := option; fmap := fun _ _ f o => option_map f o |}`.
- `Theory/Adamek/Corollaries.v:87` — `Program Definition NatF : Coq ⟶ Coq := {| fobj := fun X => option X; ... |}` (verified to be the same option endofunctor).
- `Theory/Coq/Maybe.v` supplies `Maybe_Functor`/`Maybe_Applicative`/`Maybe_Monad`, but `Theory/Coq/Functor.v:28` states plainly that the laws are *not* recorded for those Haskell-style classes, so they cannot carry a naturality argument.
- Missing entirely: any statement counting or characterizing `Nat(Id, option)` or `Nat(option, Id)`. The verifier's own reading was that the endofunctor's presence makes this arguably PARTIAL, and that the classifier's ABSENT is the honest call because the item *is* the counting claim and none of it is in tree.

## Work to be done

Suggested module: `Instance/Sets/AddPoint.v` (new), or an extension of `Instance/Sets.v`.

1. Build the add-a-point endofunctor on `Sets` (not merely on `Coq`): `X ↦ X + 1` over `option_setoid`, which `Instance/Sets/Par.v:27` already uses for the partial-map category. Prove functoriality with the setoid discipline.
2. Prove that `Nat(Id, (−)₊)` has exactly one element, the "inject" transformation `x ↦ Some x`, and prove it *is* natural. The uniqueness argument probes with maps out of a singleton, which `Instance/Sets.v:248` `Sets_Terminal` supplies.
3. Prove `Nat((−)₊, Id)` is empty, by evaluating at the empty set (`Instance/Sets.v:265` `Sets_Initial`): a component at `∅` would be a map `1 ⟶ ∅`.
4. State both as isomorphisms of setoids (a singleton setoid, resp. the empty setoid) rather than as informal counts, so the results compose with the rest of the library.
5. Header note connecting the endofunctor to `Instance/Sets/Par.v`'s `Part` and to the pointed-sets equivalence of issue #708, since it is the same construction seen three ways.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 1.4.iv, printed p. 30 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The add-a-point endofunctor on `Sets` is constructed and proved functorial
- [ ] `Nat(Id, (−)₊)` is proved to be a singleton, exhibiting the unique element
- [ ] `Nat((−)₊, Id)` is proved empty
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both classification results
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Sets/AddPoint.v
coqtop -R . Category -l Instance/Sets/AddPoint.v
#   Print Assumptions nat_id_to_addpoint_unique.
#   Print Assumptions nat_addpoint_to_id_empty.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.4 (printed p. 30)"; the emptiness proof must use the empty set, and the uniqueness proof must genuinely quantify over all natural families.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:1.4:exiv"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 1.5/1.6: Transporting a morphism along isomorphisms — the conjugation toolkit"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.5:lem10, riehl:1.5:exiii, riehl:1.6:lem12, riehl:1.6:lem13]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 33 and p. 38 (PDF pp. 53, 58); Section 1.6 ("The art of the diagram chase"), printed p. 43 (PDF p. 63).
- Items: `riehl:1.5:lem10` (Lemma 1.5.10), `riehl:1.5:exiii` (Exercise 1.5.iii), `riehl:1.6:lem12` (Lemma 1.6.12), `riehl:1.6:lem13` (Lemma 1.6.13).

## Background

Given a morphism and isomorphisms on each end, there is a unique conjugated morphism making any — equivalently all — of the four resulting squares commute; the triangle form of this says a commuting triangle stays commuting when an isomorphism edge is reversed; and a commuting square of isomorphisms inverts to a commuting square. These are the workhorse diagram lemmas Riehl uses throughout, and this library repeatedly reproves fragments of them inline.

- nLab: <https://ncatlab.org/nlab/show/isomorphism>, <https://ncatlab.org/nlab/show/commutative+diagram>

## Current state in the library

The ingredients are scattered, one of them is duplicated in two files, and none of the four statements is asserted.

- `Structure/Premonoidal.v:171` — `Lemma premon_square_from {a b c d : C} (i : a ≅ b) (j : c ≅ d) (f : a ~> c) (g : b ~> d) : g ∘ to i ≈ to j ∘ f → f ∘ from i ≈ from j ∘ g`. **This is the finding that overturned the Phase-C ABSENT verdict for Lemma 1.5.10**: despite living in `Section Premonoidal`, its statement and proof never mention the `Binoidal` context, so it is a general-category lemma, and it is exactly one implication of Riehl's "any one — equivalently all — of the four squares" clause.
- `Theory/Equivalence/Monoidal.v:98` — `Lemma iso_from_natural {x y x' y' : A} (i : x ≅ y) (j : x' ≅ y') (f : x ~> x') (g : y ~> y') (H : g ∘ to i ≈ to j ∘ f) : f ∘ from i ≈ from j ∘ g` — a **verbatim duplicate** of `premon_square_from`, independently proved, with neither file referencing the other. Worse for reuse, the verifier established that it is nested inside `Module MonoidalTransportSpine` (opened at `Theory/Equivalence/Monoidal.v:80`, closed at `:287`, `Import`ed only locally at `:289`), so a downstream consumer must qualify or import the module explicitly — it is not available as a general-purpose lemma.
- `Theory/Bicategory/Adjunction.v:215` — `Lemma iso_conj_from` is the same shape one level up, for 2-cells.
- `Theory/Equivalence/Monoidal.v:114/123` — `iso_cancel_spine_tf` / `iso_cancel_spine_ft`, the two spine-cancellation identities, written for monoidal-coherence proofs.
- `Theory/Isomorphism.v:264/275/286` — `iso_to_monic`/`iso_from_monic`/`iso_to_epic`; `:301` `comp_inverse_unique`; `:166` `iso_compose` (which asserts `(f ∘ g)⁻¹ ≈ g⁻¹ ∘ f⁻¹`); `:317` `to_equiv_implies_iso_equiv`.
- Missing: (a) **existence** — no lemma introduces `f' := to v ∘ f ∘ from u` as *the* morphism making the square commute; the composite occurs only inline (`Theory/Functor.v:159`, `Theory/Equivalence/FullFaithful.v:71,125`, `Theory/Equivalence.v:243`, `Construction/Karoubi/Universal.v:284`); (b) **uniqueness** — never concluded, though it is the load-bearing half for Riehl's Theorem 1.5.9; (c) the **four-way equivalence** — only the one implication above, and the two squares mixing `u` with `v⁻¹` and `u⁻¹` with `v` are never mentioned; (d) the triangle biconditional `h ≈ g ∘ f ↔ h ∘ f⁻¹ ≈ g` and its dual (`rg -n '↔'` filtered for iso/inv finds nothing of the sort); (e) the all-four-inverted square of Lemma 1.6.13 — `iso_from_natural` inverts only the two isomorphisms it is handed and keeps the other legs in their original direction.

## Work to be done

Suggested module: `Theory/Isomorphism/Transport.v` (new), placed so that both `Structure/Premonoidal.v` and `Theory/Equivalence/Monoidal.v` can consume it.

1. `iso_transport (f : a ~> b) (u : a ≅ a') (v : b ≅ b') : b' ^ a'` — define `f' := to v ∘ f ∘ from u`, prove it makes the square commute, and prove it is the **unique** such morphism (`Structure/UniversalProperty.v`'s `Unique` is the in-tree packaging).
2. Prove all four squares of Lemma 1.5.10 mutually equivalent (Exercise 1.5.iii), generalizing `premon_square_from` and giving the two mixed squares that no in-tree lemma currently mentions.
3. Lemma 1.6.12: the triangle biconditional `h ≈ g ∘ f ↔ h ∘ from f ≈ g` for an isomorphism `f`, and the dual for an isomorphism on the other leg. `iso_cancel_spine_tf`/`iso_cancel_spine_ft` plus `iso_to_epic`/`iso_to_monic` are the ingredients; `premon_square_from` instantiated at `j := iso_id` already gives the forward direction of one orientation.
4. Lemma 1.6.13: a commuting square all four of whose morphisms are isomorphisms inverts to a commuting square, in Riehl's form `from f ∘ from h ≈ from g ∘ from k`. Deriving it by four applications of the triangle lemma (or two of Lemma 1.5.10) is the book's own route and keeps the development honest.
5. **De-duplicate, as part of this issue:** `Theory/Equivalence/Monoidal.v:98` `iso_from_natural` and `Structure/Premonoidal.v:171` `premon_square_from` are the same lemma proved twice. Re-route both to the new general lemma and delete the duplicated proofs, keeping the old names as thin aliases if downstream call sites need them.

## Definition of Done

- [ ] Statement fidelity to Riehl Lemma 1.5.10, Exercise 1.5.iii, Lemmas 1.6.12 and 1.6.13 (setoid `≈` discipline; never `=` on morphisms)
- [ ] Existence *and* uniqueness of the transported morphism are proved
- [ ] All four commutativity conditions are proved mutually equivalent, including the two mixed squares
- [ ] The triangle biconditional and its dual are proved
- [ ] The inverted square of Lemma 1.6.13 is proved, in the all-four-inverted form
- [ ] `iso_from_natural` and `premon_square_from` are re-routed to the new lemma, with the duplicated proofs removed
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the transport lemma, the four-way equivalence, and both diagram lemmas
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Isomorphism/Transport.v
coqtop -R . Category -l Theory/Isomorphism/Transport.v
#   Print Assumptions iso_transport_unique.
#   Print Assumptions iso_square_four_equivalent.
rg -n 'premon_square_from|iso_from_natural' --glob '*.v'   # both now aliases, one proof
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §§1.5, 1.6 (printed pp. 33, 38, 43)"; confirm the uniqueness clause is present — it is the half Riehl's Theorem 1.5.9 actually consumes.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:1.5:lem10","riehl:1.5:exiii","riehl:1.6:lem12","riehl:1.6:lem13"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 1.5: The essential image of a functor, and a fully faithful functor as an equivalence onto it"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.5:example11]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 35 (PDF p. 55).
- Items: `riehl:1.5:example11` (Example 1.5.11).

## Background

The essential image of a functor is the full subcategory of the codomain spanned by all objects isomorphic to something in the image — the replete closure of the strict image. A fully faithful functor is an equivalence onto its essential image, which is the standard way of saying that "fully faithful" means "an embedding up to isomorphism".

- nLab: <https://ncatlab.org/nlab/show/essential+image>

## Current state in the library

Both halves are missing, while both tools are in place.

- `rg -i 'essential[ _]?image'` over `*.v` → **0 hits**, confirmed twice by the verifier.
- The apparatus for the construction exists: `Construction/Subcategory.v` `Record Subcategory` (line 31, with `sobj : C → Type` at 32 and `shom` at 34), `Sub` (50), `Incl` (59), `Full` (69), `Replete` (87). The essential image is the instance `sobj d := ∃ c, F c ≅ d` with `shom` total — and no file instantiates it that way.
- The theorem it feeds is also in place: `Theory/Equivalence/FullFaithful.v:160` `FF_ESO_Equivalence` (full + faithful + essentially surjective ⇒ equivalence), and `Theory/Equivalence.v:141` `Class EssentiallySurjective` in its split, data-carrying `{eso_obj; eso_iso}` form.
- `rg -i 'onto its image|corestrict|spanned by'` reaches only `Instance/Sets/Image.v`, which is the epi-mono factorization of a single *morphism* in `Sets` — an unrelated notion.
- The verifier's framing, which should guide the implementation: this is a short derivation on top of existing tools rather than new mathematics.

## Work to be done

Suggested module: `Construction/Subcategory/EssentialImage.v` (new).

1. `EssentialImage (F : C ⟶ D) : Subcategory D` with `sobj d := ∃ c, F c ≅ d` and `shom` total, plus the `Full` witness and the `Replete` witness (repleteness is what distinguishes the *essential* image from the strict image built in issue #712).
2. The corestriction `F' : C ⟶ Sub (EssentialImage F)` with `Incl ◯ F' ≈ F`.
3. `F'` is essentially surjective by construction; if `F` is full and faithful then so is `F'`; conclude via `FF_ESO_Equivalence` that `C ≃ Sub (EssentialImage F)`.
4. Relate to issue #712's full-image factorization: the essential image is the replete closure of the full image, and the two agree exactly when the codomain's isomorphism classes meeting the image are singletons — state the comparison functor at minimum.
5. Header note: because the split `EssentiallySurjective` carries the chosen isomorphism as data, the equivalence here is axiom-free, unlike the classical statement; this is the same discipline `Theory/Equivalence.v:102-117` already discusses in prose.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.5 Example 1.5.11, printed p. 35 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `EssentialImage` is constructed, with its `Full` and `Replete` witnesses
- [ ] The corestriction is constructed and `Incl ◯ F' ≈ F` is proved
- [ ] The equivalence `C ≃ Sub (EssentialImage F)` for fully faithful `F` is proved through `FF_ESO_Equivalence`
- [ ] The comparison with the full-image factorization is stated
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `EssentialImage` and the equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Subcategory/EssentialImage.v
coqtop -R . Category -l Construction/Subcategory/EssentialImage.v
#   Print Assumptions EssentialImage.
#   Print Assumptions ff_equivalence_onto_essential_image.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 35)"; confirm repleteness is proved, since that is what makes the subcategory the *essential* image rather than the strict one.

## Dependencies

- Depends on: #712 (the full-image factorization of a functor)
- Depends on: #231 (full and faithful functors, subcategories, and reflection of monics)

<!-- catalog: {"ids":["riehl:1.5:example11"],"deps":["#712","#231"]} -->

---8<---

```yaml
title: "Riehl 1.5: Essentially small and essentially discrete categories"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.5:def-essentially-small, riehl:1.5:exvii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 38 (PDF p. 58).
- Items: `riehl:1.5:def-essentially-small` (unnumbered, running prose), `riehl:1.5:exvii` (Exercise 1.5.vii).

## Background

Smallness and discreteness are not invariant under equivalence, so each has an equivalence-invariant repair: a category is essentially small when it is equivalent to a small one, and essentially discrete when it is equivalent to a discrete one. Riehl introduces both immediately after warning against "evil" definitions, and the exercise asks for an intrinsic characterization of the essentially discrete categories.

- nLab: <https://ncatlab.org/nlab/show/essentially+small+category>, <https://ncatlab.org/nlab/show/principle+of+equivalence>

## Current state in the library

Neither notion exists, and one of the two prerequisites is itself a documented gap.

- `rg -in 'essentially small|essentially_small|essentially discrete|EssentiallyDiscrete'` → **0 hits**, re-run and confirmed by the verifier.
- Discreteness *does* exist, in the evil form: `Structure/Discrete.v:28` `Definition Discrete (C : Category) := ∀ x y (f : x ~> y), ∃ H : x = y, f ~= rew H in id`, with `Instance/Discrete.v:37` `DiscreteCat` and the bridge `Instance/Discrete.v:65` `DiscreteCat_Discrete`. The file's own header (`Structure/Discrete.v:19-22`) says the predicate uses object *equality* and thereby violates the principle of equivalence — the library already knows the repair is missing.
- Smallness does not exist at all: `Category` is universe-polymorphic in `{o h p}` and size is carried by universe levels, so "equivalent to a small category" cannot be stated until a size predicate exists. That is why this issue depends on the size issue.
- Neither `Structure/Discrete.v`'s predicate nor `DiscreteCat` is ever related to the bundled `≃` (`Theory/Equivalence/Bundled.v`), and no skeleton construction exists to route through.
- The verifier kept both items ABSENT rather than OUT_OF_SCOPE: a size predicate is constructible here, so the definitions are within reach once it lands.

## Work to be done

Suggested module: `Theory/Equivalence/Essential.v` (new).

1. `EssentiallySmall (C : Category) := ∃ D, Small D ∧ C ≃ D` over whatever `Small` predicate issue #253 delivers, plus the equivalent formulation via the skeleton once issue #374 lands ("essentially small iff its skeleton is small").
2. `EssentiallyDiscrete (C : Category) := ∃ (A : Type), C ≃ DiscreteCat A`, using the bundled `≃` of `Theory/Equivalence/Bundled.v`.
3. Prove the repair claim for each: both predicates are invariant under equivalence (which `Discrete` and `Small` are not), stating the failure of the un-repaired versions as a counterexample rather than as prose.
4. Riehl 1.5.vii: characterize the essentially discrete categories intrinsically — a category is essentially discrete exactly when every hom-setoid is either empty or a singleton *and* every morphism is an isomorphism (equivalently, it is a groupoid whose skeleton is discrete). Prove both directions. Once issue #248's `IsGroupoid` lands, state the groupoid clause against it.
5. Update `Structure/Discrete.v`'s header to point at the repaired predicate, since it currently only records that the repair is needed.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.5, printed p. 38 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `EssentiallySmall` and `EssentiallyDiscrete` are defined against the bundled `≃`
- [ ] Equivalence-invariance of both is proved, with a counterexample showing `Discrete` is not invariant
- [ ] The intrinsic characterization of essentially discrete categories is proved in both directions
- [ ] `Structure/Discrete.v`'s header is updated to reference the repaired predicate
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both predicates and the characterization
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Equivalence/Essential.v
coqtop -R . Category -l Theory/Equivalence/Essential.v
#   Print Assumptions EssentiallyDiscrete.
#   Print Assumptions essentially_discrete_iff.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 38)"; confirm the characterization is proved in both directions and not merely stated.

## Dependencies

- Depends on: #253 (size and foundations vocabulary — supplies the `Small` predicate; see the Riehl §1.1 append there)
- Depends on: #374 (skeletons and skeletal categories)
- Depends on: #248 (groupoids and the structure of connected groupoids)

<!-- catalog: {"ids":["riehl:1.5:def-essentially-small","riehl:1.5:exvii"],"deps":["#253","#374","#248"]} -->

---8<---

```yaml
title: "Riehl 1.5: Equivalence-invariance of categorical notions"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.5:remark-equivalence-invariance]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 37 (PDF pp. 57–58).
- Items: `riehl:1.5:remark-equivalence-invariance` (unnumbered guiding principle plus a bulleted list).

## Background

Riehl's guiding principle is that a categorically defined concept should be invariant under equivalence, and she lists six concrete instances — invariance of isomorphism-of-arrows and of objects, of local smallness, of being a groupoid, of the opposite construction, and of products — calling any definition that fails this "evil". Making the list a theorem rather than a slogan is what turns the principle into something the library can enforce.

- nLab: <https://ncatlab.org/nlab/show/principle+of+equivalence>

## Current state in the library

Three of the six claims are in tree; three are unstatable or unstated.

Present:
- `Theory/Functor.v:227` — `#[export] Program Instance fobj_iso (F : C ⟶ D) : Proper (Isomorphism ==> Isomorphism) (fobj[F])`, with `to := fmap[F] (to X)` and `from := fmap (from X)`, giving the preservation direction for both arrow- and object-isomorphism.
- `Theory/Equivalence/Limit.v:456` — `Definition equivalence_reflects_isos : ReflectsIsos F := ff_reflects_isos (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E)`, the reflection direction; and `Theory/Functor.v:355` `Lemma FullyFaithful ... : ∀ x y, F x ≅ F y → x ≅ y` for objects.
- `Theory/Equivalence/Limit.v:524` — `Definition EquivalenceOfCategories_op ... : @EquivalenceOfCategories (C^op) (D^op) (F^op)`, i.e. `C ≃ D ⇒ C^op ≃ D^op`. (The verifier's own blind pass missed this one and the classifier found it; it is genuinely there.)

Absent:
- "equivalent to a locally small category ⇒ locally small": there is no smallness or local-smallness predicate at all (`rg -i 'locally small'` returns four comment-only hits, in `Functor/Hom.v`, `Functor/Representable.v`, `Structure/Complete.v`, `Construction/Enriched.v`), so the claim cannot be stated before a size predicate exists.
- "equivalent to a groupoid ⇒ groupoid": there is no groupoid *predicate* — `Construction/Groupoid.v:103` defines only the core construction.
- "the product of a pair of categories is equivalent to the product of any pair of equivalent categories": no such transport along `Construction/Product.v`'s `C ∏ D` exists.
- The "evil"/non-evil discipline itself is nowhere named, although `Structure/Discrete.v:19-22` records exactly this criticism of its own predicate in prose.

## Work to be done

Suggested module: `Theory/Equivalence/Invariance.v` (new), collecting the six claims in one place.

1. Package the two present isomorphism claims as named, citable lemmas over the bundled `≃` (`Theory/Equivalence/Bundled.v:115` `Equivalence_trans` etc.), rather than leaving them as an `Instance` plus a `ReflectsIsos` derivation in a limits file — the point of the remark is that the list is quotable.
2. Prove product-invariance: `C ≃ C' → D ≃ D' → C ∏ D ≃ C' ∏ D'`, over `Construction/Product.v:95`.
3. Restate `EquivalenceOfCategories_op` as the bundled `C ≃ D → C^op ≃ D^op` and place it with the others.
4. Prove groupoid-invariance once issue #248's `IsGroupoid` predicate lands: `C ≃ D → IsGroupoid C → IsGroupoid D` (immediate from `fobj_iso` plus essential surjectivity, but currently unstatable).
5. Prove local-smallness-invariance once issue #253 supplies a predicate.
6. Header essay stating the principle, listing which in-tree definitions are evil by this standard (`Structure/Discrete.v:28` uses object equality; the object-isomorphism-as-equality idiom in `Instance/StrictCat.v`) and pointing at the repaired versions.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.5, printed p. 37 (setoid `≈` discipline; never `=` on morphisms)
- [ ] All six bulleted claims are stated; each is either proved or explicitly recorded as blocked on a named prerequisite issue, with nothing left as prose
- [ ] Product-invariance of equivalence is proved
- [ ] The opposite-invariance statement is available in bundled `≃` form
- [ ] The header lists the in-tree definitions that fail the principle, with pointers to their repairs
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each invariance lemma
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Equivalence/Invariance.v
coqtop -R . Category -l Theory/Equivalence/Invariance.v
#   Print Assumptions equivalence_product_invariant.
#   Print Assumptions equivalence_op_invariant.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 37)"; confirm each of the six claims appears explicitly, blocked ones included.

## Dependencies

- Depends on: #248 (groupoids and the structure of connected groupoids)
- Depends on: #253 (size and foundations vocabulary; see the Riehl §1.1 append there)

<!-- catalog: {"ids":["riehl:1.5:remark-equivalence-invariance"],"deps":["#248","#253"]} -->

---8<---

```yaml
title: "Riehl 1.5: Segal's category Gamma and the opposite of finite pointed sets"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:1.5:exii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 38 (PDF p. 58).
- Items: `riehl:1.5:exii` (Exercise 1.5.ii).

## Background

Segal's category has finite sets as objects and, as morphisms, maps into the power set with pairwise disjoint values; the exercise is to prove it equivalent to the opposite of the category of finite pointed sets, which is the identification underlying Segal's approach to commutative monoids in algebraic topology (Γ-spaces).

- nLab: <https://ncatlab.org/nlab/show/Segal%27s+category>
- Wikipedia: <https://en.wikipedia.org/wiki/Universal_coefficient_theorem> is unrelated; see instead the nLab entry above and <https://ncatlab.org/nlab/show/pointed+set>

## Current state in the library

Nothing exists.

- `rg -i 'segal'` over `*.v` → **0 hits**, re-run and confirmed.
- There is no category of pointed sets: the five "pointed set" occurrences (`Instance/Coq/Par.v:34-36`, `Instance/Coq/ParE.v:116`, `Construction/Slice.v:82`) are all prose, and `Instance/Coq/Par.v:34` is careful to label its claim ("equivalent — not isomorphic — to the category of pointed sets") a remark rather than a theorem.
- `Instance/Fun.v:230` `Class Pointed` is about *pointed endofunctors* (a transformation `Id ⟹ F`), with `WellPointed` at `:240` — an unrelated notion that a naive search will surface.
- `Structure/Topos.v:129` `Pow a := Ω ^ a` is an internal power *object* in a topos and cannot carry Segal's hom description, as the verifier confirmed.
- The skeletal finite-set side is present and usable: `Instance/FinSet.v` (objects the naturals, computable coproducts) and `Instance/FinSet/Product.v`/`Closed.v`/`Classifier.v`.

## Work to be done

Suggested module: `Instance/Segal.v` (new), over the finite pointed sets that issue #261 delivers (restricted to the finite case, or built directly on `Instance/FinSet.v`).

1. Build `Fin_*`, the category of finite pointed sets and basepoint-preserving maps — either as the pointed restriction of issue #261's `Set_*` or directly over `Instance/FinSet.v`, whichever keeps the skeletal computability that `Instance/FinSet.v` already enjoys.
2. Build `Gamma`: objects finite sets; a morphism `S ⟶ T` is a map `θ : S → P(T)` with `θ(α)` and `θ(β)` disjoint for `α ≠ β`; composition `ψ(α) = ⋃_{β ∈ θ(α)} φ(β)`. Prove associativity and unitality — the disjointness condition is the part that needs care.
3. Construct the comparison functor and prove `Gamma ≃ Fin_*^op`, using the split `EssentiallySurjective` of `Theory/Equivalence.v:141` and `Theory/Equivalence/FullFaithful.v:160` `FF_ESO_Equivalence` so the result is axiom-free.
4. Deduce the exercise's corollary: the commutative-monoid functors of Riehl Example 1.3.2(xi) (`M^{(A,a)} = M^{A ∖ a}`, transitions by summing over fibres) define presheaves on `Gamma`. `Instance/CMon.v:140` supplies the commutative monoids.
5. Header note distinguishing `Gamma` from the simplex category (issue #225), with which it is easily confused.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 1.5.ii, printed p. 38 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `Gamma` is constructed with its category laws proved, including the disjointness condition on composites
- [ ] `Fin_*` is constructed (or imported) and `Gamma ≃ Fin_*^op` is proved
- [ ] The Γ-presheaf corollary for commutative monoids is proved
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Gamma`, the equivalence, and the corollary
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Segal.v
coqtop -R . Category -l Instance/Segal.v
#   Print Assumptions Gamma.  Print Assumptions gamma_equiv_finpointed_op.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 38)"; confirm the equivalence is with the *opposite* of finite pointed sets and that the composite formula is the union over fibres, not the direct image.

## Dependencies

- Depends on: #261 (Set_*, the category of pointed sets)
- Depends on: #225 (the simplicial category Delta — for the header contrast only; not a build prerequisite)

<!-- catalog: {"ids":["riehl:1.5:exii"],"deps":["#261","#225"]} -->

---8<---

```yaml
title: "Riehl 1.5: Affine and projective planes as equivalent groupoids"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:1.5:exviii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 38 (PDF p. 58).
- Items: `riehl:1.5:exviii` (Exercise 1.5.viii).

## Background

Klein's Erlangen programme reads a geometry as the study of the invariants of a group of transformations; categorically, a geometry is a groupoid, and comparing geometries means comparing groupoids up to equivalence. The exercise asks for the classical comparison: affine planes are equivalent to projective planes equipped with a distinguished line at infinity.

- nLab: <https://ncatlab.org/nlab/show/projective+plane>
- Wikipedia: <https://en.wikipedia.org/wiki/Affine_plane_(incidence_geometry)>

## Current state in the library

There is no incidence geometry of any kind.

- "affine plane", "projective plane", "incidence", "Erlangen", "line at infinity" → 0 hits each. Every apparent "incidence" hit is the substring of "coincidence".
- The only "affine" hits are affine = semicartesian monoidal (`Structure/Monoidal/Semicartesian.v`, `Structure/Monoidal/Markov.v`); the only "projective" hits are "enough projectives" (`Structure/Abelian.v:97`) and "projective limit" (`Structure/Limit.v:43,51`).
- `Construction/Groupoid.v` is generic; there is no groupoid predicate to state "the groupoid of affine planes" against (that is issue #248).
- The verifier kept this ABSENT rather than OUT_OF_SCOPE: the statement is perfectly formalizable, the library simply has no geometry layer.

## Work to be done

Suggested module: `Instance/Geometry/Plane.v` (new).

1. Define an incidence structure (points, lines, an incidence relation) and the two axiom sets: affine planes and projective planes.
2. Build the two groupoids: `Affine` with morphisms the pairs of bijections on points and on lines that preserve *and reflect* incidence; `Proj_l` likewise, additionally preserving the distinguished line. Prove each is a groupoid against issue #248's `IsGroupoid`.
3. Construct `Proj_l ⟶ Affine` by deleting the line at infinity and its points, and prove it fully faithful and essentially surjective.
4. Construct the inverse equivalence explicitly (adjoining the line at infinity from the parallel classes), so the equivalence is exhibited rather than obtained by an existence argument — this is what the exercise asks for.
5. Header essay on the Erlangen reading, connecting to `Construction/Groupoid.v`'s existing background essay.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 1.5.viii, printed p. 38 (setoid `≈` discipline; never `=` on morphisms)
- [ ] Both groupoids are constructed and proved to satisfy the groupoid predicate
- [ ] The forgetting functor and an *explicit* inverse equivalence are constructed, with the unit and counit isomorphisms proved
- [ ] The morphism condition preserves *and reflects* incidence, as the exercise requires
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both groupoids and the equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Geometry/Plane.v
coqtop -R . Category -l Instance/Geometry/Plane.v
#   Print Assumptions affine_equiv_projective_pointed.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 38)"; the inverse equivalence must be constructed explicitly, not merely shown to exist.

## Dependencies

- Depends on: #248 (groupoids and the structure of connected groupoids)

<!-- catalog: {"ids":["riehl:1.5:exviii"],"deps":["#248"]} -->

---8<---

```yaml
title: "Riehl 1.5: The action groupoid and the categorified orbit-stabilizer theorem"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.5:example19]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.5 ("Equivalence of categories"), printed p. 37 (PDF p. 57).
- Items: `riehl:1.5:example19` (Example 1.5.19).

## Background

The action groupoid of a group acting on a set has the elements of the set as objects and one morphism for each group element carrying one point to another. Its skeleton has the orbits as objects and the stabilizers as automorphism groups, so the orbit–stabilizer theorem falls out as a decategorification of "a groupoid is equivalent to its skeleton".

- nLab: <https://ncatlab.org/nlab/show/action+groupoid>, <https://ncatlab.org/nlab/show/orbit>
- Wikipedia: <https://en.wikipedia.org/wiki/Orbit-stabilizer_theorem>

## Current state in the library

Every ingredient is absent, and the verifier flagged one search trap worth repeating here.

- `rg -i 'orbit'` over `*.v` → **0 hits**. `rg -i 'stabilizer'` → 1 hit, `Instance/ZX.v:137`, a bibliography line about stabilizer quantum mechanics. `rg -i 'action groupoid|translation groupoid'` → 0 hits.
- **Search trap:** a naive `rg -i 'G-set'` appears to hit `Structure/Closed.v:52` and `Theory/Lawvere/Sets.v`, but those are substring matches inside "underlyin(g-set) functor". There is genuinely no `G`-set construction in the tree.
- `Structure/Group.v` defines only `GroupObject` internal to a cartesian monoidal category, with no action; there is no delooping of a group into a one-object category, hence no `X : BG ⟶ Sets` to take the action groupoid of.
- There is no groupoid predicate, no connectedness predicate and no skeleton, so none of the example's three steps has a subject.

## Work to be done

Suggested module: `Construction/ActionGroupoid.v` (new).

1. Over the delooping of issue #220 and the `G`-set correspondence of issue #234, define `X // G` for `X : BG ⟶ Sets`: objects the elements of `X`, a morphism `x ⟶ y` for each `g` with `g · x ≈ y`, composition by multiplication. Prove it is a category and that it satisfies issue #248's `IsGroupoid`.
2. Define orbits as the connected components of `X // G` (issue #248 supplies the `Connected` predicate; the components are its equivalence classes) and stabilizers as the automorphism groups `Hom_{X//G}(x, x)`, proving the latter is a subgroup of `G`.
3. Prove that elements in the same orbit have isomorphic stabilizers, as a corollary of issue #248's conjugation isomorphism between vertex groups.
4. Prove the skeleton computation: the objects of `sk(X // G)` are the orbits and its automorphism groups the stabilizers, so the skeleton is the disjoint union of stabilizer groups indexed by orbits. Route through issue #374's skeleton relation rather than choosing representatives ad hoc.
5. Decategorify: the set of morphisms of `X // G` out of `x` is in bijection with `G` and decomposes over the orbit, giving `|G| = |orbit| · |stabilizer|` for a finite group — state it over `Instance/FinSet.v` so it is an actual counting theorem rather than a remark.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.5 Example 1.5.19, printed p. 37 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `X // G` is constructed and proved a groupoid
- [ ] Orbits and stabilizers are defined, and same-orbit elements are proved to have isomorphic stabilizers
- [ ] The skeleton computation is proved
- [ ] The orbit–stabilizer counting corollary is proved for a finite group
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the action groupoid, the skeleton computation and the counting corollary
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/ActionGroupoid.v
coqtop -R . Category -l Construction/ActionGroupoid.v
#   Print Assumptions ActionGroupoid.  Print Assumptions orbit_stabilizer.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.5 (printed p. 37)"; the counting corollary must be derived from the skeleton computation, not proved independently — that derivation is the example's point.

## Dependencies

- Depends on: #220 (delooping monoids and groups into one-object categories)
- Depends on: #234 (functors between preorders, groups, and representation categories — G-actions as functors out of a delooping)
- Depends on: #248 (groupoids and the structure of connected groupoids)
- Depends on: #374 (skeletons and skeletal categories)

<!-- catalog: {"ids":["riehl:1.5:example19"],"deps":["#220","#234","#248","#374"]} -->

---8<---

```yaml
title: "Riehl 1.6: Cancellation criteria for pasted squares, and the failure of the converse"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.6:remark21, riehl:1.6:lem22]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.6 ("The art of the diagram chase"), printed p. 46 (PDF pp. 66–67).
- Items: `riehl:1.6:remark21` (Remark 1.6.21), `riehl:1.6:lem22` (Lemma 1.6.22).

## Background

Two adjacent commuting squares paste to a commuting rectangle, but the converse fails: a commuting rectangle need not have commuting halves, and one commuting half plus the rectangle does not in general give the other. What rescues it is a cancellation hypothesis — a monomorphism on the right or an epimorphism on the left. This is the diagram-chase discipline Riehl spends §1.6 installing.

- nLab: <https://ncatlab.org/nlab/show/pasting+law+for+pullbacks> (the pullback-specific analogue), <https://ncatlab.org/nlab/show/commutative+diagram>

## Current state in the library

The positive half is proved; the cancellation criterion and both negative statements are absent.

- Pasting is genuinely proved, not axiomatized: `Construction/Sq.v:47` `Program Definition Sq (C : Category) : DoubleCategory := {| ...; dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h; ... |}`, whose `dsq_hcomp` obligation at `Construction/Sq.v:69-72` reads `(* dsq_hcomp : (k' ∘ k) ∘ u ≈ w ∘ (h' ∘ h) *)` with proof `rewrite <- comp_assoc, X, comp_assoc, X0, <- comp_assoc` — exactly the adjacent-squares-paste-to-rectangle step. The general field is `Theory/DoubleCategory.v:243` `dsq_hcomp`.
- The cancellation vocabulary is present: `Theory/Morphisms.v:116` `Class Monic {x y} (f : x ~> y) := { monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2 }` and `:104` `Class Epic ... { epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2 }`.
- Missing (Lemma 1.6.22): no lemma with the rectangle hypotheses exists, in either orientation. The two closest in-tree assertions are shape-specific specializations — `Theory/Subobject.v:78` `Lemma sub_le_unique (u v : SubObj x) (k k' : sub_dom u ~> sub_dom v) : sub_mono v ∘ k ≈ sub_mono u → sub_mono v ∘ k' ≈ sub_mono u → k ≈ k'` (the *triangle* version, cancelling one mono, proved by `apply (monic (Monic:=sub_is_monic v))`), and `Theory/Morphisms/Stability.v:226` `monic_pullback_stable`, whose proof at lines 234–240 executes precisely the Lemma 1.6.22 step — deriving `snd ∘ g1 ≈ snd ∘ g2` from a commuting outer configuration by `apply mono` — but only as an internal `assert`.
- Missing (Remark 1.6.21): both negative statements. The tree contains **no** negative statement about commuting squares at all; the only counterexample-style result about diagrams anywhere is `Construction/Funny/Comparison.v:154` `Corollary FunnyToProduct_not_faithful : Faithful (@FunnyToProduct _2 _2) → False`. Riehl's own counterexample lives in the category of abelian groups, which does not exist in tree.

## Work to be done

Suggested module: `Theory/Morphisms/Rectangle.v` (new), or a section added to `Theory/Morphisms/Stability.v`.

1. `rectangle_left_from_right : (l ∘ j) ∘ f ≈ (m ∘ k) ∘ g → l ∘ j ≈ m ∘ h → Monic m → k ∘ g ≈ h ∘ f` — Riehl's clause (i), stated exactly as the rectangle hypothesis plus the right square plus monicity.
2. The dual clause (ii) with an epimorphism on the left, obtained *by duality through `C^op`* rather than reproved — the section's methodological point.
3. Refactor `Theory/Morphisms/Stability.v:226` `monic_pullback_stable` to consume the new lemma instead of its inline `assert`, so the general statement earns its place.
4. Remark 1.6.21, negative half (a): exhibit a commuting rectangle whose two halves do not commute, as a proved `→ False` statement. Riehl's witness needs the category of abelian groups, but a cheaper in-tree witness should be sought first — a two-element hom-setoid in a small concrete category, or `Instance/CMon.v` with the zero morphism playing the role of the zero map.
5. Remark 1.6.21, negative half (b): exhibit a commuting rectangle plus one commuting square whose other square does not commute.
6. Header note recording that both negatives are about *cancelability*, and pointing at `Theory/Morphisms.v:116/104` as the hypotheses that repair them.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.6 Remark 1.6.21 and Lemma 1.6.22, printed pp. 46–47 (setoid `≈` discipline; never `=` on morphisms)
- [ ] Both clauses of the cancellation criterion are proved, with the second derived by duality
- [ ] `monic_pullback_stable` is re-routed through the new lemma
- [ ] Both failures of the converse are witnessed by proved negative statements, not prose
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the two criteria and the two counterexamples
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Morphisms/Rectangle.v
coqtop -R . Category -l Theory/Morphisms/Rectangle.v
#   Print Assumptions rectangle_left_from_right.
#   Print Assumptions rectangle_converse_fails.
rg -n 'assert .*Epic|apply mono' Theory/Morphisms/Stability.v   # inline chase gone
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.6 (printed pp. 46–47)"; the dual clause must be obtained through `C^op`, and the counterexamples must be `→ False` statements rather than comments.

## Dependencies

- Depends on: #250 (monic/epi cancellation and a non-invertible bimorphism)

<!-- catalog: {"ids":["riehl:1.6:remark21","riehl:1.6:lem22"],"deps":["#250"]} -->

---8<---

```yaml
title: "Riehl 1.7: Size of functor categories — local smallness of [C, D]"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:1.7:remark3, riehl:1.7:exi]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 1.7 ("The 2-category of categories"), printed p. 48 and p. 51 (PDF pp. 68, 71).
- Items: `riehl:1.7:remark3` (Remark 1.7.3), `riehl:1.7:exi` (Exercise 1.7.i).

## Background

Forming a functor category can increase size: it preserves smallness, but two large locally small categories can have a functor category that is not locally small. What does suffice is that the domain be small and the codomain locally small, proved by sending a natural transformation to its family of components.

- nLab: <https://ncatlab.org/nlab/show/locally+small+category>, <https://ncatlab.org/nlab/show/functor+category>

## Current state in the library

The mathematical content is discharged silently by universe inference; none of the three clauses is stated as a theorem.

- `Instance/Fun.v:108` — `Program Definition Fun : Category := {| obj := C ⟶ D; hom := @Transform C D; id := @nat_id C D; compose := @nat_compose C D; compose_respects := @nat_compose_respects C D |}`. The size closure is recorded only as a universe constraint solved at elaboration time, never as a proposition.
- `Theory/Category.v:111` — `Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)}` with `hom : obj → obj → uhom` at `Type@{h}`; `Theory/Functor.v:96` `Class Functor@{o1 h1 p1 o2 h2 p2}`.
- `Theory/Natural/Transformation.v:139` — `Program Instance Transform_Setoid : Setoid Transform := {| equiv N0 N1 := ∀ x, (@transform N0 x) ≈ (@transform N1 x) |}`. This **is** the exercise's hint in definitional form: two natural transformations are identified exactly when their component families agree, so "send a natural transformation to its collection of components" is injective by construction. Only the size conclusion drawn from that injection is missing.
- There is no smallness vocabulary at all: `rg 'Class .*Small|Definition .*Small|IsSmall|LocallySmall|Record .*Small'` → **0 hits** (verifier re-ran it); every "locally small" occurrence is header prose (`Functor/Representable.v:29`, `Functor/Hom.v:18`, `Construction/Enriched.v:26`, `Structure/Complete.v:16-111`, `Adjunction/SAFT.v:56-90`, `Theory/Lawvere/Sets.v:44`, `Instance/Cat.v:22-26,108-114`).
- Consequently the remark's counterexample clause — large locally small `C` and `D` with `[C,D]` not locally small — is not expressible either.

## Work to be done

Suggested module: `Instance/Fun/Size.v` (new), over whatever size predicate issue #253 delivers.

1. Once issue #253 supplies `Small`/`LocallySmall` as bundled predicates (a category whose objects and homs lie below a given level), state and prove:
   - `Small C → Small D → Small (Fun C D)`;
   - `Small C → LocallySmall D → LocallySmall (Fun C D)` — Exercise 1.7.i, whose proof is the monomorphism from `Transform F G` into the product of hom-collections given by `Theory/Natural/Transformation.v:139`.
2. Make the injection explicit as a named map `components : Transform F G → ∀ x, F x ~> G x` together with the injectivity lemma, so the exercise's hint is a first-class artifact rather than a definitional accident.
3. Record the negative clause honestly: exhibiting large locally small `C, D` with `[C,D]` not locally small requires a proper-class-sized index, which this library's universe discipline cannot express as a *failure*; disclose that in the header as a scope limit rather than leaving it as an unproved claim, in the same style as `Instance/Cat.v:22-26`.
4. Optionally add `Fail Check` demonstrations in `Test/Size.v` (the file issue #253 proposes) showing where the universe constraint actually bites, which is the machine-checked shadow of the remark.

## Definition of Done

- [ ] Statement fidelity to Riehl §1.7 Remark 1.7.3 and Exercise 1.7.i, printed pp. 48, 51 (setoid `≈` discipline; never `=` on morphisms)
- [ ] Both positive closure statements are proved against the size predicate
- [ ] The `components` injection and its injectivity are named lemmas
- [ ] The unprovable negative clause is disclosed in the header as a scope limit, with the reason
- [ ] No `Admitted`, `admit`, or new `Axiom` (zero-axiom core per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both closure theorems
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Fun/Size.v
coqtop -R . Category -l Instance/Fun/Size.v
#   Print Assumptions fun_locally_small.
#   Print Assumptions components_injective.
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```

Reviewer checklist: "statement matches Riehl §1.7 (printed pp. 48, 51)"; confirm the proof genuinely uses the component injection rather than falling out of universe inference.

## Dependencies

- Depends on: #253 (size and foundations vocabulary — supplies the `Small`/`LocallySmall` predicates; see the Riehl §1.1 append there)
- Depends on: #276 (functor categories over discrete shapes and their size)

<!-- catalog: {"ids":["riehl:1.7:remark3","riehl:1.7:exi"],"deps":["#253","#276"]} -->


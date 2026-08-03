```yaml
title: "Seven Sketches 7.2.1: Epi-mono factorization — uniqueness in Sets, and the factorization carried by every topos"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.2.1:def-epi-mono-factorization, 7sketches:7.2.1:remark-topos-properties]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.2.1, printed pp. 225 and 227 (PDF pp. 237, 239). Items `7sketches:7.2.1:def-epi-mono-factorization` (the whole item) and `7sketches:7.2.1:remark-topos-properties` (clause (iv) only — the colimits clause of that remark is recorded on #405).

## Background

Every morphism of a topos factors as an epimorphism onto its image followed by a monomorphism, and that factorization is unique up to a unique isomorphism; abstractly this is the (epi, mono) orthogonal factorization system that a topos carries. See the nLab on [image](https://ncatlab.org/nlab/show/image) and on [orthogonal factorization system](https://ncatlab.org/nlab/show/orthogonal+factorization+system), and Wikipedia on [image (category theory)](https://en.wikipedia.org/wiki/Image_(category_theory)).

## Current state in the library

The existence half is present for `Sets` and nowhere else; both the uniqueness half and the topos-level statement are missing.

- `Instance/Sets/Image.v:143` gives `Sets_Image_Factorization`, with the epi leg proved epic at `:113` (`Sets_Image_epi_epic`), the mono leg proved monic at `:134` (`Sets_Image_mono_monic`), and the commuting triangle at `:103` by pointwise reflexivity. This is exactly the book's concrete factorization of a function through its image.
- `Structure/Factorization.v:125` defines `Record Factorization`, and `:216` states `factorization_unique` — but that lemma is stated over an `{O : OFS E M}` instance. The tree contains exactly two `OFS` instances: `Structure/Abelian.v:441` (`Abelian_OFS`, at (Epi, Mono) but only for abelian categories) and `Structure/Regular/Factorization.v:282` (`Regular_OFS`, at (RegularEpi, Mono)). There is **no `Regular` instance anywhere** — `Structure/Regular.v:66` declares `Class Regular` and `Structure/Regular/Factorization.v:125` only takes one as a `Context` hypothesis — so neither route reaches `Sets`. The book's clause "and this factorization is unique up to isomorphism" is therefore not instantiable for the very factorization the library builds.
- Nothing derives a factorization from a topos. `Structure/Topos.v:112` `Class ElementaryTopos` has exactly five fields (`topos_terminal`, `topos_cartesian`, `topos_pullbacks`, `topos_closed`, `topos_classifier`) and no factorization field; a tree-wide search for `ElementaryTopos` returns seven hits, of which the only definition-level ones are the class itself, `Pow`/`relations_iso` in the same file, and the sole witness `Instance/FinSet/Topos.v:38` (`FinSet_Topos`). No `OFS`, `Factorization` or `Regular` instance takes an `ElementaryTopos` as input.
- Phase-D sharpening, folded here because it changes what the issue must ask for: the remark's own corollary — "since Set is a topos, all five properties hold for Set" — is also unavailable, because there is **no `ElementaryTopos Sets` instance at all**. `Instance/Sets/Classifier.v` deliberately supplies cross-universe classifier *theorems* (`sets_char_pullback` at `:224`, `sets_char_unique` at `:283`, `sets_char_subobject` at `:341`) rather than an instance, and the header at `Structure/Topos.v:104-110` discloses the one-universe-up truth-value obstruction. `FinSet_Topos` is the only assembled topos in the tree. So the Sets leg of this issue must be stated for `Sets` directly, not obtained by specializing a topos theorem.

## Work to be done

Two independent legs, one PR.

1. **Uniqueness in Sets.** New `Instance/Sets/Factorization.v`: prove the orthogonality lifting for `Sets` — every epi is left-orthogonal to every mono (`Theory/Orthogonality.v`'s `⫫`) — and package it as `Sets_OFS : OFS EpiClass MonoClass` over `Theory/Morphisms/Classes.v`'s `MorphismClass` vocabulary. Then `Structure/Factorization.v:216`'s `factorization_unique` applies to `Sets_Image_Factorization` and delivers the book's "unique up to isomorphism" clause as a corollary; state that corollary explicitly (`sets_image_unique`), since the point of the exercise is the concrete statement, not the abstract one.
2. **Factorization in a topos.** New `Structure/Topos/Factorization.v`: from `ElementaryTopos C` derive an (epi, mono) factorization of every morphism, and package it as `Topos_OFS : OFS EpiClass MonoClass`. The library's own image machinery is the donor — `Structure/Regular/Factorization.v:132` `image_obj`, `:270` `regular_factorization`, `:282` `Regular_OFS` — so the cleanest route is to first prove `Topos_Regular : ElementaryTopos C → Regular C` (kernel pairs exist because a topos has pullbacks; every epi in a topos is regular; regular epis are stable under pullback) and then read off `Regular_OFS`. That also supplies the tree's **first** `Regular` instance, which several downstream obligations of this chapter want. Record the corollary `topos_epi_is_regular`.
3. Check both against the sole computable witness: instantiate at `Instance/FinSet/Topos.v:38`'s `FinSet_Topos` and confirm the factorization of a concrete finite map computes.

In-tree donors: `Instance/Sets/Image.v`, `Structure/Factorization.v`, `Theory/Orthogonality.v`, `Theory/Morphisms/Classes.v`, `Structure/Regular.v`, `Structure/Regular/Factorization.v`, `Structure/Topos.v`, `Theory/Morphisms/Stability.v` (pullback stability toolkit), `Instance/FinSet/Topos.v`.

## Definition of Done

- [ ] `Sets_OFS : OFS EpiClass MonoClass` proved, and the book's uniqueness clause stated as a named corollary about `Sets_Image_Factorization`.
- [ ] `Topos_Regular : ElementaryTopos C → Regular C` proved — the first `Regular` instance in the tree.
- [ ] `Topos_OFS`, giving every morphism of a topos an epi-mono factorization, with `topos_epi_is_regular` recorded.
- [ ] Both instantiated at `FinSet_Topos` with at least one computed example.
- [ ] Statement fidelity to Seven Sketches §7.2.1 (printed pp. 225, 227); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level (a topos-level factorization system is).

## Verification

```bash
coqc -R . Category Instance/Sets/Factorization.v
coqc -R . Category Structure/Topos/Factorization.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_OFS.
Print Assumptions Topos_OFS.
Print Assumptions Topos_Regular.
```
Reviewer: statement matches Seven Sketches §7.2.1 — in particular that the *uniqueness* clause is proved for the concrete `Sets` factorization, not only stated abstractly; and that clause (iv) of the topos-properties list is now a theorem about `ElementaryTopos`, not an axiom of the class.

## Dependencies

Depends on: #245 — the identification of epis in `Sets` with surjections is what makes `Sets_Image_epi_epic` usable as the book reads it.
Depends on: #405 — the sibling clause of the same topos-properties remark (colimits) is that issue's obligation; this issue deliberately does not restate it.

<!-- catalog: {"ids":["7sketches:7.2.1:def-epi-mono-factorization","7sketches:7.2.1:remark-topos-properties"],"deps":["#245","#405"]} -->

---8<---

```yaml
title: "Seven Sketches 7.2.1: A quantale whose tensor computes binary meets is a cartesian closed preorder"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:7.2.1:ex7.11]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.2.1, Exercise 7.11, printed p. 227 (PDF p. 239). Item `7sketches:7.2.1:ex7.11`.

## Background

A unital commutative quantale in which the unit is the top element and the tensor is the binary meet is exactly a Heyting prealgebra: the residuation of the quantale becomes the exponential, so the thin category is cartesian closed. See the nLab on [quantale](https://ncatlab.org/nlab/show/quantale) and on [cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

Nothing of the exercise is in force, and the verifier reproduced the decisive negative independently: a whole-tree search for "quantale" returns exactly **one** hit and it is a comment (`Construction/Enriched.v:78`, "preorder- and quantale-enriched categories"). There is no `Quantale` class, record or definition, no residuation, no join-semilattice or complete-lattice structure, and no "closed preorder" or "monoidal preorder" notion; a search for `Heyting` returns seven hits, all header prose.

What does exist is one *example* of the conclusion, with no hypothesis attached to it: `Instance/Props.v:39` builds the thin category of propositions under implication, with `Props_Cartesian` at `:69` (`product_obj := and`), `Props_Cocartesian` at `:80` and `Props_Closed` at `:94` (`exponent_obj := Basics.impl`, with `exp_iso` as the currying bijection) — that is, a cartesian closed preorder, but never presented as arising from a quantale. `Instance/Proset.v:33`'s `Proset` turns any `PreOrder` into a thin category and carries no cartesian or closed structure. Note also that the in-tree `ClosedMonoidal` class already *bundles* `CartesianMonoidal` (`Structure/Monoidal/Closed.v:47`), and only the direction `Closed → ClosedMonoidal` is proved (`Structure/Monoidal/Internal/Product.v:442`), so the exercise's converse question cannot be routed through it either.

## Work to be done

Over the quantale class that Seven Sketches §2.5 schedules (#799), state and prove the exercise.

1. New `Structure/Quantale/Cartesian.v`. Define the exercise's hypothesis pack on a unital commutative quantale `V`: `v ≤ I` for all `v`; `v ⊗ w ≤ v` and `v ⊗ w ≤ w`; and `x ≤ v → x ≤ w → x ≤ v ⊗ w`. Prove from it that `I` is the top element, that `⊗` is the binary meet, and hence that the thin category `Proset V` is `Terminal` and `Cartesian`.
2. Prove `Closed` for that thin category, taking the exponential to be the quantale's residuation (hom-element) — the currying bijection is degenerate in a thin category, so the content is the two inequalities. Conclude `quantale_meet_cartesian_closed`.
3. Part (2) of the exercise — does every cartesian closed preorder arise this way? — is a genuine mathematical question and its honest answer is a *characterization*, not a yes/no: a cartesian closed preorder gives a quantale under this recipe exactly when it has all joins (a quantale is required to be a sup-lattice with a join-distributing tensor). Formalize that as a two-way statement: (a) the construction above from a quantale satisfying the three conditions; (b) from a cartesian closed preorder *with all joins*, the quantale `(V, ≤, ⊤, ∧)` and a proof that it satisfies the three conditions. Then exhibit `Instance/Props.v`'s `Props` as a worked instance of (b), closing the loop with the example that already exists in-tree.

In-tree donors: `Instance/Proset.v` (`Proset`), `Instance/Props.v` (`Props_Cartesian`, `Props_Cocartesian`, `Props_Closed` as the worked model), `Structure/Cartesian.v`, `Structure/Cartesian/Closed.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] The exercise's three conditions are a named hypothesis pack over the quantale class, and `I = ⊤`, `⊗ = ∧` are proved from them.
- [ ] `quantale_meet_cartesian_closed` — the thin category of such a quantale is `Terminal` + `Cartesian` + `Closed`.
- [ ] Part (2) answered as a characterization: the converse construction from a cartesian closed preorder with all joins, plus the explicit statement that joins are what the converse needs.
- [ ] `Props` exhibited as an instance of the converse.
- [ ] Statement fidelity to Seven Sketches §7.2.1 (printed p. 227); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Structure/Quantale/Cartesian.v
make && make todo
```
```coq
Print Assumptions quantale_meet_cartesian_closed.
```
Reviewer: statement matches Seven Sketches Exercise 7.11 (printed p. 227), including that part (2) is answered with the joins caveat rather than a bare "yes".

## Dependencies

Depends on: #799 — the unital commutative quantale class and its join vocabulary.
Depends on: #797 — symmetric monoidal closed preorders, the hom-element that becomes the exponential here.
Depends on: #801 — closedness of a monoidal preorder as distributivity of the tensor over joins, which is exactly the hinge of part (2).

<!-- catalog: {"ids":["7sketches:7.2.1:ex7.11"],"deps":["#799","#797","#801"]} -->

---8<---

```yaml
title: "Seven Sketches 7.2.3: The internal connectives on a subobject classifier — AND, OR, NOT and implication"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.2.3:construction-and, 7sketches:7.2.3:construction-or, 7sketches:7.2.3:ex7.19, 7sketches:7.2.3:ex7.20]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.2.3, printed pp. 230–231 (PDF pp. 242–243). Items `7sketches:7.2.3:construction-and`, `7sketches:7.2.3:construction-or`, `7sketches:7.2.3:ex7.19`, `7sketches:7.2.3:ex7.20`.

## Background

In a topos the logical connectives are *morphisms* `Ω × Ω ⟶ Ω`, each defined as the characteristic map of an explicitly named subobject: conjunction classifies the point `(true, true)`, disjunction classifies the union of `{true} × Ω` and `Ω × {true}`, negation classifies the point `false`, and implication classifies the internal order relation. See the nLab on [subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier) and on [internal logic](https://ncatlab.org/nlab/show/internal+logic).

## Current state in the library

No connective on a classifier exists anywhere in the tree — this is the chapter's largest single hole, and everything downstream in §7.4 (the Heyting structure on predicates, the modalities, the internal language) is blocked on it.

- There is no morphism of type `Ω × Ω ~> Ω` (nor `4 ~{FinSet}~> 2`) in the tree; the point `⟨truth, truth⟩ : 1 ~> Ω × Ω` is never formed and no lemma identifies any conjunction with `char` of it. `Instance/FinSet/Topos.v:69` defines `point_true` (with `point_true_monic`) and **no point `false`** at all, so even the negation exercise's subobject cannot be named.
- What is in-tree is meets and joins in *external* truth-value posets, not in a topos: `Instance/Props.v:69` `Props_Cartesian` (`product_obj := and`), `:80` `Props_Cocartesian` (`product_obj := or` — the in-file comment explains that `Cocartesian` is `Cartesian` read in `Props^op`, so the field name is not a transcription error), `:94` `Props_Closed` (`exponent_obj := Basics.impl`); and `Instance/Two/Monoidal.v:80` `Two_Cartesian`, whose `two_meet` at `:37` is literally the AND truth table on the two-element object. Phase-D flagged an asymmetry worth carrying into the work: `Instance/Two/Monoidal.v` supplies `two_meet` but **no `two_join`**, so the disjunction table is not in-tree the way the conjunction table is.
- Part (1) of the negation exercise — "what *sort* of thing does NOT classify?" — genuinely *is* answered in-tree, and in a stronger form than the book asks: `Structure/SubobjectClassifier.v:159` `classifier_char_roundtrip` and `:174` `classifier_pullback_roundtrip`, packaged as `:187` `classifier_classifies : SubObj x ≅ (x ~> Ω)` in `Sets`, say that every `h : x ~> Ω` is the characteristic map of exactly one subobject. Part (2) — that NOT is `char` of the point `false` — has no statement.
- The implication exercise needs two further things that are missing: the equational characterization of the order on truth values, `P ≤ Q ⟺ P ≈ P ∧ Q`, is nowhere stated (not for `Props`, not for `_2`, not generally); and the subobject of `Ω × Ω` that implication classifies — the internal order relation — is never constructed, consistent with the library having no meets or joins of subobjects at all. `Theory/Subobject.v` carries only `sub_le` (`:59`), `sub_le_refl`/`trans`/`unique` (`:62`/`:67`/`:78`) and `sub_equiv_iff_mutual` (`:93`); the nearest trace of intersection is the prose remark at `Structure/Pullback.v:92-95`, with no operation defined from it.

## Work to be done

New `Structure/Topos/Logic.v`, over `Structure/Topos.v`'s `ElementaryTopos`.

1. **Conjunction.** Build `truth_pair : 1 ~> Ω × Ω` as `⟨truth, truth⟩`, prove it `Monic` (a map out of a terminal object into any object is monic as soon as the target has a global element separating it; here the product projections plus `truth_monic` suffice), and define `omega_and := char truth_pair _`. Prove the classifying property in the form the book uses: a generalized element of `Ω × Ω` is sent to `truth` exactly when both components are.
2. **Disjunction.** Build the subobject `{true} × Ω ∪ Ω × {true}` of `Ω × Ω` as the union of two subobjects and define `omega_or := char` of it. This is where the union of subobjects is needed; that operation is #445's obligation and this issue consumes it rather than re-deriving it. Record the book's own framing — the subobject is a colimit of limits built from `1`, `truth` and products — so the construction transports to any topos verbatim.
3. **Negation.** Build `false : 1 ~> Ω` the way the book does — as `char` of the subobject `0 ↣ 1`, i.e. of `zero : 0 ~> 1` (`Structure/Initial.v:109`), which is monic in a topos — and then define `omega_not := char false _` for the point `false : 1 ↣ Ω`, proving that point monic. Answer part (1) of Exercise 7.19 formally by citing `classifier_classifies`, and part (2) by the definition. Note that `false` is entirely new: `Instance/FinSet/Topos.v:69` defines `point_true` and nothing dual to it.
4. **Implication.** Prove the order lemma `le_iff_meet : P ≤ Q ↔ P ≈ P ∧ Q` in a cartesian thin setting, then define `omega_impl` as the characteristic map of the equalizer of `π₁` and `omega_and` on `Ω × Ω` (that equalizer *is* the internal order relation, which is the exercise's part (4) answer), and prove `omega_impl` is right adjoint to `omega_and` in the internal order.
5. **Truth tables.** New `Instance/FinSet/Logic.v`: instantiate all four at `FinSet_Topos` where `Ω = 2`, and check each truth table by `eq_refl` `Example`s, in the style already used at `Instance/FinSet/Topos.v:77-91` (`FinSet_char_at_true`, `FinSet_char_at_false`, `FinSet_Pow_membership`). Supply the missing `two_join` on `Instance/Two/Monoidal.v` while here, so the external disjunction table exists alongside `two_meet`.

In-tree donors: `Structure/SubobjectClassifier.v` (`char`, `char_pullback`, `char_unique`, `truth_subobject` at `:72`, `classifier_classifies`), `Structure/Topos.v`, `Structure/Cartesian.v`, `Structure/Initial.v`, `Structure/Equalizer/Fork.v`, `Instance/FinSet/Classifier.v`, `Instance/FinSet/Topos.v`, `Instance/Two/Monoidal.v`, `Instance/Props.v` (as the external sanity model).

## Definition of Done

- [ ] `omega_and`, `omega_or`, `omega_not`, `omega_impl` defined in an arbitrary `ElementaryTopos`, each as the characteristic map of the subobject the book names.
- [ ] `truth_pair` and `point_false` constructed with their `Monic` proofs (`point_false` is entirely new — the tree has only `point_true`).
- [ ] `le_iff_meet` proved, answering the defining equation of Exercise 7.20.
- [ ] The internal order relation on `Ω × Ω` constructed, and identified as the subobject implication classifies (Exercise 7.20 part 4).
- [ ] Exercise 7.19 part (1) answered by an explicit appeal to `classifier_classifies`, part (2) by the definition of `omega_not`.
- [ ] All four truth tables checked by `eq_refl` at `FinSet_Topos`.
- [ ] `two_join` added to `Instance/Two/Monoidal.v`, closing the asymmetry with the existing `two_meet`.
- [ ] Statement fidelity to Seven Sketches §7.2.3 (printed pp. 230–231); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the internal logic of a topos is flagship-level.

## Verification

```bash
coqc -R . Category Structure/Topos/Logic.v
coqc -R . Category Instance/FinSet/Logic.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions omega_and.
Print Assumptions omega_or.
Print Assumptions omega_not.
Print Assumptions omega_impl.
```
Reviewer: statement matches Seven Sketches §7.2.3 (printed pp. 230–231) — in particular that each connective is *defined* as a characteristic map, not postulated with its truth table, and that the disjunction is built from the union of two subobjects so the recipe transports to an arbitrary topos.

## Dependencies

Depends on: #402 — the classifier of `Sets` with `Ω = {true, false}` and the classification rule the truth tables are read against.
Depends on: #445 — intersections and unions of subobjects; the disjunction construction consumes the union operation, which that issue owns.

<!-- catalog: {"ids":["7sketches:7.2.3:construction-and","7sketches:7.2.3:construction-or","7sketches:7.2.3:ex7.19","7sketches:7.2.3:ex7.20"],"deps":["#402","#445"]} -->

---8<---

```yaml
title: "Seven Sketches 7.2.2/7.2.3: Worked characteristic maps — the identity and empty subobjects, and boolean combinations"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:7.2.2:ex7.16, 7sketches:7.2.2:ex7.17, 7sketches:7.2.3:ex7.21]
deps_item_ids: [7sketches:7.2.3:construction-and]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §§7.2.2–7.2.3, Exercises 7.16, 7.17 and 7.21, printed pp. 229 and 231 (PDF pp. 241–243). Items `7sketches:7.2.2:ex7.16`, `7sketches:7.2.2:ex7.17`, `7sketches:7.2.3:ex7.21`.

## Background

These three exercises are the computational drill on the classification rule: evaluate the characteristic map of a concrete subset at concrete points, identify the characteristic maps of the two extreme subobjects (everything and nothing), and combine characteristic maps with the connectives. See the nLab on [subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier) and Wikipedia on [indicator function](https://en.wikipedia.org/wiki/Indicator_function).

## Current state in the library

The general rule is in-tree; not one instance of it is computed, and the two extreme cases have no statement.

- `Instance/FinSet/Classifier.v:353` `FinSet_Classifier` gives `Ω := 2%nat`, `truth := fun _ => fin_true` and `char := ... fin_of_bool (fin_existsb (fun a => fin_eqb (m a) b))` — literally the book's image-membership rule — with both obligations closed by `Qed` (`char_pullback` at `:361`, `char_unique` at `:392`) and `finset_monic_iff_injective` at `:335` giving monos = injections. The only *evaluated* characteristic values in the whole tree are `Instance/FinSet/Topos.v:77-81` (`FinSet_char_at_true`, `FinSet_char_at_false`), both for the single point `truth : 1 ~> 2`.
- The two extreme cases of Exercise 7.17 have no counterpart: a search for `char_id`, `char_identity`, `char_top`, `char_bot` returns nothing, and `Theory/Subobject.v` has no top or bottom element of `SubObj` (its whole API is `SubObj`, `sub_le`, `sub_le_refl`/`trans`/`unique`, `sub_equiv_iff_mutual`). `Instance/FinSet.v:223` `FinSet_Initial` exists but no lemma computes its characteristic morphism.
- Exercise 7.21's arithmetic subsets of ℕ (evens, primes, ≥ 10) are not defined anywhere, and boolean combinations of characteristic maps cannot be formed at all: a search for `sub_join`, `sub_meet`, `sub_union`, `sub_inter` returns no definitions, and no connective exists on any classifier's truth values.
- **Phase-D correction, and it overrides the Phase-C reading**: the coverage record originally classified Exercise 7.16 PARTIAL by citing the general `char` rule. The verifier overturned that to ABSENT, on the ground that the general rule belongs to the classifier construction of §7.2.2 (recorded on #402) and re-citing it once per exercise double-counts a single gap. It also established the hard blocker for Exercise 7.16 specifically: **the integers do not exist anywhere in the library** (`ZArith`/`BinInt` are never imported), so the mono ℕ ↣ ℤ cannot be written at all. Any implementation must either add the integers or substitute a finite model.

## Work to be done

New `Instance/FinSet/Classifier/Examples.v` (or an extension of `Instance/FinSet/Topos.v`, which already holds the two existing `eq_refl` examples).

1. **The extreme subobjects (Exercise 7.17).** In an arbitrary `ElementaryTopos`, prove `char_id : char id[x] _ ≈ truth ∘ one` (the identity mono is classified by the constant-true predicate) and `char_initial : char (zero : 0 ~> x) _ ≈ false ∘ one`, where `zero` is `Structure/Initial.v:109`'s initial morphism (the unique map out of an initial object is classified by the constant-false predicate). These are the general forms of the exercise's two parts and are reusable well beyond it; state them generically, then check them by `eq_refl` at `FinSet_Topos`.
2. **Point evaluations (Exercise 7.16).** Rather than adding `ZArith` for a single exercise, state the exercise's content in the finite model the library already computes in: for an explicit injection `m : Fin.t k ↪ Fin.t n`, prove `Example`s by `eq_refl` computing `char m` at a point *in* the image and at a point *outside* it. Record in the file header that the book's ℕ ↣ ℤ instance is not representable in-tree because the integers are absent, and that the finite instance is the faithful substitute for the same rule. If the implementer prefers, adding `ZArith` and a `Sets`-level inclusion ℕ ↣ ℤ is acceptable, but then the `Sets` classifier obstruction applies (see #402) and the computation would have to be done in the cross-universe setting of `Instance/Sets/Classifier.v`.
3. **Boolean combinations (Exercise 7.21).** With the connectives of this chapter's §7.2.3 issue available, define three decidable subsets of a finite carrier standing in for the book's evens/primes/≥10, compute their characteristic maps, form `(char E ∧ char P) ∨ char T` using `omega_and`/`omega_or`, and identify the three least elements of the subobject it classifies — by `eq_refl` where the carrier is finite.

In-tree donors: `Instance/FinSet/Classifier.v` (`FinSet_Classifier`, `fin_existsb_sound`/`complete` at `:82`/`:94`, `fin_select_sat` at `:188`, `fin_select_rank` at `:201`), `Instance/FinSet/Topos.v` (the `eq_refl` `Example` style), `Instance/FinSet.v` (`FinSet_Initial` at `:223`), `Structure/SubobjectClassifier.v`, `Structure/Topos.v`.

## Definition of Done

- [ ] `char_id` and `char_initial` proved generically for an `ElementaryTopos`, and checked by `eq_refl` at `FinSet_Topos` — the first named results about the two extreme subobjects in the tree.
- [ ] `Example`s computing `char m` at an in-image and an out-of-image point, by `eq_refl`.
- [ ] The boolean-combination computation of Exercise 7.21 carried out with the connectives, with the classified subobject identified.
- [ ] The file header records why the book's ℕ ↣ ℤ instance is replaced by a finite one (the integers are not in the tree), so the substitution is disclosed rather than silent.
- [ ] Statement fidelity to Seven Sketches Exercises 7.16, 7.17, 7.21 (printed pp. 229, 231); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/FinSet/Classifier/Examples.v
make && make todo
```
```coq
Print Assumptions char_id.
Print Assumptions char_initial.
```
Reviewer: statement matches Seven Sketches Exercises 7.16/7.17/7.21, and the header discloses the finite substitution for the ℕ ↣ ℤ instance.

## Dependencies

Depends on: #402 — the classifier of `Sets` and the classification rule these exercises drill.
Depends on: `7sketches:7.2.3:construction-and` — Exercise 7.21 combines characteristic maps with AND and OR, which that issue defines.

<!-- catalog: {"ids":["7sketches:7.2.2:ex7.16","7sketches:7.2.2:ex7.17","7sketches:7.2.3:ex7.21"],"deps":["#402","7sketches:7.2.3:construction-and"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.2: The metric topology — ε-balls generate a topology on any metric space"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.2:example7.26, 7sketches:7.3.2:ex7.27]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.2, Example 7.26 and Exercise 7.27, printed pp. 234–235 (PDF pp. 246–247). Items `7sketches:7.3.2:example7.26`, `7sketches:7.3.2:ex7.27`.

## Background

Declaring a subset open when every one of its points has an ε-ball inside it turns any metric space into a topological space; this is the standard bridge between §2.3's metric spaces and §7.3.2's topologies. See the nLab on [metric space](https://ncatlab.org/nlab/show/metric+space) and Wikipedia on [metric space](https://en.wikipedia.org/wiki/Metric_space).

## Current state in the library

Neither end of the bridge exists.

- Metric spaces appear only as prose. Every hit for "metric space" in the tree is a background citation of Lawvere's *Metric spaces, generalized logic and closed categories* (`Theory/Profunctor.v:100`, `Instance/Poset.v:75-77`, `Instance/Two.v:71`, `Construction/Enriched.v`); there is no `MetricSpace` class, and the three "triangle inequality" hits are all prose explaining what `ecompose` *would* be under a `[0,∞]` enrichment that is never built. The only enrichment bases instantiated in-tree are `Sets` (`Construction/Enriched.v:163`) and the walking arrow `_2` (`Construction/Enriched/Two.v`).
- Topologies do not exist either: searches for "open set", "topology on", `OpenSets`/`Opens`/`open_sets` all return zero, and every "continuous" hit is the limit-preservation sense (`Adjunction/Continuity.v`, `Structure/Limit/Preservation.v`).
- **The reals are never imported.** A tree-wide search for `Coq.Reals`, `Rdefinitions`, `R_scope` and `QArith` returns zero hits; `nat` (via `Instance/FinSet.v` and `Instance/Omega.v`) is the only numeric carrier in the library. So neither `d(x₁,x₂) = |x₁ − x₂|` on ℝ nor Euclidean distance on ℝ² has a carrier today, and the implementer must decide up front whether to import `Coq.Reals` or to work over an abstract ordered field / a `[0,∞]` value object.

## Work to be done

New `Instance/Top/Metric.v`, over the `Top` construction that #259 schedules.

1. Define a metric space in the form the chapter uses, and connect it to the Lawvere/`Cost`-enriched presentation that Seven Sketches §2.3 gives (#787) rather than introducing a second incompatible notion — the two must be the same object, or the chapter's cross-references break.
2. Define the ε-ball `B(p; ε) := {p' | d(p,p') < ε}` and the metric topology: `U` is open iff for every `p ∈ U` there is `ε > 0` with `B(p; ε) ⊆ U`. Prove the three topology axioms (the whole space is open; closed under binary intersection; closed under arbitrary unions, the empty family giving that ∅ is open), i.e. that this really is a topology in the sense of §7.3.2.
3. Instantiate on the line (Exercise 7.27 parts 1–2): the one-dimensional ball `B(x, ε)`, and openness of an arbitrary subset of the carrier. Then parts (3) and (4): exhibit a concrete finite cover `U = U₁ ∪ U₂` of an open set, and an open set with an infinite indexed covering family — these are the chapter's first concrete *covers*, and the sheaf development of §7.3.3 consumes exactly that notion.
4. Record the plane instance of Example 7.26 (Euclidean distance) if the reals are imported; otherwise state it over an abstract metric and note the specialization.

Numeric substrate: the file header must state which choice was made. Importing `Coq.Reals` brings stdlib axioms with it, which is permitted in the `Instance/` layer per docs/AXIOMS.md but must be enumerated there.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Construction/Enriched.v`, `Construction/Enriched/Two.v`, and the `Top`/`Open(X)` constructions of #259 and #268.

## Definition of Done

- [ ] A metric-space notion compatible with the `Cost`-enriched presentation of #787 (same object, not a rival definition).
- [ ] `ball` defined and the metric topology proved to satisfy all three topology axioms, including the empty-union case giving ∅ open.
- [ ] The one-dimensional instance with its openness criterion (Exercise 7.27 parts 1–2).
- [ ] A concrete two-element cover and a concrete infinite covering family (Exercise 7.27 parts 3–4).
- [ ] The numeric substrate choice disclosed in the file header, and any stdlib axioms it introduces enumerated in docs/AXIOMS.md.
- [ ] Statement fidelity to Seven Sketches §7.3.2 (printed pp. 234–235); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond stdlib axioms recorded in docs/AXIOMS.md for the `Instance/` layer.
- [ ] `Print Assumptions` closed (or explicitly enumerated) for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Top/Metric.v
make && make todo
```
```coq
Print Assumptions metric_topology.
```
Reviewer: statement matches Seven Sketches Example 7.26 and Exercise 7.27 (printed pp. 234–235); the metric-space notion agrees with the one used in Chapter 2.

## Dependencies

Depends on: #259 — the category `Top` and the definition of a topological space.
Depends on: #787 — Lawvere metric spaces as `Cost`-categories; this issue must reuse that notion rather than introduce a second one.

<!-- catalog: {"ids":["7sketches:7.3.2:example7.26","7sketches:7.3.2:ex7.27"],"deps":["#259","#787"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.2/7.3.3: The Sierpiński space — the four topologies on a two-element set, its opens, and its sheaves"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.2:example7.30, 7sketches:7.3.2:ex7.31, 7sketches:7.3.3:ex7.49]
deps_item_ids: [7sketches:7.3.3:def7.35]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.2 Example 7.30 and Exercise 7.31 (printed pp. 235–236; PDF pp. 247–248), and §7.3.3 Exercise 7.49 (printed p. 242; PDF p. 254). Items `7sketches:7.3.2:example7.30`, `7sketches:7.3.2:ex7.31`, `7sketches:7.3.3:ex7.49`.

## Background

There are exactly four topologies on a two-element set; the two non-extreme ones are isomorphic, and either is the Sierpiński space, the smallest space that is not discrete or indiscrete. Its poset of opens is a three-element chain, and a sheaf on it is the same thing as a function. See the nLab on [Sierpiński space](https://ncatlab.org/nlab/show/Sierpinski+space) and Wikipedia on [Sierpiński space](https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space).

## Current state in the library

The name appears nowhere: a whole-tree search for "Sierpinski" across all `.v` files returns **zero** files, and so does "homeomorph", so even "the two spaces are isomorphic" has no counterpart. There is no topology notion at all (see #259), hence no lattice-of-topologies development in which "exactly four" could be stated, and no Hasse-diagram construction from an order (`Instance/Shapes.v` and `Instance/Roof.v` are hand-built finite shape categories, not builders). The only code-level occurrence of "cover" is `Theory/Sheaf.v`'s `covering_family`/`coverage` fields, whose class has no instance in the tree, so no concrete list of covers exists for any object.

Phase-D checked and rejected the one tempting near-miss, and the rejection should be carried into the work: `Instance/Two.v`'s `_2` (the walking arrow, with `Two_Cartesian`/`Two_Terminal`/`Two_Monoidal` in `Instance/Two/Monoidal.v`) is the *specialization preorder* of the Sierpiński space, not its poset of opens — the poset of opens is the **three**-element chain ∅ ⊂ {1} ⊂ X, which is not built anywhere either.

## Work to be done

New `Instance/Top/Sierpinski.v`.

1. Enumerate the topologies on a two-element carrier and prove there are exactly four: the two extremes (which #456 constructs as the values of the discrete and indiscrete functors) and the two singleton-opens topologies `Op₁ = {∅, {1}, X}`, `Op₂ = {∅, {2}, X}`. Decidability makes the enumeration a finite check; state it as a genuine classification (a bijection with a four-element type, or an exhaustive case analysis), not as four separate existence facts.
2. Prove `Op₁ ≅ Op₂` in `Top` (the swap of the carrier is a homeomorphism), justifying "either one is called the Sierpiński space".
3. Build the poset of opens of the Sierpiński space explicitly as the three-element chain, and derive its thin category through `Instance/Proset.v:33`'s `Proset` — this is the Hasse diagram of Exercise 7.31 part (1) in the form the library can hold. Enumerate all its covers (part (2)); with three opens this is a short finite list, and it is the chapter's first fully explicit coverage.
4. Exercise 7.49: with the sheaf definition of this chapter's §7.3.3 issue in hand, describe presheaves on the three-element chain (part 2), unfold the sheaf condition for the one non-trivial cover (part 3), and prove the payoff (part 4) — the category of sheaves on the Sierpiński space is equivalent to the arrow category of `Sets`, so "a sheaf on it is a function". State that as an `≅[Cat]`/equivalence, and connect it to `Construction/Arrow.v:110`'s `Arrow := Id[C] |> Id[C]`, whose own header at `:105-108` explicitly records that no comparison with a functor category over the walking arrow is developed in-tree — this issue closes that gap from the sheaf side.

In-tree donors: `Instance/Two.v`, `Instance/Two/Monoidal.v`, `Instance/Two/Discrete.v`, `Instance/Proset.v`, `Construction/Arrow.v`, and the `Top`/`Open(X)` constructions of #259 and #268.

## Definition of Done

- [ ] The classification "exactly four topologies on a two-element set", proved as an exhaustive statement rather than four existence facts.
- [ ] `Op₁ ≅ Op₂` in `Top`.
- [ ] The Sierpiński space's poset of opens built as the three-element chain (explicitly *not* `_2`, which is its specialization preorder), with its thin category through `Proset`.
- [ ] All covers of the Sierpiński space enumerated.
- [ ] Sheaves on the Sierpiński space shown equivalent to functions, i.e. to the arrow category of `Sets`, closing the comparison that `Construction/Arrow.v:105-108` records as missing.
- [ ] Statement fidelity to Seven Sketches Example 7.30, Exercises 7.31 and 7.49 (printed pp. 235–236, 242); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Top/Sierpinski.v
make && make todo
```
```coq
Print Assumptions sierpinski_topologies_four.
Print Assumptions sheaves_sierpinski_arrow.
```
Reviewer: statement matches Seven Sketches Example 7.30, Exercise 7.31 and Exercise 7.49; in particular the poset of opens is the three-element chain, not the walking arrow.

## Dependencies

Depends on: #259 — the category `Top`.
Depends on: #268 — `Open(X)` as a category.
Depends on: #456 — the discrete and indiscrete topologies, which are two of the four.
Depends on: `7sketches:7.3.3:def7.35` — the sheaf condition, needed for Exercise 7.49.

<!-- catalog: {"ids":["7sketches:7.3.2:example7.30","7sketches:7.3.2:ex7.31","7sketches:7.3.3:ex7.49"],"deps":["#259","#268","#456","7sketches:7.3.3:def7.35"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.2: The quantale of open sets, and categories enriched in it"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.2:remark7.33, 7sketches:7.3.2:ex7.34]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.2, Remark 7.33 and Exercise 7.34, printed p. 236 (PDF p. 248). Items `7sketches:7.3.2:remark7.33`, `7sketches:7.3.2:ex7.34`.

## Background

The opens of a topological space, ordered by inclusion with the whole space as unit and intersection as tensor, form a unital commutative quantale; enriching in that quantale gives a set in which "x ≤ y" is not a truth value but the open region of the space on which the comparison holds. See the nLab on [quantale](https://ncatlab.org/nlab/show/quantale), on [locale](https://ncatlab.org/nlab/show/locale) (the same structure under its other name), and on [enriched category](https://ncatlab.org/nlab/show/enriched+category).

## Current state in the library

The general enrichment machinery is real and proved; the base this exercise needs cannot be formed.

- Present: `Construction/Enriched.v:111` `Class Enriched (K : Category)` with its `eobj`/`ehom`/`eid`/`ecompose` fields and unit/associativity laws; `Construction/Enriched.v:163` `Theorem Category_is_Enriched_over_Set : Enriched Sets ↔ Category`; and the exercise's recalled premise proved both ways for the boolean base — `Construction/Enriched/Two.v:165` `Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder` (closed with `Defined.`, so both legs are transparent) and `:183` `EnrichedFunctor_Two_monotone`. Phase D flagged one honest caveat that the issue must not paper over: `TwoPreorder` (`Construction/Enriched/Two.v:60`) carries a `tpre_dec` decidability field, so the in-tree correspondence is with **decidable** preorders — weaker than the book's unqualified "Bool-categories are preorders".
- Absent: there is no quantale in the tree (one comment hit only, `Construction/Enriched.v:78`), no locale or frame, no Heyting-algebra class (seven hits, all prose), no complete lattice, no residuation and no order-theoretic joins; and there is no topological space, so `(Op, ⊆, X, ∩)` has neither carrier nor structure. `_2` with `Two_Monoidal` (`Instance/Two/Monoidal.v:105`) is a cartesian monoidal thin category and requires no joins, so it is not a quantale in the sense this exercise needs.
- The second base the exercise recalls — `Cost`-categories as Lawvere metric spaces — is prose-only: no `[0,∞]` monoidal base is instantiated anywhere.

## Work to be done

New `Instance/Top/Opens/Quantale.v` and `Construction/Enriched/Opens.v`.

1. Build the quantale of opens: over the poset of opens of a space (owned by #268), give arbitrary joins (unions — the topology axiom supplies them), the unit `X`, the tensor `∩`, and prove the quantale laws including distributivity of `∩` over arbitrary unions. This is a *frame*, and it is worth naming it as such, since the same object is the substrate for the Heyting structure of §7.4.2 and for the subobject classifier of `Shv(X)` in §7.4.1.
2. Instantiate the enrichment class at that base, and give the exercise's answer as a characterization theorem, not as prose: an `Op`-enriched category on a carrier `A` is exactly a family of opens `d(a,b) ⊆ X` with `X ⊆ d(a,a)` and `d(a,b) ∩ d(b,c) ⊆ d(a,c)` — that is, a set with an *open region of validity* for each comparison. Prove it in both directions, in the style of `Enriched_Two_preorder`.
3. Record the two recalled specializations honestly: the boolean case is `Enriched_Two_preorder` (with the decidability caveat above stated in the header), and the `Cost` case remains unavailable until a `[0,∞]` base is built — note that as a scope boundary rather than silently omitting it.

In-tree donors: `Construction/Enriched.v`, `Construction/Enriched/Two.v`, `Instance/Two/Monoidal.v`, `Instance/Proset.v`, and the quantale class of #799 plus the `Open(X)` category of #268.

## Definition of Done

- [ ] The opens of a space assembled as a unital commutative quantale (equivalently a frame), with distributivity over arbitrary joins proved.
- [ ] `@Enriched` instantiated at that base.
- [ ] The characterization of `Op`-enriched categories proved in both directions (family of opens with the reflexivity and composition inclusions).
- [ ] The header states the `tpre_dec` decidability caveat inherited from `Enriched_Two_preorder`, and records that the `Cost` specialization is out of scope until a `[0,∞]` base exists.
- [ ] Statement fidelity to Seven Sketches Remark 7.33 and Exercise 7.34 (printed p. 236); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — a frame/quantale of opens is a substrate several later results consume.

## Verification

```bash
coqc -R . Category Instance/Top/Opens/Quantale.v
coqc -R . Category Construction/Enriched/Opens.v
make && make todo
```
```coq
Print Assumptions opens_quantale.
Print Assumptions Enriched_Opens_characterization.
```
Reviewer: statement matches Seven Sketches Remark 7.33 and Exercise 7.34 (printed p. 236); the enriched characterization is proved in both directions, as the Bool case already is.

## Dependencies

Depends on: #259 — the category `Top` and the notion of a topological space.
Depends on: #268 — `Open(X)` as a category.
Depends on: #799 — the unital commutative quantale class.
Depends on: #785 — preorders as Bool-categories, the recalled premise of the exercise.
Depends on: #787 — Lawvere metric spaces as Cost-categories, the second recalled premise.

<!-- catalog: {"ids":["7sketches:7.3.2:remark7.33","7sketches:7.3.2:ex7.34"],"deps":["#259","#268","#799","#785","#787"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.3: Sheaves on a topological space — matching families, unique gluing, and Shv(X, Op)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.3:def7.35, 7sketches:7.3.3:example7.36]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.3, Definition 7.35 and Example 7.36, printed p. 237 (PDF p. 249). Items `7sketches:7.3.3:def7.35`, `7sketches:7.3.3:example7.36`.

## Background

A presheaf on the opens of a space is a sheaf when every matching family of local sections over an open cover has a unique gluing; the sheaves form a full subcategory `Shv(X, Op)` of presheaves. See the nLab on [sheaf](https://ncatlab.org/nlab/show/sheaf) and Wikipedia on [sheaf (mathematics)](https://en.wikipedia.org/wiki/Sheaf_(mathematics)).

## Current state in the library

There is a `Sheaf` predicate and a category `Sheaves`, but neither is the book's, and Phase-D verification established that the in-tree predicate is **provably degenerate** — this is the single most important finding of the chapter and it changes what has to be built.

- Present: `Theory/Sheaf.v:159` `Class Site (C : Category)` (with `covering_family u := sigT (Vector.t (exists ui, ui ~> u))` at `:162`, `coverage` at `:167`, `coverage_condition` at `:170`, `ForallT_nil` at `:137`); `Theory/Sheaf.v:192` `Class Sheaf` with its single `restriction` field at `:193`; and `Theory/Sheaf/Category.v:81` `Sheaves` as a full subcategory of presheaves, with `Sheaves_Full` (`:94`), `Sheaves_Faithful` (`:103`) and repleteness `sheaf_iso_closed` (`:119`). Both files are registered in `_CoqProject` (lines 473–474).
- Gap (a): **no topological spaces.** There is no `Top`, no topology, no poset of opens anywhere in the tree, so the book's site `Op(X)` is never instantiated and `Shv(X, Op)` as such does not exist. In fact `Class Site` has **no instance at all** in the tree — a search for `Site` returns the class, one `Context` hypothesis in `Theory/Sheaf/Category.v:68`, and prose.
- Gap (b): **the sheaf predicate is not the book's.** Gluing is stated per-leg rather than over a simultaneous matching family, and the compatibility antecedent is self-contradictory except on subsingleton fibres, so the predicate is vacuous at any covered object carrying two inequivalent sections. `Theory/Sheaf/Category.v:28-47` is the library's own scope note disclosing this; re-founding the class on honest matching families is already a named in-tree deferral.
- Gap (c): a `Site` picks **one** covering family per object, not a collection of them, so "satisfies the sheaf condition for *every* open cover" is not even statable. The vector-indexed covering family also admits the empty vector.
- **LIBRARY DEFECT, found in Phase D and not disclosed anywhere in-tree.** The `coverage_condition` field of `Class Site` (`Theory/Sheaf.v:170-178`) is *vacuous*: the witness `hs` is existentially quantified over arbitrary vectors of morphisms into `v`, and `covering_family v` carries no covering requirement, so `hs := (0; nil)` discharges the condition via `ForallT_nil` for **every** category and every choice function. The verifier proved this against the built library (Rocq 9.1) in a probe that compiles `coverage_condition_is_vacuous`, `Site_from_any_choice`, `Empty_Site` and `every_presheaf_is_a_sheaf : forall C X, @Sheaf C (Empty_Site C) X`. So `Site C` imposes nothing beyond a choice function, and over the empty site every presheaf is a `Sheaf`. This is a **fourth** weakening beyond the three the scope note admits, and it means the eventual theorem "sheaves form a topos" would, as currently founded, be a theorem about a degenerate predicate.

## Work to be done

Re-found the sheaf development on the book's definition, then specialize it to a space.

1. **Fix the coverage axiom.** In `Theory/Sheaf.v`, restrict `coverage_condition`'s witness so that it is a covering family *of `v`* in a sense that is not discharged by the empty vector — i.e. carry the covering datum in the type rather than existentially quantifying over arbitrary vectors — and add a regression check that the empty-coverage site can no longer be built (a `Site_from_any_choice`-style construction must stop compiling, and `every_presheaf_is_a_sheaf` must fail). The scope note in `Theory/Sheaf/Category.v:28-47` must be updated to record that the fourth weakening has been closed.
2. **Matching families.** Define `MatchingFamily P (U_i) := { s : ∀ i, P (U_i) | ∀ i j, restrict (s i) ≈ restrict (s j) on U_i ∩ U_j }` and `Gluing` as a section over `U` restricting to each `s i`, and restate the sheaf condition as "every matching family has a unique gluing" — a simultaneous condition, replacing the per-leg one. Prove the equivalent equalizer formulation `P(U) → ∏ᵢ P(Uᵢ) ⇉ ∏_{i,j} P(Uᵢ ∩ Uⱼ)`, since it is the form the topos proof of §7.4 will want (`Structure/Equalizer/Fork.v` is the donor).
3. **Sheaf for every cover.** Change the quantification so a sheaf is required to satisfy the condition for *all* covers of every open, not for one chosen family — this is gap (c) and it is a change to the class, not an added lemma.
4. **Sheaves on a space.** New `Theory/Sheaf/Space.v`: the site of opens of a topological space, and `Shv(X, Op)` as the resulting category, with morphisms of sheaves being natural transformations of the underlying presheaves (so `Sheaves_Full`/`Sheaves_Faithful` carry over).
5. **The empty cover (Example 7.36).** Prove the necessary condition `P(∅) ≅ 1` for any sheaf, from the fact that the empty family covers ∅ and the empty tuple is its unique matching family. This is precisely the statement the current predicate is *incapable* of expressing, so it doubles as the acceptance test for the re-founding: it must be a theorem afterwards and it must have been unprovable before.

In-tree donors: `Theory/Sheaf.v`, `Theory/Sheaf/Category.v`, `Construction/Subcategory.v`, `Structure/Equalizer/Fork.v`, `Structure/Limit/Product.v` (indexed products for the equalizer form), `Instance/Sets.v` (`Sets_Terminal` at `:248`, `Sets_Initial` at `:265`), plus the `Top`/`Open(X)` constructions of #259 and #268.

## Definition of Done

- [ ] **The vacuity defect in `Theory/Sheaf.v:170-178` is fixed**: `coverage_condition` is no longer dischargeable by the empty vector, and a regression witness records that an "any choice function is a site" construction no longer typechecks.
- [ ] The per-leg gluing condition is replaced by a genuine matching-family condition, and `Theory/Sheaf/Category.v:28-47`'s scope note is rewritten to reflect what is now in force (including the fourth weakening being closed).
- [ ] `MatchingFamily`, `Gluing` and the sheaf condition defined per Definition 7.35, with the equalizer formulation proved equivalent.
- [ ] A sheaf is required to satisfy the condition for *every* cover of every object, not one chosen family.
- [ ] `Shv(X, Op)` constructed for an arbitrary topological space, with the full/faithful/replete inclusion into presheaves carried over.
- [ ] `P(∅) ≅ 1` proved for every sheaf (Example 7.36) — the acceptance test for the re-founding.
- [ ] At least one **positive** instance of the new `Sheaf` predicate exists in the tree (today there is none at all), so the predicate is demonstrably non-vacuous in both directions.
- [ ] Statement fidelity to Seven Sketches Definition 7.35 and Example 7.36 (printed p. 237); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the `Theory/Sheaf.v` entry currently advertises the per-leg predicate and must be corrected.

## Verification

```bash
coqc -R . Category Theory/Sheaf.v
coqc -R . Category Theory/Sheaf/Category.v
coqc -R . Category Theory/Sheaf/Space.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sheaf.
Print Assumptions sheaf_empty_terminal.
```
Reviewer: statement matches Seven Sketches Definition 7.35 (printed p. 237) — matching families are simultaneous, gluings are unique, and the condition is quantified over all covers. Confirm that the pre-existing degeneracy is gone by checking that no site can be built from a bare choice function and that `P(∅) ≅ 1` is now derivable.

## Dependencies

Depends on: #460 — the gluing/sheaf-condition statement for the sheaf of continuous functions; this issue generalizes it to an arbitrary space, re-founds the in-tree predicate, and builds the category, and deliberately does not restate that issue's concrete instance.
Depends on: #259 — the category `Top`.
Depends on: #268 — `Open(X)` as a category, the site this issue instantiates.

<!-- catalog: {"ids":["7sketches:7.3.3:def7.35","7sketches:7.3.3:example7.36"],"deps":["#460","#259","#268"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.3: The sheaf of sections of a map, from the discrete case to a continuous bundle"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.3:ex7.38, 7sketches:7.3.3:construction-sections-sheaf, 7sketches:7.3.3:ex7.40, 7sketches:7.3.3:ex7.42, 7sketches:7.3.3:ex7.44, 7sketches:7.3.3:example7.45, 7sketches:7.3.3:ex7.47]
deps_item_ids: [7sketches:7.3.3:def7.35]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.3, printed pp. 238–242 (PDF pp. 250–254): Exercise 7.38, the extended sections example, Exercises 7.40, 7.42 and 7.44, Example 7.45 and Exercise 7.47. Items `7sketches:7.3.3:ex7.38`, `7sketches:7.3.3:construction-sections-sheaf`, `7sketches:7.3.3:ex7.40`, `7sketches:7.3.3:ex7.42`, `7sketches:7.3.3:ex7.44`, `7sketches:7.3.3:example7.45`, `7sketches:7.3.3:ex7.47`.

## Background

For a map `f : X → Y`, sending each open `U ⊆ Y` to the set of sections of `f` over `U` gives the archetypal sheaf: matching local choices of preimages glue uniquely. See the nLab on [sheaf](https://ncatlab.org/nlab/show/sheaf) and on [section](https://ncatlab.org/nlab/show/section).

## Current state in the library

The whole development is missing, and so is every ingredient it needs beyond the underlying category theory.

- No fibres: every one of the ~118 "fiber"/"fibre" hits is Grothendieck-fibration or fibre-*category* machinery (`Theory/Fibration.v`, `Theory/Displayed.v`, `Construction/Grothendieck/Fiber.v`, `Construction/Displayed/Codomain.v`). `Structure/Regular.v:46`'s `kernel_pair f := pullback f f` is the pullback of `f` along *itself*, not the preimage of a point; `Instance/Sets/Image.v:69,76` builds the image setoid `{y & {x & f x ≈ y}}`, never the fibre at a fixed `y`. And `Instance/FinSet/Classifier.v:264` `FinSet_Pullbacks` is the only concrete `HasPullbacks` instance in the tree — `Sets` has none — so even "the fibre is the pullback along a global element" is unavailable in `Sets`.
- No sections sheaf: "sheaf of sections" returns nothing; the two `Sec_` hits are `freyd_sec_eq` in `Structure/Premonoidal/Freyd.v:63,212` and are unrelated; "étale" appears only in bibliography. The ~20 "sections" hits are split monomorphisms (`Theory/Morphisms.v:179` `sections_are_monic`) and chosen sections of `fmap` (`Theory/Functor.v:334`) — a different sense entirely.
- No restriction maps: the only `restriction` identifier in the tree is the single field of the `Sheaf` class (`Theory/Sheaf.v:193`), i.e. the gluing axiom, not a restriction map; presheaf restriction is generic `fmap` on `Presheaf U C := U^op ⟶ C` (`Theory/Sheaf.v:124`), which asserts nothing about any particular presheaf. `Instance/Poset.v:116` and `Instance/Proset.v:33` do turn orders into categories generically, but no instance is a powerset poset, so an inclusion such as `{a,c} ⊆ {a,b,c}` has no in-tree referent.
- No worked sheaf at all: `matching famil` has exactly six hits, all in `Theory/Sheaf/Category.v` (the scope note at `:35,46` and the `sheaf_iso_closed` proof script at `:112,113,130,131`), none exhibiting a matching or non-matching family; and the `Sheaf` class has no instance anywhere.
- Phase-D observation worth acting on: the sections construction is *expressible* with existing machinery — hom-sets of `Construction/Slice.v` over `Y`, restricted along `Op(Y)^op` — so the blocker is the missing `Op(Y)`, not the sections idea. `Instance/Discrete.v:37`'s `DiscreteCat` is the discrete *category* on a type (homs are equality proofs), **not** a discrete topological space, and must not be mistaken for one.

## Work to be done

New `Theory/Sheaf/Sections.v`, plus a worked finite instance file.

1. **Fibres (Exercise 7.38).** Define the fibre of a function over a point in `Sets`/`FinSet` and compute the exercise's three fibres for an explicit finite map, plus the requested variant map all of whose fibres have one or two elements. Prove the fibre is the pullback along the corresponding global element wherever the ambient category has the pullbacks (this is where `Sets` needing a `HasPullbacks` instance shows up; supplying one is in scope if convenient).
2. **The sections presheaf.** For `f : X → Y` with `Y` discrete, define `Sec_f (U) := { s : U → X | f ∘ s = incl_U }` with restriction along inclusions given by function restriction, and prove functoriality — i.e. that `Sec_f : Op(Y)^op ⟶ Sets` is a presheaf.
3. **The sheaf condition.** Prove `Sec_f` is a sheaf: a matching family over a cover glues uniquely, because a section is determined pointwise and the matching condition forces agreement on overlaps. This is intended to be the tree's **first positive instance** of the (re-founded) `Sheaf` predicate, so it doubles as the non-vacuity witness that this chapter's §7.3.3 sheaf issue requires.
4. **The worked exercises.** For the book's explicit five-element base: enumerate `Sec_f` over `{a,b,c}` and `{a,b,c,d}` and count over `{a,b,d,e}` (Exercise 7.40); write out the restriction map along `{a,c} ⊆ {a,b,c}` explicitly (Exercise 7.42); and exhibit a non-matching pair with the failure of gluing, plus a matching pair distinct from the book's picture together with its glued section (Exercise 7.44). Carry these in `FinSet`, where they compute by `eq_refl` in the style of `Instance/FinSet/Topos.v:77-91`.
5. **The continuous case (Example 7.45).** Generalize to a continuous `f : (X, Op_X) → (Y, Op_Y)` with `Sec_f (U) := { g : U → X | g continuous and f ∘ g = incl_U }`, and prove the sheaf condition again — continuity is local, so the glued function is continuous.
6. **Exercise 7.47, stated at the level the library can hold.** The exercise asks whether sheaves on a space correspond to vector fields. Formalize the honest answer abstractly: for a bundle `p : E → M`, the vector fields are the *global sections* of the single sheaf `Sec_p`, i.e. elements of one object of `Shv(M)`, not objects of `Shv(M)` — so there is no correspondence, and the relation is "vector fields = `Sec_p(M)` for the tangent bundle". State it as `Sec_p` being one object of `Shv(M)` with `Sec_p(M)` its global sections, and record in the header that the tangent-bundle instance is out of reach because manifolds are not in the tree.

In-tree donors: `Construction/Slice.v`, `Instance/Sets.v`, `Instance/FinSet.v`, `Instance/Sets/Image.v`, `Structure/Pullback.v`, `Theory/Sheaf.v`, `Functor/Diagonal.v` (`Diagonal` at `:33`, the constant-presheaf pattern), and the `Top`/`Open(X)` constructions of #259, #268.

## Definition of Done

- [ ] Fibres defined and the three requested fibres computed, with the pullback characterization proved.
- [ ] `Sec_f` built as a presheaf on the opens of a discrete space, with its restriction maps.
- [ ] `Sec_f` proved to be a sheaf — the tree's first positive `Sheaf` instance.
- [ ] Exercises 7.40, 7.42, 7.44 carried out concretely, including the non-matching pair whose gluing *fails*.
- [ ] The continuous generalization of Example 7.45 proved a sheaf.
- [ ] Exercise 7.47 answered as a statement about global sections of one sheaf, with the manifold limitation disclosed in the header.
- [ ] Statement fidelity to Seven Sketches §7.3.3 (printed pp. 238–242); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the first worked sheaf in the library is worth indexing.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Sections.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sec_is_Sheaf.
Print Assumptions Sec_continuous_is_Sheaf.
```
Reviewer: statement matches Seven Sketches §7.3.3 (printed pp. 238–242), including that Exercise 7.44's non-matching pair is shown *not* to glue.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the sheaf condition and `Shv(X, Op)`, which this issue instantiates.
Depends on: #456 — the discrete topology, over which the extended example runs.
Depends on: #259 — the category `Top` and continuity, needed for Example 7.45.

<!-- catalog: {"ids":["7sketches:7.3.3:ex7.38","7sketches:7.3.3:construction-sections-sheaf","7sketches:7.3.3:ex7.40","7sketches:7.3.3:ex7.42","7sketches:7.3.3:ex7.44","7sketches:7.3.3:example7.45","7sketches:7.3.3:ex7.47"],"deps":["7sketches:7.3.3:def7.35","#456","#259"]} -->

---8<---

```yaml
title: "Seven Sketches 7.3.3/7.4.1: Sheaves on the one-point space are sets"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.3.3:example7.48, 7sketches:7.4.1:ex7.52]
deps_item_ids: [7sketches:7.3.3:def7.35, 7sketches:7.4.1:eq7.50]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.3.3 Example 7.48 (printed p. 242; PDF p. 254) and §7.4.1 Exercise 7.52 (printed p. 244; PDF p. 256). Items `7sketches:7.3.3:example7.48`, `7sketches:7.4.1:ex7.52`.

## Background

The one-point space has exactly two opens, and its category of sheaves is equivalent to `Set`: the base case of the whole sheaf-topos story, and the reconciliation of "the classifier of `Set` is the booleans" with "the classifier of `Shv(X)` assigns to `U` the opens contained in `U`". See the nLab on [point of a topos](https://ncatlab.org/nlab/show/point+of+a+topos) and Wikipedia on [topos](https://en.wikipedia.org/wiki/Topos).

## Current state in the library

Neither clause exists.

- `[1, C] ≃ C` appears only as *prose*: `Instance/One.v:22` and `Instance/One/Diagonal.v:30` both state it informally, and the only assertion in the latter file is `Diagonal_Unique : ∀ J C D d, Delta[J](d) ≈[Cat] Delta(d) ∘ one` at `:33`. No proof of `[1, C] ≃ C` exists anywhere.
- `Sets` is genuinely **not** an `ElementaryTopos` instance: `Structure/Topos.v:104-110` discloses the one-universe-up truth-value obstruction, and `Instance/Sets/Classifier.v` carries only cross-universe theorems (`sets_char_pullback` at `:224`, `sets_char_unique` at `:283`, `sets_char_subobject` at `:341`). So "Set is the topos of sheaves on a point" has neither side available.
- For Exercise 7.52 the *endpoint* is in-tree but only for the skeletal finite model: `Instance/FinSet/Classifier.v:353` `FinSet_Classifier` has `Ω := 2%nat` with `truth := fun _ => fin_true`, and `fin2_cases` at `:321` gives the two-value case analysis. In `Sets` the in-tree classifier object is a `Prop`-setoid one universe up (`PropSetoid` at `Instance/Sets/Classifier.v:151`, under `iffT`), not a two-element set — so the book's identification `Ω_Set = {true,false}` holds in-tree only for `FinSet`. There is no one-point space, no `Op(pt)`, and no `Shv(1) ≃ Set`.

## Work to be done

New `Theory/Sheaf/Point.v`.

1. Build the one-point space and compute its poset of opens: exactly two, `∅ ⊂ {⋆}`, i.e. the walking arrow. Prove that `Op(pt)` is (isomorphic to) `Instance/Two.v`'s `_2`.
2. Prove `Shv(pt) ≃ Sets`. The route: a presheaf on the two-element chain is a pair of sets with a restriction map; the sheaf condition at the empty cover of ∅ forces the value at ∅ to be terminal (the `P(∅) ≅ 1` lemma of this chapter's §7.3.3 issue), and the remaining data is a single set. Prove it as an equivalence of categories using `Theory/Equivalence.v`, not merely as a bijection of objects. Along the way, `[1, C] ≃ C` becomes provable and should be recorded, closing the prose promise at `Instance/One.v:22`.
3. Exercise 7.52: instantiate the classifier recipe of this chapter's §7.4.1 issue at the one-point space and show `Ω(⋆) = {∅, {⋆}}`, a two-element set; then transport along `Shv(pt) ≃ Sets` to reconcile with the boolean classifier. State honestly in the header that the target of the reconciliation is `FinSet`'s `Ω = 2` rather than a `SubobjectClassifier Sets` instance, because the latter does not exist at a single universe level (see `Instance/Sets/Classifier.v`'s header for the library's own account of the obstruction).

In-tree donors: `Instance/One.v`, `Instance/One/Diagonal.v`, `Instance/Two.v`, `Instance/Two/Monoidal.v`, `Theory/Equivalence.v`, `Instance/FinSet/Classifier.v`, `Instance/Sets/Classifier.v`, and the `Top` construction of #259.

## Definition of Done

- [ ] The one-point space built, with its two opens and `Op(pt) ≅ _2`.
- [ ] `Shv(pt) ≃ Sets` proved as an equivalence of categories.
- [ ] `[1, C] ≃ C` recorded as a theorem, closing the prose claim at `Instance/One.v:22`.
- [ ] Exercise 7.52's reconciliation carried out: the classifier recipe over the point yields exactly two truth values.
- [ ] The header discloses that the boolean side of the reconciliation is `FinSet`'s `Ω = 2`, since `Sets` carries no single-level classifier instance.
- [ ] Statement fidelity to Seven Sketches Example 7.48 and Exercise 7.52 (printed pp. 242, 244); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Point.v
make && make todo
```
```coq
Print Assumptions Shv_point_equiv_Sets.
Print Assumptions Fun_one_equiv.
```
Reviewer: statement matches Seven Sketches Example 7.48 and Exercise 7.52; the equivalence is proved at the level of categories, not object bijections.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the sheaf condition and `Shv(X, Op)`.
Depends on: `7sketches:7.4.1:eq7.50` — the classifier recipe that Exercise 7.52 evaluates at the point.
Depends on: #259 — the category `Top`.
Depends on: #402 — the classifier of `Sets`, the other side of the reconciliation.

<!-- catalog: {"ids":["7sketches:7.3.3:example7.48","7sketches:7.4.1:ex7.52"],"deps":["7sketches:7.3.3:def7.35","7sketches:7.4.1:eq7.50","#259","#402"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4: A topos is a category of sheaves — Shv(X, Op) as an elementary topos"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4:def-topos, 7sketches:7.3:remark-presheaf-topos]
deps_item_ids: [7sketches:7.3.3:def7.35, 7sketches:7.4.1:construction-omega-classifier]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4 opening (printed pp. 242–243; PDF pp. 254–255) and §7.3 opening remark (printed pp. 231–232; PDF p. 244). Items `7sketches:7.4:def-topos` (the whole item) and `7sketches:7.3:remark-presheaf-topos` (the *site* half only — the claim that presheaf categories are toposes is recorded on #404).

## Background

Seven Sketches takes "topos" to *mean* a category of sheaves: `Shv(X, Op)` for a space, `Set` for the point, and — presheaves being sheaves for the trivial coverage — the instance category of any finitely presented schema. That is the Grothendieck notion; Lawvere's elementary topos, which the library takes as primitive, is the more general axiomatic one. See the nLab on [Grothendieck topos](https://ncatlab.org/nlab/show/Grothendieck+topos) and on [elementary topos](https://ncatlab.org/nlab/show/elementary+topos).

## Current state in the library

The library starts from the book's *footnote* notion and never states the book's definition.

- Present: `Structure/Topos.v:112` `Class ElementaryTopos` (terminal, cartesian, pullbacks, closed, classifier), derived power objects `Pow a := Ω ^ a` at `:129` and `relations_iso` at `:146`; `Theory/Sheaf/Category.v:81` `Sheaves` with `Sheaves_Full` at `:94`; `Instance/Fun/Cartesian.v:111` `Functor_Category_Cartesian`, giving functor categories their cartesian structure. All three files are registered in `_CoqProject` (199, 370, 474).
- Missing: (1) no theorem or instance `ElementaryTopos (Sheaves C)` — `Theory/Sheaf/Category.v` proves only that `Sheaves` is a category with a full, faithful, replete inclusion into presheaves; (2) no theorem that a presheaf category is a topos, and no trivial/canonical coverage making presheaves sheaves — `Class Site` has **no instance at all** in the tree, so the site half of the §7.3 remark is entirely unwritten; (3) no Grothendieck-topos definition and no Giraud-style characterization; (4) `Sets` is not an `ElementaryTopos` instance, so "Set is a topos" is available only as the cross-universe classifier theorems of `Instance/Sets/Classifier.v`; `Instance/FinSet/Topos.v:38` `FinSet_Topos` is the sole assembled witness in the whole library.
- Phase-D addenda, both folded here. First, the ingredient inventory for the presheaf case is sharper than the coverage record said: functor categories have **products** (`Functor_Category_Cartesian`), but neither the closed structure nor a classifier — `ls Instance/Fun/` contains `Cartesian.v` and nothing else, so there is no `Closed`, `Terminal` or `HasPullbacks` for `@Fun`. Second, and this changes the order of work: the vacuity defect recorded on this chapter's §7.3.3 sheaf issue means that, as currently founded, "`Sheaves C` is a topos" would be **a theorem about a degenerate predicate** — over the empty site every presheaf is a `Sheaf`. The re-founding must land before this theorem is worth proving. `Construction/Slice.v:110-116` separately names the fundamental theorem of topos theory as "not yet formalized here".

## Work to be done

New `Structure/Topos/Sheaves.v`, plus a small `Theory/Sheaf/Trivial.v`.

1. **The definition.** Introduce the book's notion — a (Grothendieck) topos is a category equivalent to `Shv(C, J)` for a site — as a predicate, and prove it implies `ElementaryTopos`. Keep the two notions distinct and related by a theorem; do not redefine `ElementaryTopos`.
2. **`Shv(X, Op)` is an elementary topos.** Assemble the five fields: terminal object (the constant one-point sheaf), finite products (pointwise, then check the sheaf condition), pullbacks (pointwise), exponentials (the standard `Hom(-× U, -)` formula, restricted to sheaves), and the classifier from this chapter's §7.4.1 issue. Sheafification is the natural tool for the colimit side and for exponentials; the honest alternative, if sheafification is deferred, is to restrict to the cases where the pointwise construction is already a sheaf and to say so in the header.
3. **The trivial coverage.** `Theory/Sheaf/Trivial.v`: exhibit the coverage on an arbitrary small category under which every presheaf is a sheaf, and prove `Sheaves(C, trivial) ≃ [C^op, Sets]`. This is the site half of the §7.3 remark and it is what makes the book's footnote ("presheaves count as sheaves") precise. **Note the trap**: with the coverage axiom as it stands today, this statement is true for a *degenerate* reason (the empty coverage discharges everything); it only becomes meaningful after the re-founding, and the issue must land on the re-founded definition.
4. **The two corollaries the book draws on the spot.** `Set` is a topos (via `Shv(pt) ≃ Sets` from this chapter's one-point issue), and the instance category of a finitely presented schema is a topos (via the trivial coverage plus #404).

In-tree donors: `Structure/Topos.v`, `Theory/Sheaf/Category.v`, `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Structure/SubobjectClassifier.v`, `Structure/Cartesian/Closed.v`, `Construction/Subcategory.v`, `Instance/FinSet/Topos.v` (the shape of an assembled topos).

## Definition of Done

- [ ] A Grothendieck-topos predicate defined, and `Grothendieck_topos → ElementaryTopos` proved.
- [ ] `ElementaryTopos (Shv(X, Op))` assembled with all five fields, for an arbitrary topological space.
- [ ] The trivial coverage built and `Sheaves(C, trivial) ≃ [C^op, Sets]` proved, making the book's "presheaves count as sheaves" precise.
- [ ] "Set is a topos" derived from `Shv(pt) ≃ Sets` rather than assumed.
- [ ] The header states which construction (if any) is restricted for want of sheafification, so the scope is disclosed rather than implied.
- [ ] The issue is not merged against the pre-existing degenerate sheaf predicate: the re-founded definition of this chapter's §7.3.3 issue is a prerequisite, and the DoD of that issue (a positive `Sheaf` instance exists, `P(∅) ≅ 1` is a theorem) must already hold.
- [ ] Statement fidelity to Seven Sketches §7.4 (printed pp. 242–243) and §7.3 (printed pp. 231–232); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is the chapter's flagship result and the `Structure/Topos.v` entry currently records only the elementary notion.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Trivial.v
coqc -R . Category Structure/Topos/Sheaves.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Shv_ElementaryTopos.
Print Assumptions Sheaves_trivial_presheaves.
```
Reviewer: statement matches Seven Sketches §7.4 (printed pp. 242–243) — the topos is *defined* as a category of sheaves and the elementary axioms are derived, not assumed; and confirm the sheaf predicate in force is the re-founded one.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the re-founded sheaf condition and `Shv(X, Op)`.
Depends on: `7sketches:7.4.1:construction-omega-classifier` — the classifier field of the topos structure.
Depends on: #404 — `Sets` and presheaf categories as elementary toposes; this issue supplies the site framing rather than restating that theorem.
Depends on: #405 — finite colimits in an elementary topos.
Depends on: #718 — exponentials of presheaves, the donor for the exponential field.
Depends on: #715 — colimits in a functor category are pointwise, needed for the colimit side.

<!-- catalog: {"ids":["7sketches:7.4:def-topos","7sketches:7.3:remark-presheaf-topos"],"deps":["7sketches:7.3.3:def7.35","7sketches:7.4.1:construction-omega-classifier","#404","#405","#718","#715"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.1: The subobject classifier of Shv(X, Op) is the sheaf of opens"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.1:eq7.50, 7sketches:7.4.1:eq7.51, 7sketches:7.4.1:ex7.53, 7sketches:7.4.1:construction-omega-classifier]
deps_item_ids: [7sketches:7.3.3:def7.35]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.1, displays (7.50) and (7.51), Exercise 7.53, and the unnumbered construction that follows; printed pp. 243–244 (PDF pp. 255–256). Items `7sketches:7.4.1:eq7.50`, `7sketches:7.4.1:eq7.51`, `7sketches:7.4.1:ex7.53`, `7sketches:7.4.1:construction-omega-classifier`.

## Background

For sheaves on a space the object of truth values sends each open `U` to the set of opens contained in `U`, with restriction given by intersection; it is a sheaf, and with the morphism picking out `U` itself it classifies subsheaves. Truth values are therefore *regions*: a proposition holds in some places and not others. See the nLab on [subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier) and on [sieve](https://ncatlab.org/nlab/show/sieve).

## Current state in the library

Only the generic shadow of the construction exists.

- `Theory/Subobject/Functor.v:180` builds `Sub : C^op ⟶ Sets` by chosen-pullback reindexing, with `fmap := sub_reindex (unop f)` where `sub_reindex` is defined at `:35` as the pullback of a subobject's mono along `f`; functoriality is exactly the content of Exercise 7.53 and is proved — `sub_reindex_id` at `:143` and `sub_reindex_comp` at `:152` discharge the `Program` obligations at `:190-199`. `Structure/SubobjectClassifier.v:187` `classifier_classifies : SubObj x ≅ (x ~> Ω)` in `Sets` is the generic classification theorem. Phase D confirms the honest reading: at `C` a poset of opens, `SubObj U` genuinely *is* `{V : V ⊆ U}`, so `Sub` is the generic form of display (7.50), and `sub_reindex_id` is a real counterpart to part (2) of the exercise (identities must be preserved, not just composites).
- Two things are missing and they are the whole point. First, the concrete side: no topological space, no frame or locale of opens, so the assignment `U ↦ {V open : V ⊆ U}` with restriction `V ↦ V ∩ W` cannot be written, and no in-tree computation identifies reindexing with intersection. Note `sub_reindex` needs an ambient `HasPullbacks`, whereas the book's restriction is elementary intersection. Second, the sheaf side: nothing verifies the sheaf condition for the truth-value presheaf, and no `truth` morphism from a terminal sheaf is built — the class field `truth : 1 ~> Ω` (`Structure/SubobjectClassifier.v:46`) is the generic shape, not this construction.
- The only concrete classifiers in the tree remain `Instance/FinSet/Classifier.v:353` and the cross-universe `Sets` theorems; there is no classifier on `Sheaves`, and "sieve" appears only twice, both prose (`Theory/Sheaf.v:80`, `Construction/Localization.v:101`).

## Work to be done

New `Theory/Sheaf/Classifier.v`.

1. Build the truth-value presheaf `Ω(U) := {V open : V ⊆ U}` with restriction `Ω(U) → Ω(V)`, `W ↦ W ∩ V`, and prove it is a presheaf: functoriality (Exercise 7.53 part 1) and preservation of identities (part 2, which the exercise poses as a question — the answer is that functoriality alone is not enough).
2. Prove it satisfies the sheaf condition. This is the construction's real content and the book gives the argument: given a cover of `U` by `Uᵢ` and a matching family `Vᵢ ⊆ Uᵢ` with `Vᵢ ∩ Uⱼ = Vⱼ ∩ Uᵢ`, the union `V := ⋃ᵢ Vᵢ` is a gluing, by distributing intersection over union — so the frame distributivity law of this chapter's §7.3.2 quantale issue is the load-bearing input. Prove uniqueness too.
3. Build the truth morphism: the terminal sheaf sends every open to a one-element set, and `true` at `U` picks out `U` itself, the largest open contained in `U`. Prove `truth` is monic.
4. Assemble `SubobjectClassifier (Shv(X, Op))`, discharging `char_pullback` and `char_unique`; the characteristic map of a subsheaf `S' ↪ S` sends a section `s ∈ S(U)` to the largest open on which `s` restricts into `S'`.
5. Record the upshot the book puts in a run-in: the truth values of `Shv(X, Op)` are the opens of `X`, with `X` meaning fully true and `∅` fully false. Connect the generic `Sub` functor to this construction by proving that at `C = Op(X)` the two agree, so `Theory/Subobject/Functor.v`'s existing functoriality is reused rather than duplicated.

In-tree donors: `Theory/Subobject.v`, `Theory/Subobject/Functor.v` (`Sub`, `sub_reindex`, `sub_reindex_id`, `sub_reindex_comp`), `Structure/SubobjectClassifier.v`, `Theory/Sheaf/Category.v`, `Instance/Sets.v`, and the frame of opens from this chapter's §7.3.2 quantale issue.

## Definition of Done

- [ ] The truth-value presheaf built with intersection as restriction, and proved a presheaf (identities *and* composites, answering both parts of Exercise 7.53).
- [ ] The sheaf condition proved for it, with the union as gluing and uniqueness established.
- [ ] The `truth` morphism from the terminal sheaf built and proved monic.
- [ ] `SubobjectClassifier (Shv(X, Op))` assembled, with `char_pullback` and `char_unique` discharged.
- [ ] The identification with the generic `Sub : C^op ⟶ Sets` at `C = Op(X)` proved, so the existing functoriality is reused.
- [ ] Statement fidelity to Seven Sketches §7.4.1 (printed pp. 243–244); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the second concrete subobject classifier in the library.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Classifier.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Omega_Shv.
Print Assumptions Shv_Classifier.
```
Reviewer: statement matches Seven Sketches §7.4.1 (printed pp. 243–244) — the sheaf condition for the truth-value presheaf is *proved* by the distributivity argument, not assumed, and `truth` picks out the largest open.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the sheaf condition and `Shv(X, Op)`.
Depends on: `7sketches:7.3.2:remark7.33` — the frame/quantale of opens, whose distributivity is what makes the union a gluing.
Depends on: #403 — subobject classifiers for functor categories, the presheaf-level precedent.
Depends on: #268 — `Open(X)` as a category.

<!-- catalog: {"ids":["7sketches:7.4.1:eq7.50","7sketches:7.4.1:eq7.51","7sketches:7.4.1:ex7.53","7sketches:7.4.1:construction-omega-classifier"],"deps":["7sketches:7.3.3:def7.35","7sketches:7.3.2:remark7.33","#403","#268"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.1: The subobject classifier of the topos of graphs"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.1:example7.54, 7sketches:7.4.1:ex7.55]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.1, Example 7.54 and Exercise 7.55, printed pp. 244–245 (PDF pp. 256–257). Items `7sketches:7.4.1:example7.54`, `7sketches:7.4.1:ex7.55`.

## Background

Directed graphs are the presheaves on the two-object arrow shape, so they form a topos; its subobject classifier is a concrete small graph with two vertices and five arrows, and the characteristic homomorphism of a subgraph records, arrow by arrow, which endpoints survive. See the nLab on [quiver](https://ncatlab.org/nlab/show/quiver) and on [subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier).

## Current state in the library

Both the carrier and the classifier are missing, though two near-misses exist and neither is evidence.

- `Construction/Free/Quiver.v:358` `QuiverCategory` is the category of graphs (with `Class Quiver` at `:54`, whose `edges : nodes → nodes → uedges` is a *dependent family*), and `Instance/Parallel.v:166` `Presheaf_Graph : Parallel^op ⟶ Sets` is one specific graph-as-presheaf (vertices `nat`, edges `nat * nat`). Neither carries products, exponentials, a classifier or a topos structure. `Instance/Parallel.v:80` `Parallel` is exactly the book's arrow shape — two objects with two non-identity arrows — and its variance is right: in `Parallel^op` the maps go `ParY → ParX`, so `fmap` sends an edge to its endpoints.
- A tree-wide search for `subgraph` returns **zero** hits, so the exercise's subgraph cannot be named, let alone classified. `ElementaryTopos` has the single `FinSet` witness, so the graph topos does not exist at any level of generality.

## Work to be done

New `Instance/Parallel/Classifier.v`.

1. Build the topos of graphs as `[Parallel^op, Sets]`, or obtain it from the general presheaf-topos theorem (#404) once that lands; either way the classifier must be exhibited concretely, since that is the example's content.
2. Construct the classifier graph explicitly: two vertices `0` and `V`, five arrows — a loop at `0`, two loops at `V`, and one arrow in each direction between `0` and `V` — matching the book's labels. Build the terminal graph (one vertex, one loop) and the truth morphism sending its loop to the "both endpoints in, arrow in" arrow of the classifier.
3. Prove it classifies: for a subgraph `H ⊆ G`, define the characteristic homomorphism sending a vertex to `V` when it lies in `H` and to `0` otherwise, and an arrow to the arrow of the classifier determined by which of {arrow in `H`, source only, target only, both endpoints but not the arrow, neither} holds; then prove the classifying square is a pullback and the map is unique. This is `SubobjectClassifier` for the graph topos.
4. Exercise 7.55: the book's four-vertex graph with a parallel pair, a chain of two further arrows, and the three-vertex one-arrow subgraph — compute the classifying homomorphism explicitly, by `eq_refl` if the carriers are finite.
5. The example remarks that the classifier is easiest to find via the Yoneda lemma. `Theory/Yoneda.v` is in-tree; deriving `Ω(c) = Sub(y c)` and specializing at the two objects of the arrow shape is the principled route and should be preferred to guessing the five arrows.

In-tree donors: `Instance/Parallel.v`, `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Theory/Yoneda.v`, `Structure/SubobjectClassifier.v`, `Construction/Free/Quiver.v`, `Instance/FinSet/Classifier.v` (as the model for a computable classifier).

## Definition of Done

- [ ] The classifier graph built with exactly the two vertices and five arrows of the example, and the terminal graph with its truth morphism.
- [ ] `SubobjectClassifier` proved for the graph topos, with the five-case characteristic homomorphism, the pullback square and uniqueness.
- [ ] A `subgraph` notion introduced (the tree has none) and the classifying homomorphism computed for the book's concrete instance (Exercise 7.55).
- [ ] The derivation is routed through Yoneda (`Ω(c) ≅ Sub(y c)`), as the example advises, rather than asserted.
- [ ] Statement fidelity to Seven Sketches Example 7.54 and Exercise 7.55 (printed pp. 244–245); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Instance/Parallel/Classifier.v
make && make todo
```
```coq
Print Assumptions Graph_Classifier.
```
Reviewer: statement matches Seven Sketches Example 7.54 (printed pp. 244–245), including the five arrows of the classifier and the case analysis of the characteristic homomorphism on arrows.

## Dependencies

Depends on: #403 — subobject classifiers for functor categories, of which this is the concrete instance.
Depends on: #705 — the category of directed graphs as a functor category, the carrier this issue classifies in.
Depends on: #404 — presheaf categories as elementary toposes, the ambient claim.

<!-- catalog: {"ids":["7sketches:7.4.1:example7.54","7sketches:7.4.1:ex7.55"],"deps":["#403","#705","#404"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.3: Predicates in a topos — comprehension and the entailment order"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.3:def-predicate, 7sketches:7.4.3:ex7.62, 7sketches:7.4.3:eq7.63, 7sketches:7.4.3:ex7.64]
deps_item_ids: [7sketches:7.4:def-topos, 7sketches:7.4.1:construction-omega-classifier]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.3, printed pp. 247–248 (PDF pp. 259–260): the unnumbered definition of a predicate, Exercise 7.62, display (7.63), and Exercise 7.64. Items `7sketches:7.4.3:def-predicate`, `7sketches:7.4.3:ex7.62`, `7sketches:7.4.3:eq7.63`, `7sketches:7.4.3:ex7.64`.

## Background

A predicate on an object `S` of a topos is a morphism `S ⟶ Ω`; it cuts out a subobject by comprehension, and the predicates on `S` form a poset under entailment, which in a sheaf topos says that one predicate's region of validity is contained in the other's. See the nLab on [subobject classifier](https://ncatlab.org/nlab/show/subobject+classifier) and on the [Mitchell–Bénabou language](https://ncatlab.org/nlab/show/Mitchell-Benabou+language).

## Current state in the library

The abstract half is present; the order, the comprehension API and the sheaf-level reading are all missing.

- Present: `Structure/SubobjectClassifier.v:44` `Class SubobjectClassifier` with `Ω`, `truth : 1 ~> Ω`, `char {u x} (m : u ~> x) (M : Monic m) : x ~> Ω`, `char_pullback` and `char_unique` (`char_respects` is a derived lemma at `:143`, not a field); `:159` `classifier_char_roundtrip` and `:174` `classifier_pullback_roundtrip`, packaged as `:187` `classifier_classifies : SubObj x ≅ (x ~> Ω)` in `Sets`, ending in `Defined.`; `Theory/Subobject.v:59` `sub_le` with `sub_le_refl`/`trans`/`unique` at `:62`/`:67`/`:78` and `sub_equiv_iff_mutual` at `:93`, which *is* the book's antisymmetry (mutual factorization ⇔ equality in the `SubObj` setoid quotient); `Instance/FinSet/Classifier.v:188` `fin_select_sat` and `:201` `fin_select_rank`.
- Missing, precisely: (1) **no order on predicates.** `sub_le` lives on `SubObj x` and nothing defines `p ≤ q` for `p q : x ~> Ω`, nor transports `sub_le` along `classifier_classifies` (which is only an iso of setoids, with no order structure). Phase D re-ran the decisive check: `sub_le` has **zero** uses outside `Theory/Subobject.v`. (2) **No comprehension API**: a tree-wide search for `comprehension` returns zero hits; the operation exists only as the anonymous composite `sub_reindex h truth_subobject` (`Theory/Subobject/Functor.v:35`, `Structure/SubobjectClassifier.v:72`), with no notation, no membership lemma and no elementwise characterization. (3) `Sub : C^op ⟶ Sets` (`Theory/Subobject/Functor.v:180`) is **Sets-valued, not poset-valued**, so the order is carried by no functorial structure. (4) The `S = 1` specialization — "propositions are morphisms `1 ⟶ Ω`" — is never named; the only such arrows in the tree are `truth` and `Instance/FinSet/Topos.v:69`'s `point_true`. (5) There is no `SubobjectClassifier Sheaves` and no `ElementaryTopos Sheaves`, so the sheaf-level semantics (`Ω(U)` = opens of `U`, `p(s)` as the region of validity, compatibility with restriction) has no counterpart; and there is no named `Predicate` abbreviation anywhere.

## Work to be done

New `Structure/Topos/Predicate.v`, plus a sheaf-level companion.

1. Name the notion: `Predicate S := S ~> Ω` in an `ElementaryTopos`, with the `S = 1` specialization named `Proposition`, and record `truth` and `point_true` as its first instances.
2. **Comprehension.** Give the composite `sub_reindex p truth_subobject` a name and a notation (`{ S | p }`), prove the membership characterization — a generalized element `x ⟶ S` factors through `{S | p}` exactly when `p ∘ x ≈ truth ∘ one` — and prove the round trip against `classifier_classifies`. This is a reusable API that several later obligations of this chapter consume, which is why it is specified here rather than inline.
3. **The entailment order.** Define `p ⊢ q` on `Predicate S`, prove it a preorder, and prove antisymmetry in the setoid sense by transporting `sub_equiv_iff_mutual` along the classification isomorphism — this is display (7.63) and it is the first use `sub_le` will have had outside its defining file. Two equivalent definitions should be given and proved equal: the subobject-level one (`{S|p} ≤ {S|q}` in `sub_le`) and the elementwise one (for every generalized element, `p` holds implies `q` holds).
4. **The sheaf reading.** In `Shv(X, Op)`, unfold a predicate to a family of functions `S(U) → Ω(U)` natural in `U`, so that `p(s)` is an open subset of `U`, and prove the entailment order agrees with pointwise containment of those opens — the book's defining formula. Answer Exercise 7.62 as a theorem: the sections of `{S|p}` over `U` are exactly the `s ∈ S(U)` with `p(s) = U`.
5. **Exercise 7.64.** Exhibit a concrete space, sheaf and pair of predicates with `p ⊢ q`, as an `Example`. The Sierpiński space or the sections sheaf of this chapter's §7.3.3 work are the cheapest carriers.

In-tree donors: `Structure/SubobjectClassifier.v`, `Theory/Subobject.v`, `Theory/Subobject/Functor.v`, `Structure/Topos.v`, `Instance/FinSet/Classifier.v`, `Instance/FinSet/Topos.v`, and the classifier of `Shv(X, Op)` from this chapter's §7.4.1 work.

## Definition of Done

- [ ] `Predicate` and `Proposition` named, with the two in-tree instances recorded.
- [ ] Comprehension named, notated, and equipped with a membership lemma and the classification round trip — closing the tree's zero-hit `comprehension` gap.
- [ ] The entailment order defined, proved a preorder, and proved antisymmetric via `sub_equiv_iff_mutual`; the subobject-level and elementwise definitions proved equivalent.
- [ ] The sheaf-level unfolding proved: predicates as natural families `S(U) → Ω(U)`, entailment as pointwise containment of opens.
- [ ] Exercise 7.62 answered as a theorem about sections of the comprehension over an arbitrary open.
- [ ] Exercise 7.64 witnessed by a concrete `Example`.
- [ ] Statement fidelity to Seven Sketches §7.4.3 (printed pp. 247–248); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — comprehension and the predicate order are the entry point to the internal logic.

## Verification

```bash
coqc -R . Category Structure/Topos/Predicate.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions comprehension.
Print Assumptions entails_antisym.
```
Reviewer: statement matches Seven Sketches §7.4.3 (printed pp. 247–248) — antisymmetry is proved, not assumed, and the sheaf-level reading of entailment is containment of opens pointwise in `U` and `s`.

## Dependencies

Depends on: `7sketches:7.4:def-topos` — the topos structure on `Shv(X, Op)` in which the sheaf-level reading is stated.
Depends on: `7sketches:7.4.1:construction-omega-classifier` — the classifier whose values are the opens.
Depends on: #669 — the subobject preorder and its poset quotient, the order this issue transports.
Depends on: #671 — comprehension subobjects, the precedent for the comprehension API.
Depends on: #721 — representability of the subobject functor and the naturality of the classifying bijection.

<!-- catalog: {"ids":["7sketches:7.4.3:def-predicate","7sketches:7.4.3:ex7.62","7sketches:7.4.3:eq7.63","7sketches:7.4.3:ex7.64"],"deps":["7sketches:7.4:def-topos","7sketches:7.4.1:construction-omega-classifier","#669","#671","#721"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.2/7.4.3: The Heyting algebra of predicates on an object of a topos"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.3:remark-heyting-predicates, 7sketches:7.4.2:example7.61]
deps_item_ids: [7sketches:7.4.3:eq7.63, 7sketches:7.2.3:construction-and]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.3, the unnumbered Heyting remark, printed p. 248 (PDF p. 260); and §7.4.2, Example 7.61, printed pp. 246–247 (PDF pp. 258–259). Items `7sketches:7.4.3:remark-heyting-predicates`, `7sketches:7.4.2:example7.61`.

## Background

Every connective on truth values extends pointwise to predicates on an object `S`, and with respect to entailment the extensions are the meet, join and residual — so the predicates on `S`, equivalently the subobjects of `S`, form a Heyting algebra. See the nLab on [Heyting algebra](https://ncatlab.org/nlab/show/Heyting+algebra) and on [Heyting category](https://ncatlab.org/nlab/show/Heyting+category), and Wikipedia on [Heyting algebra](https://en.wikipedia.org/wiki/Heyting_algebra).

## Current state in the library

The Heyting structure exists only on Coq's `Prop`, and nothing connects it to a topos.

- Present: `Instance/Props.v` assembles a bicartesian closed thin category — `Props_Cartesian` at `:69` (`product_obj := and`), `Props_Cocartesian` at `:80` (`product_obj := or`), `Props_Closed` at `:94` (`exponent_obj := Basics.impl`) — i.e. a Heyting prealgebra, and the file states that reading explicitly at `:15-27`.
- Missing: (i) **no binary operation on predicates in a topos**, and no proof that `∧` is the meet and `∨` the join for the entailment order — a tree-wide search finds no order-theoretic meet or join at all, every `join` hit being monad multiplication; (ii) **no Heyting-algebra class**, and no theorem "`Sub(S)` is a Heyting algebra in any elementary topos" — `Heyting` has exactly seven hits, all header prose, including `Structure/Topos.v:81` which states the fact only as background; (iii) **no pointwise mechanism**: `Instance/Fun/Cartesian.v` gives pointwise products in a functor category but no pointwise exponentials or coproducts, and in any case that concerns presheaves, not predicates on a fixed object. `Props` is never connected to `Instance/Sets/Classifier.v`'s `PropSetoid` or to any `Ω`.
- Phase D flagged this record as sitting on the PARTIAL/ABSENT boundary and its instruction to Phase E is explicit: treat the remark's actual content — pointwise connectives on predicates, `∧` as meet and `∨` as join for entailment, and `Sub(S)` Heyting in any topos — as **entirely unformalized**. The `Props` evidence is a model of the conclusion, not an instance of the claim.
- For Example 7.61: there is no bundle object, no vector field, no manifold and no tangent bundle in the tree; the four "section" hits are split monomorphisms in `Theory/Morphisms.v`, a different sense. And with the abstract `Site`/`Sheaf` pair never instantiated, "the largest open on which a property holds" has no in-tree meaning.

## Work to be done

New `Structure/Topos/Heyting.v`.

1. Introduce a `HeytingAlgebra` class over a thin category or a poset carrier — but check first whether #683 has already landed it, and if so *use* that class rather than declaring a second one; this issue's obligation is the topos-level theorem, not a rival definition.
2. Define the pointwise connectives on `Predicate S`: `(p ∧ q) := omega_and ∘ ⟨p, q⟩` and likewise for `∨`, `⇒`, `¬`, with `⊤ := truth ∘ one` and `⊥ := false ∘ one`. Prove each is well defined up to `≈` (a `Proper` instance).
3. Prove the order-theoretic content: `∧` is the binary meet and `∨` the binary join for the entailment order of this chapter's §7.4.3 issue, `⊤` and `⊥` are top and bottom, and `⇒` is the residual — `p ∧ q ⊢ r ↔ p ⊢ (q ⇒ r)`. That last is the Heyting adjunction and is the real theorem.
4. Conclude `Predicate S` — equivalently, transporting along `classifier_classifies`, `Sub(S)` — is a Heyting algebra in any elementary topos. Instantiate at `FinSet_Topos` to get a computable witness, and at `Shv(X, Op)` to recover the pointwise-in-`U` description the book gives.
5. Example 7.61, at the level the library can hold: for a continuous bundle `p : E → X`, the sheaf of sections is one object of `Shv(X)` (this chapter's §7.3.3 sections work), and predicates on it are morphisms into `Ω`; state the two predicates the example names as *given* predicates and prove that their conjunction and disjunction cut out the expected subobjects, i.e. that the internal reasoning the example describes is exactly the Heyting structure just proved. Disclose in the header that the tangent-bundle instance (manifolds, vector fields, gradients) is out of reach because none of that is in the tree.

In-tree donors: `Instance/Props.v` (the model to check against), `Structure/SubobjectClassifier.v`, `Theory/Subobject.v`, `Structure/Topos.v`, `Instance/FinSet/Topos.v`, and the connectives of this chapter's §7.2.3 issue.

## Definition of Done

- [ ] Pointwise connectives on `Predicate S` defined, each `Proper` for `≈`.
- [ ] `∧` proved the meet and `∨` the join for entailment; `⊤`/`⊥` proved top/bottom.
- [ ] The Heyting adjunction `p ∧ q ⊢ r ↔ p ⊢ (q ⇒ r)` proved.
- [ ] `Predicate S` (equivalently `Sub S`) proved a Heyting algebra in an arbitrary elementary topos — upgrading `Structure/Topos.v:81` from background prose to a theorem.
- [ ] Instantiated at `FinSet_Topos` (computable) and at `Shv(X, Op)` (recovering the pointwise-in-`U` description).
- [ ] No second Heyting-algebra class is introduced if #683 already provides one.
- [ ] Example 7.61 formalized at the abstract-bundle level, with the manifold limitation disclosed in the header.
- [ ] Statement fidelity to Seven Sketches §7.4.3 (printed p. 248) and Example 7.61 (printed pp. 246–247); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — "subobjects of any object of a topos form a Heyting algebra" is flagship-level.

## Verification

```bash
coqc -R . Category Structure/Topos/Heyting.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions pred_heyting.
Print Assumptions pred_impl_adjoint.
```
Reviewer: statement matches Seven Sketches §7.4.3 (printed p. 248) — the connectives are computed pointwise and the meet/join claims are proved against the entailment order of display (7.63), not asserted.

## Dependencies

Depends on: `7sketches:7.4.3:eq7.63` — the entailment order against which meet and join are proved.
Depends on: `7sketches:7.2.3:construction-and` — the connectives on `Ω` that are being extended pointwise.
Depends on: `7sketches:7.3.3:construction-sections-sheaf` — the sheaf of sections of a bundle, the carrier of Example 7.61.
Depends on: #683 — the Heyting-algebra class; this issue reuses it rather than declaring a second one.
Depends on: #685 — the open-set lattice as a complete Heyting algebra, the concrete model in the sheaf case.
Depends on: #445 — intersections and unions of subobjects, the subobject-level reading of meet and join.

<!-- catalog: {"ids":["7sketches:7.4.3:remark-heyting-predicates","7sketches:7.4.2:example7.61"],"deps":["7sketches:7.4.3:eq7.63","7sketches:7.2.3:construction-and","7sketches:7.3.3:construction-sections-sheaf","#683","#685","#445"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.4: Quantifiers in a topos — ∀ by the exponential pullback and ∃ by image factorization"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.4:example7.65, 7sketches:7.4.4:ex7.66, 7sketches:7.4.4:def-universal-quantification, 7sketches:7.4.4:ex7.67, 7sketches:7.4.4:def-existential-quantification, 7sketches:7.4.4:ex7.68]
deps_item_ids: [7sketches:7.4.3:def-predicate, 7sketches:7.2.1:def-epi-mono-factorization]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.4, printed pp. 248–250 (PDF pp. 260–262): Example 7.65, Exercise 7.66, the two unnumbered quantifier definitions, and Exercises 7.67 and 7.68. Items `7sketches:7.4.4:example7.65`, `7sketches:7.4.4:ex7.66`, `7sketches:7.4.4:def-universal-quantification`, `7sketches:7.4.4:ex7.67`, `7sketches:7.4.4:def-existential-quantification`, `7sketches:7.4.4:ex7.68`.

## Background

Each quantifier turns a predicate in `n+1` variables into one in `n`. In a topos, `∀` is defined by a pullback against the exponential transpose of the predicate, and `∃` by taking the epi-mono factorization of the projected subobject — which is why the existential quantifier is only *locally* witnessed, a cover rather than a global section. See the nLab on [universal quantifier](https://ncatlab.org/nlab/show/universal+quantifier), [existential quantifier](https://ncatlab.org/nlab/show/existential+quantifier) and [hyperdoctrine](https://ncatlab.org/nlab/show/hyperdoctrine).

## Current state in the library

Neither quantifier exists at any level of generality, and the categorical route to them is a commented-out stub.

- No operation of type `Hom(x × y, Ω) → Hom(x, Ω)` exists. Every "quantif" hit is header prose — `Theory/Adjunction.v:75-76` names the hyperdoctrine triple `∃ ⊣ subst ⊣ ∀` as background, and `Structure/Topos.v:84` mentions it — or the unrelated Coq sense of "quantified over".
- The slice-level route is explicitly unfinished: `Construction/Slice/Pullback.v:50` `Bang_Functor` (`Σ_f`) and `:67` `Star_Functor` (`f*`) are the only live definitions in the file; `Base_Functor_Adjunction` is a **fully commented-out stub** beginning at `:121`; and the header at `:30-40` leaves `Σ_f ⊣ f* ⊣ Π_f` as a remark with `Π_f` never defined. So the universal quantifier is missing both as `Π_f` and as the book's `Ω^T` pullback.
- The ingredients for the book's constructions do exist and should be used rather than rebuilt: `Structure/Topos.v:129` `Pow a := Ω ^ a` and `:146` `relations_iso : SubObj (a × b) ≅ (a ~> Pow b)` are exactly the currying transpose the `∀` definition's bottom leg needs, though nothing forms the pullback; and for `∃`, `Structure/Regular/Factorization.v:132` `image_obj`, `:270` `regular_factorization`, `:282` `Regular_OFS`, `Structure/Abelian.v:261/264` and `Instance/Sets/Image.v:143` supply genuine image machinery — but `Class Regular` (`Structure/Regular.v:66`) has no instance derived from `ElementaryTopos`, and no lemma anywhere composes a mono with a projection and names the result `∃`.
- For Exercise 7.66 there is no natural-numbers object (`NNO` returns zero hits) and no `fin_forall` counterpart to `fin_existsb`, and `Sets` has no classifier instance, so "the topos of sets with `Ω = 2`" is not available as a setting either.

## Work to be done

New `Structure/Topos/Quantifier.v`.

1. **Universal quantification.** For `p : S × T ⟶ Ω`, define `∀_T p : S ⟶ Ω` as the classifying map of the pullback of `truth^T : 1 ⟶ Ω^T` along the exponential transpose `curry p : S ⟶ Ω^T` — precisely the square the book draws. Prove the elementwise characterization: a generalized element `s` satisfies `∀_T p` exactly when `p ∘ ⟨s ∘ !, t⟩` holds for every `t`. In `Shv(X, Op)` prove the book's concrete formula: `(∀_T p)(s)` is the largest open `V ⊆ U` such that `p` holds on all of `V` for every section of `T` over `V`.
2. **Existential quantification.** For the same `p`, take the subobject of `S × T` it classifies, compose its mono with the projection to `S`, take the epi-mono factorization of the composite, and define `∃_T p` as the classifying map of the mono half. This consumes the factorization system of this chapter's §7.2.1 issue. Prove the sheaf-level formula — the union of opens over which a *local* witness exists — and state explicitly, as the book stresses, that this does **not** produce a global section of `T`: the existential quantifier involves coverings.
3. **Adjointness.** Prove `∃_T ⊣ π* ⊣ ∀_T` on predicate posets, connecting the two constructions to the hyperdoctrine framing of #384 and #728. This is the sanity check that the two definitions are the right ones.
4. **Exercises.** Example 7.65 and Exercises 7.67/7.68 are the informal readings; formalize them as instantiations of the definitions at a concrete sheaf pair (the sections sheaves of this chapter's §7.3.3 work will serve), each stated as a lemma computing the returned open. Exercise 7.66 is the `Set`-level drill; carry it in `FinSet` over finite carriers standing in for ℕ and ℤ (the integers are not in the tree), computing the four requested subsets by `eq_refl`, and disclose the substitution in the header.

In-tree donors: `Structure/Topos.v` (`Pow`, `relations_iso`), `Structure/Cartesian/Closed.v` (`exp_iso`), `Structure/Pullback.v`, `Theory/Morphisms/Stability.v`, `Structure/Regular/Factorization.v`, `Construction/Slice/Pullback.v` (`Bang_Functor`, `Star_Functor` — and the place where `Π_f` belongs), `Instance/FinSet/Classifier.v`.

## Definition of Done

- [ ] `∀_T` defined by the pullback the book draws, with the elementwise characterization proved.
- [ ] `∃_T` defined by epi-mono factorization, with the local-witness (covering) reading proved and the *absence* of a global witness stated as a lemma or a documented non-theorem.
- [ ] `∃_T ⊣ π* ⊣ ∀_T` proved on predicate posets.
- [ ] The sheaf-level formulas of both definitions proved in `Shv(X, Op)`.
- [ ] Exercise 7.66 computed in a finite model, with the ℕ/ℤ substitution disclosed.
- [ ] Examples 7.65 / Exercises 7.67, 7.68 formalized as computations of the returned open at a concrete sheaf pair.
- [ ] If `Π_f` is built along the way, `Construction/Slice/Pullback.v:30-40`'s dangling remark and the commented-out `Base_Functor_Adjunction` stub at `:121` are resolved rather than left in place.
- [ ] Statement fidelity to Seven Sketches §7.4.4 (printed pp. 248–250); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — quantifiers in a topos are flagship-level.

## Verification

```bash
coqc -R . Category Structure/Topos/Quantifier.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions topos_forall.
Print Assumptions topos_exists.
Print Assumptions quantifier_adjunctions.
```
Reviewer: statement matches Seven Sketches §7.4.4 (printed pp. 248–250) — `∀` is the pullback against `Ω^T` and `∃` is the image of the projected subobject, and the covering caveat on `∃` is recorded.

## Dependencies

Depends on: `7sketches:7.4.3:def-predicate` — predicates, comprehension and the entailment order the quantifiers act on.
Depends on: `7sketches:7.2.1:def-epi-mono-factorization` — the (epi, mono) factorization in a topos that defines `∃`.
Depends on: #384 — quantifiers as adjoints to substitution, the powerset-level precedent.
Depends on: #728 — quantifiers as adjoints to weakening and the hyperdoctrine framing.

<!-- catalog: {"ids":["7sketches:7.4.4:example7.65","7sketches:7.4.4:ex7.66","7sketches:7.4.4:def-universal-quantification","7sketches:7.4.4:ex7.67","7sketches:7.4.4:def-existential-quantification","7sketches:7.4.4:ex7.68"],"deps":["7sketches:7.4.3:def-predicate","7sketches:7.2.1:def-epi-mono-factorization","#384","#728"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.5: Modalities (Lawvere–Tierney operators) on the subobject classifier"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.5:def7.69, 7sketches:7.4.5:ex7.70, 7sketches:7.4.5:prop7.71, 7sketches:7.4.5:ex7.72]
deps_item_ids: [7sketches:7.2.3:construction-and, 7sketches:7.4.3:eq7.63]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.5, Definition 7.69, Exercise 7.70, Proposition 7.71 and Exercise 7.72, printed pp. 250–251 (PDF pp. 262–263). Items `7sketches:7.4.5:def7.69`, `7sketches:7.4.5:ex7.70`, `7sketches:7.4.5:prop7.71`, `7sketches:7.4.5:ex7.72`.

## Background

A modality is an endomorphism `j : Ω ⟶ Ω` that is inflationary, idempotent and preserves binary meets — a Lawvere–Tierney topology, the datum that cuts out a subtopos and internalizes a Grothendieck topology. See the nLab on [Lawvere–Tierney topology](https://ncatlab.org/nlab/show/Lawvere-Tierney+topology) and on [nucleus](https://ncatlab.org/nlab/show/nucleus), and Wikipedia on [Lawvere–Tierney topology](https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology).

## Current state in the library

Nothing of the notion exists, and the library's own header essay already names it as background rather than content.

- `Lawvere-Tierney` has exactly two hits, both in `Structure/Topos.v`'s header essay: a Wikipedia URL at `:34` and the background sentence at `:86-89` stating that a Grothendieck topology is encoded by an idempotent, finite-meet-preserving endomorphism `j : Ω ⟶ Ω`. There is no class, record, definition or lemma. `modality` has four hits, all prose about the linear-logic `!` and reflective modalities; `nucleus`, `local operator` and `inflationary` return no code hits.
- **No endomorphism of `Ω` is ever constructed.** `Ω` occurs in code only as the classifier field, in `Pow a := Ω ^ a`, and in `relations_iso`.
- The three modalities of Proposition 7.71 cannot be written for a further reason: the connectives `⇒` and `∨` on `Ω` do not exist (see this chapter's §7.2.3 issue), and there is no order on predicates (`sub_le` has no use outside `Theory/Subobject.v`), so neither `p ⇒ −` nor `− ∨ p` nor relative double negation is expressible. `double negation` returns zero hits.
- Two near-misses, both correctly rejected by Phase D and worth recording so they are not mistaken for donors: `Construction/Reflective/Idempotent.v:81` `IdempotentMonad` is a monad on a *category*, not an endomorphism of a truth-value object; and `Theory/Coq/Monad.v:154-162` `arrow_Monad` (the reader monad) is the categorified form of clause (a) of Proposition 7.71 with no relation to a classifier and no meet-preservation content.

## Work to be done

New `Structure/Topos/Modality.v`.

1. Define `Modality` on an `ElementaryTopos`: `j : Ω ~> Ω` with `p ⊢ j p`, `j (j p) ⊢ j p`, and `j (p ∧ q) ≈ j p ∧ j q`, all stated with the predicate order of this chapter's §7.4.3 issue so that in a sheaf topos the conditions hold uniformly in `U` — the book is explicit that `j` is a *sheaf morphism*, so the conditions are not pointwise-in-elements but natural. Note deliberately, as the book does, that monotonicity and preservation of the top element are **not** separately required.
2. Exercise 7.70: prove that under the inflationary law, `j (j q) ⊢ j q` is equivalent to `j (j q) ≈ j q`, i.e. that condition (b) is genuine idempotence. The `⇐` direction is trivial; the `⇒` direction uses antisymmetry of the predicate order — `sub_equiv_iff_mutual` transported, per this chapter's §7.4.3 issue.
3. Proposition 7.71: fix a proposition `p : 1 ⟶ Ω` and prove that each of `q ↦ (p ⇒ q)`, `q ↦ (p ∨ q)` and `q ↦ ((q ⇒ p) ⇒ p)` is a modality. The book states this without proof, so all three are genuine obligations; each needs the Heyting laws of this chapter's §7.4.3 Heyting issue.
4. Exercise 7.72: instantiate at a concrete sheaf and a concrete `p` and answer the six parts — what a predicate assigns to a section over an interval, what its `j`-value is, whether `p ⊢ j p` (yes, by clause (a)), whether `j³ = j²` (yes, by idempotence), and whether `j` preserves a binary conjunction (yes, by clause (c)). Carry these as lemmas about an arbitrary modality plus one worked instance, so the exercise's content is a theorem and not a comment.
5. Record the payoff: a modality cuts out a subtopos of `j`-sheaves. Proving that in full is not in scope here, but state it in the header with a pointer, so the file is honest about what it does and does not establish.

In-tree donors: `Structure/SubobjectClassifier.v`, `Structure/Topos.v` (whose header already describes the notion), and the connectives, predicate order and Heyting structure produced by this chapter's §§7.2.3 and 7.4.3 issues.

## Definition of Done

- [ ] `Modality` defined with the three conditions stated naturally (as befits a sheaf morphism), and the header records that monotonicity and top-preservation are deliberately not required.
- [ ] Exercise 7.70 proved: under (a), condition (b) is equivalent to `j ∘ j ≈ j`.
- [ ] All three modalities of Proposition 7.71 proved to satisfy the definition — the book gives no proof, so none may be assumed.
- [ ] Exercise 7.72's six parts discharged as lemmas about an arbitrary modality plus a worked instance.
- [ ] `Structure/Topos.v:86-89`'s background sentence upgraded from prose to a cross-reference to the new definition.
- [ ] Statement fidelity to Seven Sketches §7.4.5 (printed pp. 250–251); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — Lawvere–Tierney operators are flagship-level and currently appear only as background prose.

## Verification

```bash
coqc -R . Category Structure/Topos/Modality.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Modality.
Print Assumptions modality_idempotent_iff.
Print Assumptions modality_implies_p.
Print Assumptions modality_or_p.
Print Assumptions modality_double_negation_p.
```
Reviewer: statement matches Seven Sketches Definition 7.69 and Proposition 7.71 (printed pp. 250–251), and all three of the proposition's modalities are proved rather than asserted.

## Dependencies

Depends on: `7sketches:7.2.3:construction-and` — the connectives on `Ω` that the three conditions and the three examples use.
Depends on: `7sketches:7.4.3:eq7.63` — the order on predicates in which the conditions are stated, and its antisymmetry.
Depends on: `7sketches:7.4.3:remark-heyting-predicates` — the Heyting laws needed for Proposition 7.71.
Depends on: #685 — the open-set Heyting algebra, the concrete model in which the modalities are read.

<!-- catalog: {"ids":["7sketches:7.4.5:def7.69","7sketches:7.4.5:ex7.70","7sketches:7.4.5:prop7.71","7sketches:7.4.5:ex7.72"],"deps":["7sketches:7.2.3:construction-and","7sketches:7.4.3:eq7.63","7sketches:7.4.3:remark-heyting-predicates","#685"]} -->

---8<---

```yaml
title: "Seven Sketches 7.4.6: The internal language of a topos and its Kripke–Joyal semantics"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.4.6:eq7.73, 7sketches:7.4.6:example7.74]
deps_item_ids: [7sketches:7.4.4:def-universal-quantification]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.4.6, display (7.73) and Example 7.74, printed p. 251 (PDF pp. 263–264). Items `7sketches:7.4.6:eq7.73`, `7sketches:7.4.6:example7.74`.

## Background

Every topos carries a formal internal language whose types are objects and whose formulas are `Ω`-valued terms, together with a sound compiler from formal statements to facts about the topos — the Mitchell–Bénabou language with Kripke–Joyal (categorical) semantics. Under it, one sentence says "f is surjective" and compiles, in each topos, to that topos's own notion of surjectivity. See the nLab on [Kripke–Joyal semantics](https://ncatlab.org/nlab/show/Kripke-Joyal+semantics) and on [internal logic](https://ncatlab.org/nlab/show/internal+logic).

## Current state in the library

The apparatus is present; the logic is not. **This corrects the Phase-C framing, which the verifier explicitly downgraded:** of the two formal languages in the tree, only one is a legitimate sub-layer of this item.

- Legitimate: `Instance/AST.v:45` `Inductive Obj`, `:54` `Fixpoint denote`, `:72` `Inductive Hom` and `:94` `Program Fixpoint interp` give Lambek's internal language of a (bi)cartesian closed category — the *equational* fragment on which the Mitchell–Bénabou language is built.
- Not an instance of the item: `Solver/Expr.v:73` `Inductive Expr : Set := Top | Bottom | And | Or | Impl | Equiv`, with `Solver/Denote.v:106` `exprD`, `Solver/Decide.v:91` `expr_tauto`, `:136` `expr_sound` and `Solver/Normal.v:376` `exprAD_sound`, is a **reflection tactic's goal syntax**: `exprD` compiles it into *external* Coq propositions about morphism equality, not into subobjects or `Ω`-valued truth of any topos. The "formula-to-fact compiler" reading of that layer is an analogy, and Phase D records that a strict reading of the item would classify it ABSENT on that basis. Do not cite `Solver/*` as partial coverage of Kripke–Joyal semantics.
- Missing, precisely: (1) a formal internal language whose types are objects and whose formulas are terms of type `Ω`, with `∀`/`∃` interpreted by right and left adjoints to base change — neither `Solver/Expr.v`'s propositional `Expr` nor `Instance/AST.v`'s and `Instance/Lambda`'s quantifier-free typed terms has quantifiers, and `Ω` never appears in either syntax; the library also has no base-change functor `f*` in force and no locally-cartesian-closed structure (only `Theory/Morphisms/Stability.v`'s pullback-pasting lemmas); (2) the forcing relation `U ⊩ φ` and its clauses; (3) a soundness theorem for a deductive calculus — the in-tree soundness results are about reduction and decision procedures. `Kripke`, `Joyal` (outside Joyal–Street citations), `internal language` and `forcing` return only prose, and `Mitchell-Benabou` appears once, as prose at `Structure/Topos.v:84`.
- For Example 7.74 the `Sets` compilation has a specific hole. `Instance/Sets.v:429` `surjectivity_is_epic` — the biconditional "`(∀ b, ∃ a, h a ≈ b) ↔ Epic h`" — **ends at `Abort.` on line 476**, with the reverse direction commented out, so it does **not** enter the environment. The completed neighbours are `Lib/Setoid.v:120-121`'s `Class surjective` (split surjectivity with a chosen preimage) and `Instance/Sets.v:401` `bijective_is_iso`, which is bijection-implies-iso, not the epi/surjective biconditional. `Instance/Sets/Image.v:113` `Sets_Image_epi_epic` is proved. And for the sheaf compilation there is no substrate at all, since no `Site` instance exists.

## Work to be done

New `Structure/Topos/Language.v` and `Structure/Topos/KripkeJoyal.v`.

1. **Syntax.** Define the internal language over an `ElementaryTopos`: types are objects, terms are typed in context, formulas are terms of type `Ω`, with the connectives of this chapter's §7.2.3 issue and the quantifiers of its §7.4.4 issue as formula constructors. `Instance/AST.v` is the model for the term layer and should be extended rather than duplicated.
2. **Semantics.** Define the interpretation of a formula in context as a morphism `⟦Γ⟧ ⟶ Ω`, i.e. as a predicate, and prove it respects substitution. Then define the forcing relation `U ⊩ φ` for `Shv(X, Op)` and prove the Kripke–Joyal clauses: conjunction is intersection, disjunction and existential quantification involve *covers*, implication and universal quantification quantify over all smaller opens.
3. **Soundness.** State a deductive calculus for the fragment covered (intuitionistic first-order logic over the Heyting structure of this chapter's §7.4.3 issue) and prove that every derivable sequent interprets to an entailment of predicates. This is the "sound semantics" the section asserts for every topos.
4. **Example 7.74.** Prove the headline claim: `f : S ⟶ T` is an epimorphism if and only if the sentence "for every `t : T` there exists `s : S` with `f(s) = t`" holds internally. Then compile it in two toposes: in a presheaf topos (the book's database-instance reading) to objectwise surjectivity of the natural transformation, and in `Shv(X, Op)` to *local* surjectivity — every section over `U` is, after passing to a cover, in the image. Completing `Instance/Sets.v:429`'s aborted `surjectivity_is_epic` is a prerequisite for the `Set`-level reading and should be done here or on #245.
5. **Book erratum, to be handled explicitly.** As printed, the roles of `S` and `T` (and the quantifier order) in Example 7.74's two compiled boxes do not line up with the direction of `f` in display (7.73). Formalize the mathematically correct statement — quantify universally over the codomain and existentially over the domain — and record the discrepancy in the file header so a reader comparing with the book is not misled.

In-tree donors: `Instance/AST.v`, `Instance/Lambda/*`, `Structure/BiCCC.v`, `Structure/Topos.v`, `Instance/Sets.v`, `Instance/Sets/Image.v`, `Theory/Sheaf/Category.v`, plus the connectives, predicates, Heyting structure and quantifiers built earlier in this chapter.

## Definition of Done

- [ ] An internal language with `Ω`-valued formulas and both quantifiers, defined over an arbitrary `ElementaryTopos`.
- [ ] Interpretation into predicates, with substitution preserved.
- [ ] The Kripke–Joyal forcing clauses proved for `Shv(X, Op)`, with covers appearing in the `∨` and `∃` clauses.
- [ ] A soundness theorem for the deductive calculus in scope.
- [ ] "`f` is epi ⟺ the surjectivity sentence holds internally" proved, and compiled in a presheaf topos (objectwise) and in a sheaf topos (locally).
- [ ] `Instance/Sets.v:429`'s aborted `surjectivity_is_epic` completed (or its completion on #245 consumed), so the `Set` reading rests on a theorem and not on an `Abort`ed statement.
- [ ] The header records the printed erratum in Example 7.74's compiled boxes and states which reading was formalized.
- [ ] The header states plainly that `Solver/*` is a reflection tactic's syntax and is *not* an instance of this semantics, so the distinction survives in the tree.
- [ ] Statement fidelity to Seven Sketches §7.4.6 (printed p. 251); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the internal language of a topos is flagship-level.

## Verification

```bash
coqc -R . Category Structure/Topos/Language.v
coqc -R . Category Structure/Topos/KripkeJoyal.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions internal_soundness.
Print Assumptions epi_iff_internally_surjective.
Print Assumptions surjectivity_is_epic.
```
Reviewer: statement matches Seven Sketches §7.4.6 (printed p. 251); confirm that the `∃` clause of the forcing relation is the covering one, and that the printed erratum in Example 7.74 is documented rather than reproduced.

## Dependencies

Depends on: `7sketches:7.4.4:def-universal-quantification` — the quantifiers the language's formulas use.
Depends on: `7sketches:7.4.3:remark-heyting-predicates` — the Heyting structure the calculus is sound for.
Depends on: #695 — the internal language of a cartesian closed category, the equational layer this extends.
Depends on: #245 — epis in `Sets` are exactly the surjections; Example 7.74's `Set` compilation rests on it, and the in-tree statement is currently `Abort`ed.

<!-- catalog: {"ids":["7sketches:7.4.6:eq7.73","7sketches:7.4.6:example7.74"],"deps":["7sketches:7.4.4:def-universal-quantification","7sketches:7.4.3:remark-heyting-predicates","#695","#245"]} -->

---8<---

```yaml
title: "Seven Sketches 7.5.1: The interval domain and the topos of behavior types"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.5.1:def-interval-domain, 7sketches:7.5.1:ex7.76, 7sketches:7.5.1:construction-behavior-types, 7sketches:7.5.1:ex7.77, 7sketches:7.5.2:remark-truth-values-interval-domain]
deps_item_ids: [7sketches:7.4:def-topos, 7sketches:7.4.1:construction-omega-classifier]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.5.1, printed pp. 252–253 (PDF pp. 264–265): the unnumbered definition of the interval domain, Exercise 7.76, the behavior-types construction and Exercise 7.77; plus §7.5.2's unnumbered truth-values remark, printed p. 254 (PDF pp. 266–267). Items `7sketches:7.5.1:def-interval-domain`, `7sketches:7.5.1:ex7.76`, `7sketches:7.5.1:construction-behavior-types`, `7sketches:7.5.1:ex7.77`, `7sketches:7.5.2:remark-truth-values-interval-domain`.

## Background

The interval domain has the closed intervals of the line as points, topologized by the basic opens `{[d,u] : a < d, u < b}`; sheaves on it are "behavior types", whose truth values are time regions rather than instants. See the nLab on [Scott topology](https://ncatlab.org/nlab/show/Scott+topology) and Wikipedia on [domain theory](https://en.wikipedia.org/wiki/Domain_theory) and [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic).

## Current state in the library

Every prerequisite is missing and one homonym must be avoided.

- Zero hits, tree-wide, for "topological space", "open set", "basic open", "interval domain", "degenerate interval" and "subspace topology"; and zero hits for any real-number import (`Coq.Reals`, `Rdefinitions`, `Rle`, `Rlt`) — `nat`, via `Instance/FinSet.v` and `Instance/Omega.v`, is the library's only numeric carrier.
- **Homonym warning:** the "Interval" hits in the tree are the *interval category* nickname for the walking arrow (`Instance/Two.v`, `Instance/Fact.v`) and have nothing to do with the interval domain.
- `Class Site` (`Theory/Sheaf.v:159`) and its one `Context` use (`Theory/Sheaf/Category.v:68`) are the only occurrences of `Site` in the tree, so `Sheaves` (`Theory/Sheaf/Category.v:81`) is never instantiated at any site; `ElementaryTopos` outside `Structure/Topos.v` occurs only at `Instance/FinSet/Topos.v:38` and one prose mention at `Construction/Slice.v:114`. So "sheaves on a space form a topos" — the sentence that defines behavior types — is nowhere stated. The only in-tree trace of the item at all is the background citation at `Theory/Sheaf.v:91-94` ("Fong and Spivak model a behavior type as a sheaf on a space of time… safety becomes a statement of temporal logic"), which is prose, not coverage.
- For the truth-values remark: the generic classifier exists (`Structure/SubobjectClassifier.v:44`, `:187`) but its only instantiations are `FinSet`'s `Ω = 2` and the cross-universe `Sets` theorems, neither a sheaf topos and both with pointwise truth values — which is exactly the reading the remark argues against.

## Work to be done

New `Instance/Top/Interval.v` and `Instance/Top/Interval/BehaviorTypes.v`.

1. Build the interval domain: the carrier is the set of pairs `d ≤ u` (closed intervals, degenerate ones allowed), the basic opens are `B(a,b) := {[d,u] : a < d ∧ u < b}` for `a < b`, and the topology is generated by them (a subset is open iff it is a union of basic opens). Prove it is a topology. As with the metric-topology work of §7.3.2, the numeric substrate must be chosen and disclosed — importing `Coq.Reals` is permitted in the `Instance/` layer with its axioms enumerated in docs/AXIOMS.md, and a rational or abstract dense-linear-order substrate is an acceptable alternative.
2. Exercise 7.76: prove `[2,6] ∈ B(0,8)`, and prove `[2,6] ∉ B(0,5) ∪ B(4,8)`. The second is the book's own warning that basic opens are not closed under union in the naive way, and it is the sharpest small test that the topology has been defined correctly — it should be an explicit `Lemma`, not a comment.
3. Define the topos of behavior types as `Shv(IR, Op)`, using the topos theorem of this chapter's §7.4 issue.
4. Exercise 7.77 and the subspace claim: prove the degenerate intervals form a subspace isomorphic to the line, and that the subspace topology it inherits agrees with the usual (metric) topology of §7.3.2 — an "iff" statement, in both directions.
5. The truth-values remark: prove that the classifier of `Shv(IR, Op)` assigns to each open `U` the set of opens contained in `U` (instantiating this chapter's §7.4.1 result), and then prove the remark's substantive claim as a *theorem about the topology*, not as anecdote: exhibit an open `U` and a subsheaf whose predicate holds on `B(0,5)` and on `B(4,8)` but not on `B(0,8)`, so truth values are demonstrably not determined pointwise. The book's two informal illustrations (a watch handed over between shifts; a cumulative market fall) are the intuition; the formal content is the failure of pointwise determination, and the counterexample of Exercise 7.76 already supplies the geometry for it.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Structure/SubobjectClassifier.v`, plus `Top` (#259), the subspace topology (#457), and the metric topology and sheaf-topos results of this chapter.

## Definition of Done

- [ ] The interval domain built with its basic opens, and proved a topological space.
- [ ] Exercise 7.76 proved as two explicit lemmas, including the non-membership in the union of two basic opens.
- [ ] `Shv(IR, Op)` constructed and named as the topos of behavior types.
- [ ] The real line proved isomorphic to the degenerate-interval subspace, and Exercise 7.77's topology agreement proved in both directions.
- [ ] The classifier of the behavior-type topos computed as the sheaf of opens, and the failure of pointwise determination of truth values proved by an explicit counterexample.
- [ ] The numeric substrate choice disclosed in the file header, with any stdlib axioms enumerated in docs/AXIOMS.md.
- [ ] The header warns that "interval" elsewhere in the tree means the walking arrow, so the homonym does not propagate.
- [ ] Statement fidelity to Seven Sketches §7.5.1 (printed pp. 252–253) and the §7.5.2 truth-values remark (printed p. 254); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond stdlib axioms recorded in docs/AXIOMS.md for the `Instance/` layer.
- [ ] `Print Assumptions` closed (or explicitly enumerated) for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — `Theory/Sheaf.v:91-94` currently cites behavior types as background, and this makes them in-tree.

## Verification

```bash
coqc -R . Category Instance/Top/Interval.v
coqc -R . Category Instance/Top/Interval/BehaviorTypes.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions IntervalDomain_Topology.
Print Assumptions interval_2_6_not_in_union.
Print Assumptions BehaviorTypes.
```
Reviewer: statement matches Seven Sketches §7.5.1 (printed pp. 252–253); in particular the non-closure of basic opens under union is a proved lemma, and the truth-values remark is backed by an explicit counterexample rather than prose.

## Dependencies

Depends on: `7sketches:7.4:def-topos` — sheaves on a space form a topos, which is what makes behavior types a topos.
Depends on: `7sketches:7.4.1:construction-omega-classifier` — the classifier whose values are the opens.
Depends on: `7sketches:7.3.2:example7.26` — the usual topology on the line, the comparison target of Exercise 7.77.
Depends on: #259 — the category `Top`.
Depends on: #457 — the subspace topology.

<!-- catalog: {"ids":["7sketches:7.5.1:def-interval-domain","7sketches:7.5.1:ex7.76","7sketches:7.5.1:construction-behavior-types","7sketches:7.5.1:ex7.77","7sketches:7.5.2:remark-truth-values-interval-domain"],"deps":["7sketches:7.4:def-topos","7sketches:7.4.1:construction-omega-classifier","7sketches:7.3.2:example7.26","#259","#457"]} -->

---8<---

```yaml
title: "Seven Sketches 7.5.2: A sheaf is determined by its values on a basis, continuously"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.5.2:remark-basic-open-continuity]
deps_item_ids: [7sketches:7.3.3:def7.35, 7sketches:7.5.1:def-interval-domain]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.5.2, the unnumbered basic-opens remark with its display, printed p. 253 (PDF p. 265). Item `7sketches:7.5.2:remark-basic-open-continuity`.

## Background

Because every open is a union of basic opens, a sheaf is determined by its values on a basis — and the sheaf condition forces those values to vary continuously, which on the interval domain means the value at `B(a,b)` is the limit of the values at the slightly larger `B(a−ε, b+ε)`. See the nLab on [sheaf](https://ncatlab.org/nlab/show/sheaf) and Wikipedia on [base (topology)](https://en.wikipedia.org/wiki/Base_(topology)).

## Current state in the library

Nothing of either clause exists, and the current sheaf predicate could not carry them.

- `Theory/Sheaf.v:192-211`'s `Sheaf` class has the single field `restriction` stating a per-leg gluing condition over the **one** chosen coverage of a `Site`; nothing about determination by a basis, and no limit or continuity consequence is derived from it anywhere. The identifier `restriction` occurs only at `Theory/Sheaf.v:193` and its single consumer `Theory/Sheaf/Category.v:125`; every other hit is unrelated prose or `ColouredPROP` base-change restriction.
- Zero hits for "stalk", "germ" and "sheaf on a basis". And the library's own scope note at `Theory/Sheaf/Category.v:30-46` records that the inherited predicate is per-leg and vacuous beyond subsingleton fibres — so as founded today the predicate cannot force anything about values on a basis. This issue therefore lands **after** the re-founding scheduled by this chapter's §7.3.3 issue.

## Work to be done

New `Theory/Sheaf/Basis.v`.

1. Define a basis of a topology (a family of opens such that every open is a union of members) and the restriction of a sheaf to a basis.
2. Prove the determination theorem: a sheaf on a space is determined by its values on a basis, in the strong form — the restriction functor from sheaves on the space to "sheaves on the basis" (presheaves on the basis satisfying the sheaf condition for basic covers) is an equivalence of categories. Prove it as an equivalence, not as a bijection on objects; that is the form later work can use.
3. Prove the continuity clause on the interval domain: for a sheaf `F` on the interval domain, `F(B(a,b))` is the limit over shrinking `ε > 0` of `F(B(a−ε, b+ε))`. This is a filtered limit over the shrinking family and follows from the sheaf condition applied to the cover of `B(a,b)` by the smaller basic opens; `Structure/Limit.v` and the (co)limit vocabulary of `Structure/Limit/Preservation.v` are the donors.
4. Record the intended reading, which is the point of the remark for the rest of §7.5: a sheaf on the interval domain sends an open to the set of events taking place throughout it, restriction views an event over a shorter interval, and the sheaf condition says local events matching on overlaps glue uniquely.

In-tree donors: `Theory/Sheaf.v`, `Theory/Sheaf/Category.v`, `Structure/Limit.v`, `Structure/Limit/Preservation.v`, `Theory/Equivalence.v`, and the interval domain of this chapter's §7.5.1 issue.

## Definition of Done

- [ ] A basis of a topology defined, together with the sheaf condition restricted to basic covers.
- [ ] The determination theorem proved as an equivalence between sheaves on a space and sheaves on a basis.
- [ ] The continuity clause proved on the interval domain: the value at `B(a,b)` is the limit of the values at `B(a−ε, b+ε)`.
- [ ] The work is stated against the re-founded sheaf predicate, not the per-leg one; the file header says so.
- [ ] Statement fidelity to Seven Sketches §7.5.2 (printed p. 253); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Basis.v
make && make todo
```
```coq
Print Assumptions sheaf_basis_equivalence.
Print Assumptions interval_sheaf_continuity.
```
Reviewer: statement matches Seven Sketches §7.5.2 (printed p. 253) — the determination claim is an equivalence of categories and the continuity claim is a genuine limit.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the re-founded sheaf condition; the determination theorem is false for the per-leg predicate currently in force.
Depends on: `7sketches:7.5.1:def-interval-domain` — the space on which the continuity clause is stated.

<!-- catalog: {"ids":["7sketches:7.5.2:remark-basic-open-continuity"],"deps":["7sketches:7.3.3:def7.35","7sketches:7.5.1:def-interval-domain"]} -->

---8<---

```yaml
title: "Seven Sketches 7.5.2: Behavior types — the constant sheaf and sheaves of locally defined continuous maps"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.5.2:example7.78, 7sketches:7.5.2:example7.79, 7sketches:7.5.2:ex7.80]
deps_item_ids: [7sketches:7.3.3:def7.35, 7sketches:7.5.1:def-interval-domain]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.5.2, Examples 7.78 and 7.79 and Exercise 7.80, printed pp. 253–254 (PDF pp. 265–266). Items `7sketches:7.5.2:example7.78`, `7sketches:7.5.2:example7.79`, `7sketches:7.5.2:ex7.80`.

## Background

The first behavior types are the simplest sheaves: a set read as a value that never changes, and the locally defined continuous maps into a fixed space. See the nLab on [constant sheaf](https://ncatlab.org/nlab/show/constant+sheaf), Wikipedia on [constant sheaf](https://en.wikipedia.org/wiki/Constant_sheaf), and the nLab on [sheafification](https://ncatlab.org/nlab/show/sheafification).

## Current state in the library

Only the presheaf half of the first example exists, and it exists generically rather than over the space the example names.

- Present: `Functor/Diagonal.v:33` `Diagonal {C} (J : Category) : C → [J, C]`, whose object part sends `x` to the constant functor and whose morphism part is the constant transformation. Instantiated at `C := Sets` and `J := Op(X)^op`, this **is** the book's constant presheaf: value `A` on every open, identity restrictions. The file is registered at `_CoqProject:138`.
- Missing: the interval domain and its site (there is none), any instance of `Class Site` (there is none in the tree), and therefore any way to *state* "is a sheaf"; and there is no verified sheaf example of any kind in the library. Zero hits for "constant sheaf", "constant presheaf" and "locally constant"; zero hits for "continuous map"/"continuous function" in the topological sense — every "continuous" hit is the limit-preservation sense. `Functor/Hom.v:60` `Curried_Hom : C^op → [C, Sets]` is the nearest neighbour for Example 7.79 but no representable is ever asserted to be a sheaf.
- **Phase-D sharpening that changes what must be proved, and it must not be lost.** The literal constant presheaf is **not** a sheaf under Definition 7.35 when `|A| ≥ 2`: the empty family covers `∅`, its empty matching family must glue to a *unique* element of `P(∅) = A`, and that fails — which is exactly the book's own Example 7.36. The object that is a sheaf is the sheafification, i.e. the sheaf of locally constant functions (equivalently, the constant presheaf corrected at `∅`). An issue that asked for "the constant presheaf is a sheaf" would be asking for a false theorem.

## Work to be done

New `Theory/Sheaf/Constant.v`.

1. Instantiate `Functor/Diagonal.v:33`'s `Diagonal` at the site of the interval domain to get the constant presheaf on a set `A`, and prove — as a *negative* result — that it fails the sheaf condition for `|A| ≥ 2`, citing the empty-cover lemma of this chapter's §7.3.3 issue. Stating the failure explicitly is part of the work: it is what makes the next step necessary.
2. Build the object the book means: the sheaf of locally constant `A`-valued functions on the interval domain (equivalently the sheafification of the constant presheaf), and prove it is a sheaf. Prove that on a connected open its sections are `A`, recovering the reading "an element of `A` is a behavior that never changes".
3. Example 7.79: for a topological space `X`, build the sheaf `U ↦ {continuous maps U → X}` on the interval domain, and the variant `U ↦ {continuous maps (U ∩ ℝ) → X}` restricted to the degenerate-interval line; prove both are sheaves. These reuse the continuous-sections construction of this chapter's §7.3.3 issue and should be stated as instances of it, not rebuilt.
4. Exercise 7.80: for an *arbitrary* subset `R` of the interval domain, decide whether `U ↦ {continuous maps (U ∩ R) → X}` is a presheaf (yes — exhibit the restriction maps) and whether it is a sheaf, with proof. Give the honest answer with its hypothesis: gluing works because continuity of a map on `U ∩ R` is a local condition, so the general statement is a theorem for every `R` provided `R` carries the subspace topology; if the implementation finds a counterexample for some `R`, the counterexample is the deliverable instead. Either way the exercise must end in a proof, not in prose. Note the printed cross-reference is to Example 7.78 where 7.79 is meant; record that in the header.

In-tree donors: `Functor/Diagonal.v`, `Functor/Hom.v`, `Instance/Sets.v`, `Theory/Sheaf.v`, plus the interval domain (§7.5.1 of this chapter), the sections sheaf (§7.3.3), and the subspace topology (#457).

## Definition of Done

- [ ] The constant presheaf instantiated from `Diagonal`, and its **failure** of the sheaf condition for `|A| ≥ 2` proved, with the empty-cover argument cited.
- [ ] The sheaf of locally constant functions built and proved a sheaf, with sections over a connected open shown to be `A`.
- [ ] Both sheaves of Example 7.79 built and proved sheaves, as instances of the continuous-sections construction.
- [ ] Exercise 7.80 answered with proof for arbitrary `R` (or with an explicit counterexample), and the printed cross-reference slip recorded in the header.
- [ ] Statement fidelity to Seven Sketches §7.5.2 (printed pp. 253–254); setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping).
- [ ] `Print Assumptions` closed under the global context for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is judged flagship-level.

## Verification

```bash
coqc -R . Category Theory/Sheaf/Constant.v
make && make todo
```
```coq
Print Assumptions constant_presheaf_not_sheaf.
Print Assumptions locally_constant_sheaf.
Print Assumptions local_maps_sheaf.
```
Reviewer: statement matches Seven Sketches Examples 7.78/7.79 and Exercise 7.80 (printed pp. 253–254) — and in particular that the *constant presheaf* is shown not to be a sheaf, with the locally constant sheaf supplied in its place.

## Dependencies

Depends on: `7sketches:7.3.3:def7.35` — the sheaf condition, and the `P(∅) ≅ 1` lemma that defeats the naive constant presheaf.
Depends on: `7sketches:7.5.1:def-interval-domain` — the space these sheaves live on.
Depends on: `7sketches:7.3.3:construction-sections-sheaf` — the continuous-sections construction that Examples 7.79 and Exercise 7.80 instantiate.
Depends on: #259 — the category `Top` and continuity.

<!-- catalog: {"ids":["7sketches:7.5.2:example7.78","7sketches:7.5.2:example7.79","7sketches:7.5.2:ex7.80"],"deps":["7sketches:7.3.3:def7.35","7sketches:7.5.1:def-interval-domain","7sketches:7.3.3:construction-sections-sheaf","#259"]} -->

---8<---

```yaml
title: "Seven Sketches 7.5.3: A behavior contract as a formula of the internal temporal logic"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:7.5.3:eq7.82]
deps_item_ids: [7sketches:7.4.6:eq7.73, 7sketches:7.4.5:def7.69, 7sketches:7.5.1:construction-behavior-types]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §7.5.3, display (7.82), printed p. 256 (PDF p. 268). Item `7sketches:7.5.3:eq7.82`.

## Background

The chapter's payoff: a safety guarantee — "within one second of the dials signalling a bad position the thrusters engage, and stay engaged for five seconds" — written as a single sentence of the internal language of the topos of behavior types, using the "holds near time `t`" modality; evaluating it against actual behaviors returns the open time-region on which the contract holds, so violations are recorded in the classifier. See the nLab on [temporal logic](https://ncatlab.org/nlab/show/temporal+logic) and Wikipedia on [temporal logic](https://en.wikipedia.org/wiki/Temporal_logic).

## Current state in the library

Every ingredient is missing.

- "Temporal" has exactly two hits, both prose (`Theory/Sheaf.v:94` in the Fong–Spivak citation, and a metaphor in `Construction/Funny/Swap.v`).
- The modality the formula depends on does not exist: `Lawvere-Tierney` appears once, as prose at `Structure/Topos.v:88` describing an idempotent finite-meet-preserving `j : Ω ⟶ Ω` that "cuts out the subtoposes", and no such `j` is ever defined. The "modal" hits are the linear-logic exponential-as-comonad prose in the comonad files.
- The formula also needs quantifiers over the reals and a topos-internal language, neither of which exists; `Solver/Expr.v:73` is the tree's only formal statement language and it is quantifier-free and modality-free (see this chapter's §7.4.6 issue for why it is not an instance of Kripke–Joyal semantics).

## Work to be done

New `Instance/Top/Interval/Contract.v`.

1. Define the "at `t`" modality on the classifier of the topos of behavior types: for a proposition `q`, `at_t q` asserts that `q` holds on some small enough neighborhood of `t`. Prove it is a modality in the sense of this chapter's §7.4.5 issue, and confirm the book's classification of it as an instance of clause (c) of Proposition 7.71 (relative double negation) — that classification is stated in the book without proof and is a genuine obligation here.
2. Fix two behavior types (a "dials" sheaf and a "thrusters" sheaf; the sheaves of locally constant or of locally continuous values from this chapter's §7.5.2 issue will serve) and two predicates on them: "the dials read a bad position" and "the thrusters are engaged".
3. Write display (7.82) as a formula of the internal language: for every real `t`, if `at_t` holds of the bad-dials proposition, then there is `r ∈ (0,1)` such that for every `r' ∈ (0,5)`, `at_{t+r+r'}` holds of the thrusters-engaged proposition. Interpret it via the Kripke–Joyal semantics of this chapter's §7.4.6 issue.
4. Prove the evaluation property that makes the contract useful: applied to a concrete pair of sections over a time period `U`, the formula's interpretation returns the open sub-region of `U` on which the contract holds — so a violation is recorded as a strictly smaller open, not as a bare `false`. Exhibit at least one pair of sections satisfying the contract on all of `U` and one violating it on a named sub-region.

In-tree donors: everything this chapter builds — the interval domain and behavior types (§7.5.1), the constant and continuous behavior sheaves (§7.5.2), the classifier of a sheaf topos (§7.4.1), modalities (§7.4.5) and the internal language (§7.4.6).

## Definition of Done

- [ ] The "at `t`" operator defined and proved a modality, and its identification as an instance of Proposition 7.71 clause (c) proved rather than assumed.
- [ ] Two behavior types and two predicates fixed, with the contract written as a single formula of the internal language.
- [ ] The interpretation computed, and the evaluation property proved: the formula returns the open region on which the contract holds.
- [ ] One satisfying and one violating pair of sections exhibited, with the violating region named.
- [ ] Statement fidelity to Seven Sketches display (7.82) (printed p. 256), including the quantifier ranges `r ∈ (0,1)` and `r' ∈ (0,5)`; setoid discipline — `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond stdlib axioms recorded in docs/AXIOMS.md for the `Instance/` layer.
- [ ] `Print Assumptions` closed (or explicitly enumerated) for each principal artifact.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is the applied capstone of the whole chapter and `Theory/Sheaf.v:91-94` currently cites it only as background.

## Verification

```bash
coqc -R . Category Instance/Top/Interval/Contract.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions at_t_Modality.
Print Assumptions contract_region.
```
Reviewer: statement matches Seven Sketches display (7.82) (printed p. 256) — the modality is proved to be one, and the contract's value is an open region rather than a truth value.

## Dependencies

Depends on: `7sketches:7.4.6:eq7.73` — the internal language and its semantics, in which the contract is a formula.
Depends on: `7sketches:7.4.5:def7.69` — the modality notion, of which "at `t`" must be shown an instance.
Depends on: `7sketches:7.5.1:construction-behavior-types` — the topos the contract is interpreted in.
Depends on: `7sketches:7.5.2:example7.78` — the behavior sheaves the contract's predicates live on.

<!-- catalog: {"ids":["7sketches:7.5.3:eq7.82"],"deps":["7sketches:7.4.6:eq7.73","7sketches:7.4.5:def7.69","7sketches:7.5.1:construction-behavior-types","7sketches:7.5.2:example7.78"]} -->

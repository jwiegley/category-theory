```yaml
title: "MacLane X.1: The formal criterion for the existence of an adjoint via comma-category limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.1:remark2, maclane:X.1:lem1, maclane:X.1:thm2, maclane:X.1:ex1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (Springer GTM 5), §X.1 "Adjoints and Limits", book pp. 233–235, PDF pp. 240–242. Items: `maclane:X.1:remark2` (initial object as a limit of the identity), `maclane:X.1:lem1` (Lemma 1: a limiting cone over the identity yields an initial object), `maclane:X.1:thm2` (Theorem 2: the formal criterion for a left adjoint), `maclane:X.1:ex1` (Exercise 1: the dual criterion for a right adjoint).

## Background

Mac Lane's "formal criterion" says a functor has a left adjoint exactly when it preserves the limits that exist and each comma category `x ↓ G` has a limit, in which case the value of the adjoint at `x` is that comma limit; the engine is the observation that an initial object is precisely the limit of the identity functor. See the nLab on the [adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem) and Wikipedia on [adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors). This is distinct from the solution-set (Freyd) form: it trades the solution set for the hypothesis that the individual comma limits exist.

## Current state in the library

The forward half is present. Right adjoints preserve limits (RAPL) is proven as `rapl_is_alimit` (`Adjunction/Continuity.v:183`), and its dual, that a functor with a right adjoint preserves colimits (LAPC), as `left_adjoint_preserves_colimits` (`Adjunction/Continuity.v:223`). The reverse assembly — universal arrows at every object give a left adjoint — exists as `AdjunctionFromUniversalArrows` (`Theory/Universal/Arrow.v:214`), and comma categories are complete when the base is, via `Comma_Complete` (`Construction/Comma/Limit.v:245`), though that requires full completeness of the base rather than the single comma limit Mac Lane's criterion (ii) assumes.

The distinctive content is missing. There is no lemma that a limiting cone over (a subdiagram of) the identity functor forces its apex to be initial — `Terminal_Limit` (`Structure/Limit/Terminal.v:33`) only equates a terminal object with the limit of the *empty* diagram (dually, an initial object with the colimit of the empty diagram), never with the limit of the whole identity functor. Consequently the construction of the adjoint as `F x = Lim(Q : (x ↓ G) → A)`, and the biconditional stated as a formal criterion, are absent; the only in-tree route to an adjoint is Freyd's theorem (issue #436), which needs a completeness-plus-solution-set hypothesis strictly stronger than criterion (ii). The dual (right-adjoint) direction has only its forward conjunct (LAPC); the right-adjoint-from-terminal-arrows assembly is not built (`Theory/Universal/Arrow.v` builds only the left-adjoint direction).

## Work to be done

- Prove Mac Lane's Lemma 1: given a cone `λ : d ⇒ Id_C` whose restriction along a functor `F` is a limiting cone for `F`, the apex `d` is initial in `C`; specialise to obtain `e ≅ Lim Id_C` when the limit of the identity exists. Suggested home: `Structure/Limit/Initial.v` (new) or an addition to `Structure/Initial.v`, using `Structure/Cone.v` and `Structure/Limit.v`.
- Instantiate the lemma in the comma category `x ↓ G` so that a limit of the comma projection `Q : (x ↓ G) → A` is an initial object of the comma, i.e. a universal arrow; then feed `AdjunctionFromUniversalArrows` (`Theory/Universal/Arrow.v:214`) to build the left adjoint with `F x = Lim(Q)`. Suggested home: `Adjunction/Formal.v` (new), building on `Construction/Comma.v`, `Construction/Comma/Limit.v`, and the RAPL lemma (`Adjunction/Continuity.v:183`) for the forward direction.
- State the biconditional: `G` has a left adjoint iff `G` preserves the limits that exist and each `x ↓ G` has a limit.
- Give the dual (Exercise 1): the right-adjoint criterion via colimits of `F ↓ c`, reusing the library's duality so the statement follows from the left case at the opposite categories; supply the missing right-adjoint-from-terminal-arrows assembly (dual of `AdjunctionFromUniversalArrows`).

## Definition of Done

- [ ] Statement matches Mac Lane §X.1 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the Lemma-1 lemma, the criterion theorem, and its dual
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Adjunction/Formal.v` (and the new limit/initial file) compiles from a clean tree.
- After `Require Import`, run `Print Assumptions` on the Lemma-1 lemma, the left-adjoint criterion, and its dual; confirm each reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the statement matches §X.1 Theorem 2 and Exercise 1 (comma-limit construction `F x = Lim(Q)`, not the solution-set form).

## Dependencies

None in-catalog. Related in-tree: Freyd's adjoint functor theorem (issue #436) is the stronger-hypothesis route already filed; RAPL/LAPC are present (`Adjunction/Continuity.v`).

<!-- catalog: {"ids":["maclane:X.1:remark2","maclane:X.1:lem1","maclane:X.1:thm2","maclane:X.1:ex1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.1: Formal criteria for representability and universal arrows (Bénabou)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.1:ex2, maclane:X.1:ex3, maclane:X.1:ex4]
deps_item_ids: [maclane:X.1:lem1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.1 "Adjoints and Limits", book p. 235, PDF p. 242. Items: `maclane:X.1:ex2` (Bénabou's criterion for representability), `maclane:X.1:ex3` (the criterion for a universal arrow), `maclane:X.1:ex4` (weakening the preservation hypothesis).

## Background

These exercises are the per-object companions of the formal adjoint criterion: a set-valued functor `K : C → Set` is representable exactly when it preserves the limits that exist and the comma category `* ↓ K` has a limit, and analogously a universal arrow from `x` to `G` exists exactly when `X(x, G−)` preserves limits and `x ↓ G` has a limit. See the nLab on [representable functor](https://ncatlab.org/nlab/show/representable+functor) and the [adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem). Exercise 4 sharpens both by observing that only preservation of the single comma limit is needed.

## Current state in the library

The bare notion of representability exists as `Representable` (`Functor/Representable.v:46`) and a universal arrow as `UniversalArrow` (`Theory/Universal/Arrow.v:127`, an initial object of the comma `=(c) ↓ F`), but neither existence *criterion* is stated. Crucially the forward conjunct — that a hom-functor / representable preserves the limits that exist — is not proven anywhere (`Functor/Hom.v` and `Functor/Hom/Yoneda.v` carry only the Yoneda material, no limit preservation), so even the "only if" halves are absent. The reverse construction (a limit of the comma projection is the initial object of the comma) is exactly the Lemma 1 that §X.1 Theorem 2 rests on and is likewise absent; `Comma_Complete` (`Construction/Comma/Limit.v:245`) builds all comma limits from full completeness of the base but never states the single-comma-limit existence criterion. The weakened-hypothesis refinements have no counterpart because the criteria they refine are not present.

## Work to be done

- Prove that a covariant hom-functor (and hence any representable) `C(x, G−) : A → Set` preserves the limits that exist in `A`; suggested home: `Functor/Hom/Continuity.v` (new) or an addition to `Functor/Hom.v`, using `Structure/Limit.v` and the cone-level preservation vocabulary of `Structure/Limit/Preservation.v`.
- State and prove the universal-arrow existence criterion (Exercise 3): a universal arrow from `x` to `G` exists iff `X(x, G−)` preserves the limits that exist and `x ↓ G` has a limit; obtain the representability criterion (Exercise 2) as the special case `G = K : C → Set`, `x = *` (a representation is a universal arrow from the one-point set). Reuse the Lemma-1 lifting supplied by the §X.1 formal-criterion issue. Suggested home: `Adjunction/Formal.v` or `Structure/UniversalProperty/Representable.v` (new).
- Prove Exercise 4: in both criteria the "preserves all limits that exist" hypothesis may be weakened to "preserves the particular limit of the comma projection".

## Definition of Done

- [ ] Statement matches Mac Lane §X.1 Exercises 2–4 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the hom-functor-preserves-limits lemma and both criteria
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category` on the new hom-continuity and criterion files compiles from a clean tree.
- `Print Assumptions` on the representability criterion and the universal-arrow criterion reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the statements match §X.1 Exercises 2, 3, 4 and that Exercise 2 is derived as the `* ↓ K` special case of Exercise 3.

## Dependencies

Depends on: maclane:X.1:lem1

<!-- catalog: {"ids":["maclane:X.1:ex2","maclane:X.1:ex3","maclane:X.1:ex4"],"deps":["maclane:X.1:lem1"]} -->

---8<---

```yaml
title: "MacLane X.1: The Bénabou collage of a set-valued functor and representability via a left adjoint"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.1:ex5]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.1 "Adjoints and Limits", book p. 235, PDF p. 242. Item: `maclane:X.1:ex5` (Bénabou: representability through a freely adjoined object).

## Background

Given `K : C → Set`, one forms a new category `C_K` by adjoining a single object `∞` whose incoming hom-sets are the values of `K` (`C_K(∞, c) = K c`), with `C_K(c, ∞)` empty and `C_K(∞, ∞)` a one-point set; the exercise is that `K` is representable exactly when the inclusion `J_K : C → C_K` has a left adjoint. This `C_K` is the collage (cograph) of the profunctor `K`; see the nLab on [representable functor](https://ncatlab.org/nlab/show/representable+functor) and Wikipedia on [representable functors](https://en.wikipedia.org/wiki/Representable_functor).

## Current state in the library

Nothing builds the collage of a functor: searches for a construction adjoining one object to a category with hom-sets supplied by a functor return no hits, and there is no "`K` representable iff `J_K` has a left adjoint" theorem. The ingredients exist separately — `Representable` (`Functor/Representable.v:46`), `Adjunction` (`Theory/Adjunction.v:130`), and profunctors `C ⇸ D := C^op ∏ D ⟶ Sets` (`Theory/Profunctor.v`) — but the collage category `C_K` (the collage of the profunctor `K : 1 ⇸ C`) and the equivalence are not present.

## Work to be done

- Construct the collage category `C_K` for `K : C → Sets`: objects are those of `C` plus a new terminal-ish object `∞`; hom-setoids are `C(a,b)` on the old objects, `K c` for `∞ → c`, empty for `c → ∞`, and a singleton for `∞ → ∞`, with composition given by the functorial action of `K`. Verify the category laws (associativity/identity as setoid equalities on morphisms). Suggested home: `Construction/Collage.v` (new), reusing `Instance/Sets.v` for the hom-setoids.
- Define the full inclusion `J_K : C → C_K`.
- Prove `K` is representable iff `J_K` has a left adjoint, exhibiting the representing object as the value of the adjoint at `∞`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.1 Exercise 5 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the collage category and the representability equivalence
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Construction/Collage.v` compiles from a clean tree.
- `Print Assumptions` on the collage category and the `K` representable ⇔ `J_K` left adjoint theorem reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the collage hom-sets match §X.1 Exercise 5 and the equivalence is proved both ways.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:X.1:ex5"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.2: Weak universal arrows and weak (co)limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.2:def1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.2 "Weak Universality", book p. 235, PDF p. 242. Item: `maclane:X.2:def1` (weak universal arrow, weak product, weak limit, weak coproduct).

## Background

A weak universal arrow is a universal arrow with existence but not uniqueness of the mediating map: from `x` to `G` it is a pair `⟨r, w : x → G r⟩` such that every `f : x → G a` factors (not necessarily uniquely) as `G f' ∘ w`; dropping uniqueness likewise yields weak limits, weak products, and weak coproducts. See the nLab on [weak limit](https://ncatlab.org/nlab/show/weak+limit) and [weakly initial object](https://ncatlab.org/nlab/show/weakly+initial+object). These support §X.2's second proof of Freyd's initial-object existence theorem.

## Current state in the library

Only the weakly-initial-set case is formalised: `WeaklyInitialFamily` (`Theory/WeaklyInitial.v:58`) packages an index type, a family of objects, and for every object a chosen — not unique — covering arrow, which is precisely the weak-universality notion specialised to initial objects and bundled as a family. The general weak universal arrow for an arbitrary functor `G` (the drop-uniqueness weakening of `UniversalArrow`, `Theory/Universal/Arrow.v:127`) is not defined, and neither weak product, weak limit, nor weak coproduct exists anywhere in the tree. (§X.2's main theorem, that a weakly-initial family yields an initial object, is already present as `initial_from_weakly_initial`, `Theory/WeaklyInitial.v:89`, and needs no work.)

## Work to be done

- Define a weak universal arrow from an object to a functor as the existence-only weakening of `UniversalArrow` (`Theory/Universal/Arrow.v`), i.e. an arrow `w : x → G r` through which every `f : x → G a` factors, without a uniqueness field. Suggested home: `Theory/Universal/Weak.v` (new) or an addition to `Theory/Universal/Arrow.v`.
- Define weak limits and weak colimits as cones/cocones with a (not-necessarily-unique) mediating map, and weak products / weak coproducts as their discrete-diagram instances; suggested home: `Structure/Limit/Weak.v` (new), reusing `Structure/Cone.v`, `Structure/Limit.v`.
- Relate the weakly-initial family (`Theory/WeaklyInitial.v`) to the general weak-universal notion as a sanity check.

## Definition of Done

- [ ] Statement matches Mac Lane §X.2 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the weak-universal-arrow and weak-(co)limit definitions and any lemmas
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category` on the new weak-universal and weak-limit files compiles from a clean tree.
- `Print Assumptions` on the weak universal arrow, weak limit, and weak product definitions reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the definitions match §X.2 (existence without uniqueness) and that the existing weakly-initial family is exhibited as an instance.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:X.2:def1"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.3: The pointwise (co)limit formula for Kan extensions"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.3:thm1, maclane:X.3:def2]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.3 "The Kan Extension", book pp. 237–240, PDF pp. 244–247. Items: `maclane:X.3:thm1` (Theorem 1: right Kan extension as a pointwise limit over the comma category) and `maclane:X.3:def2` (the dual pointwise colimit formula for the left Kan extension).

## Background

The pointwise formula computes a right Kan extension `Ran_K T` at `c` as the limit of `T` over the comma category `c ↓ K` (dually the left extension `Lan_K T` at `c` as the colimit of `T` over `K ↓ c`), together with the induced functoriality and the counit read off the identity component. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and Wikipedia on [Kan extension](https://en.wikipedia.org/wiki/Kan_extension). This is the concrete construction underlying every existence and pointwise result in the chapter.

## Current state in the library

The abstract Kan extensions are present as adjoints of precomposition — `Induced` (`Theory/Kan/Extension.v:127`), `RightKan`/`LeftKan` (`:140`/`:222`), with the local universal properties `LocalRightKan` (`:154`) and `LocalLeftKan` (`:234`) — and the definitional core of the left extension is complete. The pointwise (co)limit *formula* is not built. The only bridge to limits is `Kan_Limit` (`Structure/Limit/Kan/Extension.v:46`), which handles only `K = ` the terminal functor `Erase J : J → 1` and only in the identification direction (assume both a limit and a `RightKan` exist, then equate them) — this is really the §X.7 "limit is a Kan extension" content, not §X.3's construction of the extension from comma limits. There is no general functor `R` with `R c := Lim(c ↓ K)`, no proof of its functoriality, and no counit `ε_n = λ_{1_{K n}}`; on the left side there is no colimit formula at all (no `Kan_Colimit`, and `Structure/Limit/Kan/Extension.v` contains only `Kan_Limit`). The header of `Theory/Kan/Extension.v` explicitly flags the comma-category (co)limit formulas as "a bridge not yet formalized".

## Work to be done

- Construct, for `K : M → C` and `T : M → A` such that each `T ∘ Q` over `c ↓ K` has a limit, the object assignment `R c := Lim(c ↓ K)`, prove it extends to a functor `R : C → A` (the mediating arrows between limits), and read off the counit `ε : R ∘ K ⇒ T` from the identity components; prove `⟨R, ε⟩` is the right Kan extension (i.e. inhabits `LocalRightKan T`). Suggested home: `Structure/Limit/Kan/Pointwise.v` (new), extending `Structure/Limit/Kan/Extension.v` and reusing `Construction/Comma.v`, `Structure/Cone.v`, `Structure/Limit.v`.
- Dually build the pointwise colimit formula `L c := Colim(K ↓ c)` inhabiting `LocalLeftKan T`, closing the gap in the left-extension item (its universal-property core is already present; only the colimit formula is missing).
- Prove the counit/unit components match the abstract `ran_transform` / `lan_transform` up to the setoid equivalence.

## Definition of Done

- [ ] Statement matches Mac Lane §X.3 Theorem 1 and the dual (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the pointwise `Ran` and `Lan` constructions
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship Kan-extension result)

## Verification

- `coqc -R . Category Structure/Limit/Kan/Pointwise.v` compiles from a clean tree.
- `Print Assumptions` on the pointwise `Ran` and `Lan` constructions reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms `R c ≅ Lim(c ↓ K)` and `L c ≅ Colim(K ↓ c)` with the counit/unit read off the identity components, matching §X.3.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:X.3:thm1","maclane:X.3:def2"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.3: Existence of Kan extensions from completeness and the global adjoint to precomposition"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.3:cor2, maclane:X.3:remark1]
deps_item_ids: [maclane:X.3:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.3 "The Kan Extension", book pp. 237, 239, PDF pp. 244, 246. Items: `maclane:X.3:cor2` (Corollary 2: existence of all right Kan extensions when `M` is small and `A` complete) and `maclane:X.3:remark1` (the pointwise extensions assemble into a right adjoint of precomposition).

## Background

When the diagram category is small and the target complete, the pointwise limit formula produces a right Kan extension for every `T`, and these assemble into an honest right adjoint `Ran_K` of the precomposition functor `A^K`, with the universal counit as the counit of the adjunction. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension). This is the existence theorem behind treating `Ran_K` as a functor.

## Current state in the library

The global adjoint `RightKan := { Ran : [A,C] ⟶ [B,C]; ran_adjoint : Induced ⊣ Ran }` (`Theory/Kan/Extension.v:140`) posits the right adjoint of precomposition as a primitive, and `RightKan_to_LocalRightKan` (`Theory/Kan/Extension.v:180`) derives the pointwise (local) extensions *from* it — the reverse of the remark's direction. No instance of the `RightKan` class is ever constructed from a completeness or "`M` small" hypothesis (the only inhabitants tree-wide are the global-to-local converters), so there is no existence theorem, and the local-to-global assembly (from all pointwise extensions to the global adjoint) is not formalised. The general local-to-global machinery `AdjunctionFromUniversalArrows` (`Theory/Universal/Arrow.v:214`) exists but is not wired to the Kan classes.

## Work to be done

- Prove Corollary 2: if `M` is small and `A` is complete (`Structure/Complete.v`), the pointwise limit formula supplies a right Kan extension of every `T : M → A` along any `K`, hence a `LocalRightKan T` at each `T`. Suggested home: `Structure/Limit/Kan/Existence.v` (new), consuming the pointwise construction and `Structure/Complete.v`.
- Prove the remark: assemble the family of pointwise right Kan extensions into a global right adjoint `Induced ⊣ Ran` (an instance of `RightKan`), with the pointwise counits as the adjunction counit — connecting the Kan classes to `AdjunctionFromUniversalArrows` (`Theory/Universal/Arrow.v`).
- Dually record the left version (colimits, `Lan`) where the base is cocomplete.

## Definition of Done

- [ ] Statement matches Mac Lane §X.3 Corollary 2 and the adjoint remark (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the existence corollary and the global-adjoint assembly
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Structure/Limit/Kan/Existence.v` compiles from a clean tree.
- `Print Assumptions` on the existence corollary and the `RightKan` instance reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the existence hypotheses (`M` small, `A` complete) and that the assembled `Ran` is a genuine right adjoint of `Induced`, matching §X.3.

## Dependencies

Depends on: maclane:X.3:thm1

<!-- catalog: {"ids":["maclane:X.3:cor2","maclane:X.3:remark1"],"deps":["maclane:X.3:thm1"]} -->

---8<---

```yaml
title: "MacLane X.3: Fully faithful K — an invertible Kan counit and extension along an inclusion"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.3:cor3, maclane:X.3:cor4, maclane:X.3:ex4]
deps_item_ids: [maclane:X.3:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.3 "The Kan Extension", book pp. 239–240, PDF pp. 246–247. Items: `maclane:X.3:cor3` (Corollary 3: a full and faithful `K` makes the counit invertible), `maclane:X.3:cor4` (Corollary 4: the extension genuinely extends `T` along a full-subcategory inclusion), `maclane:X.3:ex4` (Ulmer: weakening "full and faithful" to "full and as faithful as `T`").

## Background

When `K` is full and faithful the identity `1_{K n}` is initial in the comma `K n ↓ K`, so the pointwise limit is attained there and the Kan counit `ε : R K ⇒ T` is a natural isomorphism; hence along a full-subcategory inclusion the right Kan extension is an actual extension (`R K = T`). See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension). Ulmer's refinement relaxes faithfulness of `K` to "as faithful as `T`".

## Current state in the library

Nothing ties full-and-faithfulness of the along-functor to invertibility of a Kan counit: the general "fully faithful reflects isomorphisms" lemmas (`Theory/Functor.v:349`, `Theory/Equivalence/Limit.v:296`) concern functors reflecting isos, not the counit `ran_transform` of a Kan extension, which carries no full/faithful hypothesis (`Theory/Kan/Extension.v`). Corollary 4 (an extension `R` with `R K = T` along an inclusion) and the Ulmer weakening are absent a fortiori, since Corollary 3 and the underlying comma-category argument are not present.

## Work to be done

- Prove Corollary 3: for a full and faithful `K`, the pointwise right Kan extension's counit `ε : R ∘ K ⇒ T` is a natural isomorphism, via `1_{K n}` being initial in `K n ↓ K`. Suggested home: `Structure/Limit/Kan/FullyFaithful.v` (new), building on the pointwise construction and `Theory/Functor.v` (fullness/faithfulness).
- Prove Corollary 4: for `M` a full subcategory of `C`, the right Kan extension along the inclusion is an actual extension (`R ∘ K ≅ T` with identity counit).
- Prove Exercise 4 (Ulmer): the invertible-counit conclusion still holds when "`K` faithful" is weakened to "`K h = K h'` implies `T h = T h'`" ("`K` as faithful as `T`").

## Definition of Done

- [ ] Statement matches Mac Lane §X.3 Corollaries 3–4 and Exercise 4 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the invertible-counit corollary, the inclusion-extension corollary, and the Ulmer variant
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Structure/Limit/Kan/FullyFaithful.v` compiles from a clean tree.
- `Print Assumptions` on the three results reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the counit is exhibited as a natural isomorphism (setoid `≈`) and the "as faithful as `T`" hypothesis matches §X.3 Exercise 4.

## Dependencies

Depends on: maclane:X.3:thm1

<!-- catalog: {"ids":["maclane:X.3:cor3","maclane:X.3:cor4","maclane:X.3:ex4"],"deps":["maclane:X.3:thm1"]} -->

---8<---

```yaml
title: "MacLane X.3: Kan extensions between sets — images, representables, and non-existence"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.3:ex1, maclane:X.3:ex2, maclane:X.3:ex3]
deps_item_ids: [maclane:X.3:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.3 "The Kan Extension", book p. 240, PDF p. 247. Items: `maclane:X.3:ex1` (Kan extensions of subsets as direct image / coimage), `maclane:X.3:ex2` (left Kan extension of a representable is representable), `maclane:X.3:ex3` (non-existence along a non-surjective set map).

## Background

These worked examples pin down Kan extensions in familiar settings: a functor into the arrow category `2` is a subset, and its left Kan extension along a function of sets is the direct image `K[T]` (dually the coimage for the right extension); the left Kan extension of the representable `M(m,−)` along `K` is the representable `C(K m, −)` with unit determined by `η(m) = 1_{K m}`; and for functions of sets a Kan extension can fail to exist when `K` is not surjective. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [representable functor](https://ncatlab.org/nlab/show/representable+functor).

## Current state in the library

No Kan extension is ever computed for a functor valued in the arrow category `2` (`Instance/Two.v`), and there is no direct-image / power-set functor `2^M ≅ P(M)` in the tree. No result links representables to Kan extensions: `Functor/Hom.v` and `Functor/Representable.v` define representables, `Theory/Coend/Yoneda.v` gives co-Yoneda purely as coend/end isomorphisms, but none states `Lan_K M(m,−) ≅ C(K m,−)`. The library treats Kan extensions only as possibly-absent universal-property classes and never exhibits a case where one provably fails to exist. All three exercises are absent.

## Work to be done

- Show a functor `M → 2` is a subset of `M`, `2^M ≅ P(M)`, and compute `Lan_K T` as the direct image `K[T]` and `Ran_K T` as the coimage, for `K` a function of sets. Suggested home: `Instance/Sets/Kan.v` (new), using `Instance/Two.v`, the pointwise (co)limit formula, and the Set-level (co)products of `Instance/Sets.v`.
- Prove `Lan_K M(m,−) ≅ C(K m,−)` with unit fixed by `η(m) = 1_{K m}`, reusing `Functor/Hom.v` / `Functor/Representable.v`.
- Prove that for functions of sets with `|A| ≥ 2` and `K` not surjective, neither `Lan_K T` nor `Ran_K T` exists.

## Definition of Done

- [ ] Statement matches Mac Lane §X.3 Exercises 1–3 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping (Instance-layer axioms per docs/AXIOMS.md permitted)
- [ ] `Print Assumptions` reported for the direct-image computation, the representable computation, and the non-existence result (only the enumerated Instance-layer axioms, if any)
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Instance/Sets/Kan.v` compiles from a clean tree.
- `Print Assumptions` on the three results is inspected against docs/AXIOMS.md (Instance-layer axioms only).
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the direct-image and representable identities and the non-existence counterexample match §X.3 Exercises 1–3.

## Dependencies

Depends on: maclane:X.3:thm1

<!-- catalog: {"ids":["maclane:X.3:ex1","maclane:X.3:ex2","maclane:X.3:ex3"],"deps":["maclane:X.3:thm1"]} -->

---8<---

```yaml
title: "MacLane X.4: Kan extensions as (co)ends — the pointwise coend and end formulas"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.4:thm1, maclane:X.4:thm2, maclane:X.4:remark1, maclane:X.4:ex1, maclane:X.7:ex2]
deps_item_ids: [maclane:X.3:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.4 "Kan Extensions as Coends" (and §X.7 Exercise 2), book pp. 240–243, 250, PDF pp. 247–250, 257. Items: `maclane:X.4:thm1` (Theorem 1: `Lan_K T` as a coend of copowers), `maclane:X.4:thm2` (Theorem 2: the unit of that coend extension), `maclane:X.4:remark1` (the dual end-of-powers formula for `Ran_K T`), `maclane:X.4:ex1` (the coend agrees with the comma-colimit formula), `maclane:X.7:ex2` (recover the Yoneda Lemma from the `Ran_K` end formula).

## Background

Kelly's (co)end formulas present the left Kan extension pointwise as `(Lan_K T) c = ∫^m C(K m, c) · T m` (a coend of copowers) and the right extension as `(Ran_K T) c = ∫_m T m ^ C(c, K m)` (an end of powers), with the unit built from a copower coprojection followed by the coend wedge. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension), [end](https://ncatlab.org/nlab/show/end), and [copower](https://ncatlab.org/nlab/show/copower). Specialising the `Ran` end formula at `K = Id` reproduces the Yoneda Lemma.

## Current state in the library

The pieces exist separately but are not connected. The end/coend calculus is present (`Structure/End.v` — `End:35`, `Coend:58`; `Instance/Sets/End.v`, `Instance/Sets/Coend.v`) and the abstract Kan extension is built through an adjunction (`Theory/Kan/Extension.v`), but no theorem equates a Kan extension with a (co)end — the header of `Theory/Kan/Extension.v` calls this "a bridge not yet formalized", and `Structure/Coend.v` describes the pointwise-`Lan` coend as the presentation the adjunction route "instead" avoids. Copowers `C(K m, c) · T m` are not defined (issue #321, powers and copowers, supplies them), so the very integrand cannot yet be formed in a general target. `Construction/Day.v` realises one coend that is mathematically a `Lan` (Day convolution) but its header states it "does not prove the universal property itself". The Yoneda-recovery is present only in the degenerate `K = Id` end form (`yoneda_reduction`, `Theory/Coend/Yoneda.v:297`); the general `Ran_K` end formula that §X.7 Exercise 2 asks to specialise is absent.

## Work to be done

- Using copowers/powers (issue #321) and the coend calculus (`Structure/Coend.v`, `Structure/End.v`), prove `(Lan_K T) c ≅ ∫^m C(K m, c) · T m` and, dually, `(Ran_K T) c ≅ ∫_m T m ^ C(c, K m)`, each holding exactly when the indicated (co)end exists. Suggested home: `Structure/Coend/Kan.v` (new).
- Construct the unit of the coend `Lan` as the copower coprojection at `f = 1_{K n}` followed by the coend wedge component (Theorem 2).
- Prove Exercise 1: when the coends exist they realise the comma-category colimits of the pointwise formula, so the two presentations of `Lan_K` agree.
- Derive §X.7 Exercise 2: obtain the Yoneda Lemma from the general `Ran_K` end formula, independent of the §X.3 argument (the `K = Id` case already exists as `yoneda_reduction`, `Theory/Coend/Yoneda.v:297`).

## Definition of Done

- [ ] Statement matches Mac Lane §X.4 Theorems 1–2, the end remark, Exercise 1, and §X.7 Exercise 2 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the coend `Lan` formula, the end `Ran` formula, the unit, and the Yoneda recovery
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (this is a flagship Kan/coend bridge)

## Verification

- `coqc -R . Category Structure/Coend/Kan.v` compiles from a clean tree.
- `Print Assumptions` on the coend/end formulas, the unit, and the Yoneda-recovery result reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the (co)end formulas and unit match §X.4 and that the Yoneda Lemma is derived from the `Ran_K` end formula (§X.7 Exercise 2).

## Dependencies

Depends on: #321
Depends on: maclane:X.3:thm1

<!-- catalog: {"ids":["maclane:X.4:thm1","maclane:X.4:thm2","maclane:X.4:remark1","maclane:X.4:ex1","maclane:X.7:ex2"],"deps":["#321","maclane:X.3:thm1"]} -->

---8<---

```yaml
title: "MacLane X.4: Kan extensions as (co)ends in the functor category (Ulmer; Day–Kelly)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.4:ex4, maclane:X.4:ex5]
deps_item_ids: [maclane:X.4:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.4 "Kan Extensions as Coends", book p. 243, PDF p. 250. Items: `maclane:X.4:ex4` (Ulmer; Day–Kelly: `Lan_K T` as a coend interpreted in `A^C`) and `maclane:X.4:ex5` (Ulmer: the dual end condition for `Ran_K T`).

## Background

These exercises lift the (co)end formulas into the functor category: `⟨m', m⟩ ↦ C(K m', −) · T m` is a bifunctor `M^op × M → A^C`, and `T` has a left Kan extension along `K` exactly when this bifunctor has a coend in `A^C`, with `Lan_K T = ∫^m C(K m, −) · T m`; the dual gives a necessary-and-sufficient end condition for `Ran_K T`. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [coend](https://ncatlab.org/nlab/show/coend).

## Current state in the library

The coend calculus (`Structure/Coend.v`, `Instance/Sets/Coend.v`) exists but is never applied to Kan extensions, and copowers `C(K m', c) · T m` are not defined (issue #321), so the integrand bifunctor cannot be formed. There is no statement of `Lan_K T` (or `Ran_K T`) as a (co)end in the functor category `A^C`, and no existence-iff criterion in those terms. `Construction/Day.v` builds one such coend directly but does not prove it is a Kan extension.

## Work to be done

- Show `⟨m', m⟩ ↦ C(K m', −) · T m` is a functor `M^op × M → A^C` (copowers from issue #321, functor category from `Instance/Fun.v`).
- Prove `T` has a left Kan extension along `K` iff this bifunctor has a coend in `A^C`, and then `Lan_K T = ∫^m C(K m, −) · T m`, describing the universal arrow via the coend. Suggested home: `Structure/Coend/Kan.v` (extending the pointwise (co)end file).
- Prove the dual (Exercise 5): the necessary-and-sufficient end condition for the existence of `Ran_K T`, with `Ran_K T = ∫_m T m ^ C(−, K m)` in `A^C`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.4 Exercises 4–5 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the `A^C` coend/end characterisations
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Structure/Coend/Kan.v` compiles from a clean tree.
- `Print Assumptions` on the functor-category coend/end characterisations reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the bifunctor, the existence-iff, and the `A^C` (co)end formulas match §X.4 Exercises 4–5.

## Dependencies

Depends on: #321
Depends on: maclane:X.4:thm1

<!-- catalog: {"ids":["maclane:X.4:ex4","maclane:X.4:ex5"],"deps":["#321","maclane:X.4:thm1"]} -->

---8<---

```yaml
title: "MacLane X.4: Additive (Ab-enriched) Kan extensions via cotensor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.4:construction1]
deps_item_ids: [maclane:X.4:remark1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.4 "Kan Extensions as Coends", book p. 242, PDF p. 249. Item: `maclane:X.4:construction1` (the additive right Kan extension via the cotensor).

## Background

Over `Ab`-categories the Kan bijection is required to be natural in additive functors, giving an `Ab`-enriched right Kan extension `R'` that generally differs from the ordinary one; it is computed by the end formula with the set-power replaced by the cotensor `c^C` defined by `A(b, c^C) ≅ Ab(C, A(b, c))`. See the nLab on [enriched category](https://ncatlab.org/nlab/show/enriched+category) and [weighted limit](https://ncatlab.org/nlab/show/weighted+limit). This is the `V = Ab` case of the enriched Kan extension.

## Current state in the library

There is no enriched Kan extension and no cotensor anywhere in the tree: the abstract Kan extension (`Theory/Kan/Extension.v`) is `Cat`/`Set`-enriched, and `Construction/Enriched/` (Compose, Fun, Natural, Sets, Two) carries enriched functors and transformations but no Kan/cotensor/weighted machinery. `Ab`-categories are available (`Structure/Preadditive.v`, `Structure/Additive.v`, `Instance/CMon.v`), but the additive Kan bijection and the cotensor `A(b, c^C) ≅ Ab(C, A(b, c))` are absent.

## Work to be done

- Define the cotensor of an object by a hom-object in a `Preadditive`/`Ab`-category via the natural adjunction `A(b, c^C) ≅ Ab(C, A(b, c))`. Suggested home: `Construction/Enriched/Cotensor.v` (new), reusing `Structure/Preadditive.v`.
- Define the additive right Kan extension as the additive functor with the Kan bijection natural over additive functors, computed by the end formula with power replaced by cotensor; contrast it with the ordinary right Kan extension. Suggested home: `Construction/Enriched/Kan.v` (new), reusing the end formula and `Construction/Enriched.v`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.4 (the additive Kan construction, paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the cotensor and the additive Kan extension
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Construction/Enriched/Cotensor.v Construction/Enriched/Kan.v` compiles from a clean tree.
- `Print Assumptions` on the cotensor and the additive Kan extension reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the cotensor adjunction and the additive Kan bijection match §X.4.

## Dependencies

Depends on: maclane:X.4:remark1

<!-- catalog: {"ids":["maclane:X.4:construction1"],"deps":["maclane:X.4:remark1"]} -->

---8<---

```yaml
title: "MacLane X.4: Left derived functors as a right Ab-enriched Kan extension"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.4:remark2]
deps_item_ids: [maclane:X.4:construction1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.4 "Kan Extensions as Coends", book p. 242, PDF pp. 249–250. Item: `maclane:X.4:remark2` (left derived functors packaged as a right `Ab`-Kan extension).

## Background

The left derived functors `T_n` of a right-exact functor form a connected (delta) sequence with a universal property; they can be packaged as a single additive functor `T_*` on an `Ext`-graded `Ab`-category `E` (objects `⟨C, n⟩`, hom-groups `Ext^{n-m}(C, B)` under the Yoneda product), and `T_*` is then the right `Ab`-Kan extension of `T = T_0` along an embedding, with identity unit. See Wikipedia on [derived functor](https://en.wikipedia.org/wiki/Derived_functor) and the nLab on [derived functor](https://ncatlab.org/nlab/show/derived+functor). This is an advanced application requiring a homological-algebra apparatus.

## Current state in the library

None of the apparatus exists: searches for derived functors, `Ext`/`Tor`, projective resolutions, connected/universal sequences, or an `Ext`-graded category return only background-essay prose (paper titles, historical remarks) — there are no such definitions in the `.v` tree. The nearest filed homological infrastructure is chain complexes and homology objects (issue #557). Together with the absence of the additive Kan extension itself, this example has no in-tree counterpart.

## Work to be done

This is a large, advanced item. It requires, in order:
- a homological-algebra apparatus — projective resolutions, left derived functors `T_n` of a right-exact functor, and their universal (connected/delta-sequence) property — built on the abelian-category spine (`Structure/Abelian.v`) and chain complexes (issue #557); the `Ext` bifunctor with the Yoneda product;
- the `Ext`-graded `Ab`-category `E` with objects `⟨C, n⟩` and hom-groups `Ext^{n-m}(C, B)`;
- the packaging of `{T_n}` as one additive functor `T_* : E → Ab`, exhibited as the right `Ab`-Kan extension of `T_0` along the embedding `Ab`-category `↪ E`, with identity unit.
Suggested home: `Structure/Abelian/Derived.v` and `Structure/Abelian/Ext.v` (new), with the Kan step in `Construction/Enriched/Kan.v`. The homological prerequisites are not yet cataloged as their own issues and are the bulk of the effort; scope them here or split them out during implementation.

## Definition of Done

- [ ] Statement matches Mac Lane §X.4 (derived functors as a right `Ab`-Kan extension, paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the derived-functor packaging and the Kan identification
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship if the homological apparatus lands)

## Verification

- `coqc -R . Category` on the new derived-functor / Ext / Kan files compiles from a clean tree.
- `Print Assumptions` on `T_*` and its Kan-extension identification reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the `Ext`-graded category, the connected-sequence universal property, and the `Ab`-Kan identification match §X.4.

## Dependencies

Depends on: maclane:X.4:construction1
Depends on: #557

<!-- catalog: {"ids":["maclane:X.4:remark2"],"deps":["maclane:X.4:construction1","#557"]} -->

---8<---

```yaml
title: "MacLane X.4: Composition of right Kan extensions (Dubuc)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.4:ex3]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.4 "Kan Extensions as Coends", book p. 243, PDF p. 250. Item: `maclane:X.4:ex3` (Dubuc: composition/pasting of right Kan extensions along composed functors).

## Background

Dubuc's law: given that `Ran_K T` exists and `L : C → D` is any functor, `Ran_{L K} T` exists iff `Ran_L(Ran_K T)` exists, and then the two — with their universal arrows — coincide; i.e. right Kan extensions compose, `Ran_L ∘ Ran_K = Ran_{L∘K}`. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension).

## Current state in the library

No composition/pasting lemma for Kan extensions exists: there is no statement relating `Ran` along `L ∘ K` to the iterate `Ran_L ∘ Ran_K`. `Theory/Kan/Extension.v` carries only the abstract classes and their local/global conversions, and `Structure/Limit/Kan/Extension.v` only `Kan_Limit`; the name "Dubuc" appears in the tree solely in the adjoint-triangle context (`Monad/Lifting.v`), unrelated.

## Work to be done

- Prove that if `Ran_K T` exists then, for any `L`, `Ran_{L K} T` exists iff `Ran_L(Ran_K T)` exists, and in that case the two extensions and their universal counits agree. Work through the universal property of `LocalRightKan` (`Theory/Kan/Extension.v:154`). Suggested home: `Theory/Kan/Compose.v` (new), reusing `Theory/Kan/Extension.v`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.4 Exercise 3 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the composition law
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Theory/Kan/Compose.v` compiles from a clean tree.
- `Print Assumptions` on the composition law reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the existence-iff and the agreement of universal arrows match §X.4 Exercise 3.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:X.4:ex3"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.5: Preservation of Kan extensions; right adjoints and representables preserve them"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.5:def1, maclane:X.5:thm1, maclane:X.5:cor2, maclane:X.5:ex1]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.5 "Pointwise Kan Extensions", book pp. 243–245, PDF pp. 250–252. Items: `maclane:X.5:def1` (preservation of a right Kan extension by a functor), `maclane:X.5:thm1` (Theorem 1: right adjoints preserve right Kan extensions), `maclane:X.5:cor2` (Corollary 2: representables preserve right Kan extensions), `maclane:X.5:ex1` (Exercise 1: the canonical comparison map and "preserves iff it is iso").

## Background

A functor `G` *preserves* a right Kan extension `⟨Ran_K T, ε⟩` when `⟨G ∘ Ran_K T, G ε⟩` is again a right Kan extension of `G T` along `K` — a condition strictly stronger than a bare isomorphism `G ∘ Ran_K T ≅ Ran_K(G T)`, because it tracks the counit; equivalently the canonical comparison map is invertible. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension). Right adjoints preserve right Kan extensions, and (having copower left adjoints) so do representables.

## Current state in the library

A preservation predicate exists but as the *weaker* bare-isomorphism notion: `preserves_right_Kan` (`Theory/Kan/Extension.v:313`) and `preserves_left_Kan` (`:307`) assert only `R ◯ Ran K G ≈ Ran K (R ◯ G)` for the global `Ran`, never that the whiskered counit `G ε` is the witnessing one, and they are quantified over the global adjoint classes (a "preserves all" predicate with no per-extension form). The key hom-iso ingredient is proven — `left_adjoint_impl` (`Theory/Kan/Extension.v:328`, `Qed`) is exactly `Nat(F H, L) ≅ Nat(H, G L)` — but the preservation theorem itself is not: `left_adjoints_preserve` (`Theory/Kan/Extension.v:386`) is abandoned (`admit` ×3, `Abort` at `:438`, so it is in no environment and adds no axioms). Representable preservation is absent (copowers, needed for the copower-left-adjoint-to-representable argument, come from issue #321), and the canonical comparison map `w` with `ε' · (w K) = G ε` and the equivalence "preserves iff `w` iso" are not constructed anywhere.

## Work to be done

- Strengthen the preservation predicate: define preservation of a *specified* (local) right Kan extension so that `⟨G ∘ Ran_K T, G ε⟩` is a right Kan extension of `G T`, tracking the counit — a predicate over `LocalRightKan` (`Theory/Kan/Extension.v:154`), not only the global bare-`≈` form. Replace or supplement the existing weak `preserves_right_Kan`.
- Prove Theorem 1: a functor with a left adjoint preserves right Kan extensions, discharging the three admitted obligations of the abandoned `left_adjoints_preserve` (`Theory/Kan/Extension.v:386`) and removing that `Abort`ed stub; use `left_adjoint_impl` (`:328`) and the RAPL toolkit (`Adjunction/Continuity.v`).
- Prove Corollary 2: each representable `A(a, −)` preserves right Kan extensions, via its copower left adjoint (issue #321).
- Prove Exercise 1: construct the canonical comparison `w : G ∘ Ran_K T ⇒ Ran_K(G T)`, prove it unique with `ε' · (w K) = G ε`, and prove `G` preserves `Ran_K T` iff `w` is an isomorphism.
Suggested home: `Theory/Kan/Preservation.v` (new) plus edits to `Theory/Kan/Extension.v`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.5 def, Theorem 1, Corollary 2, Exercise 1 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] The abandoned `left_adjoints_preserve` stub (`Theory/Kan/Extension.v:386`, `admit`×3 + `Abort` at `:438`) is replaced by a proved theorem (or removed)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the preservation predicate, Theorem 1, Corollary 2, and the comparison-map equivalence
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Theory/Kan/Preservation.v` and `Theory/Kan/Extension.v` compile from a clean tree.
- `grep -n 'admit\|Abort' Theory/Kan/Extension.v` shows the former `left_adjoints_preserve` stub is gone.
- `Print Assumptions` on Theorem 1, Corollary 2, and the comparison-map equivalence reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the preservation predicate is the counit-tracking (strong) form of §X.5, not the bare isomorphism.

## Dependencies

Depends on: #321

<!-- catalog: {"ids":["maclane:X.5:def1","maclane:X.5:thm1","maclane:X.5:cor2","maclane:X.5:ex1"],"deps":["#321"]} -->

---8<---

```yaml
title: "MacLane X.5: Pointwise Kan extensions and the comma-category limit criterion"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.5:def2, maclane:X.5:thm3, maclane:X.5:lem1, maclane:X.5:cor4]
deps_item_ids: [maclane:X.5:def1, maclane:X.3:thm1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.5 "Pointwise Kan Extensions", book pp. 244–245, PDF pp. 251–252. Items: `maclane:X.5:def2` (pointwise right Kan extension), `maclane:X.5:thm3` (Theorem 3: pointwise Kan extension exists iff the comma limits exist), `maclane:X.5:lem1` (the cone/natural-transformation bijection over the comma category), `maclane:X.5:cor4` (Corollary 4: pointwise Kan extension via a hom-set bijection).

## Background

A right Kan extension is *pointwise* when it is preserved by all representables `A(a, −)`; equivalently it exists (and is given by the §X.3 limit formula) exactly when each comma limit exists, and is characterised by the bijection `A(a, R c) ≅ Nat(C(c, K−), A(a, T−))`. See the nLab on [pointwise Kan extension](https://ncatlab.org/nlab/show/pointwise+Kan+extension) and [weighted limit](https://ncatlab.org/nlab/show/weighted+limit). Pointwise Kan extensions are the "honest" ones and underpin the density theory of §X.6.

## Current state in the library

"Pointwise" appears only in motivational prose (`Theory/Kan/Extension.v:74`, `Theory/DoubleCategory.v:140`); no predicate defines a pointwise Kan extension. `LocalRightKan` (`Theory/Kan/Extension.v:154`) is the bare universal-property notion, not Mac Lane's representably-preserved one, and the existence-iff via comma limits is absent (`Kan_Limit`, `Structure/Limit/Kan/Extension.v:46`, is only the terminal-functor special case). The cone bijection is not present: `Instance/Cones/Comma.v` gives the converse identification (cones over `F` as a comma category), and `Structure/Limit/Weighted.v` (`HomDiagram:49`, `WeightedLimit:101`) gives a structurally similar hom/`Nat` bijection for weighted limits, but neither is tied to the comma category `c ↓ K` of a Kan extension. The `A(a, R c) ≅ Nat(C(c, K−), A(a, T−))` characterisation is absent.

## Work to be done

- Define a pointwise right Kan extension as one preserved by every representable `A(a, −)` (using the strong preservation predicate from the §X.5 preservation issue). Suggested home: `Theory/Kan/Pointwise.v` (new).
- Prove Lemma 1: a bijection between cones from `a` to `T ∘ Q` over `c ↓ K` and natural transformations `C(c, K−) ⇒ A(a, T−)`; connect to `Structure/Limit/Weighted.v`.
- Prove Theorem 3: a pointwise right Kan extension exists iff each comma limit `Lim(c ↓ K)` exists, and is then given by the §X.3 limit formula (forward via representables preserving limits, converse via the cone bijection).
- Prove Corollary 4: `⟨R, ε⟩` is pointwise iff `A(a, R c) ≅ Nat(C(c, K−), A(a, T−))` for all `a, c`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.5 def, Lemma, Theorem 3, Corollary 4 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the pointwise definition, Theorem 3, and Corollary 4
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (pointwise Kan extensions are flagship-level)

## Verification

- `coqc -R . Category Theory/Kan/Pointwise.v` compiles from a clean tree.
- `Print Assumptions` on the pointwise definition, Theorem 3, and Corollary 4 reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the pointwise notion is "preserved by all representables" and the existence criterion matches §X.5 Theorem 3.

## Dependencies

Depends on: maclane:X.5:def1
Depends on: maclane:X.3:thm1

<!-- catalog: {"ids":["maclane:X.5:def2","maclane:X.5:thm3","maclane:X.5:lem1","maclane:X.5:cor4"],"deps":["maclane:X.5:def1","maclane:X.3:thm1"]} -->

---8<---

```yaml
title: "MacLane X.6: Dense and codense functors and the full-faithfulness (nerve) criteria"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.6:def1, maclane:X.6:def2, maclane:X.6:remark1, maclane:X.6:prop2, maclane:X.6:remark2, maclane:X.6:cor3, maclane:X.6:ex3, maclane:X.6:ex4]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.6 "Density", book pp. 245–247, PDF pp. 252–254. Items: `maclane:X.6:def1` (dense functor / dense subcategory), `maclane:X.6:def2` (codense functor), `maclane:X.6:remark1` (the one-point set is dense in Set), `maclane:X.6:prop2` (codense iff `c ↦ C(c, K−)` is full and faithful), `maclane:X.6:remark2` (dense iff `c ↦ C(K−, c)` is full and faithful), `maclane:X.6:cor3` (the Yoneda embedding is codense), `maclane:X.6:ex3` (density descends to the image subcategory `K M`), `maclane:X.6:ex4` (generators via faithfulness of `c ↦ C(K−, c)`).

## Background

A functor `K : M → C` is dense when every `c` is the colimit of the canonical diagram `K ↓ c → M → C` (codense dually via `c ↓ K`), equivalently when the nerve `c ↦ C(K−, c)` (resp. `c ↦ C(c, K−)`) is full and faithful; the one-point set is dense in Set and the Yoneda embedding is codense. See the nLab on [dense functor](https://ncatlab.org/nlab/show/dense+functor) and [dense subcategory](https://ncatlab.org/nlab/show/dense+subcategory). (This general notion generalises the set-valued density theorem already filed as issue #346.)

## Current state in the library

There is no density notion in the tree: `dense`/`codense`/`codensity` occur only as codensity-monad prose in the essay of `Theory/Kan/Extension.v`, and `grep -nwi dense` over the `.v` sources returns nothing. No canonical-colimit condition `c = Colim(K ↓ c)` is formalised. The nerve functors `c ↦ C(K−, c)` and `c ↦ C(c, K−)` for a general `K` are not defined; the only full-and-faithful hom-embedding is `Curried_Hom : C^op ⟶ [C, Sets]` (`Functor/Hom.v:60`, with `Yoneda_Faithful:85` / `Yoneda_Full:96`), i.e. the `K = Id` special case. The Yoneda engine (`Yoneda_Lemma`, `Functor/Hom/Yoneda.v:132`) is present but the codensity conclusion is a different theorem. No image-subcategory-of-a-functor construction exists, and there is no plain generator/separator notion (only the dual `Cogenerator`, `Adjunction/SAFT.v:99`).

## Work to be done

- Define dense and codense functors via the canonical (co)cone over `K ↓ c` / `c ↓ K` being (co)limiting, i.e. the canonical map `Colim(K ↓ c) → c` (resp. `c → Lim(c ↓ K)`) an isomorphism. Suggested home: `Theory/Kan/Density.v` (new), using `Construction/Comma.v`, `Structure/Cone.v`, `Structure/Limit.v`.
- Define the nerve `N_K : C → [M^op, Sets]`, `c ↦ C(K−, c)` (and the dual into `[M, Sets]`) via restricted Yoneda (`Functor/Hom.v`); prove Proposition 2 and its dual (density/codensity iff the nerve is full and faithful).
- Prove Corollary 3: the Yoneda embedding is codense (every `M → Ens` is a canonical limit of representables), from `Yoneda_Lemma`.
- Prove the example that the one-point set is dense in Set (`Instance/Sets.v` coproducts).
- Prove Exercise 3: density descends to the image subcategory `K M` (define the image subcategory of a functor).
- Prove Exercise 4: the objects of `M` generate `C` iff `c ↦ C(K−, c)` is faithful (define a generator/separating family, dual to `Cogenerator`).

## Definition of Done

- [ ] Statement matches Mac Lane §X.6 defs, Propositions/Corollary, Exercises 3–4 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the density/codensity definitions, the nerve criteria, and the Yoneda-codensity corollary
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (density is a flagship notion)

## Verification

- `coqc -R . Category Theory/Kan/Density.v` compiles from a clean tree.
- `Print Assumptions` on the dense/codense definitions, the nerve full-faithfulness criteria, and the Yoneda-codensity corollary reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the definitions match §X.6 and that Corollary 3 (Yoneda codense) is derived from the Yoneda Lemma.

## Dependencies

None in-catalog. Related: the set-valued density theorem is filed as issue #346 (a special case).

<!-- catalog: {"ids":["maclane:X.6:def1","maclane:X.6:def2","maclane:X.6:remark1","maclane:X.6:prop2","maclane:X.6:remark2","maclane:X.6:cor3","maclane:X.6:ex3","maclane:X.6:ex4"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.6: Density in Ab and in R-Mod"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.6:remark3, maclane:X.6:ex1, maclane:X.6:ex2]
deps_item_ids: [maclane:X.6:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.6 "Density", book p. 247, PDF p. 254. Items: `maclane:X.6:remark3` (finitely generated abelian groups, and the single object `ℤ⊕ℤ`, are dense in Ab), `maclane:X.6:ex1` (`R⊕R` is dense in R-Mod), `maclane:X.6:ex2` (the single object `ℤ` is not dense in Ab).

## Background

Concrete density facts: the full subcategory of finitely generated abelian groups is dense in Ab, and even the one-object subcategory on `ℤ⊕ℤ` suffices (because group operations are binary), whereas `ℤ` alone is not dense; dually `R⊕R` is dense in R-Mod. See the nLab on [dense subcategory](https://ncatlab.org/nlab/show/dense+subcategory) and Wikipedia on the [category of abelian groups](https://en.wikipedia.org/wiki/Category_of_abelian_groups).

## Current state in the library

Neither pillar is present. There is no density notion (see §X.6, above), and there is no concrete category Ab of abelian groups or R-Mod of modules: `Structure/Abelian.v` is the abstract abelian-category structure, `Structure/Group.v` is the group-object structure, and `Instance/CMon.v` is commutative monoids; `Instance/` lists no `Ab`, no `Mod`/`R-Mod`. The category Ab is filed as issue #256 and R-Mod as issue #258. The bijection `Ab(A, B) ≅ Nat(Ab(K−, A), Ab(K−, B))` has no counterpart.

## Work to be done

- Once the density notion (§X.6) and the concrete categories Ab (issue #256) and R-Mod (issue #258) are available, prove that the full subcategory of finitely generated abelian groups — and the one-object subcategory on `ℤ⊕ℤ` — is dense in Ab, via the bijection `Ab(A, B) ≅ Nat(Ab(K−, A), Ab(K−, B))` (injective because homomorphisms agreeing on cyclic subgroups agree, surjective by evaluating on maps out of `ℤ`).
- Prove `R⊕R` is dense in R-Mod.
- Prove the single object `ℤ` is not dense in Ab (a counterexample to density).
Suggested home: `Instance/Ab/Density.v` and `Instance/Module/Density.v` (new), on top of the density file.

## Definition of Done

- [ ] Statement matches Mac Lane §X.6 (density in Ab and R-Mod, paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping (Instance-layer axioms per docs/AXIOMS.md permitted)
- [ ] `Print Assumptions` reported for the density and non-density results (only the enumerated Instance-layer axioms, if any)
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Instance/Ab/Density.v Instance/Module/Density.v` compiles from a clean tree.
- `Print Assumptions` on the density and non-density results is inspected against docs/AXIOMS.md.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the `ℤ⊕ℤ` density, the `R⊕R` density, and the `ℤ` non-density match §X.6.

## Dependencies

Depends on: maclane:X.6:def1
Depends on: #256
Depends on: #258

<!-- catalog: {"ids":["maclane:X.6:remark3","maclane:X.6:ex1","maclane:X.6:ex2"],"deps":["maclane:X.6:def1","#256","#258"]} -->

---8<---

```yaml
title: "MacLane X.6: Density as a coend of copowers"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:X.6:ex5]
deps_item_ids: [maclane:X.6:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.6 "Density", book p. 247, PDF p. 254. Item: `maclane:X.6:ex5` (density as a coend of copowers).

## Background

When the copowers exist, `K : M → C` is dense exactly when every object is the coend `c = ∫^m C(K m, c) · K m`, with wedge `ω^c_m` sending the copower injection `i_f` to `f : K m → c`. See the nLab on [coend](https://ncatlab.org/nlab/show/coend) and [copower](https://ncatlab.org/nlab/show/copower). This is the coend form of the density condition.

## Current state in the library

Density is absent (see §X.6), and there is no copower `C(K m, c) · K m` (issue #321), so the biconditional cannot be stated. The coend calculus is available (`Structure/Coend.v` — `Coend`, `coend_obj`, `coend_inj`, `Build_Coend`), so the coend side of the formula could be written once density and copowers exist, but the equivalence is not present.

## Work to be done

- Prove `K` is dense iff each `c` is the coend `∫^m C(K m, c) · K m` with the wedge described above, using copowers (issue #321), the coend calculus (`Structure/Coend.v`), and the density notion (§X.6). Suggested home: `Theory/Kan/Density.v` (extending the density file) or `Structure/Coend/Density.v` (new).

## Definition of Done

- [ ] Statement matches Mac Lane §X.6 Exercise 5 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the coend characterisation of density
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category` on the density-coend file compiles from a clean tree.
- `Print Assumptions` on the coend characterisation reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the coend `c = ∫^m C(K m, c) · K m` and its wedge match §X.6 Exercise 5.

## Dependencies

Depends on: maclane:X.6:def1
Depends on: #321

<!-- catalog: {"ids":["maclane:X.6:ex5"],"deps":["maclane:X.6:def1","#321"]} -->

---8<---

```yaml
title: "MacLane X.7: Kan extensions along the identity and the terminal functor give functors and (co)limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.7:thm1, maclane:X.7:remark1, maclane:X.3:ex5]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.7 "All Concepts Are Kan Extensions" and §X.3, book pp. 240, 249, PDF pp. 247, 255–256. Items: `maclane:X.7:thm1` (Theorem 1: colimits are left Kan extensions along `M → 1`, limits are right Kan extensions), `maclane:X.7:remark1` (Kan extension along the identity is the identity), `maclane:X.3:ex5` (colimit as a left Kan extension along adjoining a terminal object).

## Background

Two degenerate Kan extensions: along the identity, `Lan_Id T = T` and `Ran_Id T = T`; along the unique functor `K_1 : M → 1` (or the inclusion `M ↪ M_∞`), the left Kan extension is the colimit of `T` and the right Kan extension the limit. See the nLab on [Kan extension](https://ncatlab.org/nlab/show/Kan+extension). These are the base cases of "all concepts are Kan extensions".

## Current state in the library

Only the limit half is present and only in the identification direction: `Kan_Limit` (`Structure/Limit/Kan/Extension.v:46`) states `Lim F ≅ Ran(Erase J) F ttt` given both a `Limit` and a global `RightKan`, where `Erase` (`Instance/One.v:47`) is the terminal functor `K_1`. There is no `Kan_Colimit` (the primary colimit-as-`Lan` direction has no theorem; `Colimit` exists by duality, `Structure/Limit.v:158`), no existence biconditional ("`F` has a colimit iff it has a `Lan` along `K_1`"), no local-Kan formulation, no `M_∞` construction, and no `Lan_Id/Ran_Id = Id` lemma (searches for Kan-along-identity return only unrelated hits, though it is trivial from the precomposition adjunction, `Induced` along `Id` being the identity functor).

## Work to be done

- Prove `Lan_Id T ≅ T` and `Ran_Id T ≅ T` (`Induced` along the identity is the identity functor, so its adjoints are the identity). Suggested home: `Theory/Kan/Extension.v` (addition) or `Structure/Limit/Kan/Extension.v`.
- Prove Theorem 1 as an existence biconditional: `T` has a colimit iff it has a left Kan extension along `Erase : M → 1`, and then `Colim T` is its value at the point; dually for limits (strengthen `Kan_Limit` from an identification to the existence-transfer, and add the colimit dual `Kan_Colimit`).
- Prove Exercise 5 (§X.3): construct `M_∞` (adjoin a terminal object) and show a colimiting cocone for `T` is exactly a left Kan extension of `T` along `M ↪ M_∞`, evaluated at the new object.
Suggested home: `Structure/Limit/Kan/Extension.v` and `Construction/Adjoin.v` (new, for `M_∞`).

## Definition of Done

- [ ] Statement matches Mac Lane §X.7 Theorem 1, the identity remark, and §X.3 Exercise 5 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for `Kan_Colimit`, the identity-Kan lemmas, and the `M_∞` characterisation
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

- `coqc -R . Category Structure/Limit/Kan/Extension.v Construction/Adjoin.v` compiles from a clean tree.
- `Print Assumptions` on `Kan_Colimit`, the identity-Kan lemmas, and the `M_∞` characterisation reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the colimit-as-`Lan` direction and the identity-Kan lemmas match §X.7 (and §X.3 Exercise 5).

## Dependencies

None.

<!-- catalog: {"ids":["maclane:X.7:thm1","maclane:X.7:remark1","maclane:X.3:ex5"],"deps":[]} -->

---8<---

```yaml
title: "MacLane X.7: The adjoint criterion via the Kan extension of the identity, and absolute Kan extensions"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.7:thm2, maclane:X.7:prop3, maclane:X.7:ex1]
deps_item_ids: [maclane:X.5:def1]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.7 "All Concepts Are Kan Extensions", book pp. 248–250, PDF pp. 255–257. Items: `maclane:X.7:thm2` (Theorem 2: `G` has a left adjoint iff `Ran_G 1_A` exists and is preserved by `G`, and then `F = Ran_G 1_A`), `maclane:X.7:prop3` (Proposition 3: a left adjoint yields an absolute right Kan extension `Ran_G 1_A = F`), `maclane:X.7:ex1` (Exercise 1: the §X.7 hom-bijection is a special case of the adjoint-square/mates bijection).

## Background

The capstone criterion: `G` has a left adjoint exactly when the right Kan extension of the identity along `G` exists and is preserved by `G`, in which case that extension *is* the left adjoint and its counit *is* the adjunction counit; conversely a left adjoint makes `Ran_G 1_A` absolute (preserved by every functor). See the nLab on [absolute Kan extension](https://ncatlab.org/nlab/show/absolute+Kan+extension) and [adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors). Exercise 1 places the underlying hom-bijection inside the mates ([mate](https://ncatlab.org/nlab/show/mate)) correspondence.

## Current state in the library

The Kan-extension form of the criterion is absent: `Ran_G 1_A` (the right Kan extension of the identity along a functor) is never instantiated, and no construction turns a preserved `Ran` into an adjunction. The one relevant attempt, `left_adjoints_preserve` (`Theory/Kan/Extension.v:386`), is `Abort`ed (three `admit`s, `Abort` at `:438`) and is only the "adjoint ⟹ preserves" half. The proven building block `left_adjoint_impl` (`Theory/Kan/Extension.v:328`, `Qed`) is a hom-iso *consequence* of an existing adjoint, not a criterion for one. "Absolute" occurs in the tree only for absolute colimits / split coequalizers (`Structure/Coequalizer/Split.v`, `Construction/Karoubi.v`), never for Kan extensions. The GAFT/SAFT machinery (`Adjunction/GAFT.v`) is the distinct comma-limit / solution-set criterion, not the Ran-of-identity form. The general mates bijection is present — `mate_iso` (`Theory/Bicategory/Mates.v:515`), unfolded in Cat as `Cat_mate_unfold` (`Instance/Cat/Bicategory/Adjunction.v:260`) — but §X.7's bijection is not exhibited as one of its instances.

## Work to be done

- Define an absolute right Kan extension (preserved by every functor), reusing the preservation predicate from the §X.5 preservation issue. Suggested home: `Theory/Kan/Absolute.v` (new).
- Prove Theorem 2: `G` has a left adjoint iff `Ran_G 1_A` exists and is preserved by `G`; when so, `F := Ran_G 1_A` is a left adjoint with the Kan counit as the adjunction counit (both directions, via the triangle identities and `left_adjoint_impl`). Suggested home: `Adjunction/Kan.v` (new).
- Prove Proposition 3: a left adjoint `F` with counit `ε` makes `Ran_G 1_A` exist, equal `F`, and be absolute.
- Prove Exercise 1: exhibit §X.7's hom-bijection as an instance of the adjoint-square/mates bijection `mate_iso` (issue #398), unfolding via `Cat_mate_unfold`.

## Definition of Done

- [ ] Statement matches Mac Lane §X.7 Theorem 2, Proposition 3, Exercise 1 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the absolute-Kan definition, Theorem 2, Proposition 3, and the mates instance
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the adjoint-as-Kan criterion is flagship-level)

## Verification

- `coqc -R . Category Theory/Kan/Absolute.v Adjunction/Kan.v` compiles from a clean tree.
- `Print Assumptions` on Theorem 2, Proposition 3, and the mates instance reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms `F = Ran_G 1_A` with the Kan counit as the adjunction counit, the absoluteness of Proposition 3, and the mates specialisation, matching §X.7.

## Dependencies

Depends on: maclane:X.5:def1
Depends on: #398

<!-- catalog: {"ids":["maclane:X.7:thm2","maclane:X.7:prop3","maclane:X.7:ex1"],"deps":["maclane:X.5:def1","#398"]} -->

---8<---

```yaml
title: "MacLane X.7: The codensity monad and codensity as Ran_K K"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:X.7:ex3, maclane:X.6:prop1]
deps_item_ids: [maclane:X.6:def1, maclane:X.5:def2]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §X.7 "All Concepts Are Kan Extensions" and §X.6, book pp. 246, 250, PDF pp. 253, 257. Items: `maclane:X.7:ex3` (the codensity monad of `K`) and `maclane:X.6:prop1` (Proposition 1: `K` is codense iff the identity is the pointwise `Ran_K K`).

## Background

If `K` has a right Kan extension `R = Ran_K K` along itself, then `⟨R, η, μ⟩` — with `η = φ^{-1}(1_K)` and `μ = φ^{-1}(ε · R ε)` — is a monad on `C`, the codensity monad of `K`; `K` is codense exactly when `η` is invertible (equivalently the identity is the pointwise `Ran_K K`), and for `G` with left adjoint `F` the codensity monad is `⟨G F, η, G ε F⟩`, the monad of the adjunction. See the nLab on [codensity monad](https://ncatlab.org/nlab/show/codensity+monad).

## Current state in the library

The codensity monad is absent: no monad is ever built on a right Kan extension (`Ran_K K` is never instantiated, though it is expressible via `LocalRightKan`/`RightKan`), and there is no dense/codense notion, so "codense iff `η` iso" is unstatable. The only present piece is the target monad of part (c): `Adjunction_Induced_Monad` (`Monad/Comparison.v:123`) builds `⟨U ∘ F, η, U ε F⟩` directly from an adjunction — exactly `⟨G F, η, G ε F⟩` — but from the adjunction, not as a codensity monad, and it is never identified with one. The codensity monad is named only in the essay of `Theory/Kan/Extension.v` as motivation.

## Work to be done

- Prove Proposition 1 (§X.6): `K` is codense iff the identity functor (with identity natural transformation) is the pointwise right Kan extension `Ran_K K` — connecting the codense notion (§X.6) to the pointwise Kan extension (§X.5).
- Construct the codensity monad: given `R = Ran_K K` with the transposition `φ`, build `⟨R, η, μ⟩` with `η = φ^{-1}(1_K)`, `μ = φ^{-1}(ε · R ε)`, and prove the monad laws. Suggested home: `Monad/Codensity.v` (new), reusing `Theory/Kan/Extension.v` and `Theory/Monad.v`.
- Prove `K` codense iff `η` is an isomorphism.
- Prove that for `G` with left adjoint `F` the codensity monad exists and equals `⟨G F, η, G ε F⟩`, identifying it with `Adjunction_Induced_Monad` (`Monad/Comparison.v:123`).

## Definition of Done

- [ ] Statement matches Mac Lane §X.7 Exercise 3 and §X.6 Proposition 1 (paraphrased), with setoid `≈` used for morphism equality throughout (never `=` on morphisms)
- [ ] No `Admitted`, `admit`, or `Axiom`; zero axioms in the core theory per docs/AXIOMS.md scoping
- [ ] `Print Assumptions` reported closed for the codensity monad, the codensity criterion, and the adjunction identification
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19 / 8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the codensity monad is a flagship notion)

## Verification

- `coqc -R . Category Monad/Codensity.v` compiles from a clean tree.
- `Print Assumptions` on the codensity monad, the "codense iff `η` iso" criterion, and the adjunction identification reports *Closed under the global context*.
- `nix build .#category-theory_9_1` and `nix build .#category-theory_8_20` succeed.
- Reviewer confirms the monad structure on `Ran_K K`, the density criterion, and the identification with `⟨G F, η, G ε F⟩` match §X.7 Exercise 3 and §X.6 Proposition 1.

## Dependencies

Depends on: maclane:X.6:def1
Depends on: maclane:X.5:def2

<!-- catalog: {"ids":["maclane:X.7:ex3","maclane:X.6:prop1"],"deps":["maclane:X.6:def1","maclane:X.5:def2"]} -->

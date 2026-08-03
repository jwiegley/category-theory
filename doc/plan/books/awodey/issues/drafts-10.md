```yaml
title: "Awodey 10.4: The comonad induced by an adjunction, with its counit and comultiplication exposed"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.4:construction-comonad-from-adjunction, awodey:10:ex7]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.4 "Comonads and coalgebras", printed page 278 (PDF page 287), and the chapter's Exercise 10.6.7(a)–(b), printed page 292 (PDF page 301).
Item IDs: `awodey:10.4:construction-comonad-from-adjunction`, `awodey:10:ex7` (parts (a) and (b); part (c) is filed separately).

## Background

Dually to the monad an adjunction induces on the domain of its right adjoint, an adjoint pair induces a comonad on the *other* side: the composite of the two functors the other way round, with the adjunction counit as the comonad counit and the unit whiskered on both sides as the comultiplication ([nLab: comonad](https://ncatlab.org/nlab/show/comonad)). Awodey states this and leaves it "as an exercise in duality", then re-poses it as Exercise 10.6.7(a). Part (b) asks for coalgebras and for the converse — that every comonad arises from some, not necessarily unique, adjunction.

## Current state in the library

The comonad itself is constructed. `Comonad/Duality.v:170` defines

```coq
Definition Adjunction_Comonad (A : F ⊣ U) : @Comonad C (F ◯ U) := ...
```

by dualising `Adjunction_Monad` along `Opposite_Adjunction` and repackaging the fields with `Build_Monad`. The converse half of Exercise 10.6.7(b) is likewise fully in place: both resolutions of an arbitrary comonad exist and are proved to recover it — `Comonad/Duality.v:324` `CoEM_Adjunction`, `:329` `CoEM_counit_agrees`, `:362` `CoEM_Comonad_agrees`, and the co-Kleisli trio at `:233`, `:238`, `:265` — and coalgebras are defined clause-for-clause at `Comonad/Coalgebra.v:116` (`WCoalgebra`, with `w_counit_law` and `w_coaction`), `:132` (`WCoalgebraHom`) and `:224` (`WCoalgebras`).

The precise gap is the *identification of the structure maps* that both the section text and the exercise ask one to exhibit. `Adjunction_Comonad` reads its `ret`/`join` off `Adjunction_Monad`, and `Monad/Adjunction.v:48` `Adjunction_Monad` is a `Theorem` closed with `Qed` (line 82). The resulting fields are therefore opaque, and the two equations

* `extract (Adjunction_Comonad A) x ≈ counit A x`, and
* `duplicate (Adjunction_Comonad A) x ≈ fmap[F] (unit A (U x))`

cannot even be *stated and proved* against the current term. `Comonad/Duality.v:150-153` discloses exactly this in its own header. The asymmetry is an accident of packaging rather than a mathematical obstacle: the monad side already has the transparent counterpart, `Monad/Comparison.v:123` `Adjunction_Induced_Monad`, a plain `Definition` whose `ret` is the adjunction unit and whose `join` is `fmap[U] (counit (F x))`, with the laws discharged from the zig-zag identities. There is no `Adjunction_Induced_Comonad`.

## Work to be done

Build the transparent dual of `Adjunction_Induced_Monad`, and expose the readings.

* Suggested module: `Comonad/Adjunction.v` (new), sitting beside `Monad/Comparison.v`'s transparent monad and above `Comonad/Duality.v` in the dependency order, or as a new section of `Comonad/Duality.v` if the import graph makes that cheaper.
* Define `Adjunction_Induced_Comonad {F : C ⟶ D} {U : D ⟶ C} (A : F ⊣ U) : @Comonad D (F ◯ U)` as a transparent `Definition`, with `extract := counit A` and `duplicate x := fmap[F] (unit A (U x))`, discharging the three comonad laws from `adj_unit_natural`, `counit_fmap_unit` and `fmap_counit_unit` (the mirror image of `Monad/Comparison.v:89-108`).
* Prove the agreement lemmas `Adjunction_Comonad_extract` and `Adjunction_Comonad_duplicate` relating the new transparent comonad to `Comonad/Duality.v:170`'s `Adjunction_Comonad` (or, if the two are made definitionally equal, prove the readings directly of the existing name and retire the opaque route).
* In-tree donors: `Monad/Comparison.v:89-135` (the exact monad-side template), `Theory/Adjunction.v:264/272/280/288` (`to_adj_unit`, `from_adj_counit`, `counit_fmap_unit`, `fmap_counit_unit`), `Comonad/Core.v` (the covariant `extract`/`duplicate` API), `Comonad/Duality.v` (the existing dualisation and its disclosure note).
* For Exercise 10.6.7(b), no new mathematics is required: add a short section (or file-header pointer) recording that `CoEM_Adjunction`/`CoEM_Comonad_agrees` and `CoKleisli_Adjunction`/`CoKleisli_Comonad_agrees` are the two witnesses of "every comonad comes from a (not necessarily unique) adjunction", and that `CoEM_counit_agrees` supplies the counit clause the exercise asks for.

## Definition of Done

- [ ] `Adjunction_Induced_Comonad` defined transparently on `F ◯ U`, with all comonad laws proved.
- [ ] `extract` of the induced comonad proved `≈` the adjunction counit; `duplicate` proved `≈` `fmap[F] (unit …)` — the two readings Awodey and Exercise 10.6.7(a) ask one to exhibit.
- [ ] The relation to the existing `Comonad/Duality.v:170` `Adjunction_Comonad` is stated (agreement lemmas, or the old definition re-based on the new one), and the disclosure note at `Comonad/Duality.v:150-153` is updated to match reality.
- [ ] Exercise 10.6.7(b)'s converse is discharged by an explicit cross-reference to `CoEM_Adjunction`/`CoKleisli_Adjunction` with the counit identification, not left implicit.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` reports "Closed under the global context" for `Adjunction_Induced_Comonad` and each agreement lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for the Comonad development updated to name the transparent constructor.

## Verification

```bash
coqc -R . Category Comonad/Adjunction.v
```

```coq
Print Assumptions Adjunction_Induced_Comonad.
Print Assumptions Adjunction_Comonad_extract.
Print Assumptions Adjunction_Comonad_duplicate.
```

```bash
make -j
nix build .#category-theory_8_20
nix build .#category-theory_9_1
make todo
```

Review items: the comonad is on `F ◯ U` (not `U ◯ F`); the counit and comultiplication match Awodey §10.4's `ε` and `F η U`; the construction is transparent, so a downstream consumer can rewrite with the readings — check by compiling a two-line scratch lemma that rewrites `extract` to `counit`.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:10.4:construction-comonad-from-adjunction","awodey:10:ex7"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 10.4: Comonadic functors — the co-Eilenberg–Moore comparison and the Comonadic predicate"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.4:def-coalgebra]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.4 "Comonads and coalgebras", printed page 278 (PDF page 287).
Item ID: `awodey:10.4:def-coalgebra`.

## Background

A functor is *comonadic* when it has a right adjoint and the induced comparison functor into the category of coalgebras for the resulting comonad is an equivalence — the exact dual of monadicity ([nLab: comonadic functor](https://ncatlab.org/nlab/show/comonadic+functor), [nLab: coalgebra over a comonad](https://ncatlab.org/nlab/show/coalgebra+over+a+comonad)). Awodey defines coalgebras and comonadic functors together as the duals of `T`-algebras and monadic functors, while warning that the dual notions deserve study in their own right because a category can have properties its opposite lacks.

## Current state in the library

The coalgebra half is complete and faithful: `Comonad/Coalgebra.v:116` gives

```coq
Class WCoalgebra (W : C ⟶ C) {H : @Comonad C W} (a : C) := {
  w_coalg    : a ~> W a;
  w_counit_law : extract a ∘ w_coalg ≈ id;
  w_coaction : fmap[W] w_coalg ∘ w_coalg ≈ duplicate a ∘ w_coalg }.
```

with `WCoalgebraHom` at `:132`, the category `WCoalgebras` at `:224`, and its identification with `CoEilenbergMoore := (EilenbergMoore (C^op) (W^op))^op` at `:304`. The cofree/forgetful adjunction a comonadicity predicate must compare against also exists: `Comonad/Duality.v:324` `CoEM_Adjunction` and `:362` `CoEM_Comonad_agrees`.

The comonadic-functor half has no in-tree counterpart at all. A case-sensitive search for `Comonadic` over the tree returns exactly one hit, a paper title in a bibliography comment (`Comonad/Core.v:38`); the two places that describe comonadicity (`Comonad/Coalgebra.v:86`, `Comonad/Duality.v:84`) are header prose. Concretely missing: (i) the dual of `Monad/Comparison.v:186` `EM_Comparison` — a functor from the domain of a left adjoint into the coalgebras of the induced comonad, with the dual commutations of `EM_Comparison_Forget` (`:198`) and `EM_Comparison_Free` (`:260`); and (ii) the predicate itself, dual to `Monad/Comparison.v:273`

```coq
Definition Monadic {C D : Category} (U : C ⟶ D) : Type :=
  ∃ (F : D ⟶ C) (A : F ⊣ U), EquivalenceOfCategories (EM_Comparison A).
```

This is **not** obtainable for free by op-ing `Monadic`: that predicate is stated over `EM_Comparison`, which is defined only for the covariant `EilenbergMoore`, so the dual comparison must be built explicitly, exactly as `WCoalgebras`/`CoEilenbergMoore` were.

## Work to be done

* Suggested module: `Comonad/Comparison.v` (new), mirroring `Monad/Comparison.v` file for file.
* Define `CoEM_Comparison`: for an adjunction `F ⊣ U` with `F : C ⟶ D`, the comonad `G = F ◯ U` on `D`, and a functor `D ⟶ CoEilenbergMoore G` sending `d` to the coalgebra on `d` whose structure map is `fmap[F] (unit … (U d))` — the dual of `EM_Comparison_Algebra` (`Monad/Comparison.v:151`), with the two coalgebra laws as the duals of `EM_Comparison_Algebra_id` (`:137`) and `EM_Comparison_Algebra_action` (`:141`).
* Prove the two commutations: `CoEM_Forget ◯ CoEM_Comparison ≈ F` and `CoEM_Comparison ◯ U ≈ CoEM_Cofree` (the duals of `EM_Comparison_Forget`/`EM_Comparison_Free`), being explicit in the file header about which of the two natural isomorphisms has identity components and which does not (`Monad/Comparison.v:245-252` is the precedent for that disclosure).
* Define `Comonadic (F : C ⟶ D) : Type := ∃ (U : D ⟶ C) (A : F ⊣ U), EquivalenceOfCategories (CoEM_Comparison A)`.
* Sanity witness: the identity comonad, dual to `Monad/Monadicity/Examples.v:154` `Identity_Monadic`, so the predicate is demonstrably inhabited.
* In-tree donors: `Monad/Comparison.v` (the whole file is the template), `Comonad/Coalgebra.v` (coalgebras and the `WCoalgebras ≅ CoEilenbergMoore` bridge), `Comonad/Duality.v` (the cofree adjunction and the dualisation idiom), `Theory/Equivalence.v:151` `EquivalenceOfCategories`.

## Definition of Done

- [ ] `CoEM_Comparison` defined, with both coalgebra laws proved.
- [ ] Both commutation theorems proved, and the header states which comparison isomorphism is identity-componented.
- [ ] `Comonadic` defined as the dual of `Monadic`, with the header noting why it cannot be derived from `Monadic` by op-ing.
- [ ] At least one inhabitant of `Comonadic` (the identity comonad witness).
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` closed for `CoEM_Comparison`, both commutations, and the inhabitant of `Comonadic`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for the Comonad development updated (comonadicity is flagship-adjacent to the Beck material already indexed).

## Verification

```bash
coqc -R . Category Comonad/Comparison.v
```

```coq
Print Assumptions CoEM_Comparison.
Print Assumptions Comonadic.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the definition matches Awodey §10.4 ("a functor is comonadic when it has a right adjoint whose induced comparison into the coalgebras is an equivalence"); the comparison lands in coalgebras for `F ◯ U`, not `U ◯ F`; the header records the non-derivability from `Monadic`.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:10.4:def-coalgebra"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 10.6 Ex 7(c): The category of sets with an endomorphism and its eventually-fixed-points comonad"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:10:ex7]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Exercise 10.6.7(c), printed page 292 (PDF page 301).
Item ID: `awodey:10:ex7` (part (c) only; parts (a) and (b) are covered by the transparent-comonad issue for §10.4).

## Background

Sets equipped with a self-map, with equivariant functions as morphisms, form a category — equivalently the presheaves on the free monoid on one generator, i.e. discrete dynamical systems. Awodey asks for the sub-object of *eventually fixed* points (a special case of a preperiodic point, [Wikipedia: periodic point](https://en.wikipedia.org/wiki/Periodic_point)) to be shown to carry a comonad structure ([nLab: comonad](https://ncatlab.org/nlab/show/comonad)). It is a small but genuinely concrete comonad, of which the library currently has very few.

## Current state in the library

Nothing. There is no category of sets-equipped-with-an-endomorphism: searches for a category of "sets equipped with", for equivariant maps, and for eventually fixed or eventually periodic points return no hits, and `Instance/` contains no `Endo.v`. The nearest-named file, `Theory/Multicategory/Endomorphism.v`, is the endomorphism *operad* of an object and is unrelated. The comonad API the exercise needs does exist — `Theory/Monad.v:144` `Comonad := @Monad (C^op) (M^op)` with the covariant readings `extract`/`duplicate` in `Comonad/Core.v` — but no concrete comonad of this kind is built anywhere; the concrete comonads in-tree are the Env/Store/Traced instances under `Instance/Coq/Comonad/`.

## Work to be done

* Suggested modules: `Instance/Endo.v` for the category, `Instance/Endo/Eventually.v` for the comonad (or one file if it stays small).
* Define the category: objects are a carrier together with an endomorphism `e`; morphisms are maps commuting with the endomorphisms; the hom-setoid is the ambient one (build over `Sets` so the setoid discipline is inherited, or over `Coq` if that keeps the proofs axiom-free — state the choice in the header and say why).
* Define the endofunctor `G` sending `(S, e)` to the sub-object of points `x` for which `e^(n+1) x = e^n x` for some `n`, with `e` restricted (well-definedness: `e` maps eventually-fixed points to eventually-fixed points), and its action on equivariant maps.
* Prove `G` is the functor part of a comonad: `extract` is the inclusion into `(S, e)`, `duplicate` is the corestriction, and the three comonad laws follow from the fact that an eventually-fixed point of the restriction is already one in `S`.
* Optionally record what the coalgebras are, using `Comonad/Coalgebra.v`'s `WCoalgebras`.
* In-tree donors: `Instance/Sets.v` (setoid objects), `Instance/Coq/Comonad/` (the shape of a concrete comonad instance), `Comonad/Core.v` (covariant comonad API), `Theory/Monad.v:144`.

## Definition of Done

- [ ] The category of sets-with-an-endomorphism defined, with its category laws proved.
- [ ] The eventually-fixed-points assignment defined and proved functorial (including well-definedness of the restriction).
- [ ] The comonad structure proved: counit, comultiplication, both counit laws and coassociativity, stated through `Comonad/Core.v`'s covariant API.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material; if a choice of ambient category forces an extensionality axiom, the file header discloses it and `docs/AXIOMS.md` is updated (the concrete instance layer is the sanctioned place for stdlib axioms).
- [ ] `Print Assumptions` reported for the category and the comonad, and consistent with the header's disclosure.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated only if the instance is judged flagship-level (it is a small example; a pointer from the Comonad entry suffices).

## Verification

```bash
coqc -R . Category Instance/Endo.v
coqc -R . Category Instance/Endo/Eventually.v
```

```coq
Print Assumptions Endo.
Print Assumptions Eventually_Comonad.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the carrier of `G (S, e)` is exactly Awodey's eventually-fixed set (`e^(n+1) x = e^n x` for *some* `n`), not the fixed points; morphisms are equivariant; the comonad laws are checked, not assumed.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:10:ex7"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 10.4: Adjoint triples — the induced monad, the induced comonad, and T ⊣ G"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.4:construction-adjoint-triple, awodey:10.4:remark-modal-s5]
deps_item_ids: [awodey:10.4:construction-comonad-from-adjunction]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.4 "Comonads and coalgebras", printed page 279 (PDF page 288) — the adjoint-triple construction and the modal-operator remark that specialises it.
Item IDs: `awodey:10.4:construction-adjoint-triple`, `awodey:10.4:remark-modal-s5`.

## Background

Three composable adjoint functors `L ⊣ U ⊣ R` produce a monad and a comonad on the same category, and the two are themselves adjoint ([nLab: adjoint triple](https://ncatlab.org/nlab/show/adjoint+triple), [nLab: adjoint modality](https://ncatlab.org/nlab/show/adjoint+modality)). Awodey's headline instance is `colim ⊣ Δ ⊣ lim` on a diagram category, and he remarks that in propositional modal logic possibility is the monad, necessity is the comonad, and their adjointness corresponds to the axiom scheme [S5](https://en.wikipedia.org/wiki/S5_(modal_logic)).

## Current state in the library

Every general clause is available, but only as an unassembled instantiation. `Adjunction/Compose.v:173`

```coq
Definition Adjunction_Compose : (F' ◯ F) ⊣ (U ◯ U')
```

applied to `L ⊣ U` and `U ⊣ R` type-checks and yields literally `(U ◯ L) ⊣ (U ◯ R)`, i.e. `T ⊣ G`, with no extra hypotheses; `Monad/Adjunction.v:48` `Adjunction_Monad` gives the monad `T = U ◯ L` at the left leg, and `Comonad/Duality.v:170` `Adjunction_Comonad` gives the comonad `G = U ◯ R` at the right leg.

Two things are missing. First, the construction is never *packaged*: there is no `AdjointTriple` record and no theorem naming `T`, `G` and `T ⊣ G` together — adjoint triples occur in-tree only as header prose (`Theory/Adjunction.v:75-76`, `Instance/Poset.v:70`, `Comonad/Coalgebra.v:97`, `Functor/Diagonal.v:28`, `Instance/Fun.v:70`), so a reader must reassemble the instantiation by hand each time. Second, the book's instantiating example is unavailable at any arity beyond two: the only diagonal adjunction in the tree is the binary `Adjunction/Diagonal/Product.v:37` `Diagonal_Product C ⊣ ×(C)`, and there is no limit or colimit *functor* `[J,C] ⟶ C` to be adjoint to `Functor/Diagonal.v:33`'s `Δ` — `Structure/Limit.v` presents a limit object-by-object as a terminal cone. Third, the modal reading has no carrier: `◇` does not occur anywhere in the tree and `□` is the funny tensor of `Construction/Funny.v`.

## Work to be done

* Suggested module: `Adjunction/Triple.v` (new), beside `Adjunction/Compose.v`.
* Package `AdjointTriple`: a record over `L R : C ⟶ D`, `U : D ⟶ C` carrying `L ⊣ U` and `U ⊣ R`, with named projections for the induced monad `T := U ◯ L`, the induced comonad `G := U ◯ R`, and the theorem `triple_adjoint : T ⊣ G` proved by `Adjunction_Compose`.
* Add the two identification lemmas that make the packaging useful: the monad's unit/multiplication are those of the left leg, and the comonad's counit/comultiplication are those of the right leg — the latter needs the transparent induced comonad (see Dependencies), since the current `Adjunction_Comonad` seals those readings behind a `Qed`.
* Suggested module for the modal reading: `Instance/Poset/Modal.v` (new). Instantiate the triple at a preorder: for monotone maps `◇ ⊣ □` on a preorder viewed as a thin category (`Instance/Proset.v`, `Instance/Poset.v:116`), derive that `◇` is a monad (inflationary, idempotent) and `□` a comonad (deflationary, idempotent), and record the S4/S5 readings of the resulting inequalities as *inequalities in the preorder*, not as a syntactic derivability claim.
* Scope note to put in the file header: the equivalence with the S5 axiom *scheme* is deliberately out of scope, because the tree has no propositional modal syntax, deduction system, or interior algebra; only the semantic/categorical half is formalised.
* In-tree donors: `Adjunction/Compose.v`, `Monad/Adjunction.v`, `Comonad/Duality.v`, `Instance/Proset.v`, `Instance/Poset.v`, `Adjunction/Diagonal/Product.v` (the binary instance, as a sanity instantiation of the packaging).

## Definition of Done

- [ ] `AdjointTriple` packaged, with `T`, `G` and `T ⊣ G` as named projections/theorems.
- [ ] The induced monad and comonad of a triple are identified with those of the respective legs (unit/multiplication, counit/comultiplication).
- [ ] The packaging is exercised on at least one in-tree instance (the binary `Δ ⊣ ×` case, or the preorder case).
- [ ] The preorder/modal instance built: `◇` a monad, `□` a comonad, `◇ ⊣ □`, with the S5 syntactic half explicitly scoped out in the header and the reason given.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` closed for `AdjointTriple`'s principal artifacts and `triple_adjoint`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (an `AdjointTriple` becomes a reusable dependency target).

## Verification

```bash
coqc -R . Category Adjunction/Triple.v
coqc -R . Category Instance/Poset/Modal.v
```

```coq
Print Assumptions triple_adjoint.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the monad and comonad are on the *same* category (the codomain of `U`); the adjointness proved is between the monad and the comonad, not between `T` and `U` (Awodey's printed text has a slip there, corrected in the paraphrase above); the modal file claims only the categorical half.

## Dependencies

Depends on: `awodey:10.4:construction-comonad-from-adjunction` — the comonad-side identification lemmas need the transparent induced comonad.

<!-- catalog: {"ids":["awodey:10.4:construction-adjoint-triple","awodey:10.4:remark-modal-s5"],"deps":["awodey:10.4:construction-comonad-from-adjunction"]} -->

---8<---

```yaml
title: "Awodey 10.4: The comonad Δ∘lim on a diagram category, and Sets as its coalgebras"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.4:example-limit-comonad]
deps_item_ids: [awodey:10.4:def-coalgebra]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.4 "Comonads and coalgebras", printed page 279 (PDF page 288) — the worked comonad on a diagram category.
Item ID: `awodey:10.4:example-limit-comonad`.

## Background

The constant-diagram functor is left adjoint to the limit functor ([nLab: limit](https://ncatlab.org/nlab/show/limit)), so the composite `Δ ∘ lim` is a comonad on the diagram category ([nLab: comonad](https://ncatlab.org/nlab/show/comonad)). Awodey asserts that its coalgebras are exactly the constant diagrams, hence that the base category is comonadic over the diagram category — a case where the comonad is the natural object of study because the diagram category is a topos while its opposite is not.

## Current state in the library

Nothing of the example is in place, and one ingredient is missing outright. There is no limit *functor* `[J,C] ⟶ C`: `Structure/Limit.v` presents `Limit F` diagram-by-diagram as a terminal cone and never assembles it into a right adjoint, so the endofunctor `Δ ∘ lim` cannot currently be written down. The constant-diagram functor does exist (`Functor/Diagonal.v:33`, notation `Δ[J](c)`), and `colim ⊣ Δ ⊣ lim` appears as prose at `Functor/Diagonal.v:28` and `Instance/Fun.v:70`, but the only diagonal adjunction actually constructed is the binary `Adjunction/Diagonal/Product.v:37`. There is also no comonadicity predicate to state the conclusion with (see the comonadic-functor issue for §10.4), and `[C, Sets]` carries no `ElementaryTopos` instance, so "the coalgebras again form a topos" has no in-tree counterpart either (the in-tree topos witness is `Instance/FinSet/Topos.v`'s `FinSet_Topos`).

## Work to be done

* Suggested module: `Comonad/Diagram.v` (new).
* On top of the general `Δ ⊣ lim` adjunction (see Dependencies), form the induced comonad on `[J, Sets]` and give it a name.
* Prove the coalgebra classification: a coalgebra for `Δ ∘ lim` is (isomorphic to) a constant diagram. Concretely, build the two functors between `WCoalgebras (Δ ◯ lim)` and `Sets` and prove they form an equivalence; the counit law forces the structure map to be a section of the counit, and naturality forces the diagram to be constant.
* Conclude `Comonadic Δ` for the appropriate `Δ : Sets ⟶ [J, Sets]`, using the comonadicity predicate.
* Explicitly scope out the "coalgebras again form a topos" clause with a header note (no topos instance exists for a presheaf category in-tree; the only witness is `FinSet_Topos`), or file it separately if the reviewer prefers it tracked.
* In-tree donors: `Functor/Diagonal.v`, `Structure/Limit.v`, `Instance/Fun.v`, `Comonad/Coalgebra.v`, `Comonad/Duality.v`, `Theory/Equivalence.v`.

## Definition of Done

- [ ] The comonad `Δ ∘ lim` constructed on a diagram category (with the index category's completeness hypothesis stated explicitly, not assumed silently).
- [ ] Its coalgebras classified: an equivalence between the coalgebra category and the base category, with the constant-diagram description proved in both directions.
- [ ] The comonadicity conclusion stated via the `Comonadic` predicate.
- [ ] The topos clause either proved or explicitly scoped out in the header with a stated reason.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` reported for the comonad, the equivalence, and the comonadicity witness (a `Sets`-level result may legitimately use the stdlib axioms enumerated in `docs/AXIOMS.md`; if so, record it there).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (first concrete comonadic functor in the tree).

## Verification

```bash
coqc -R . Category Comonad/Diagram.v
```

```coq
Print Assumptions Limit_Comonad.
Print Assumptions Limit_Comonad_coalgebras.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the comonad is `Δ ∘ lim` (not `lim ∘ Δ`); the classification says coalgebras *are* the constant diagrams, matching Awodey §10.4; the comonadicity claim is stated with the same predicate used elsewhere in the tree.

## Dependencies

Depends on: #353 — the limit and colimit functors as adjoints of the diagonal, which supply the `Δ ⊣ lim` adjunction this example composes.
Depends on: `awodey:10.4:def-coalgebra` — the `Comonadic` predicate and the co-Eilenberg–Moore comparison the conclusion is stated with.

<!-- catalog: {"ids":["awodey:10.4:example-limit-comonad"],"deps":["#353","awodey:10.4:def-coalgebra"]} -->

---8<---

```yaml
title: "Awodey 10.4/10.6 Ex 8: The interior comonad and the closure monad on the subsets of a space"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.4:example-interior-closure, awodey:10:ex8]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.4, printed page 279 (PDF page 288) — the interior/closure example, whose details are deferred; and Exercise 10.6.8, printed page 292 (PDF page 301), which asks for the verification plus the isomorphism of the two structured categories.
Item IDs: `awodey:10.4:example-interior-closure`, `awodey:10:ex8`.

## Background

On the inclusion-ordered subsets of a topological space, topological closure is inflationary, monotone and idempotent — a monad on that poset, i.e. a [closure operator](https://ncatlab.org/nlab/show/closure+operator) in the sense of the [Kuratowski axioms](https://en.wikipedia.org/wiki/Kuratowski_closure_axioms) — while topological [interior](https://ncatlab.org/nlab/show/interior) is deflationary, monotone and idempotent, hence a comonad. Awodey asks for both, and for the resulting categories of coalgebras and of algebras (the open and the closed subsets) to be shown isomorphic.

## Current state in the library

Nothing. There is no topological space anywhere in the tree: searches for spaces, open sets, lattices of opens, locales and frames come back empty (the only "topology" hits are Grothendieck topologies in `Theory/Sheaf.v` and bibliographic references). There is no inclusion-ordered poset of subsets either — `Structure/Topos.v:129`'s `Pow a := Ω ^ a` is an *internal* power object in an elementary topos, not the subsets of a space, and `Theory/Subobject.v`'s `SubObj` is a quotient of monos never instantiated at a space. Searches for interior/closure operators, inflationary and deflationary maps return no declarations.

The one *near* miss is prose, and it is also a defect: `Instance/Poset.v:46-54` and `:64-68` assert in the file's background essay that "a monad is a closure operator, the unit giving extensivity and the multiplication idempotency", and discuss Moore closure operators, but that file's only declarations are `eq_equiv` (`:111`), `Poset` (`:116`) and `LessThanEqualTo_Category` (`:120`) — the dictionary is asserted and never proved, and no interior/comonad counterpart is offered even in prose.

## Work to be done

* Suggested modules: `Instance/Powerset.v` (the poset of subsets of a type ordered by inclusion, as a thin category through `Instance/Proset.v`/`Instance/Poset.v`), `Instance/Topology.v` (a topological space, presented by its family of open sets or equivalently by a Kuratowski closure operator — pick one and say why in the header), and `Instance/Topology/Modalities.v` for the pair and the comparison.
* Prove: closure is a monad on the subset poset (monotone functor, unit = extensivity, multiplication = idempotency); interior is a comonad (counit = the inclusion of the interior, comultiplication = idempotency).
* Prove that the algebras of the closure monad are the closed subsets and the coalgebras of the interior comonad are the open subsets, and give the isomorphism of the two categories Awodey asks for (via complementation).
* In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Theory/Monad.v`, `Comonad/Core.v`, `Monad/Algebra.v` (`TAlgebra`), `Comonad/Coalgebra.v` (`WCoalgebra`, `WCoalgebras`), `Monad/Eilenberg/Moore.v`.
* Note on reuse: on a thin category the monad/comonad laws collapse to inequalities, so the proofs are short once the poset is in place; the work is almost entirely in building the subset poset and the space.

## Definition of Done

- [ ] The subsets of a type as an inclusion-ordered thin category.
- [ ] A topological space presented in-tree, with its interior and closure operations, and the Kuratowski laws proved for whichever presentation is chosen.
- [ ] Closure proved to be a monad and interior proved to be a comonad on that poset.
- [ ] Algebras of the closure monad identified with the closed subsets; coalgebras of the interior comonad identified with the open subsets.
- [ ] The two categories proved isomorphic, as Exercise 10.6.8 asks.
- [ ] **Library defect to fix while here:** `Instance/Poset.v:46-54` (and `:64-68`) assert the monad/closure-operator dictionary as if it were in force; either point those lines at the new proof or soften them to a forward reference, so the essay no longer overclaims in-tree content.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material; any propositional-extensionality or classical dependency used at the `Sets`/subset level is disclosed in the header and in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the closure monad, the interior comonad and the category isomorphism.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (a topological-space instance is a new area for the library).

## Verification

```bash
coqc -R . Category Instance/Powerset.v
coqc -R . Category Instance/Topology.v
coqc -R . Category Instance/Topology/Modalities.v
```

```coq
Print Assumptions Closure_Monad.
Print Assumptions Interior_Comonad.
Print Assumptions interior_closure_iso.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
grep -n "closure operator" Instance/Poset.v
```

Review items: closure is the monad and interior the comonad (not the other way round); the algebra/coalgebra identifications match Awodey §10.4's "open and closed subsets"; the `Instance/Poset.v` essay no longer asserts an unproven dictionary.

## Dependencies

Depends on: #727 — the interior operator as a right adjoint to the inclusion of open sets, which supplies the order-theoretic half of the interior side.
Depends on: #463 — monads on a preorder are closure operators and their algebras are the closed elements, the general theorem this example instantiates.
Depends on: #382 — targets the same new module `Instance/Powerset.v` (the powerset preorder with the direct-image/inverse-image adjunction); land it first rather than building the powerset order twice.

<!-- catalog: {"ids":["awodey:10.4:example-interior-closure","awodey:10:ex8"],"deps":["#727","#463","#382"]} -->

---8<---

```yaml
title: "Awodey 10.5: Pointwise sums of functors and the class of polynomial endofunctors"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:def-polynomial-functor]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.5 "Algebras for endofunctors", printed page 282 (PDF page 291) — the definition made in running prose inside Example 10.9, together with its infinitary generalisation.
Item ID: `awodey:10.5:def-polynomial-functor`.

## Background

A polynomial endofunctor is one of the shape `C₀ + C₁ × X + … + Cₙ × Xⁿ`, and more generally a sum of representables `∑_i C_i × X^(B_i)`; these are exactly the functors whose algebras are the models of a signature, and they are the categorical form of containers ([nLab: polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)). The class is the reusable definition on which the rest of Awodey §10.5 rests — the identification of algebraic structures with algebras for such functors, the existence of initial algebras, and the free-algebra construction all quantify over it.

## Current state in the library

The class does not exist, and — crucially — it cannot currently be assembled from existing combinators. A case-insensitive search for "polynomial" over the tree yields six hits, all prose comments (`Instance/Coq/Lists.v:18`, `Theory/Adamek/Corollaries.v:69`, an nLab link at `Instance/Shapes.v:55-56`, and two unrelated "link polynomial" mentions in `Structure/Monoidal/Braided.v`). There is no container, W-type or shapes-and-positions definition, and "finitary" occurs only in prose.

The missing primitive is the **pointwise coproduct of functors**. A constant-functor combinator *does* exist — `Functor/Diagonal.v:33` `Diagonal {C} (J : Category) : C ⟶ [J, C]`, notation `Δ[J](c)`, so `Δ[C](c) : C ⟶ C` is the constant endofunctor — but `Functor/Product.v:35`'s `F :*: G` is the pointwise *tensor* into a `@Monoidal D`, and the only monoidal instance built from finite structure is `Structure/Monoidal/Internal/Product.v:54` `CC_Monoidal`, whose tensor is `×`. There is no cocartesian monoidal instance, and `Functor/Coproduct.v:60` `CoproductFunctor` is the codiagonal `C ∐ C ⟶ C`, not a sum of two functors. So not even `C₀ + C₁ × X` can be written generically today.

The only realisations of the shape are two hand-written instances: `Instance/Coq/Lists.v:39` `ListF A X = option (A * X)` and `Theory/Adamek/Corollaries.v:87` `NatF X = option X`.

## Work to be done

* Suggested modules: `Functor/Sum.v` (new) for the pointwise coproduct, `Functor/Polynomial.v` (new) for the class.
* `Functor/Sum.v`: define the pointwise coproduct `F :+: G` of `F G : C ⟶ D` for a `@Cocartesian D`, mirroring `Functor/Product.v` field for field (`fobj x := F x + G x`, `fmap f := fmap[F] f + fmap[G] f`), with `Proper`, identity and composition laws. Optionally also supply the cocartesian monoidal instance dual to `CC_Monoidal` so that `Functor/Product.v` can be reused instead — pick one route and record the choice.
* `Functor/Polynomial.v`: define the finitary polynomial endofunctor former over a list of coefficient objects (`P X := C₀ + C₁ × X + … + Cₙ × Xⁿ`) in any category with finite products and coproducts, plus the class/predicate `PolynomialFunctor` identifying a functor with such a presentation up to natural isomorphism. Add the infinitary sum-of-powers variant `∑_{i∈I} C_i × X^(B_i)` in a category with the needed (co)limits and exponentials, guarded by explicit hypotheses rather than a completeness assumption baked into the class.
* Sanity: exhibit `ListF A` and `NatF` as instances of the new class, so the class is demonstrably inhabited by the tree's existing examples.
* In-tree donors: `Functor/Product.v` (template), `Functor/Coproduct.v`, `Functor/Diagonal.v` (constant functor), `Structure/Cartesian.v`, `Structure/Cocartesian.v`, `Structure/Monoidal/Internal/Product.v` (the cartesian monoidal precedent), `Instance/Coq.v:199` `Coq_Cocartesian`, `Instance/Sets/Cocartesian.v:28` `Sets_Cocartesian`.

## Definition of Done

- [ ] Pointwise coproduct of functors defined and proved functorial, with a `Proper` instance for the hom-setoid.
- [ ] The finitary polynomial endofunctor former defined over an arbitrary category with finite products and coproducts.
- [ ] The `PolynomialFunctor` class/predicate defined, closed under the presentation-up-to-natural-isomorphism reading.
- [ ] The infinitary variant defined, with its (co)limit hypotheses explicit.
- [ ] `ListF A` and `NatF` exhibited as instances.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` closed for the sum combinator, the polynomial former and the class.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — this is a reusable combinator that several downstream issues depend on.

## Verification

```bash
coqc -R . Category Functor/Sum.v
coqc -R . Category Functor/Polynomial.v
```

```coq
Print Assumptions Functor_Sum.
Print Assumptions PolynomialFunctor.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the sum is *pointwise* (not the codiagonal of `Functor/Coproduct.v`); the polynomial class matches Awodey §10.5's coefficient-times-power shape, including the constant term; the infinitary variant matches his `∑_i C_i × X^(B_i)`; both `ListF` and `NatF` typecheck as instances without ad-hoc glue.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:10.5:def-polynomial-functor"],"deps":[]} -->

---8<---

```yaml
title: "Awodey 10.5: Group structures as algebras for 1 + X + X × X, and signatures as polynomial endofunctors"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:construction-grpstr, awodey:10.5:example9]
deps_item_ids: [awodey:10.5:def-polynomial-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.5 "Algebras for endofunctors": the motivating group-structure construction, printed pages 280–281 (PDF pages 289–290), and Example 10.9's four clauses, printed pages 281–282 (PDF pages 290–291).
Item IDs: `awodey:10.5:construction-grpstr`, `awodey:10.5:example9`.

## Background

Bundling a unit, an inverse and a multiplication into a single arrow out of `1 + G + G × G` exhibits an equation-free "group structure" as an [algebra for an endofunctor](https://ncatlab.org/nlab/show/algebra+over+an+endofunctor), and homomorphisms become exactly the commuting squares ([nLab: polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)). Awodey uses this to motivate the general definition and then claims that polynomial functors present precisely the finitary algebraic structures, in any category with finite products and coproducts.

## Current state in the library

The general notion of an algebra for an endofunctor is present and faithful (`Theory/Functor.v:380` `FAlgebra`, `Construction/FAlg.v:105` `FAlgHom` with `falg_commutes`, `:114` `FAlg`, `:134` `FAlg_Forget`), and a category of equation-free group structures exists — but in a *different, disconnected encoding*. `Instance/Comp.v` (inside `Module UniversalAlgebra`) defines `OpSignature`, `OpAlgebra` (`:54`, `op : ∀ o, (arity o → carrier) → carrier`, with an explicit "no equations" comment), `AlgHom` (`:64`, homomorphy stated operation by operation), `Algs : Category` (`:151`) and `GroupOp` (`:298`, one nullary, one unary and one binary operation). At `S := GroupOp` those objects are exactly Awodey's `(u, i, m)` data and `AlgHom` is exactly pointwise preservation.

What is missing is precisely Awodey's point. The endofunctor `1 + X + X × X` is not constructed anywhere and cannot currently be assembled (there is no pointwise coproduct of functors — see the polynomial-functor issue for §10.5); the compression of the three operations into a single structure arrow, and the equivalence "preserves unit, inverse and multiplication pointwise" ⟺ "the square commutes", are never stated; and `Instance/Comp.v` does not import `Construction/FAlg.v` at all, so the two categories of algebras are formally unrelated. Note also that `AlgHom`'s equality is Leibniz `=` on a bare `Type` carrier, which the bridge will have to reconcile with the setoid discipline.

Of Example 10.9's four clauses, none is in-tree: (1) the `GrpStr` identification is missing as just described; (2) there is no ring endofunctor and no theorem relating finite signatures to polynomial endofunctors; (3) no infinitary sum-of-powers construction; (4) there is no covariant powerset endofunctor at all (`Structure/Topos.v:129`'s `Pow` is an internal power object).

## Work to be done

* Suggested modules: `Construction/Signature.v` (new) for the signature-to-polynomial-endofunctor translation, `Instance/Coq/GroupStr.v` (new) for the worked group and ring instances.
* Build the endofunctor `F X = 1 + X + X × X` in a category with finite products and coproducts using the polynomial machinery, and prove `FAlg F` isomorphic (or equivalent) to `UniversalAlgebra.Algs` at `GroupOp` — in particular that a map is an `AlgHom` exactly when the `FAlgHom` square commutes. State clearly in the header how the Leibniz-vs-setoid mismatch is bridged.
* Do the ring case as a second instance, `R X = 2 + X + 2 × X²`, to show the pattern is not bespoke.
* Prove the general clause (2): for a finite signature (finitely many finitary operations), the sum-of-powers endofunctor it determines has an algebra category isomorphic to the signature's, in any category with finite products and coproducts — the honest content of "polynomial functors present exactly the finitary algebraic structures".
* Clause (3): instantiate the infinitary polynomial former from the polynomial-functor issue and record which extra hypotheses it needs; clause (4): once a covariant powerset endofunctor exists, note that `FAlg` applied to it is a legitimate, non-polynomial algebra notion — no new theory is required, only the instantiation.
* In-tree donors: `Construction/FAlg.v`, `Instance/Comp.v` (the `UniversalAlgebra` module — note the module prefix on every symbol), `Structure/Cartesian.v`, `Structure/Cocartesian.v`, `Instance/Coq.v`, `Instance/Sets/Cocartesian.v`.

## Definition of Done

- [ ] The endofunctor `1 + X + X × X` constructed via the polynomial machinery.
- [ ] Its algebra category proved isomorphic/equivalent to the signature-encoded category of group structures, with the homomorphism equivalence (pointwise preservation ⟺ commuting square) stated as a lemma.
- [ ] The ring endofunctor `2 + X + 2 × X²` built and its algebras identified likewise.
- [ ] The general finite-signature ⟺ polynomial-endofunctor correspondence proved in a category with finite products and coproducts.
- [ ] The infinitary clause instantiated, with hypotheses explicit.
- [ ] (from Awodey §10.5, Example 10.9 clause 4) `FAlg` instantiated at the covariant powerset endofunctor, once that functor exists, as the worked non-polynomial example.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms; the Leibniz-equality mismatch with `Instance/Comp.v` explicitly handled and documented.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material beyond what `Instance/Comp.v` already discloses (its `from_free_unique` leans on functional extensionality, flagged at `Instance/Comp.v:124-130`); any inherited dependency is recorded in the header and `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the group-structure equivalence and the general signature correspondence.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (this connects two previously disjoint algebra developments).

## Verification

```bash
coqc -R . Category Construction/Signature.v
coqc -R . Category Instance/Coq/GroupStr.v
```

```coq
Print Assumptions GrpStr_FAlg_equiv.
Print Assumptions signature_polynomial_equiv.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the group structure carries **no equations** (Awodey is explicit about this); the single structure arrow is `[u, i, m]`; the homomorphism condition is the commuting square, proved equivalent to pointwise preservation; the correspondence is stated for an arbitrary category with finite products and coproducts, not only for `Sets`.

## Dependencies

Depends on: `awodey:10.5:def-polynomial-functor` — the pointwise sum of functors and the polynomial class.
Depends on: #227 — the covariant power-set functor, needed for Example 10.9's fourth clause.

<!-- catalog: {"ids":["awodey:10.5:construction-grpstr","awodey:10.5:example9"],"deps":["awodey:10.5:def-polynomial-functor","#227"]} -->

---8<---

```yaml
title: "Awodey 10.5/10.6 Ex 2: Lambek's lemma — the initial algebra structure map is an isomorphism"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:lem10, awodey:10:ex2]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Lemma 10.10 (Lambek), §10.5, printed page 283 (PDF pages 292–293), and Exercise 10.6.2, printed page 290 (PDF page 299), which asks for the lemma with a hint diagram and then draws two consequences.
Item IDs: `awodey:10.5:lem10`, `awodey:10:ex2`.

## Background

Lambek's lemma says the structure map of an initial algebra for an endofunctor is invertible, so an initial algebra is a fixed point of the functor ([nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor), section "Lambek's theorem"). Awodey uses it to constrain which endofunctors can have initial algebras, and the exercise draws the corollary that a natural numbers object satisfies `N + 1 ≅ N`.

## Current state in the library

`Theory/Lambek.v:40` states

```coq
Theorem lambek `(F : C ⟶ C) (I : @Initial (FAlg F)) :
  F (`1 (@initial_obj (FAlg F) I)) ≅ `1 (@initial_obj (FAlg F) I).
```

at exactly Awodey's generality (arbitrary endofunctor, arbitrary category), and the in-file proof is his hint diagram (mediate into `(F μ, fmap α)`, get `α ∘ h ≈ id` by initiality, then `h ∘ α ≈ id` by functoriality). The dual `lambek_final` follows at `:78`.

The gap is that the *conclusion is weaker than the book's*. Awodey's claim is that the initial structure map `i` **is** the isomorphism; the in-tree statement asserts only that *some* isomorphism `F μ ≅ μ` exists. The proof does build the iso from the structure map (`to := \`2 iobj`, line 67), but the theorem is closed with `Qed` at line 69 and `Isomorphism` is a `Type`-valued class (`Theory/Isomorphism.v:113`), so the witness is opaque: a downstream consumer cannot prove `to (lambek F I) ≈ \`2 (initial_obj (FAlg F) I)`, and therefore cannot use the lemma to conclude that a *given* structure map is invertible. Nothing in the tree consumes `lambek`, so nothing compensates.

The exercise's two riders: the recursion property is already available generically (`Theory/Recursion.v:63` `cata_commutes`, `:72` `cata_unique`, plus `Instance/Coq/Lists.v:86` `hom_is_fold` at element level), so that half is discharged; but `N + 1 ≅ N` has no carrier, because the library has no natural-numbers-object notion.

## Work to be done

* Suggested module: edit `Theory/Lambek.v` in place; add corollaries in `Theory/Lambek.v` or a small `Theory/Lambek/Corollaries.v`.
* Restate the lemma so the structure map is the witness. Two acceptable routes, either is fine so long as the readings become usable: (a) close `lambek` with `Defined` and add `lambek_to : to (lambek F I) ≈ \`2 (initial_obj (FAlg F) I)`; or (b) keep the opaque iso and add a separate `lambek_iso : IsIsomorphism (\`2 (initial_obj (FAlg F) I))`, proved directly, with `lambek` derived from it. Route (b) keeps the statement honest without depending on proof-term transparency and is probably preferable.
* Mirror the strengthening on the dual (`lambek_final`), so the final-coalgebra structure map is likewise proved invertible.
* Add the exercise's corollary once a natural numbers object exists: `N + 1 ≅ N` for any NNO in any category, obtained by applying the strengthened lemma to `X ↦ X + 1`.
* Add at least one consumer so the strengthened form is exercised (for instance rewrite one of the existing initial-algebra results through `lambek_iso`).
* In-tree donors: `Theory/Lambek.v`, `Construction/FAlg.v`, `Structure/Initial.v` (`zero_unique`), `Theory/Isomorphism.v`, `Theory/Recursion.v`.

## Definition of Done

- [ ] The initial structure map itself proved invertible (not merely "some isomorphism exists"), in a form a consumer can rewrite with.
- [ ] The dual statement for the final coalgebra strengthened in the same way.
- [ ] **Library defect fixed:** `Theory/Lambek.v`'s header asserts the stronger reading (that the structure map is the isomorphism) while the `Qed`-sealed statement does not support it; after this change the header and the statement must agree.
- [ ] At least one in-tree consumer of the strengthened lemma.
- [ ] The `N + 1 ≅ N` corollary proved for a natural numbers object, or — if the NNO issue has not landed — stated over an explicit NNO hypothesis so the obligation is visibly discharged rather than dropped.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom`.
- [ ] `Print Assumptions` closed for `lambek`, the new invertibility statement, the dual, and the corollary.
- [ ] `_CoqProject` updated if a new file is added.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for `Theory/Lambek.v` updated to describe the strengthened form.

## Verification

```bash
coqc -R . Category Theory/Lambek.v
```

```coq
Print Assumptions lambek.
Print Assumptions lambek_iso.
Print Assumptions lambek_final.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the statement now names the structure map, matching Awodey Lemma 10.10; a scratch consumer that rewrites `to (lambek …)` to the structure map compiles; the header no longer overclaims.

## Dependencies

Depends on: #637 — the natural-numbers object, needed to state the `N + 1 ≅ N` corollary Exercise 10.6.2 asks for.

<!-- catalog: {"ids":["awodey:10.5:lem10","awodey:10:ex2"],"deps":["#637"]} -->

---8<---

```yaml
title: "Awodey 10.5: Initial algebras unwound — binary trees, term trees, and length by initiality"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:example11]
deps_item_ids: [awodey:10.5:def-polynomial-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Example 10.11, §10.5, printed pages 284–286 (PDF pages 293–295) — unwinding initial algebras into tree types, and defining `length` by the universal property.
Item ID: `awodey:10.5:example11`.

## Background

Unwinding the isomorphism supplied by Lambek's lemma turns an initial algebra into a type of finite trees whose branching is read off the functor ([nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)); the mediating map out of the initial algebra is then a definition by structural recursion ([nLab: algebra for an endofunctor](https://ncatlab.org/nlab/show/algebra+over+an+endofunctor)). Awodey works three cases: binary trees for `1 + X²`, general trees for a finitary polynomial functor, and finite lists for `1 + A × X`, closing with `length` as the unique mediator into `[0, (a,n) ↦ 1 + n]`.

## Current state in the library

Exactly one of the three clauses is proved, in full. `Instance/Coq/Lists.v` has `ListF A X := option (A * X)` (`:39`) — literally Awodey's `1 + A × X` — with the structure map `alg` (`:67`, `None ↦ nil`, `Some (a,l) ↦ cons a l`, i.e. his `[*, @]`), the uniqueness mechanism `hom_is_fold` (`:86`), and `list_initial : @Initial (FAlg (ListF A))` (`:111`), all axiom-free by list induction over `Coq` rather than `Sets`.

The rest is missing:

* Binary trees: the endofunctor `1 + X²` is not constructed and no type is exhibited as its initial algebra. The only `Inductive Tree` in the tree is `Instance/Comp.v:88`, the free *signature* term type, which is a different (and unconnected) object.
* The general clause — for a finitary polynomial functor the initial algebra is the corresponding tree type — cannot even be stated, since there is no class of polynomial functors.
* `length : list A → nat` is never defined as the mediator out of `list_initial` into `[0, (a,n) ↦ 1 + n]`; searching for `length` finds only plain list-length uses in `Theory/Metacategory.v` and `Theory/Multicategory/Operad.v`. The two defining equations are therefore never derived from a commuting square, though the generic machinery to do so exists (`Theory/Recursion.v:57` `cata`, `:63` `cata_commutes`, `:72` `cata_unique`).

## Work to be done

* Suggested modules: `Instance/Coq/Trees.v` (new) for the binary-tree clause; extend `Instance/Coq/Lists.v` (or add `Instance/Coq/Lists/Length.v`) for the recursion clause.
* Binary trees: build the endofunctor `X ↦ 1 + X × X` (via the polynomial machinery, or hand-written in the `ListF` style with a header note if the general former is not yet available), define the inductive type of finite binary trees, and prove it initial — existence of the mediator by tree recursion, uniqueness by tree induction, mirroring `list_alg_hom`/`hom_is_fold`/`list_initial`.
* Term trees: state and prove the general clause in the sanctioned in-tree form — for a signature endofunctor, the type of closed terms is the initial algebra. `Instance/Comp.v:88`'s `Tree` at no generators (`X := Empty_set`) is exactly that carrier and `Instance/Comp.v:219` already builds the initial object of `Algs` from `induced_hom`/`from_free_unique`; what is missing is the identification with `FAlg` of the corresponding endofunctor.
* Recursion clause: define `length` as `cata` into the algebra `[0, (a,n) ↦ 1 + n]` and derive `length nil = 0` and `length (cons a l) = 1 + length l` from `cata_commutes`, then prove it agrees with the stdlib `length` — that agreement is what makes the point that the commuting square *is* the pair of defining equations.
* In-tree donors: `Instance/Coq/Lists.v` (the complete template), `Theory/Recursion.v`, `Construction/FAlg.v`, `Instance/Comp.v` (`UniversalAlgebra.Tree`, `Free`, `induced_hom`, `from_free_unique`), `Theory/Lambek.v`.

## Definition of Done

- [ ] The endofunctor `1 + X × X` built and finite binary trees proved to be its initial algebra (existence and uniqueness of the mediator).
- [ ] The signature/term-tree clause stated and proved: closed terms of a signature form the initial algebra of the corresponding endofunctor.
- [ ] `length` defined as the unique mediator out of the initial list algebra, with both defining equations derived from the commuting square and agreement with the ordinary list length proved.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms (note that `Coq` homs use pointwise equality, which is the ambient setoid there — say so in the header).
- [ ] No `Admitted`, `admit` or `Axiom` in the new material; if the signature clause inherits `Instance/Comp.v`'s functional-extensionality dependency (`Instance/Comp.v:124-130`), disclose it in the header and in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the binary-tree initiality, the term-tree initiality and `length`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for the initial-algebra witnesses extended with the new concrete instances.

## Verification

```bash
coqc -R . Category Instance/Coq/Trees.v
coqc -R . Category Instance/Coq/Lists.v
```

```coq
Print Assumptions btree_initial.
Print Assumptions length_cata.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the binary-tree carrier matches Awodey's (`*` the empty tree, `@` the grafting); `length` is *defined* by initiality rather than defined first and shown to satisfy the equations afterwards; the term-tree clause is stated for a signature endofunctor and its scope is disclosed relative to Awodey's more general "finitary polynomial functor" phrasing.

## Dependencies

Depends on: `awodey:10.5:def-polynomial-functor` — needed to build `1 + X × X` generically and to state the general finitary-polynomial clause; the binary-tree clause alone can be hand-written if that issue has not landed.

<!-- catalog: {"ids":["awodey:10.5:example11"],"deps":["awodey:10.5:def-polynomial-functor"]} -->

---8<---

```yaml
title: "Awodey 10.5: The covariant powerset functor has no initial algebra (Lambek plus Cantor)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:remark-powerset-no-initial-algebra]
deps_item_ids: [awodey:10.5:lem10]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), §10.5, printed page 286 (PDF page 295) — the remark drawing a non-existence consequence from Lemma 10.10.
Item ID: `awodey:10.5:remark-powerset-no-initial-algebra`.

## Background

Not every endofunctor has an initial algebra: by Lambek's lemma an initial algebra is a fixed point of the functor ([nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)), and [Cantor's theorem](https://ncatlab.org/nlab/show/Cantor%27s+theorem) forbids a set isomorphic to its own powerset. It is the standard first counterexample and the reason existence theorems carry preservation hypotheses.

## Current state in the library

Absent, and both ingredients are missing. There is no covariant powerset endofunctor anywhere: the only `Pow` in the tree is `Structure/Topos.v:129`'s internal power object `Ω ^ a` in an elementary topos, which is an object rather than a functor, and `Theory/Subobject/Functor.v`'s `Sub : C^op ⟶ Sets` is the contravariant subobject functor. Cantor's theorem is nowhere a lemma — the two "Cantor" hits (`Structure/Limit.v:109`, `Structure/Complete.v:69`) are prose. And there is no statement of the form `@Initial (FAlg F) → False` for any `F`: every use of `Initial (FAlg …)` in the tree is a positive existence result.

The one tool that does exist, `Theory/Lambek.v:40` `lambek`, is never applied to a non-existence result — and as it currently stands (an opaque `Qed`-sealed isomorphism) it is too weak to be applied this way without first being strengthened.

## Work to be done

* Suggested module: `Instance/Sets/Powerset.v` (new), or a section of whichever file introduces the covariant powerset endofunctor.
* Prove Cantor's theorem in the ambient setting used for the powerset functor: no surjection from a set onto its powerset, hence no isomorphism `Pow I ≅ I`.
* Apply the strengthened Lambek lemma: an initial algebra for the covariant powerset endofunctor would give `Pow I ≅ I`, contradiction; conclude `@Initial (FAlg Pow) → False`.
* State the general moral as a short corollary — not every endofunctor has an initial algebra — so the negative result is discoverable next to the positive existence theorems in `Theory/Adamek.v`.
* In-tree donors: `Theory/Lambek.v`, `Construction/FAlg.v`, `Instance/Sets.v`, `Instance/Sets/Image.v` (image factorisation, if the functor's action on maps is built as a direct image), `Structure/Initial.v`.
* Sequencing note recorded by the coverage verifier: this is cheap to close **after** a covariant powerset endofunctor and a Cantor lemma exist, and should not be bundled with the Lambek strengthening itself.

## Definition of Done

- [ ] Cantor's theorem stated and proved in-tree for the setting the powerset functor lives in.
- [ ] `@Initial (FAlg Pow) → False` proved, via the strengthened Lambek lemma.
- [ ] A corollary recording that not every endofunctor has an initial algebra, cross-referenced from the Adámek development.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` beyond what the instance layer already sanctions; any classical or extensionality dependency of the Cantor argument is disclosed in the header and in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the Cantor lemma and the non-existence theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (the first non-existence result about initial algebras).

## Verification

```bash
coqc -R . Category Instance/Sets/Powerset.v
```

```coq
Print Assumptions cantor.
Print Assumptions powerset_no_initial_algebra.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the functor is the **covariant** powerset (action by direct image), matching Awodey §10.5, not the contravariant one or the topos power object; the proof genuinely routes through Lambek's lemma rather than an ad-hoc diagonal argument on algebras.

## Dependencies

Depends on: #227 — the covariant power-set functor, which supplies the endofunctor this result is about.
Depends on: `awodey:10.5:lem10` — the strengthened Lambek lemma; the current opaque form cannot be applied to conclude a non-existence.
Depends on: #466 — targets the same new module `Instance/Sets/Powerset.v` (the power-set monad and complete semilattices); this issue reuses that carrier rather than redefining it.
Depends on: #704 — also targets `Instance/Sets/Powerset.v` (the contravariant powerset functor and the double-powerset monad); coordinate the module layout so the covariant and contravariant halves coexist.

<!-- catalog: {"ids":["awodey:10.5:remark-powerset-no-initial-algebra"],"deps":["#227","awodey:10.5:lem10","#466","#704"]} -->

---8<---

```yaml
title: "Awodey 10.5: Every polynomial endofunctor on Sets has an initial algebra"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:cor13]
deps_item_ids: [awodey:10.5:def-polynomial-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Corollary 10.13, §10.5, printed page 287 (PDF page 296), read together with Proposition 10.12 on the same page.
Item ID: `awodey:10.5:cor13`.

## Background

Adámek's construction builds the initial algebra of an ω-cocontinuous endofunctor as the colimit of the chain `0 → P0 → P²0 → …` ([nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor), section "Adámek's theorem"). Awodey's corollary applies it to [polynomial functors](https://ncatlab.org/nlab/show/polynomial+functor) on sets, which preserve ω-colimits, and thereby produces the inductive datatypes as least fixed points.

## Current state in the library

Proposition 10.12 itself is in place: `Theory/Adamek.v:285` `adamek : @Initial (FAlg F)` is a transparent definition over the ω-chain `Construction/Chain.v:33` and the ordinal of `Instance/Omega.v`, with the preservation hypothesis packaged honestly as `AdamekData` (`Theory/Adamek.v:107`), which requires the *image* of the colimiting cocone to be colimiting — the correct cone-level reading of "P preserves this ω-colimit". `Theory/Adamek/Corollaries.v:59` `adamek_cocomplete` supplies the corollary shape.

The corollary is nevertheless absent, and all three of its ingredients are missing.

* There is no class of polynomial functors, so "every polynomial functor" cannot be quantified over.
* No `AdamekData` witness is constructed for any endofunctor anywhere in the tree — the record occurs only at its definition and in two hypothesis positions (`Theory/Adamek.v:115`, `Theory/Adamek/Corollaries.v:62`) — and the `PreservesColimit → AdamekData` bridge is explicitly deferred (ledger 17, `Theory/Adamek.v:41-46`), the in-tree `PreservesColimit` being apex-only and therefore too weak.
* Neither `Sets` nor `Coq` is shown cocomplete or shown to have ω-colimits: `Structure/Complete.v:119` defines `Cocomplete` and it is used only as a hypothesis.

The only realisation of the conclusion is hand-built and bypasses the whole route: `Instance/Coq/Lists.v:111` `list_initial` proves `1 + A × X` has an initial algebra by direct list induction.

## Work to be done

* Suggested module: `Theory/Adamek/Polynomial.v` (new).
* Prove that a polynomial endofunctor preserves ω-colimits, in the cone-level sense `AdamekData` demands — i.e. construct the `AdamekData` witness for the polynomial former, clause by clause over sums, products and constants. This is the mathematical heart of the issue and the first `AdamekData` inhabitant in the tree.
* Supply the ambient ω-colimits: either prove `Cocomplete` for the ambient category, or (cheaper and sufficient) prove that `Colimit (Chain P)` exists for the chain of a polynomial functor.
* Conclude: every polynomial endofunctor on the chosen ambient category has an initial algebra, quantified over the polynomial class.
* Sanity: re-derive `Instance/Coq/Lists.v`'s `list_initial` (or an isomorphic statement) through the new corollary, so the general route is demonstrably usable and agrees with the hand-built witness.
* In-tree donors: `Theory/Adamek.v`, `Theory/Adamek/Corollaries.v`, `Construction/Chain.v`, `Instance/Omega.v`, `Structure/Limit/Preservation.v` (`IsAColimit` at `:130`, `colimit_inj` at `:135`), `Structure/Complete.v`, `Instance/Coq/Lists.v` (the agreement check).

## Definition of Done

- [ ] An `AdamekData` witness constructed for polynomial endofunctors — the first inhabitant of that record in the tree.
- [ ] The ambient ω-colimits supplied (full cocompleteness or the chain colimit specifically), with the choice justified in the header.
- [ ] The corollary proved: every polynomial endofunctor has an initial algebra, quantified over the polynomial class.
- [ ] The general route shown to agree with the existing hand-built `list_initial`.
- [ ] **Library defect to fix while here:** `Theory/Adamek.v` / `Theory/Adamek/Corollaries.v` are described as recording their missing-witness status in `docs/INHABITATION.md`, but that document does not mention Adámek at all — neither table lists `adamek` or `adamek_cocomplete`. Add the entries (and, once this issue lands, update them to record the new concrete witness).
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material; any instance-layer axiom dependency disclosed in the header and in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the `AdamekData` witness and the corollary.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for the Adámek development updated — it currently states that no concrete `AdamekData` is constructed in-tree, which this issue changes.

## Verification

```bash
coqc -R . Category Theory/Adamek/Polynomial.v
```

```coq
Print Assumptions polynomial_AdamekData.
Print Assumptions polynomial_initial_algebra.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
rg -i adamek docs/INHABITATION.md
```

Review items: preservation is established in the cone-level sense `AdamekData` requires, not merely apex-level; the corollary is quantified over the polynomial class rather than proved for one functor; `docs/INHABITATION.md` now lists the Adámek results and their witness status.

## Dependencies

Depends on: `awodey:10.5:def-polynomial-functor` — the class the corollary quantifies over.
Depends on: #329 — chain unions as colimits and the cocompleteness of Sets, which supplies the ambient ω-colimits.

<!-- catalog: {"ids":["awodey:10.5:cor13"],"deps":["awodey:10.5:def-polynomial-functor","#329"]} -->

---8<---

```yaml
title: "Awodey 10.5: When endofunctor algebras are monad algebras — the free P-algebra and the three equivalent conditions"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:10.5:prop14, awodey:10.5:construction-free-p-algebra]
deps_item_ids: [awodey:10.5:def-polynomial-functor]
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Proposition 10.14 and the free-algebra construction inside its proof, §10.5, printed pages 287–289 (PDF pages 296–298).
Item IDs: `awodey:10.5:prop14`, `awodey:10.5:construction-free-p-algebra`.

## Background

For an endofunctor `P` on a category with finite coproducts, three conditions coincide: the `P`-algebras are the algebras of a monad (compatibly with the forgetful functors); the forgetful functor from `P`-algebras has a left adjoint; and `A + P(−)` has an initial algebra for every object `A`. The monad in question is the algebraically-free monad on `P`, whose value at `A` is the initial algebra of `A + P(−)` ([nLab: free monad](https://ncatlab.org/nlab/show/free+monad)); the last implication back to the first is the province of [monadicity theorems](https://ncatlab.org/nlab/show/monadicity+theorem).

## Current state in the library

None of the three conditions, and none of the four implications between them, is stated in-tree.

* The forgetful functor exists (`Construction/FAlg.v:134` `FAlg_Forget`, referenced only once more, at `Construction/FCoalg.v:38`, as a dualisation) but has no left adjoint and carries no monadicity claim. Outside `Construction/FAlg.v` the only consumers of `FAlg` are the initial/final-algebra results (`Theory/Lambek.v`, `Theory/Recursion.v`, `Theory/Adamek.v` and its corollaries, `Construction/FCoalg.v`, `Instance/Coq/Lists.v`, `Instance/Sets/Streams.v`); nothing relates `FAlg` to monads or adjunctions.
* There is no endofunctor former `X ↦ A + P(X)`, and none can currently be assembled for want of a pointwise coproduct of functors.
* The monadicity vocabulary exists (`Monad/Comparison.v:273` `Monadic`, and the Beck development under `Monad/Monadicity/`) but is never instantiated at an algebra category's forgetful functor.
* The generic route from the third condition to the second exists but is unused: `Theory/Universal/Arrow.v:127` `UniversalArrow`, `:185` `LeftAdjointFunctorFromUniversalArrows`, `:214` `AdjunctionFromUniversalArrows`.

The free-algebra construction fares slightly better, in a restricted encoding. `Instance/Comp.v` (module `UniversalAlgebra`) has `Tree` (`:88`, generators plus operation nodes — literally `μY. X + P_S(Y)` for a signature endofunctor), `Free` (`:92`, whose `node` is Awodey's `α₂` and whose `generator` is his `α₁`), `induced_hom` (`:108`) and `from_free_unique` (`:116`). But it is stated only for signature endofunctors on `Type`; the carrier is postulated as an inductive term type rather than obtained as an initial `P_A`-algebra, so the splitting `α = [α₁, α₂]` is never made; `Free` is never made functorial; the unit `α₁ : A → U F A` is never exhibited; there is no adjunction (the file only *remarks*, at `:211-219`, that the free functor is left adjoint to the forgetful one); and `from_free_unique` leans on functional extensionality, disclosed in-file at `:124-130`.

## Work to be done

* Suggested modules: `Construction/FAlg/Free.v` (new) for the construction, `Construction/FAlg/Monadic.v` (new) for the proposition.
* Build the endofunctor former `P_A X := A + P X` for an endofunctor `P` on a category with finite coproducts.
* From "every `P_A` has an initial algebra", construct the left adjoint exactly as Awodey does: split the initial structure map as `[α₁, α₂]`, set `F A := (I_A, α₂)`, define `F` on arrows by initiality of `I_A` against `β ∘ (f + P I_B)`, and take `α₁` as the unit. Route the adjunction through `Theory/Universal/Arrow.v`'s `AdjunctionFromUniversalArrows` rather than re-deriving it.
* State the three conditions and prove the implications the book proves: (1) ⇒ (2) directly; (2) ⇒ (3) via the bijection between `P_A`-algebras and pairs consisting of a `P`-algebra and an arrow into its carrier, whose initial object is the unit; (3) ⇒ (2) by the previous bullet.
* For (2) ⇒ (1), do **not** re-prove Beck: state it over the in-tree monadicity theorem, supplying the hypotheses that theorem requires, and disclose in the header exactly which form of monadicity is used and what it costs.
* Optionally connect the restricted existing construction: show that for a signature endofunctor the new free functor agrees with `UniversalAlgebra.Free`, which would also retire that file's unproven marginal remark.
* In-tree donors: `Construction/FAlg.v`, `Theory/Universal/Arrow.v`, `Monad/Comparison.v` (`Monadic`, `EM_Comparison`), `Monad/Eilenberg/Moore/Adjunction.v`, `Monad/Monadicity/` (Beck), `Structure/Cocartesian.v`, `Instance/Comp.v`, `Theory/Adamek.v` (a source of the initial algebras condition (3) demands).

## Definition of Done

- [ ] The endofunctor former `A + P(−)` defined.
- [ ] The free `P`-algebra functor constructed from initial `P_A`-algebras, including the arrow action by initiality and the unit `α₁`.
- [ ] The adjunction `F ⊣ FAlg_Forget` proved, via the universal-arrow machinery.
- [ ] The three conditions stated, with the implications (1) ⇒ (2), (2) ⇒ (3) and (3) ⇒ (2) proved.
- [ ] (2) ⇒ (1) discharged against the in-tree Beck monadicity theorem, with the hypotheses supplied and their cost disclosed in the header — or, if that proves out of reach, stated as an explicitly scoped conditional with the reason recorded, never as an `Admitted`.
- [ ] The equivalence with the Eilenberg–Moore category is stated as commuting with the forgetful functors down to the base, as Awodey requires.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material.
- [ ] `Print Assumptions` closed for the free functor, the adjunction and each implication.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated and `docs/INHABITATION.md` extended if the result is stated conditionally — this is a flagship-level theorem.

## Verification

```bash
coqc -R . Category Construction/FAlg/Free.v
coqc -R . Category Construction/FAlg/Monadic.v
```

```coq
Print Assumptions FAlg_Free.
Print Assumptions FAlg_Free_Adjunction.
Print Assumptions FAlg_monadic_iff.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the statement matches Awodey Proposition 10.14's three conditions and the direction of each implication; the equivalence in condition (1) commutes with the forgetful functors; the free-algebra carrier is obtained as an initial `A + P(−)`-algebra rather than postulated; the Beck leg is honestly attributed and its hypotheses are visible.

## Dependencies

Depends on: `awodey:10.5:def-polynomial-functor` — the pointwise coproduct of functors, without which `A + P(−)` cannot be formed.
Depends on: #484 — Beck's monadicity theorem, which supplies the (2) ⇒ (1) leg the book itself defers.

<!-- catalog: {"ids":["awodey:10.5:prop14","awodey:10.5:construction-free-p-algebra"],"deps":["awodey:10.5:def-polynomial-functor","#484"]} -->

---8<---

```yaml
title: "Awodey 10.6 Ex 10: The final coalgebra of 1 + A × X — possibly-infinite lists"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:10:ex10]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory* (2nd edition), Exercise 10.6.10, printed page 293 (PDF page 302).
Item ID: `awodey:10:ex10`.

## Background

Coalgebras for an endofunctor are dual to algebras, and the final one is the greatest fixed point ([nLab: terminal coalgebra for an endofunctor](https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor)). For `P X = 1 + A × X` the initial algebra is the finite lists over `A` and the final coalgebra is the finite-*or*-infinite lists — the exercise's hint contrasts the two.

## Current state in the library

The duality clause is definitional and complete: `Construction/FCoalg.v:28` `FCoalg F := (FAlg (F^op))^op` with `fcoalg_hom` at `:32` proved by `reflexivity`, plus the corecursion package `ana`/`ana_commutes`/`ana_unique` (`Theory/Recursion.v:111-131`) and `lambek_final` (`Theory/Lambek.v:78`).

The exercise's actual task is not done, and the near miss is instructive. The only concrete final coalgebra in the tree is `Instance/Sets/Streams.v:231` `Stream_final : @Terminal (FCoalg StreamF)` — but `StreamF` (`:146`) has `fobj X = A × X`, with **no unit summand**, so its final coalgebra is the purely infinite streams, not Awodey's finite-or-infinite lists. Meanwhile the exact functor `1 + A × X` *does* exist in the tree, as `Instance/Coq/Lists.v:39` `ListF A`, but only on the algebra side, where its initial algebra `list A` is proved (`:111`). In other words the exercise's hint is formalised and the exercise's task is not: there is no `@Terminal (FCoalg (ListF _))` and no colist carrier anywhere.

## Work to be done

* Suggested module: `Instance/Sets/Colists.v` (new), modelled directly on `Instance/Sets/Streams.v`.
* Define the carrier of possibly-finite streams over `A` (a coinductive type, or the existing stream type extended with a termination marker), together with its bisimilarity setoid — `Instance/Sets/Streams.v` already establishes the pattern of quotienting by bisimilarity to get a `Sets` object and proving uniqueness up to it.
* Define the endofunctor `1 + A × X` on the same ambient category as the carrier (note the mismatch to resolve: `ListF A` lives on `Coq`, `StreamF` on `Sets` — pick one, state which, and say why).
* Build the coalgebra structure (head/tail-or-stop), define the anamorphism for an arbitrary coalgebra, and prove finality: existence and uniqueness of the coalgebra map.
* Optionally record the contrast the exercise draws: the same endofunctor's initial algebra is `list A`, already proved at `Instance/Coq/Lists.v:111`.
* In-tree donors: `Instance/Sets/Streams.v` (the complete template, including the bisimilarity machinery), `Construction/FCoalg.v`, `Theory/Recursion.v` (`ana`, `ana_unique`), `Theory/Lambek.v:78`, `Instance/Coq/Lists.v` (the algebra-side counterpart).

## Definition of Done

- [ ] The endofunctor `1 + A × X` available on the chosen ambient category, with the choice and any mismatch with the existing `ListF` disclosed in the header.
- [ ] The colist carrier defined with its bisimilarity setoid.
- [ ] The coalgebra structure defined and the anamorphism constructed for an arbitrary coalgebra.
- [ ] Finality proved: `@Terminal (FCoalg …)`, with uniqueness up to bisimilarity.
- [ ] The contrast with the initial algebra (finite lists) recorded, so the exercise's hint is visible in the file.
- [ ] Statement fidelity to the book: setoid `≈` discipline throughout; never `=` on morphisms.
- [ ] No `Admitted`, `admit` or `Axiom` in the new material; any coinduction-related axiom dependency disclosed in the header and in `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported for the final coalgebra.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds under the Coq 8.19 / 8.20 nix targets.
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files entry for the (co)algebra witnesses extended (currently only the stream final coalgebra is indexed).

## Verification

```bash
coqc -R . Category Instance/Sets/Colists.v
```

```coq
Print Assumptions Colist_final.
```

```bash
make -j
nix build .#category-theory_8_20
make todo
```

Review items: the endofunctor really is `1 + A × X` (with the unit summand), not `A × X`; the carrier contains the finite lists as well as the infinite ones, as Awodey's hint requires; uniqueness is proved, not assumed.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:10:ex10"],"deps":[]} -->

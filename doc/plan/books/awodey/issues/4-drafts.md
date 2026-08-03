title: "Awodey 4.3: The homomorphism theorem for categories — kernel congruence, kernel category, and the bijective-on-objects/faithful factorization of a functor"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:4.3:construction-congruence-category, awodey:4.3:def-kernel-congruence, awodey:4.3:def-kernel-category, awodey:4.3:thm7, awodey:4.3:cor8]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §4.3 "Groups as categories", printed pages 86–88 (PDF pages 95–97). Items covered: the congruence category `C^~` and its two projection functors, the kernel congruence `~_F` of a functor, the kernel category `ker(F)`, Theorem 4.7 (universal property of the quotient / homomorphism theorem for categories), and Corollary 4.8 (bijective-on-objects-full followed by faithful factorization of a functor). Item IDs `awodey:4.3:construction-congruence-category`, `awodey:4.3:def-kernel-congruence`, `awodey:4.3:def-kernel-category`, `awodey:4.3:thm7`, `awodey:4.3:cor8`.

## Background

A congruence on a category is an equivalence relation on parallel arrows compatible with composition; quotienting by it produces the [quotient category](https://ncatlab.org/nlab/show/quotient+category), and every functor determines a maximal such congruence (its kernel congruence), yielding the categorical analogue of the group homomorphism theorem and an orthogonal factorization of any functor into an identity-on-objects-full functor followed by a faithful one. See [nLab: quotient category](https://ncatlab.org/nlab/show/quotient+category) and [nLab: congruence](https://ncatlab.org/nlab/show/congruence).

## Current state in the library

The congruence notion and the quotient category already exist: `Construction/Quotient.v` provides `HomCongruence` (line 226), the quotient category `Quotient` (line 254), the identity-on-objects projection `QuotientProj` (line 294), and the lifting universal property `QuotientLift` / `QuotientLift_proj` / `QuotientLift_unique` (lines 313, 322, 334). The lift hypothesis `R x y f g -> fmap[F] f ≈ fmap[F] g` is precisely "the congruence refines the kernel of `F`", so the operative half of Awodey Theorem 4.7 (a functor that identifies related arrows factors uniquely through the quotient) is present.

What is missing, per §4.3: (1) the congruence category `C^~` whose arrows are the related pairs `⟨f,g⟩` with its two projection functors `p1, p2 : C^~ ⟶ C`; (2) the kernel congruence `~_F` of a functor, defined by `f ~_F g` iff `dom`/`cod` agree and `fmap[F] f ≈ fmap[F] g`, packaged as a `HomCongruence` instance; (3) the kernel category `ker(F) = C^{~_F}`; (4) the explicit biconditional form of Theorem 4.7 (a congruence refines `~_F` iff `F` factors through the corresponding quotient), including the currently-unstated converse direction; (5) Corollary 4.8's factorization of an arbitrary functor as an identity-on-objects (bijective-on-objects, surjective-on-homs) functor followed by a faithful one. The `Full`/`Faithful` classes needed for (5) are at `Theory/Functor.v:331,342`.

## Work to be done

Building on `Construction/Quotient.v`, add a module (suggested `Construction/Quotient/Kernel.v`) that:

- constructs the congruence category `C^~` from any `HomCongruence R`, with objects the objects of `C`, arrows the pairs `⟨f,g⟩` satisfying `R f g`, and the two projection functors to `C`;
- defines the kernel congruence `~_F` of a functor `F : C ⟶ D` and proves it is a `HomCongruence`;
- defines the kernel category `ker(F)` as the congruence category of `~_F`;
- states and proves Theorem 4.7 as a biconditional: a congruence `R` refines `~_F` iff `F` factors (necessarily uniquely, via `QuotientLift`) through `Quotient C R` — the forward direction is `QuotientLift`/`QuotientLift_unique`, the converse is the observation that any factorization forces `R ⊆ ~_F`;
- derives Corollary 4.8: every `F` factors as `F ≈ F~ ∘ QuotientProj` with `QuotientProj : C ⟶ Quotient C ~_F` identity-on-objects and full, and `F~` faithful (injective on hom-setoids up to `≈`).

Use the setoid discipline throughout (`≈` on morphisms, never `=`); "identical on objects" is `fobj` equality as in the existing `QuotientProj`.

## Definition of Done

- [ ] `C^~` (congruence category) and its two projection functors defined and proven functorial.
- [ ] Kernel congruence `~_F` defined and proven to be a `HomCongruence`.
- [ ] Kernel category `ker(F)` defined via `~_F`.
- [ ] Theorem 4.7 proven as an explicit biconditional (both the factorization and its converse), with uniqueness of the induced functor.
- [ ] Corollary 4.8 proven: the induced `QuotientProj` is identity-on-objects and full, and `F~` is faithful.
- [ ] All statements use setoid equivalence `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`; `make todo` reports no new hits.
- [ ] `Print Assumptions` is closed (no unexpected axioms) for `ker`, the Theorem 4.7 artifact, and the Corollary 4.8 factorization.
- [ ] New module registered in `_CoqProject`.
- [ ] `make` is green on Rocq 9.1 and builds on Coq 8.19/8.20 (nix targets).

## Verification

- `coqc -R . Category Construction/Quotient/Kernel.v` compiles cleanly.
- `Print Assumptions` on the kernel category, the Theorem 4.7 biconditional, and the Corollary 4.8 factorization shows no axioms beyond the library baseline (docs/AXIOMS.md).
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the statements match Awodey §4.3 (Theorem 4.7, Corollary 4.8) up to setoid presentation.

## Dependencies

Builds on `Construction/Quotient.v` (already in-tree; no coverage-gap dependency).

<!-- catalog: {"ids":["awodey:4.3:construction-congruence-category","awodey:4.3:def-kernel-congruence","awodey:4.3:def-kernel-category","awodey:4.3:thm7","awodey:4.3:cor8"],"deps":[]} -->

---8<---

title: "Awodey 4.3–4.4: Coequalizers of functors in Cat via congruence quotients"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:4.3:construction-quotient-category, awodey:4.4:construction-fp-coequalizer, awodey:4:ex5]
deps_item_ids: [awodey:4.3:construction-congruence-category, awodey:4.3:def-kernel-congruence]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §4.3 "Groups as categories" (printed p. 87, PDF p. 96), §4.4 "Finitely presented categories" (printed pp. 89–90, PDF pp. 98–99), and §4.5 Exercise 5 (starred; printed p. 92, PDF p. 101). Items covered: the quotient category `C/~` presented as a coequalizer of categories `C^~ ⇒ C → C/~`; the presentation-by-one-relation result exhibiting the quotient functor `q : C → C/~` as the coequalizer of two functors out of the walking arrow; and Exercise 5's construction of the coequalizer of an object-agreeing functor pair via a congruence. Item IDs `awodey:4.3:construction-quotient-category`, `awodey:4.4:construction-fp-coequalizer`, `awodey:4:ex5`.

## Background

The quotient of a category by a congruence is not only a category but a colimit: it is the [coequalizer](https://ncatlab.org/nlab/show/coequalizer) of the two projections of the congruence category, and more generally the coequalizer of a pair of functors that agree on objects is computed as the quotient by the congruence they generate. See [nLab: coequalizer](https://ncatlab.org/nlab/show/coequalizer) and [nLab: quotient category](https://ncatlab.org/nlab/show/quotient+category).

## Current state in the library

`Construction/Quotient.v` supplies the quotient category `Quotient` (line 254), its identity-on-objects projection `QuotientProj` (line 294), and the unique-lifting universal property `QuotientLift` / `QuotientLift_unique` (lines 313, 334). This is the reusable engine, but the colimit content is absent: `Cat` (`Instance/Cat.v`) is not shown to have coequalizers, and a search of `Instance/Cat*` for coequalizers returns nothing. Consequently three §4.3–4.5 claims are unformalized: that `C^~ ⇒ C → C/~` is a coequalizer of categories; that the quotient by a single relation `f ~ f'` is the coequalizer of the two functors selecting `f` and `f'` out of the walking arrow (`Instance/Two.v` supplies the walking arrow); and Exercise 5's specific congruence on the arrows of `D` (relate `f, g` when every `H` coequalizing the pair identifies them) together with the theorem that its quotient is the coequalizer of the object-agreeing pair. The coequalizer predicate itself exists as `Structure/Coequalizer.v` `IsCoequalizer` (line 52), so the target shape is available.

## Work to be done

In a new module (suggested `Instance/Cat/Coequalizer.v`), building on the kernel-congruence machinery of Awodey §4.3 and on `Construction/Quotient.v`:

- prove that for a `HomCongruence R`, the diagram `C^~ ⇒ C → Quotient C R` is an `IsCoequalizer` in `Cat` (the two projections of the congruence category, coequalized by `QuotientProj`);
- for a functor pair `F, G : C ⟶ D` that agree on objects, define the generated congruence on `D` (Exercise 5's relation: `f ~ g` iff every functor `H` with `H∘F = H∘G` satisfies `H f ≈ H g`), prove it is a `HomCongruence`, and prove the quotient `D/~` with its projection is the coequalizer of `F` and `G`;
- specialize to a single relation `f ~ f'` selected by two functors out of the walking arrow (`Instance/Two.v`) to recover the §4.4 presentation-as-coequalizer statement.

Note that Exercise 5's printed conclusion writes `C/~` where `D/~` is meant (a source typo); formalize the corrected statement.

Use `≈` on morphisms throughout; functor equality on objects is `fobj` equality as in `QuotientProj`.

## Definition of Done

- [ ] `C^~ ⇒ C → Quotient C R` proven to be an `IsCoequalizer` in `Cat`.
- [ ] Exercise 5's congruence on `Arr(D)` defined and proven to be a `HomCongruence`.
- [ ] The quotient of an object-agreeing pair `F, G` proven to be their coequalizer in `Cat`.
- [ ] The §4.4 single-relation presentation recovered as the coequalizer of the two walking-arrow-selecting functors.
- [ ] All statements use setoid equivalence `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`; `make todo` reports no new hits.
- [ ] `Print Assumptions` closed for each coequalizer artifact.
- [ ] New module registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.

## Verification

- `coqc -R . Category Instance/Cat/Coequalizer.v` compiles cleanly.
- `Print Assumptions` on the coequalizer witnesses shows no unexpected axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the coequalizer statements match Awodey §4.3–4.4 and the corrected Exercise 5.

## Dependencies

Depends on: awodey:4.3:construction-congruence-category
Depends on: awodey:4.3:def-kernel-congruence
Depends on: #299

<!-- catalog: {"ids":["awodey:4.3:construction-quotient-category","awodey:4.4:construction-fp-coequalizer","awodey:4:ex5"],"deps":["awodey:4.3:construction-congruence-category","awodey:4.3:def-kernel-congruence","#299"]} -->

---8<---

title: "Awodey 4.4: Finitely presented example categories — the walking isomorphism, Z/2Z, cyclic groups, and presentations of the category 3"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:4.4:example9, awodey:4:ex3]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §4.4 "Finitely presented categories" Example 4.9 (printed p. 90, PDF p. 99) and §4.5 Exercise 3 (printed p. 91, PDF p. 100). Items covered: the finite non-free presented categories of Example 4.9 — the walking isomorphism (two objects uniquely isomorphic), the two-element cyclic group `Z/2Z` and the idempotent monoid presented by one endo-generator, and the cyclic groups `Z_n` presented by `f^n = 1` on one object — together with Exercise 3's four presentations of the poset category `3` and the question of its freeness. Item IDs `awodey:4.4:example9`, `awodey:4:ex3`.

## Background

A category presented by generators and relations is the free category on a graph quotiented by the congruence generated by the relations; small finite examples (the walking isomorphism, a cyclic group as a one-object category) show that presented categories are generally not free, having cycles and finitely many arrows. See [nLab: walking structures](https://ncatlab.org/nlab/show/walking+structure) and [nLab: free category](https://ncatlab.org/nlab/show/free+category).

## Current state in the library

The building blocks exist — `Construction/Free.v` (the path category on a quiver, line 118) and `Construction/Quotient.v` (quotient by a congruence, line 254) — but none of Example 4.9's concrete categories is constructed. `Instance/Two.v` is the walking *arrow* (`0 → 1`, no inverse), not the walking *isomorphism*; a search finds no `Z/2Z`, no cyclic-group-as-one-object-category, and no idempotent-monoid presented category. The poset category `3` (the commuting triangle) is likewise not presented by generators and relations, and its freeness is not addressed. These examples all require the finitely-presented-category machinery (the congruence generated by a finite relation set), which is itself the subject of a separate issue.

## Work to be done

Once the general presented-category construction (least congruence generated by a finite relation set) is available, add example instances (suggested `Instance/WalkingIso.v` for the walking isomorphism, and a small `Instance/Presented/Cyclic.v` for the one-object examples):

- the walking isomorphism: the graph with two vertices and arrows `f : A → B`, `g : B → A`, presented by `g∘f = 1_A`, `f∘g = 1_B`; verify it is finite with a genuine cycle hence not free, and that `f` is an isomorphism in it;
- the one-object presentations: `f∘f = 1` presenting `Z/2Z`, `f∘f = f` presenting the two-element idempotent monoid, and `f^n = 1` presenting the cyclic group `Z_n`;
- Exercise 3: four distinct generators-and-relations presentations of the poset category `3` (`1 → 2 → 3` with the composite `1 → 3`), and a proof that `3` is free on the graph `1 → 2 → 3` (no relations needed — the composite is forced, not imposed), so the answer to "is `3` free?" is yes.

Use `≈` on morphisms; where a finite hom-set is exhibited, prove the enumeration and the relations decide equality.

## Definition of Done

- [ ] Walking isomorphism category constructed by presentation; `f` proven an isomorphism; non-freeness argument recorded (finite with a cycle).
- [ ] `Z/2Z`, the idempotent monoid, and the cyclic groups `Z_n` constructed as one-object presented categories.
- [ ] Four presentations of the category `3` given, and its freeness settled with proof.
- [ ] All statements use setoid equivalence `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`; `make todo` reports no new hits.
- [ ] `Print Assumptions` closed for each example category.
- [ ] New modules registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.

## Verification

- `coqc -R . Category Instance/WalkingIso.v` (and the cyclic-examples module) compiles cleanly.
- `Print Assumptions` on each example category shows no unexpected axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the presentations and the freeness verdict match Awodey Example 4.9 and Exercise 3.

## Dependencies

Depends on: #299

<!-- catalog: {"ids":["awodey:4.4:example9","awodey:4:ex3"],"deps":["#299"]} -->

---8<---

title: "Awodey 4.1: Group objects in Sets, Top, and Pos recover ordinary, topological, and ordered groups"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:4.1:example3]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §4.1 "Groups in a category" Example 4.3 (printed p. 82, PDF p. 91). The example instantiates the group-object definition in several ambient categories: a group object in Sets is an ordinary group, in Top a topological group, and in Pos an ordered group (with order-reversing inverse); ℝ under addition witnesses both the topological and the ordered cases. Item ID `awodey:4.1:example3`.

## Background

A [group object](https://ncatlab.org/nlab/show/group+object) internal to a category with finite products specializes, by choice of ambient category, to the classical structured groups — ordinary groups in Set, topological groups in Top, Lie groups in smooth manifolds. See [nLab: group object](https://ncatlab.org/nlab/show/group+object) and [Wikipedia: Group object](https://en.wikipedia.org/wiki/Group_object).

## Current state in the library

`Structure/Group.v` defines `GroupObject` (line 109) over a `CartesianMonoidal` base, and its header explicitly cites Awodey Chapter 4, but there is no `GroupObject` *instance* in any concrete category: no `@GroupObject Sets`, and the classical recovery "a group object in Sets is exactly an ordinary group" is nowhere proven. `Instance/Comp.v` carries a separate universal-algebra encoding `Group := Algebra GroupOp GroupEq` (line 382) — groups as equational models over Coq `Type` — but this is not connected to `GroupObject`, and no equivalence between the two is established. There is no category of topological spaces in-tree, so the Top instance cannot yet be formed; `Instance/Poset.v` provides Pos but carries no ordered-group object.

## Work to be done

In a new module (suggested `Instance/Sets/Group.v`):

- exhibit a `GroupObject` in `Sets` from an ordinary group (in the sense already available via `Instance/Comp.v`'s group encoding, or a direct setoid group), and conversely extract an ordinary group from any group object in `Sets`;
- prove these are mutually inverse, i.e. group objects in `Sets` correspond to ordinary groups, and (once the category of internal groups is available) that this extends to an equivalence `Group(Sets) ≃ Grp`;
- record the Top and Pos cases as scoped follow-ups: the ordered-group object over `Instance/Poset.v` (inverse as an order-reversing map, i.e. `i : G^op → G`) is formalizable now; the topological-group case is blocked on the absence of a category of topological spaces and should be noted, not attempted here.

Use `≈` on morphisms; the multiplication/unit/inverse are the `mappend`/`mempty`/`inverse` of `GroupObject`.

## Definition of Done

- [ ] A `GroupObject` instance in `Sets` constructed from an ordinary group.
- [ ] The reverse extraction and a proof that the two constructions are mutually inverse (group objects in Sets ⟺ ordinary groups).
- [ ] The ordered-group object over Pos formalized, with the order-reversing inverse.
- [ ] The topological-group case documented as blocked on a missing category of spaces (no attempt required).
- [ ] All statements use setoid equivalence `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom` in the core artifacts; `make todo` reports no new hits.
- [ ] `Print Assumptions` reported for the Sets group-object instance and the correspondence (instance-layer stdlib axioms per docs/AXIOMS.md are acceptable and must be enumerated).
- [ ] New module registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.

## Verification

- `coqc -R . Category Instance/Sets/Group.v` compiles cleanly.
- `Print Assumptions` on the Sets group-object correspondence enumerates only the expected instance-layer axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the recovery statements match Awodey Example 4.3.

## Dependencies

Depends on: #343

<!-- catalog: {"ids":["awodey:4.1:example3"],"deps":["#343"]} -->

---8<---

title: "Awodey 4.5 Ex 2: Internal groups in a slice Sets/I as an I-indexed family of groups"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:4:ex2]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §4.5 Exercise 2 (printed p. 91, PDF p. 100). The exercise applies the group-object definition to the slice `Sets/I`: an internal group `G` there determines an `I`-indexed family of ordinary groups `G_i` (the fibres), and this assignment is a functor from the category of internal groups in `Sets/I` to the category `Groups^I` of `I`-indexed families of groups and their `I`-indexed families of homomorphisms. Item ID `awodey:4:ex2`.

## Background

Group objects internal to a [slice category](https://ncatlab.org/nlab/show/slice+category) `Sets/I` are exactly `I`-indexed families of ordinary groups, since the slice `Sets/I` is equivalent to the category of `I`-indexed sets and finite products are computed fibrewise. See [nLab: group object](https://ncatlab.org/nlab/show/group+object) and [nLab: slice category](https://ncatlab.org/nlab/show/slice+category).

## Current state in the library

`Structure/Group.v` `GroupObject` (line 109) supplies the internal-group notion, and `Construction/Slice.v` `Slice` (line 123) supplies `Sets/I`, but the two are never combined: there is no analysis of group objects in a slice, no category `Groups^I` of indexed families of groups, and no functor from internal groups over the slice to that family category. The category of internal groups itself is not yet assembled in general (subject of a separate issue).

## Work to be done

In a new module (suggested `Instance/Slice/Group.v` or `Construction/Slice/Group.v`), once the category of internal groups is available:

- take a group object in `Sets/I` and construct, for each `i : I`, the fibre group `G_i` (its underlying set `G^{-1}(i)` with the fibrewise multiplication/unit/inverse), proving each is an ordinary group;
- assemble the target category `Groups^I` (I-indexed families of groups, with I-indexed families of homomorphisms) — or reuse an existing indexed-family construction if applicable;
- define the assignment on objects and morphisms and prove it is a functor `Group(Sets/I) ⟶ Groups^I`.

Use `≈` on morphisms throughout; the fibrewise structure comes from the slice's finite products.

## Definition of Done

- [ ] The fibre groups `G_i` of an internal group in `Sets/I` constructed and proven to be ordinary groups.
- [ ] The category `Groups^I` of I-indexed families of groups assembled (or an existing construction reused).
- [ ] The functor `Group(Sets/I) ⟶ Groups^I` defined and proven functorial.
- [ ] All statements use setoid equivalence `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom` in the core artifacts; `make todo` reports no new hits.
- [ ] `Print Assumptions` reported for the functor (instance-layer stdlib axioms per docs/AXIOMS.md enumerated if used).
- [ ] New module registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.

## Verification

- `coqc -R . Category Instance/Slice/Group.v` compiles cleanly.
- `Print Assumptions` on the functor enumerates only expected axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the statement matches Awodey Exercise 2 of §4.5.

## Dependencies

Depends on: #343

<!-- catalog: {"ids":["awodey:4:ex2"],"deps":["#343"]} -->

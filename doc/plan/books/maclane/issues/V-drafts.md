```yaml
title: "MacLane V.1: Creation of limits by a functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:def3, maclane:V.4:thm2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121); §V.4, book p. 117 (PDF p. 126)
- Items: `maclane:V.1:def3`, `maclane:V.4:thm2`

## Background
Creation of limits is the strongest of the three transfer notions (preserve / reflect / create): a
functor creates the limit of a diagram when every limiting cone downstairs lifts to exactly one cone
upstairs, and that lift is itself limiting. It is the property that makes "limits in an algebraic
category are computed on underlying sets" a theorem rather than a slogan, and it implies preservation
whenever the downstairs limit exists. See [nLab: created limit](https://ncatlab.org/nlab/show/created+limit)
and [nLab: preserved limit](https://ncatlab.org/nlab/show/preserved+limit).

## Current state in the library
Verified PARTIAL (definition) and ABSENT (theorem). The library has no general creation predicate:

- `Structure/Limit/Preservation.v:48` (`PreservesLimit`), `:229` (`PreservesAllLimits`) and the
  `ReflectsIsos` vocabulary in the same file are the only transfer classes; there is no
  `CreatesLimit`.
- `Monad/Monadicity/Beck.v:164` (`CreatesUSplitCoequalizers`) is a genuine creation predicate — it
  carries both the reflection clause and the uniqueness corollary — but it is hard-wired to one
  diagram shape for Beck's theorem, and its header at `:52` records the deliberate deviation from
  the book's formulation.
- `Theory/Equivalence/Limit.v:486` (`equivalence_creates_limits`) is, despite its name, only
  `Limit (F ◯ G) → Limit G` by transport along a quasi-inverse: no uniqueness-of-lift clause at all
  (verifier-confirmed).
- Prose in `Construction/Comma.v:100` and `Construction/Comma/Limit.v:33` asserts that the comma
  projection "creates" limits, but the files prove existence only.

Consequently Mac Lane's §V.4 Theorem 2 (creation plus existence implies preservation; creation of all
small limits transports completeness and continuity) cannot even be stated in-tree.

## Work to be done
Suggested module: `Structure/Limit/Creation.v` (next to `Structure/Limit/Preservation.v`).

1. Define `CreatesLimit (V : A ⟶ X) (F : J ⟶ A)`: for every limiting cone over `V ◯ F` in `X`, a cone
   over `F` in `A` lying over it, unique in the appropriate sense, and itself limiting. Decide and
   disclose the strictness question the setoid setting forces — on-the-nose equality of the image
   cone versus an invertible comparison — following the precedent and header discussion of
   `Monad/Monadicity/Beck.v:41-52`; the iso-invariant reading is the usable one.
2. Derive the shape variants Mac Lane names: creates products (`J` discrete, via
   `Instance/Discrete.v:37`), creates finite limits, and creates colimits by `C^op` duality, so the
   dual costs one line.
3. Prove §V.4 Theorem 2: if `V` creates the limit of `F` and `V ◯ F` has a limit then `V` preserves
   that limit; and if `V` creates all small limits and `X` is complete then `A` is complete
   (`Structure/Complete.v:115`) and `V` is continuous (`Structure/Limit/Preservation.v:19`).
   State preservation in the cone-level sense, not the apex-only `PreservesLimit` (see §V.4's
   definition issue).
4. Re-file the existing witnesses under the new vocabulary: give `Monad/Monadicity/Beck.v:164` a
   comparison lemma to the general class, and correct or strengthen
   `Theory/Equivalence/Limit.v:486` so its name matches what it proves.

In-tree donors: `Structure/Limit.v`, `Structure/Cone.v`, `Structure/Limit/Preservation.v`,
`Monad/Monadicity/Beck.v`, `Instance/Discrete.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121); §V.4, book p. 117 (PDF p. 126)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level
- [ ] The naming defect is resolved: either `equivalence_creates_limits` (`Theory/Equivalence/Limit.v:486`) is proved to satisfy the new `CreatesLimit` class, or it is renamed to reflect that it only transports a limit

## Verification
```bash
coqc -R . Category Structure/Limit/Creation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CreatesLimit.
Print Assumptions creation_preserves_limit.
Print Assumptions creates_limits_Complete.
```
Reviewer: the definition must have BOTH clauses of Mac Lane §V.1 (uniqueness of the lifted cone, and
that the lift is limiting) — a predicate that only transports a limit is not creation; and the §V.4
Theorem 2 statement must be the cone-level preservation, not apex-only.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.1:def3","maclane:V.4:thm2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.1: Completeness of Sets by cone sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:thm1, maclane:V.1:remark1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 110 (PDF p. 119)
- Items: `maclane:V.1:thm1`, `maclane:V.1:remark1`

## Background
Mac Lane's proof that Set is small-complete is the cone-set construction: the limit of a
`Set`-valued diagram is the set of cones from the one-point set, with the limiting cone given by
evaluation at each index. Read as a bijection natural in the apex, it is exactly the hom-set form of
the adjunction between the diagonal functor and the limit functor. See
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL. Nothing in the tree exhibits a limit of a general `Sets`-valued diagram, and
`@Complete Sets` is uninhabited — `docs/INHABITATION.md:53` records that no `Complete`/`Cocomplete`
instance exists anywhere in the library, so the GAFT/SAFT hypotheses have never been discharged at a
concrete category. What does exist:

- `Structure/Cone.v:79` (`ConePresheaf`) already names the setoid of cones over a diagram with a
  given apex, so the intended apex is literally `ConePresheaf F (terminal_obj Sets)`; what is missing
  is `IsALimit F` for it.
- `Instance/Sets/End.v:59` (`end_family`) and `:144` (`Sets_End`) build the compatible-family
  sub-setoid, but only at the wedge/end shape.
- `Instance/Sets.v:248` (`Sets_Terminal`), `Instance/Sets/Cartesian.v:32` (`Sets_Cartesian`): the
  discrete cases exist only for the empty and two-element index shapes.
- No `Sets` equalizer instance exists (`grep Sets_Equalizer` → 0 hits), so even the
  products-and-equalizers route to completeness is unavailable.
- `Structure/Limit/Kan/Extension.v:46` (`Kan_Limit`) relates a limit to a right Kan extension, but
  the limit-as-right-adjoint reading of the remark is not available for a general index category
  (only `Adjunction/Diagonal/Product.v:36`, the binary-product row).

## Work to be done
Suggested module: `Instance/Sets/Complete.v`.

1. Prove `IsALimit F (ConePresheaf F (terminal_obj Sets))` for every `F : J ⟶ Sets`: legs are
   evaluation at each index, the mediating map sends an element of the apex to the cone it induces,
   with uniqueness from extensionality of setoid maps. No choice, no funext — the setoid discipline
   makes the compatible-family carrier a plain sub-setoid, as in `Instance/Sets/End.v`.
2. Assemble `Sets_Complete : @Complete Sets`, the library's first concrete completeness witness, and
   update `docs/INHABITATION.md` accordingly.
3. Record the special cases: the discrete-shape instance is the indexed product of #254 (prove they
   agree, do not duplicate), and the parallel-pair shape gives `HasEqualizers Sets`, which several
   downstream results want by name.
4. Prove the remark's bijection `Cone(X, F) ≅ Sets(X, Cone(1, F))` natural in `X`, and identify it
   with the counit/transposition of the diagonal-limit adjunction of #353 instantiated at `Sets`, so
   the cone API and the adjunction API are visibly the same thing.

In-tree donors: `Structure/Cone.v`, `Structure/Limit.v`, `Instance/Sets.v`, `Instance/Sets/End.v`,
`Structure/Limit/Weighted.v` (the `wl_iso` naturality pattern).

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 110 (PDF p. 119)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Sets/Complete.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_Complete.
Print Assumptions Sets_cone_limit.
```
Reviewer: the apex must be the cone setoid of `Structure/Cone.v:79` (not a re-derived copy); the
limiting cone must be evaluation; the naturality of the bijection in the apex variable must be
proved, not asserted.

## Dependencies
Depends on: #254
Depends on: #353

<!-- catalog: {"ids":["maclane:V.1:thm1","maclane:V.1:remark1"],"deps":["#254","#353"]} -->
---8<---
```yaml
title: "MacLane V.1: Inverse limits of towers of sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:construction1]
deps_item_ids: [maclane:V.1:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 109 (PDF pp. 118–119)
- Items: `maclane:V.1:construction1`

## Background
The inverse (projective) limit of a tower of sets indexed by the opposite of the natural numbers is
the set of matching strings: sequences whose successive entries are carried to one another by the
transition maps. Mac Lane observes that a matching string is precisely a cone from the one-point set,
which is why the general cone-set formula specialises to the familiar description. See
[Wikipedia: Inverse limit](https://en.wikipedia.org/wiki/Inverse_limit) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL. The tower shape exists but is never given a limit: `Instance/Omega.v:72` (`Omega`)
is the ordinal ω as a thin category and `Construction/Chain.v:78` (`Cochain`) supplies the dual
orientation, yet no functor out of `Omega^op` into `Sets` is anywhere shown to have a limit. The
compatible-family idiom that the construction needs exists only at the end/wedge shape
(`Instance/Sets/End.v:59`, `:144`), and `Sets` has no indexed products (`Structure/Limit/Product.v:93`
defines `iprod` as a discrete-diagram limit with no `Sets` instance, and `:128`'s
`HasIndexedProducts` has zero instances tree-wide). `Structure/Limit.v:51-55` mentions inverse limits
and profinite objects in its background essay only.

## Work to be done
Suggested module: `Instance/Sets/InverseLimit.v`.

- For `F : Omega^op ⟶ Sets`, build the matching-string setoid — dependent sequences with the
  compatibility equation at each step, equality pointwise — with its projections, and prove it is a
  limiting cone.
- Prove it isomorphic to the general cone-set limit of §V.1 Theorem 1 (dependency below), so the
  concrete and abstract descriptions are provably the same object rather than parallel developments.
- Provide the tower API downstream issues need: the projections, the induced map out of any cone
  (the "compatible family determines an element" form), and the statement that an element is
  determined by its coordinates.
- State the construction for an arbitrary index category as the trivial specialisation remark, so
  readers are not misled into thinking the tower case is special.

In-tree donors: `Instance/Omega.v`, `Construction/Chain.v`, `Instance/Sets/End.v`, `Structure/Cone.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 109 (PDF pp. 118–119)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Sets/InverseLimit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_tower_limit.
Print Assumptions Sets_tower_limit_iso_cone_limit.
```
Reviewer: statement fidelity to Mac Lane §V.1 (matching strings, the projection cone), and the
isomorphism with the general cone-set limit must be proved.

## Dependencies
Depends on: maclane:V.1:thm1

<!-- catalog: {"ids":["maclane:V.1:construction1"],"deps":["maclane:V.1:thm1"]} -->
---8<---
```yaml
title: "MacLane V.1: The p-adic integers and formal power series as inverse limits of rings"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:construction2, maclane:V.1:ex6, maclane:V.1:ex7]
deps_item_ids: [maclane:V.1:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book pp. 110–112 (PDF pp. 119–121)
- Items: `maclane:V.1:construction2`, `maclane:V.1:ex6`, `maclane:V.1:ex7`

## Background
Mac Lane's headline example of an inverse limit: the ring of p-adic integers as the limit of the
tower of residue rings modulo successive powers of p, with the digit expansion and the schoolbook
arithmetic of left-infinite base-p strings falling out of the limit description; the same recipe over
truncated polynomial rings yields formal power series. See
[Wikipedia: p-adic number](https://en.wikipedia.org/wiki/P-adic_number) and
[Wikipedia: Formal power series](https://en.wikipedia.org/wiki/Formal_power_series).

## Current state in the library
Verified ABSENT (all three). There is no category of rings in the tree at all
(`rg -w 'Rng|CRing|RingObject'` → 0 hits; the case-insensitive "ring" matches are `pairing`,
`copairing`, `tensoring` and background prose), so neither the residue rings nor the truncated
polynomial rings can be named; `Structure/Limit.v:51` mentions the p-adic integers as an inverse
limit in its historical essay and `:53-55` mentions profinite objects, both prose only. The digit
expansion and base-p arithmetic have no in-tree counterpart (`rg -i 'digit|base-p'` → nothing
relevant), and no tower in any category is given a limit (see the tower issue below).

## Work to be done
Suggested modules: `Instance/Rng/Zp.v` and `Instance/Rng/PowerSeries.v`, over the ring category of
#257.

- The residue tower: the rings of integers modulo successive powers of a prime, with the canonical
  projections, as a functor out of `Omega^op` into rings.
- Its limit: carrier the matching-string setoid, ring operations defined coordinatewise, and the
  proof that these operations are the unique ones making all projections ring maps (this is the
  algebraic-lifting pattern of §V.1 Theorem 2, so state it that way rather than ad hoc).
- The digit expansion (Exercise 6): a bijection between p-adic integers and sequences of digits below
  p, with addition and multiplication corresponding to carry-propagating operations on digit
  sequences — decidable arithmetic on `nat`, so the proofs are computational and axiom-free.
- Formal power series (Exercise 7): the tower of polynomial rings modulo the ideal generated by a
  power of the indeterminate, with its limit shown isomorphic to the power-series ring (coefficient
  sequences with convolution product).

In-tree donors: the tower limit issue below, `Instance/Omega.v`, `Instance/CMon.v` (algebraic
structure over setoids), `Instance/Comp.v` (signature/algebra idiom).

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book pp. 110–112 (PDF pp. 119–121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Rng/Zp.v Instance/Rng/PowerSeries.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Zp_limit.
Print Assumptions Zp_digits_iso.
Print Assumptions PowerSeries_limit.
```
Reviewer: statement fidelity to Mac Lane §V.1 (book pp. 110–112) — in particular that the ring
structure on the limit is forced, not merely exhibited.

## Dependencies
Depends on: #257
Depends on: maclane:V.1:construction1

<!-- catalog: {"ids":["maclane:V.1:construction2","maclane:V.1:ex6","maclane:V.1:ex7"],"deps":["#257","maclane:V.1:construction1"]} -->
---8<---
```yaml
title: "MacLane V.1: The p-adic solenoid as a limit in Top"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:construction3]
deps_item_ids: [maclane:V.1:construction1, maclane:V.9:remark1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 111 (PDF p. 120)
- Items: `maclane:V.1:construction3`

## Background
The p-adic solenoid is the limit in the category of spaces of the tower whose objects are all circles
and whose transition maps wrap the circle p times around itself; the underlying set is the inverse
limit of the underlying sets, topologised by the coarsest topology making all projections continuous.
See [Wikipedia: Solenoid (mathematics)](https://en.wikipedia.org/wiki/Solenoid_(mathematics)) and
[nLab: Top](https://ncatlab.org/nlab/show/Top).

## Current state in the library
Verified ABSENT. There is no category of topological spaces in the tree (the full instance layer is
`Sets`, `Coq`, `Cat`, `Fun`, `FinSet`, `CMon`, `Rel`, `Poset`, `Proset`, `Lambda`, `ZX`, `Ens`,
`Comp`, `Omega`, `Two`, `One`, `Zero`, …); every occurrence of "topology" in a `.v` file is either a
Grothendieck topology in `Theory/Sheaf.v:23,44,74-80` or background prose, and `rg -i 'solenoid'`,
`rg -i 'circle'` (as a space) and `rg -i 'coarsest|initial topology'` all return nothing usable. So
neither the diagram, nor its limit, nor the topology on the limit is expressible.

## Work to be done
Suggested module: `Instance/Top/Solenoid.v`, over the category of spaces of #259.

- The circle as an object of the space category (as a quotient of the reals, or — cheaper and
  adequate for this item — as any chosen object equipped with the p-fold self-map; state which
  presentation is used in the header).
- The tower of circles with the p-fold covering maps as a functor out of `Omega^op`.
- Its limit: the matching-string set of the tower issue below, carrying the initial topology for the
  projections, proved limiting in the space category by the universal property of that topology
  (which is the content of the "Top is complete" issue in §V.9).
- Record the classical name and the fact that the underlying set is the inverse limit of underlying
  sets, i.e. the underlying-set functor preserves this limit.

In-tree donors: the tower limit issue below, `Instance/Omega.v`, the §V.9 completeness issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 111 (PDF p. 120)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Solenoid.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions solenoid_limit.
```
Reviewer: statement fidelity to Mac Lane §V.1, book p. 111 — the topology on the limit must be
characterised by its universal property, not merely posited.

## Dependencies
Depends on: #259
Depends on: maclane:V.1:construction1
Depends on: maclane:V.9:remark1

<!-- catalog: {"ids":["maclane:V.1:construction3"],"deps":["#259","maclane:V.1:construction1","maclane:V.9:remark1"]} -->
---8<---
```yaml
title: "MacLane V.1: The forgetful functor of Grp lifts and creates limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.1:thm2, maclane:V.1:thm3]
deps_item_ids: [maclane:V.1:def3, maclane:V.1:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book pp. 111–112 (PDF pp. 120–121)
- Items: `maclane:V.1:thm2`, `maclane:V.1:thm3`

## Background
The theorem behind "limits of groups are computed on underlying sets": given a diagram of groups
whose underlying diagram of sets has a limit, there is exactly one group structure on that limit
making all projections homomorphisms, and it is then the limit in groups — i.e. the underlying-set
functor creates limits. The same argument applies verbatim to rings, abelian groups and modules. See
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit) and
[Wikipedia: Category of groups](https://en.wikipedia.org/wiki/Category_of_groups).

## Current state in the library
Verified ABSENT (both). The category of groups does not exist in-tree — the three occurrences of
`Grp` are prose (`Structure/Group.v:63`, `:72`, `Structure/Complete.v:55`), `Structure/Group.v:109`
defines a group *object* internal to a cartesian category and never assembles a category of groups,
and `Instance/Comp.v:382`'s `Group := Algebra GroupOp GroupEq` is a type of algebras, not a category.
There is likewise no lifting or creation vocabulary (`rg -i 'lifts limits|creates limits'` → 0 hits)
and no limit theory for any algebra category (`Monad/Eilenberg/Moore.v`, `Monad/Algebra.v` and
`Construction/FAlg.v` contain no `Limit`/`Cone` mentions). The one forgetful functor into `Sets`,
`Instance/CMon.v:169` (`CMon_Forget`), has no consumers and is nowhere shown to preserve, reflect,
lift or create anything.

## Work to be done
Suggested module: `Instance/Grp/Limit.v`, over the group category of #255.

1. Unique lifting (Theorem 2): for a diagram of groups whose underlying diagram has a limit cone,
   construct the group structure on the limit carrier coordinatewise, prove every projection is a
   homomorphism, and prove UNIQUENESS — any group structure making all projections homomorphisms
   equals this one. Then prove the lifted cone limiting in the group category.
2. Package it as creation (Theorem 3) using the creation class of the §V.1 definition issue, and
   derive the two standard corollaries: the group category is complete whenever `Sets` is (using the
   `Sets` completeness issue below), and the forgetful functor is continuous.
3. State the argument so it is reusable for other algebraic categories — parameterise over the
   signature if that is cheap in-tree (`Instance/Comp.v`'s `Algs` is the obvious substrate), or at
   minimum leave the proof skeleton in a shape the variety issue of §V.6 can instantiate.

In-tree donors: `Instance/CMon.v` (algebraic-object-over-setoids pattern), `Structure/Cone.v`,
`Structure/Limit.v`, the creation class from the §V.1 definition issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book pp. 111–112 (PDF pp. 120–121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Grp/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Grp_Forget_lifts_limits.
Print Assumptions Grp_Forget_creates_limits.
Print Assumptions Grp_Complete.
```
Reviewer: the uniqueness half of Mac Lane's Theorem 2 must be proved (it is the whole content); and
the creation statement must use the general creation class, not a bespoke restatement.

## Dependencies
Depends on: #255
Depends on: maclane:V.1:def3
Depends on: maclane:V.1:thm1

<!-- catalog: {"ids":["maclane:V.1:thm2","maclane:V.1:thm3"],"deps":["#255","maclane:V.1:def3","maclane:V.1:thm1"]} -->
---8<---
```yaml
title: "MacLane V.1: The arrow-category projection creates limits"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.1:ex3]
deps_item_ids: [maclane:V.1:def3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121)
- Items: `maclane:V.1:ex3`

## Background
For any category, the projection from its arrow category to the product of the base with itself
(sending an arrow to its domain-codomain pair) creates limits: a limit of a diagram of arrows is
computed by taking limits of the domains and of the codomains and using the induced comparison map.
See [nLab: arrow category](https://ncatlab.org/nlab/show/arrow+category) and
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
Verified ABSENT. `Construction/Arrow.v:110` defines the arrow category as the comma category of the
identity over itself, with the arrow-category notation, and `Construction/Comma.v:185` supplies
`comma_proj : Comma ⟶ A ∏ B` — so the functor of the exercise exists — but no limit property of it is
proved anywhere; the only in-tree consumer of `Construction/Arrow.v` is
`Construction/Displayed/Codomain.v`. The creation notion itself is missing (see the §V.1 definition
issue), and `Construction/Comma/Limit.v` proves existence of comma limits only under an all-shapes
completeness oracle, never a creation statement about `comma_proj`.

## Work to be done
Suggested module: `Construction/Arrow/Limit.v`.

- Prove that `comma_proj` out of the arrow category creates limits, using the creation class from the
  §V.1 definition issue: given a limiting cone over the projected diagram in the product category,
  build the unique arrow object lying over it (the comparison map induced between the two limits),
  show the lift is unique and that it is limiting.
- Derive the corollary the exercise is used for: the arrow category is complete whenever the base is,
  with limits computed componentwise on domains and codomains.
- Keep the statement per-diagram (hypothesis: the projected diagram has a limit), not
  completeness-of-the-base, so it composes with the other creation results.

In-tree donors: `Construction/Arrow.v`, `Construction/Comma.v`, `Construction/Comma/Limit.v`,
`Structure/Cone.v`, the creation class from the §V.1 definition issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Construction/Arrow/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions arrow_proj_creates_limits.
Print Assumptions Arrow_Complete.
```
Reviewer: statement fidelity to Mac Lane §V.1 Exercise 3 (book p. 112) — creation, with the
uniqueness clause, of limits for the domain-codomain projection.

## Dependencies
Depends on: maclane:V.1:def3

<!-- catalog: {"ids":["maclane:V.1:ex3"],"deps":["maclane:V.1:def3"]} -->
---8<---
```yaml
title: "MacLane V.1: Compact Hausdorff spaces and the creation of limits"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.1:ex2]
deps_item_ids: [maclane:V.1:def3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121)
- Items: `maclane:V.1:ex2`

## Background
The underlying-set functor on compact Hausdorff spaces creates limits: the product topology on a
product of underlying sets is compact by Tychonoff and Hausdorff, and any other compact topology
making the projections continuous coincides with it, since a continuous bijection from a compact
space to a Hausdorff space is a homeomorphism. See
[nLab: compact Hausdorff space](https://ncatlab.org/nlab/show/compact+Hausdorff+space) and
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
Verified ABSENT. There is no category of compact Hausdorff spaces and no category of spaces at all:
`rg -i 'CompHaus'` → 0 hits, and the single "compact Hausdorff" mention is the bibliographic remark at
`Theory/Monad.v:65-66` about algebras of the ultrafilter monad; `rg -i 'Tychonoff'` → 0 hits. The
creation notion is likewise missing (see the §V.1 definition issue), so neither the category nor the
property of the exercise can be written down today.

## Work to be done
Suggested module: `Instance/CompHaus.v`, over the category of spaces of #259.

- Define compactness and the Hausdorff separation property for the space objects of #259, and cut out
  the full subcategory of compact Hausdorff spaces (donor: `Construction/Subcategory.v`).
- Prove the two facts the creation argument needs: a product of compact Hausdorff spaces with the
  initial topology is compact Hausdorff (Tychonoff, at whatever generality the chosen space
  presentation supports — disclose in the header if only the finite/indexed-set case is proved), and
  a continuous bijection from a compact space to a Hausdorff space is invertible.
- Prove the underlying-set functor creates limits, using the creation class of the §V.1 definition
  issue: the lifted topology is unique, and the lifted cone is limiting.
- Corollary: the category of compact Hausdorff spaces is complete, which is the hypothesis the
  Stone–Čech issues of §V.6 and §V.8 consume.

In-tree donors: #259's space category, `Construction/Subcategory.v`, the creation class from the
§V.1 definition issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/CompHaus.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CompHaus.
Print Assumptions CompHaus_Forget_creates_limits.
Print Assumptions CompHaus_Complete.
```
Reviewer: statement fidelity to Mac Lane §V.1 Exercise 2 (book p. 112); the header must disclose
exactly which form of Tychonoff's theorem is proved and at what index generality.

## Dependencies
Depends on: #259
Depends on: maclane:V.1:def3

<!-- catalog: {"ids":["maclane:V.1:ex2"],"deps":["#259","maclane:V.1:def3"]} -->
---8<---
```yaml
title: "MacLane V.1: Cat is small-complete"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.1:ex5]
deps_item_ids: [maclane:V.2:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121)
- Items: `maclane:V.1:ex5`

## Background
The category of small categories has all small limits: products are formed componentwise on objects
and arrows, equalizers are the evident subcategories, and the general limit follows by the
products-and-equalizers construction. See [nLab: Cat](https://ncatlab.org/nlab/show/Cat) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified PARTIAL. Only the finite-product corner exists: `Instance/Cat.v:142` (`Cat`),
`Instance/Cat/Cartesian.v:39` (`Cat_Cartesian`, binary products) and `Instance/One.v:54`
(`Cat_Terminal`). There are no equalizers of functors, no indexed products of categories, and no
limit file at all under `Instance/Cat/` (the directory holds `Bicategory`, `Cartesian`,
`Cocartesian` only). `@Complete Cat` is uninhabited, and the generic route to it — small products plus
equalizers give completeness — is itself missing from the tree (see the §V.2 issue below), so
supplying the two ingredients alone would not close the exercise.

## Work to be done
Suggested module: `Instance/Cat/Limit.v`.

- Indexed products of small categories: objects and arrows are families, composition and identities
  pointwise; the projections and the tupling universal property.
- Equalizers of a parallel pair of functors: the subcategory of objects and arrows on which the two
  functors agree, with the inclusion; prove the fork universal property in the
  `Structure/Equalizer/Fork.v:68` (`HasEqualizers`) form.
- Conclude `Cat_Complete : @Complete Cat` through the products-and-equalizers theorem (dependency
  below), and record the relation to #337's pullbacks in `Cat`, which become a special case.
- Mind the universe discipline: the index type must live at `Cat`'s object level; document the
  constraint in the header the way `Structure/Complete.v:30-40` does.

In-tree donors: `Instance/Cat.v`, `Instance/Cat/Cartesian.v`, `Structure/Equalizer/Fork.v`,
`Structure/Limit/Product.v`, `Construction/Subcategory.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Cat/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Cat_HasIndexedProducts.
Print Assumptions Cat_HasEqualizers.
Print Assumptions Cat_Complete.
```
Reviewer: statement fidelity to Mac Lane §V.1 Exercise 5 (book p. 112); check that the smallness side
condition is carried by universe levels and disclosed in the header.

## Dependencies
Depends on: #337
Depends on: maclane:V.2:thm1

<!-- catalog: {"ids":["maclane:V.1:ex5"],"deps":["#337","maclane:V.2:thm1"]} -->
---8<---
```yaml
title: "MacLane V.1: FinSet is finitely complete"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.1:ex4]
deps_item_ids: [maclane:V.2:def1, maclane:V.2:cor1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121)
- Items: `maclane:V.1:ex4`

## Background
Finite sets are closed under finite limits: a terminal object, binary products and equalizers suffice,
and the reduction of an arbitrary finite limit to those generators does the rest. See
[nLab: FinSet](https://ncatlab.org/nlab/show/FinSet) and
[nLab: equalizer](https://ncatlab.org/nlab/show/equalizer).

## Current state in the library
Verified PARTIAL. The skeletal finite-set category is in-tree and well equipped —
`Instance/FinSet.v:116` (`FinSet`), `:236` (`FinSet_Terminal`), `Instance/FinSet/Product.v:105`
(`FinSet_Cartesian`), `Instance/FinSet/Classifier.v:264` (`FinSet_Pullbacks`),
`Instance/FinSet/Topos.v:38` (`FinSet_Topos`) — but it has no equalizers (`rg 'qualizer' Instance/` →
0 hits) and no finite-completeness statement of any kind. Two further obstacles are disclosed in-tree:
there is no finiteness predicate on `Category`, so "every finite diagram" cannot be quantified over
(see the §V.2 definition issue), and the passage from the generators to all finite limits is
explicitly not formalized (`Structure/Topos.v:20-26`, `Structure/Regular.v:26-31`, with the
corresponding `jww` TODO at `Structure/Pullback.v:266-275`).

## Work to be done
Suggested module: `Instance/FinSet/Limit.v`.

- `FinSet_HasEqualizers`: the equalizer of a parallel pair of functions between finite skeletal sets,
  as the counted sub-object of agreement, in the positional-codec style of
  `Instance/FinSet/Product.v` and `Instance/FinSet/Classifier.v` (decidable equality on the skeleton
  keeps it computational and axiom-free).
- Instantiate the finite-limit definition and the terminal-plus-products-plus-equalizers reduction of
  §V.2 (dependencies below) to get `FinSet_FinitelyComplete`.
- Discharge the disclosure: update the `Structure/Topos.v:20-26` header note where it says the
  reduction is not formalized, and add a computable sanity example in the style of
  `Instance/FinSet/Topos.v` (an equalizer that evaluates by `eq_refl`).

In-tree donors: `Instance/FinSet.v`, `Instance/FinSet/Product.v`, `Instance/FinSet/Classifier.v`,
`Structure/Equalizer/Fork.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/FinSet/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions FinSet_HasEqualizers.
Print Assumptions FinSet_FinitelyComplete.
Compute (* the sanity example *).
```
Reviewer: statement fidelity to Mac Lane §V.1 Exercise 4 (book p. 112) — "finitely complete" must be
the quantified statement over finite index categories, not a bundle of named finite shapes.

## Dependencies
Depends on: maclane:V.2:def1
Depends on: maclane:V.2:cor1

<!-- catalog: {"ids":["maclane:V.1:ex4"],"deps":["maclane:V.2:def1","maclane:V.2:cor1"]} -->
---8<---
```yaml
title: "MacLane V.2: Limits from products and equalizers"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.2:thm1, maclane:V.2:thm2, maclane:V.2:cor2, maclane:V.4:ex2]
deps_item_ids: [maclane:V.4:def1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 113 (PDF p. 122); §V.4, book p. 118 (PDF p. 127)
- Items: `maclane:V.2:thm1`, `maclane:V.2:thm2`, `maclane:V.2:cor2`, `maclane:V.4:ex2`

## Background
The central existence theorem for limits: if a category has equalizers and products indexed by the
objects and by the arrows of the index category, then every diagram of that shape has a limit,
obtained as the equalizer of two canonical maps between those two products; hence products plus
equalizers give completeness, and a functor preserving both is continuous. See
[nLab: limit](https://ncatlab.org/nlab/show/limit) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified ABSENT (theorems and corollary) and ABSENT (the preservation exercise). Every ingredient is
present and the conclusion is nowhere drawn: `Structure/Limit/Product.v:93` (`iprod`), `:99`
(`iprod_proj`), `:105` (`iprod_ump`) and `:128` (`HasIndexedProducts`, zero instances),
`Structure/Equalizer/Fork.v:68` (`HasEqualizers`), `Structure/Limit.v:113` (`Limit`). The reduction
appears thirteen times across eight files as background prose (`Structure/Complete.v:49-53`,
`Structure/Equalizer.v:80`, `Structure/Limit.v:94-103`, `Structure/Pullback.v:272`, …) and never as a
theorem. The only related in-tree result runs the other way: `Adjunction/GAFT.v:193`
(`Complete_HasEqualizers`) extracts equalizers from completeness. On the preservation side, no lemma
derives limit preservation from preservation of products and equalizers, and
`Functor/Structure/Cartesian.v:49` (`CartesianFunctor`) is never combined with an equalizer-preservation
hypothesis.

## Work to be done
Suggested module: `Structure/Limit/FromProducts.v`.

1. The construction: for `F : J ⟶ C`, form the product over the objects of `J` and the product over
   the arrows of `J` of the codomain values, define the two canonical maps by their components
   (projection at the codomain; the diagram's action composed with the projection at the domain), and
   prove that an equalizer of them, with legs the composites with the object projections, is a
   limiting cone — including the explicit description of the limiting cone that Mac Lane's Theorem 2
   records.
2. Corollary (Corollary 2): equalizers plus all small products give `@Complete C`
   (`Structure/Complete.v:115`); dually, coequalizers plus small coproducts give `Cocomplete`.
3. The preservation corollary (§V.4 Exercise 2): a functor out of a complete category preserving all
   small products and all equalizers preserves all small limits — stated with the cone-level
   preservation notion of the §V.4 definition issue, since the apex-only class is too weak to carry
   the conclusion.
4. Use the `Instance/Discrete.v:37` discrete-diagram encoding for the indexed products so the result
   composes with `Structure/Limit/Product.v`'s existing API rather than introducing a rival one.

In-tree donors: `Structure/Limit/Product.v`, `Structure/Equalizer/Fork.v`, `Structure/Cone.v`,
`Structure/Limit.v`, `Instance/Discrete.v`, `Adjunction/GAFT.v:193` (the converse direction).

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 113 (PDF p. 122); §V.4, book p. 118 (PDF p. 127)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level
- [ ] The background-prose claims that cite this reduction (`Structure/Complete.v:49-53`, `Structure/Equalizer.v:80`, `Structure/Limit.v:94-103`) are updated to point at the new theorem instead of asserting it

## Verification
```bash
coqc -R . Category Structure/Limit/FromProducts.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions limit_of_products_equalizer.
Print Assumptions Complete_from_products_equalizers.
Print Assumptions continuous_from_products_equalizers.
```
Reviewer: statement matches Mac Lane §V.2 Theorems 1 and 2 (book p. 113) — both index products (over
objects AND over arrows) and both defining equations for the parallel pair.

## Dependencies
Depends on: maclane:V.4:def1

<!-- catalog: {"ids":["maclane:V.2:thm1","maclane:V.2:thm2","maclane:V.2:cor2","maclane:V.4:ex2"],"deps":["maclane:V.4:def1"]} -->
---8<---
```yaml
title: "MacLane V.2: Finite index categories and finite limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.2:def1, maclane:V.2:cor1]
deps_item_ids: [maclane:V.2:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 113 (PDF p. 122)
- Items: `maclane:V.2:def1`, `maclane:V.2:cor1`

## Background
A finite limit is a limit of a diagram whose index category is finite; the standard generating result
is that a terminal object, binary products and equalizers suffice for all of them. See
[nLab: limit](https://ncatlab.org/nlab/show/limit) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified PARTIAL (definition) and ABSENT (corollary). The library has no finiteness predicate on
`Category` (`rg -i 'finite category|FinCat|finite index'` finds only a prose aside in
`Theory/Metacategory/DecideExample.v`) and, more broadly, "carries NO size / smallness machinery"
(`Adjunction/SAFT.v:56`), so "every finite diagram" cannot be quantified over. "Finite limits"
therefore exists only as (a) unquantified prose naming a package of generators —
`Structure/Topos.v:114` (`ElementaryTopos`, which carries terminal + products + pullbacks explicitly
because of exactly this gap, disclosed at `:20-26`) and `Structure/Regular.v:26-31` — and (b)
individually named shapes (`Structure/Limit/Terminal.v:33`, `Structure/Limit/Cartesian.v:39`). The
equivalence of the surrogate packages with the real definition is declared unformalized in-tree.

## Work to be done
Suggested module: `Structure/Limit/Finite.v`.

1. Define finiteness for an index category — an enumeration of objects and of arrows by finite types
   (data, not a mere existence claim, so no choice is needed), with `Instance/Discrete.v` and
   `Instance/Parallel.v` as sanity witnesses and the `Theory/Metacategory` finite machinery as a
   possible donor. Disclose the chosen reading in the header.
2. Define `FinitelyComplete C` as: every diagram over a finite index category has a limit.
3. Prove the corollary: a terminal object, binary products and equalizers give finite completeness —
   via the products-and-equalizers theorem (dependency below), noting that the two products it needs
   are finite here, hence built from the binary ones by #335's iterated-product result.
4. Reconcile with the surrogate packages: prove that a finitely complete category has pullbacks (and
   conversely with #326's reductions), and update the `Structure/Topos.v` and `Structure/Regular.v`
   header disclosures.

In-tree donors: `Structure/Limit.v`, `Structure/Limit/Terminal.v`, `Structure/Limit/Cartesian.v`,
`Structure/Equalizer/Fork.v`, `Instance/Discrete.v`, `Instance/Parallel.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 113 (PDF p. 122)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Finite.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions FinitelyComplete.
Print Assumptions finitely_complete_from_generators.
```
Reviewer: statement matches Mac Lane §V.2 (book p. 113); the finiteness predicate must be usable —
i.e. the corollary's proof must actually consume the enumeration, not a placeholder.

## Dependencies
Depends on: #335
Depends on: #326
Depends on: maclane:V.2:thm1

<!-- catalog: {"ids":["maclane:V.2:def1","maclane:V.2:cor1"],"deps":["#335","#326","maclane:V.2:thm1"]} -->
---8<---
```yaml
title: "MacLane V.2: Completeness of a product category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.2:ex2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 114 (PDF p. 123)
- Items: `maclane:V.2:ex2`

## Background
Limits in a product category are computed componentwise, so a product of complete categories is
complete, and dually for cocompleteness. See
[nLab: product category](https://ncatlab.org/nlab/show/product+category) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified PARTIAL. Only structure-by-structure transport exists, and only for three structures:
`Structure/Cartesian/Product.v:38` (`Product_Cartesian`, whose header at `:32` discloses the scope),
`Structure/Cartesian/Closed/Product.v:43` (`Product_Closed`) and `Structure/Monoidal/Product.v`. There
is no `Terminal`, `Initial`, `Cocartesian` or `Bicartesian` instance on a product category, and no
componentwise construction of a general limit cone anywhere; `Complete C → Complete D →
Complete (C ∏ D)` (`Structure/Complete.v:115`) is not stated.

## Work to be done
Suggested module: `Construction/Product/Limit.v` (or an extension of `Structure/Cartesian/Product.v`).

- For a diagram into a product category, project to each factor, take limits there, and pair them:
  prove the resulting cone limiting, with the mediating morphism the pair of mediators.
- Conclude `Complete C → Complete D → Complete (C ∏ D)` and, by duality on the opposite categories,
  the cocomplete version.
- While in the file, close the neighbouring gap the verifier noted: componentwise `Terminal`,
  `Initial` and `Cocartesian` instances for a product category, which the limit result subsumes but
  which users will look for by name.

In-tree donors: `Construction/Product.v`, `Structure/Cartesian/Product.v`, `Structure/Cone.v`,
`Structure/Limit.v`, `Structure/Complete.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 114 (PDF p. 123)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Construction/Product/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Product_Limit.
Print Assumptions Product_Complete.
Print Assumptions Product_Cocomplete.
```
Reviewer: statement matches Mac Lane §V.2 Exercise 2 (book p. 114), including the cocomplete half.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.2:ex2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.2: The canonical comparison arrow for limits of composites"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.2:ex4, maclane:V.4:ex5]
deps_item_ids: [maclane:V.4:def1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 114 (PDF p. 123); §V.4, book p. 118 (PDF p. 127)
- Items: `maclane:V.2:ex4`, `maclane:V.4:ex5`

## Background
For a functor applied to a diagram there is a canonical comparison from the image of the limit to the
limit of the image, determined by the cone equations; preservation of that limit is precisely the
statement that this comparison is invertible. See
[nLab: preserved limit](https://ncatlab.org/nlab/show/preserved+limit) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL (both). Every ingredient exists and the comparison is never named: the image cone is
built ad hoc as `fmap_cone` inside `Theory/Equivalence/Limit.v:283` and again inside
`Construction/Comma/Limit.v`, and the mediator is `Structure/Limit/Preservation.v:74-76`
(`limit_med`, `limit_med_commutes`, `limit_med_unique`). There is no named
`H (Lim F) ~> Lim (H ◯ F)`, no biconditional relating it to preservation, and no reindexing of a cone
or limit along a functor between index categories, so the general shape with a change of index
category cannot even be written. The shape-specific comparison classes
`Functor/Structure/Cartesian.v:51` (`fobj_prod_iso`, `prod_out`) and
`Functor/Structure/Terminal.v:45` (`fobj_one_iso`) assume invertibility from the start and are never
related to `PreservesLimit`.

## Work to be done
Suggested module: `Structure/Limit/Comparison.v`.

1. Define reindexing along a functor between index categories: the restriction of a cone (and hence
   of a diagram) along it, with the evident functoriality lemmas.
2. Define the canonical comparison `H (Lim F) ~> Lim (H ◯ F ◯ W)` for composable index reindexing and
   a functor `H`, as the mediator out of the image cone; prove its defining equations and its
   uniqueness. Give the dual comparison for colimits.
3. Prove the biconditional (§V.4 Exercise 5): the functor preserves the limit of the diagram — in the
   cone-level sense of the §V.4 definition issue — exactly when the comparison is an isomorphism.
4. Bridge the shape-specific classes: `CartesianFunctor` and `TerminalFunctor` are exactly the
   invertibility of this comparison at the two-element discrete and empty shapes; prove it, so the
   functor-structure hierarchy and the limit-preservation hierarchy stop being unrelated developments.

In-tree donors: `Structure/Limit/Preservation.v`, `Theory/Equivalence/Limit.v` (the `fmap_cone`
pattern), `Functor/Structure/Cartesian.v`, `Functor/Structure/Terminal.v`, `Structure/Cone.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 114 (PDF p. 123); §V.4, book p. 118 (PDF p. 127)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Comparison.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions limit_comparison.
Print Assumptions preserves_iff_comparison_iso.
Print Assumptions cartesian_functor_iff_preserves_binary_products.
```
Reviewer: statements match Mac Lane §V.2 Exercise 4 and §V.4 Exercise 5 (book pp. 114, 118); the
comparison must be characterised by its cone equations plus uniqueness.

## Dependencies
Depends on: maclane:V.4:def1

<!-- catalog: {"ids":["maclane:V.2:ex4","maclane:V.4:ex5"],"deps":["maclane:V.4:def1"]} -->
---8<---
```yaml
title: "MacLane V.2: Limit as a functor on the category of diagrams"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.2:ex5]
deps_item_ids: [maclane:V.2:ex4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 115 (PDF p. 124)
- Items: `maclane:V.2:ex5`

## Background
Beyond its functoriality in the diagram at a fixed shape, the limit is functorial in the SHAPE as
well: over a complete category, taking limits is a functor on the opposite of the category whose
objects are all diagrams and whose arrows pair a change of index category with a natural
transformation. See [nLab: limit](https://ncatlab.org/nlab/show/limit) and
[nLab: comma category](https://ncatlab.org/nlab/show/comma+category).

## Current state in the library
Verified ABSENT. The comma notation of `Construction/Comma.v` is never instantiated with `Cat` on
either side (`rg 'Cat ↓|↓ Cat'` → 0 hits), there is no category of diagrams (`rg -i 'category of
diagrams'` → prose only, at `Theory/Adamek.v:64`, `Structure/Complete.v:76`,
`Structure/Cone/Const.v:32`), and no super-comma construction of any kind. The two prerequisites are
themselves missing: the limit functor at a fixed shape is #353's obligation, and the canonical
comparison arrow for a change of index category is the §V.2 comparison issue.

## Work to be done
Suggested module: `Structure/Limit/Diagrams.v`.

- Build the category of all diagrams in a fixed target: objects are functors out of arbitrary small
  index categories, arrows pair a functor between index categories with a natural transformation in
  the direction Mac Lane specifies (the "super-comma" category); check the composition law and its
  respectfulness carefully, since the arrow data mixes a strict functor component with a
  setoid-valued transformation component.
- Prove that for a complete target, taking limits is a functor from the opposite of that category,
  with arrow part the canonical comparison of the §V.2 comparison issue composed with the mediator of
  the transformation; the comma-category form over `Cat` is the sub-case where the transformation is
  the identity.
- Dualize for colimits.

In-tree donors: `Construction/Comma.v`, `Instance/Cat.v`, `Structure/Limit.v`, the comparison issue
below, #353's limit functor.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 115 (PDF p. 124)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Diagrams.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Diagrams.
Print Assumptions Lim_Diagrams_Functor.
```
Reviewer: statement matches Mac Lane §V.2 Exercise 5 (book p. 115), both parts (the comma form over
`Cat` and the super-comma form), and the variance is the opposite category.

## Dependencies
Depends on: #353
Depends on: maclane:V.2:ex4

<!-- catalog: {"ids":["maclane:V.2:ex5"],"deps":["#353","maclane:V.2:ex4"]} -->
---8<---
```yaml
title: "MacLane V.2: Manes' criterion for completeness"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.2:ex1]
deps_item_ids: [maclane:V.2:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 114 (PDF p. 123)
- Items: `maclane:V.2:ex1`

## Background
A sharpening of the products-and-equalizers criterion: a category with all small products need only
have equalizers of those parallel pairs that admit a common left inverse, because the pair produced by
the limit construction always has one. See
[nLab: equalizer](https://ncatlab.org/nlab/show/equalizer) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified ABSENT. The dual notion is in-tree and the notion itself is not: reflexive pairs (a common
right inverse) appear ten times across `Structure/Coequalizer/Reflexive.v` and
`Monad/Monadicity/*`, whereas `rg -i 'common left inverse'` and `rg -i 'coreflexive'` both return 0
hits. The base theorem the exercise refines is itself absent (see the products-and-equalizers issue),
and part (b) — the characterisation in sets of pairs with a common right inverse by the image of the
induced map containing the diagonal — has no counterpart either.

## Work to be done
Suggested module: `Structure/Equalizer/Coreflexive.v`.

- Define a coreflexive pair (a parallel pair with a common left inverse) and `HasCoreflexiveEqualizers`,
  dualizing `Structure/Coequalizer/Reflexive.v:54` so the two notions sit side by side.
- Prove Manes' criterion: small products plus coreflexive equalizers give completeness. The proof
  reuses the products-and-equalizers construction (dependency below) after checking that the parallel
  pair it builds has a common left inverse — the map induced by the object projections.
- Prove part (b) in `Sets`: a parallel pair has a common right inverse exactly when the image of the
  induced map into the square of the codomain contains the diagonal (state it with the library's
  image machinery, `Instance/Sets/Image.v`).

In-tree donors: `Structure/Coequalizer/Reflexive.v` (dualize), `Structure/Equalizer/Fork.v`,
`Structure/Limit/Product.v`, `Instance/Sets/Image.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 114 (PDF p. 123)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Equalizer/Coreflexive.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Complete_from_coreflexive_equalizers.
Print Assumptions Sets_common_section_iff_diagonal.
```
Reviewer: statement matches Mac Lane §V.2 Exercise 1 (book p. 114), both parts; the hint (the pair
built in the existence proof is coreflexive) must appear as a proved lemma.

## Dependencies
Depends on: maclane:V.2:thm1

<!-- catalog: {"ids":["maclane:V.2:ex1"],"deps":["maclane:V.2:thm1"]} -->
---8<---
```yaml
title: "MacLane V.2: Products in a preorder are greatest lower bounds"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.2:remark1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 113 (PDF pp. 122–123)
- Items: `maclane:V.2:remark1`

## Background
In a preorder regarded as a thin category, a product of a family is exactly a greatest lower bound and
a coproduct exactly a least upper bound — the reason completeness is chiefly interesting for large
categories and for preorders. See
[Wikipedia: Infimum and supremum](https://en.wikipedia.org/wiki/Infimum_and_supremum) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified PARTIAL. There is no order-theoretic vocabulary in the tree: `rg -i 'greatest lower
bound|glb|infimum|supremum'` finds only the header sentence at `Instance/Poset.v:51`, and no
meet/join or complete-lattice definition exists to state the identification against. The general
theorem — for a preorder, a product (or a J-indexed limit) in the induced thin category is a greatest
lower bound and conversely — is not stated, and there is no `Cartesian` instance on the preorder
construction at all (`Instance/Proset.v` declares only the category). The two witnesses that do exist
cover binary meets in two-element or propositional thin categories only:
`Instance/Two/Monoidal.v:37` (`two_meet`), `:80` (`Two_Cartesian`), `Instance/Props.v:69`
(`Props_Cartesian`), `:80` (`Props_Cocartesian`).

## Work to be done
Suggested module: `Instance/Proset/Limit.v` (plus a small `Structure/Lattice.v` if the order
vocabulary is wanted separately — coordinate with #389, which also wants lattice vocabulary).

- Define greatest lower bound and least upper bound for a family in a preorder.
- Prove the identification in both directions: a limiting cone over a family in the thin category
  induced by a preorder is exactly a greatest lower bound of that family, and dually for colimits and
  least upper bounds; specialise to binary products and to the empty family (top/bottom elements).
- Conclude that the induced thin category is complete exactly when the preorder has all small meets,
  and record the two existing binary witnesses as instances rather than leaving them freestanding.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Instance/Props.v`, `Instance/Two/Monoidal.v`,
`Structure/Limit.v`, `Structure/Limit/Product.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 113 (PDF pp. 122–123)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Proset/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions proset_limit_iff_glb.
Print Assumptions proset_colimit_iff_lub.
Print Assumptions proset_Complete_iff_all_meets.
```
Reviewer: statement matches Mac Lane §V.2 (book p. 113) — the J-indexed family case, not only the
binary one, and both directions of the identification.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.2:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.2: A small small-complete category is a preorder (Freyd)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.2:prop3]
deps_item_ids: [maclane:V.2:remark1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.2, book p. 114 (PDF p. 123)
- Items: `maclane:V.2:prop3`

## Background
Freyd's cardinality argument: a small category that has all small limits is necessarily a preorder,
and one in which every small family has a greatest lower bound — otherwise a product of enough copies
of one object would carry more arrows than the whole category has. It is the reason "complete" is
interesting only for large categories. See
[nLab: complete small category](https://ncatlab.org/nlab/show/complete+small+category).

## Current state in the library
Verified ABSENT. The statement is present twice as background prose (`Structure/Complete.v:63-72` and
`:99-106`) and never as a theorem. The obstacle is structural rather than incidental: the library has
no smallness predicate on categories (`Adjunction/SAFT.v:56` states outright that it carries no
size machinery), no global arrow-set, and no cardinality vocabulary beyond the finite counter in
`Theory/Metacategory.v`; there is also no "thin category" predicate to conclude with (the thin
categories in-tree — `Instance/Proset.v`, `Instance/Two.v`, `Instance/Roof.v` — are thin by
construction).

## Work to be done
Suggested module: `Structure/Complete/Freyd.v`.

- Introduce the two missing predicates as data in the library's usual style: a smallness witness for a
  category (an indexing of its arrows by a type at a fixed level) and thinness (any two parallel
  arrows are equal up to `≈`).
- Prove the theorem in the form the setoid setting supports: if a category is small (with the given
  witness) and has products indexed by arbitrary types at that level, then it is thin. The cardinality
  step becomes a diagonalisation — from two distinct parallel arrows build an injection from the
  function type into the arrow type and contradict the indexing (a Cantor-style argument; no choice
  and no classical logic needed if the two arrows are distinguished by a separating element).
- Add the second half: such a category has all small greatest lower bounds, via the preorder
  identification of the issue below.
- Update the `Structure/Complete.v` header prose to point at the theorem.

In-tree donors: `Structure/Complete.v`, `Structure/Limit/Product.v`, `Instance/Proset.v`,
`Theory/Metacategory.v` (indexing idiom).

## Definition of Done
- [ ] Statement fidelity to the book (§V.2, book p. 114 (PDF p. 123)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Complete/Freyd.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions small_complete_is_thin.
Print Assumptions small_complete_has_glbs.
```
Reviewer: statement matches Mac Lane §V.2 Proposition 3 (book p. 114); the smallness hypothesis must
be a genuine indexing that the proof consumes, and any use of classical reasoning must be disclosed
(the zero-axiom rule applies).

## Dependencies
Depends on: maclane:V.2:remark1

<!-- catalog: {"ids":["maclane:V.2:prop3"],"deps":["maclane:V.2:remark1"]} -->
---8<---
```yaml
title: "MacLane V.3: The evaluation functor on a functor category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.3:construction1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.3, book p. 115 (PDF p. 124)
- Items: `maclane:V.3:construction1`

## Background
Every object of the index category of a functor category gives an evaluation functor to the target,
sending a functor to its value there and a natural transformation to its component. It is the device
through which "limits with parameters" are phrased, being the partial application of the two-variable
evaluation. See [nLab: functor category](https://ncatlab.org/nlab/show/functor+category).

## Current state in the library
Verified PARTIAL. The two-variable evaluation exists — `Structure/Cartesian/Closed.v:75` (`eval`) and
`Instance/Cat/Cartesian/Closed.v:47` (`Cat_Closed`) — but the fixed-object evaluation functor
`[P, X] ⟶ X` is nowhere materialised: a scan for functors out of a functor category finds only
`Theory/Kan/Extension.v:127` (`Induced`, precomposition `[B,C] ⟶ [A,C]`), `Theory/Lawvere/Sets.v:83`
(`ev1`, a bespoke evaluation for Lawvere models), `Instance/CMon.v:170` and `Construction/Day.v:921`,
none of them the general `E_p`. `Functor/Bifunctor.v` supplies `bimap` but no partial-application
constructor, so the parameter/adjunct passage the section is built on has no in-tree home.

## Work to be done
Suggested module: `Instance/Fun/Eval.v`.

- Define `Eval p : [P, X] ⟶ X` for a fixed object `p` of `P`: object part `H ↦ H p`, arrow part
  `σ ↦ transform[σ] p`, functor laws componentwise from the functor-category structure of
  `Instance/Fun.v`.
- Give it as the partial application of the two-variable evaluation at `p` and prove the two agree, so
  the section's "record the evaluation functor" step is a definition and a lemma rather than a fresh
  construction.
- Prove the naturality the downstream theorem needs: `Eval p` is natural in `p` (a transformation
  between evaluation functors from each arrow of `P`), and record the parameter/adjunct passage
  `[J ∏ P, X] ≅ [J, [P, X]]` as the exponential transpose already available from `Cat_Closed`.

In-tree donors: `Instance/Fun.v`, `Structure/Cartesian/Closed.v`, `Instance/Cat/Cartesian/Closed.v`,
`Functor/Bifunctor.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.3, book p. 115 (PDF p. 124)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Fun/Eval.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Eval.
Print Assumptions Eval_partial_application.
```
Reviewer: statement fidelity to Mac Lane §V.3 (book p. 115) — the evaluation functor on objects and
on natural transformations, and its agreement with the partial application of `eval`.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.3:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.3: Pointwise limits in a functor category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.3:thm1, maclane:V.3:cor1]
deps_item_ids: [maclane:V.3:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.3, book pp. 115–116 (PDF pp. 124–125)
- Items: `maclane:V.3:thm1`, `maclane:V.3:cor1`

## Background
Limits in a functor category are computed pointwise: if each evaluation of a diagram of functors has a
limit, those limits assemble into a unique limit functor with a limiting cone, and consequently a
functor category into a complete category is complete. See
[nLab: functor category](https://ncatlab.org/nlab/show/functor+category) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL (both). Only the binary-product case is in-tree —
`Instance/Fun/Cartesian.v:111` (`Functor_Category_Cartesian`), with the general statement asserted as
header prose at `Instance/Fun.v:101-105`, `Instance/Fun/Cartesian.v:17-21` and
`Structure/Complete.v:55-58` but never proved. There is no `Terminal`, `Cocartesian` or `Equalizer`
structure on `[C, D]`, no colimit dual, and the evaluation functors the theorem is phrased through do
not exist (see the evaluation-functor issue). As a concrete consequence, the presheaf category
`[C^op, Sets]` is nowhere shown complete even though `Instance/Sets.v` provides the base.

## Work to be done
Suggested module: `Instance/Fun/Limit.v`.

1. Theorem 1 (pointwise limits): for `S : J ⟶ [P, X]` whose composite with each evaluation
   (the evaluation-functor issue) has a limit, construct the limit functor `L : P ⟶ X` — object part
   the pointwise limit apex, arrow part the mediating morphism between adjacent pointwise limits — and
   the limiting cone in `[P, X]`; prove uniqueness of the arrow part of `L`.
2. Corollary (Corollary 1): `Complete X → Complete [P, X]`, and the `Cocomplete` dual by the same
   construction over the opposite categories.
3. Apply it to record `Complete [C^op, Sets]` once the `Sets`-completeness witness lands (that is the
   §V.1 cone-set issue), so the presheaf-category completeness the library repeatedly assumes becomes
   a theorem.
4. Retire the header-prose assertions in `Instance/Fun.v` and `Structure/Complete.v` that currently
   stand in for this result.

In-tree donors: `Instance/Fun.v`, `Instance/Fun/Cartesian.v`, `Structure/Limit.v`, `Structure/Cone.v`,
`Structure/Complete.v`, the evaluation-functor issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.3, book pp. 115–116 (PDF pp. 124–125)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Fun/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Functor_Category_pointwise_limit.
Print Assumptions Functor_Category_Complete.
```
Reviewer: statement matches Mac Lane §V.3 Theorem 1 and Corollary 1 (book pp. 115–116), for an
arbitrary index category `J` — not only the two-object discrete case — including the uniqueness of the
limit functor's arrow part.

## Dependencies
Depends on: maclane:V.3:construction1

<!-- catalog: {"ids":["maclane:V.3:thm1","maclane:V.3:cor1"],"deps":["maclane:V.3:construction1"]} -->
---8<---
```yaml
title: "MacLane V.3: Pointwise limits as creation along the discrete inclusion"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.3:thm2]
deps_item_ids: [maclane:V.3:thm1, maclane:V.1:def3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.3, book p. 116 (PDF p. 125)
- Items: `maclane:V.3:thm2`

## Background
The pointwise-limit theorem has a slick restatement: precomposition with the inclusion of the discrete
subcategory on the objects of the index category creates limits, so a diagram of functors has a limit
exactly when its underlying diagram of object-indexed families does, computed pointwise. See
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit) and
[nLab: discrete category](https://ncatlab.org/nlab/show/discrete+category).

## Current state in the library
Verified ABSENT. Two pieces are missing. There is no discrete subcategory on the objects of a category
and no inclusion functor from it (`rg -i 'discrete subcategory'` → 0 hits); `Instance/Discrete.v:37`
(`DiscreteCat`) and `:52` (`DiscreteCat_Functor`) build the discrete category on a type, but their
only uses instantiate them for indexed products (`Theory/WeaklyInitial.v:90-91`,
`Structure/Limit/Product.v`, `Adjunction/GAFT.v:249-251`), never as an object-inclusion into `P`. And
the general precomposition functor `Theory/Kan/Extension.v:127` (`Induced`, the `X^i` of the theorem)
exists but no limit property whatever is proved of it. The creation vocabulary is itself absent (see
the §V.1 definition issue).

## Work to be done
Suggested module: `Instance/Fun/Creation.v`.

- Build the discrete subcategory on the objects of an index category and its inclusion functor (donor:
  `Instance/Discrete.v`, `Construction/Subcategory.v`).
- Prove that precomposition with that inclusion, `[P, X] ⟶ [|P|, X]`, creates limits — in the sense
  of the creation class of the §V.1 definition issue — by transporting the pointwise-limit theorem:
  the object-indexed families with limits are exactly the diagrams whose pointwise limits assemble,
  and the assembly is the unique lift.
- Present it explicitly as a reformulation of Theorem 1, so the two statements are provably the same
  content rather than parallel proofs.

In-tree donors: `Instance/Discrete.v`, `Theory/Kan/Extension.v` (`Induced`), `Instance/Fun.v`, the
pointwise-limit issue, the creation class from the §V.1 definition issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.3, book p. 116 (PDF p. 125)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Fun/Creation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions discrete_inclusion_creates_limits.
```
Reviewer: statement matches Mac Lane §V.3 Theorem 2 (book p. 116) — creation (with the uniqueness
clause) by precomposition along the object-discrete inclusion.

## Dependencies
Depends on: maclane:V.3:thm1
Depends on: maclane:V.1:def3

<!-- catalog: {"ids":["maclane:V.3:thm2"],"deps":["maclane:V.3:thm1","maclane:V.1:def3"]} -->
---8<---
```yaml
title: "MacLane V.4: Cone-level preservation of limits and continuous functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.4:def1, maclane:V.4:ex1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.4, book pp. 116–118 (PDF pp. 125–127)
- Items: `maclane:V.4:def1`, `maclane:V.4:ex1`

## Background
A functor preserves the limit of a diagram when it carries every limiting cone over that diagram to a
limiting cone — a demand on the cone, not merely on the apex object — and it is continuous when it
preserves all small limits; continuity is closed under composition. See
[nLab: preserved limit](https://ncatlab.org/nlab/show/preserved+limit) and
[nLab: continuous functor](https://ncatlab.org/nlab/show/continuous+functor).

## Current state in the library
Verified PARTIAL (definition) and ABSENT (the composition exercise). The library's named class
`Structure/Limit/Preservation.v:48` (`PreservesLimit`), `:229` (`PreservesAllLimits`) is apex-only and
provably too weak — its own STATUS header at `Construction/Comma/Limit.v:54` records the countermodel
(two cone structures on one apex differing by a non-invertible endomorphism). The cone-level notion
exists only as `Construction/Comma/Limit.v:110` (`PreservesImageLimit`), and only for all diagrams at
once relative to a section-fixed functor, with no per-diagram form and no colimit dual beyond the
apex-only `PreservesColimit` and the shape-restricted `Monad/Monadicity/Crude.v:100`
(`PreservesReflexiveCoequalizers`). No lemma composes two preservation witnesses
(`rg 'PreservesLimit' | grep -i comp` → 0 hits).

## Work to be done
Suggested module: extend `Structure/Limit/Preservation.v` (or a new `Structure/Limit/Preservation/ConeLevel.v`).

1. Define per-diagram cone-level preservation: `PreservesConeLimit G F` asserting that the image of a
   limiting cone over `F` (apex `F L`, legs the functor applied to the legs) is again limiting.
   Relate it to the existing `PreservesImageLimit` (the all-diagrams-at-once form) and prove it
   strictly stronger than the apex-only `PreservesLimit`, reusing the in-tree countermodel to show the
   implication does not reverse.
2. Define `Continuous G` as preservation of all small limits in this sense, and confirm the in-tree
   `Structure/Limit/Preservation.v:19` continuity reading agrees where both apply.
3. Prove Exercise 1: a composite of continuous functors is continuous (the image of a limiting cone
   under the outer functor of an already-limiting image cone is limiting), with the cone-level colimit
   dual.
4. Give the cone-level colimit class `PreservesConeColimit` so the dual statements downstream (hom
   carrying colimits to limits, left adjoints preserving colimits) have a home.

In-tree donors: `Structure/Limit/Preservation.v`, `Construction/Comma/Limit.v` (`PreservesImageLimit`
and its countermodel note), `Structure/Cone.v`, `Adjunction/Continuity.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.4, book pp. 116–118 (PDF pp. 125–127)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Preservation/ConeLevel.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions PreservesConeLimit.
Print Assumptions continuous_compose.
```
Reviewer: statement matches Mac Lane §V.4 (book p. 116) — the definition must be on the CONE (Mac
Lane's explicit emphasis), and the composition exercise must be proved at the cone level.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.4:def1","maclane:V.4:ex1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.4: Hom-functors are continuous"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.4:thm1, maclane:V.4:remark1, maclane:V.4:remark2, maclane:V.4:remark3]
deps_item_ids: [maclane:V.1:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.4, book pp. 116–117 (PDF pp. 125–126)
- Items: `maclane:V.4:thm1`, `maclane:V.4:remark1`, `maclane:V.4:remark2`, `maclane:V.4:remark3`

## Background
For any object, the covariant hom-functor to sets preserves all limits that exist — the archetypal
continuous functor — so a limit is computed representably as the hom into the limit; dually the
contravariant hom carries colimits to limits, and the statement holds into any universe of sets. See
[nLab: continuous functor](https://ncatlab.org/nlab/show/continuous+functor) and
[nLab: representable functor](https://ncatlab.org/nlab/show/representable+functor).

## Current state in the library
Verified PARTIAL (all four). #331 files the products-case preview from §III.4; §V.4 is the general
theorem and its three remarks, none of which is in-tree. There is no preservation witness for the
hom-functor — no `PreservesLimit G (Curried_Hom C c)`, no cone-level statement that
`h ↦ (limit_leg L x ∘ h)` is a limiting cone over `HomDiagram c F` in `Sets`
(`Structure/Limit/Weighted.v:49`, `:308`). The representable half `Cone(c, F) ≅ C(c, Lim F)` natural
in `c` IS present (`wl_iso`, `wlim_natural`, `Structure/UniversalProperty/Limit.v:141`
`LimitIsUniversalProperty`), but it is never read as a LIMIT IN `Sets` — that reading needs the
cone-set limit of `Sets` (the §V.1 issue) — and the contravariant form
`Functor/Hom.v:146` (`Curried_CoHom`) is nowhere shown to carry colimits to limits.

## Work to be done
Suggested module: `Functor/Hom/Continuous.v` (extending #331's `Functor/Hom/Limit.v`).

1. Prove the general Theorem 1: `C(c, −) : C ⟶ Sets` preserves every limit that exists in `C`, in the
   cone-level sense of the §V.4 definition issue — the image cone over `HomDiagram c F` is limiting,
   using the `Sets` cone-set limit (the §V.1 issue) to identify its apex. This upgrades #331 from the
   products case to all limits; build on #331 rather than re-deriving.
2. Remark 2: read the in-tree representable isomorphism `Cone(c, F) ≅ C(c, Lim F)` as the equation
   `Lim C(c, F−) = C(c, Lim F)` in `Sets`, now that both sides are limits there; record the product
   special case `∏ C(c, a_i) ≅ C(c, ∏ a_i)` as a natural isomorphism of `Sets`-objects, not merely
   the family-level UMP.
3. Remark 3: the contravariant hom `C(−, c)` carries small colimits to limits, by applying Theorem 1
   in the opposite category; give the coproduct instance `C(⨿ a_j, c) ≅ ∏ C(a_j, c)` as a natural
   isomorphism.
4. Remark 1: note the universe generalization — the statement holds for hom-functors valued in any
   universe of sets — which the library's universe polymorphism makes immediate; state it and discharge
   the `Instance/Ens.v` header caveat where relevant.

In-tree donors: `Functor/Hom.v`, `Structure/Limit/Weighted.v`, `Structure/UniversalProperty/Limit.v`,
`Structure/Limit/Preservation.v`, the §V.1 `Sets` cone-set limit, #331.

## Definition of Done
- [ ] Statement fidelity to the book (§V.4, book pp. 116–117 (PDF pp. 125–126)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Functor/Hom/Continuous.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions hom_preserves_limits.
Print Assumptions cohom_carries_colimits_to_limits.
```
Reviewer: statement matches Mac Lane §V.4 Theorem 1 and Remarks (book pp. 116–117); the general-limit
case must genuinely extend #331's products case, and both remarks must be natural isomorphisms of
`Sets`-objects, not family-level universal properties.

## Dependencies
Depends on: #331
Depends on: maclane:V.1:thm1

<!-- catalog: {"ids":["maclane:V.4:thm1","maclane:V.4:remark1","maclane:V.4:remark2","maclane:V.4:remark3"],"deps":["#331","maclane:V.1:thm1"]} -->
---8<---
```yaml
title: "MacLane V.4: Projective and injective objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.4:def3, maclane:V.4:def4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.4, book p. 118 (PDF p. 127)
- Items: `maclane:V.4:def3`, `maclane:V.4:def4`

## Background
An object is projective when its covariant hom-functor preserves epimorphisms (every map out of it
lifts through every epi), and injective when its contravariant hom-functor carries monics to epis
(every map into it extends along every mono) — the two dual lifting notions underlying homological
algebra. See [nLab: projective object](https://ncatlab.org/nlab/show/projective+object) and
[nLab: injective object](https://ncatlab.org/nlab/show/injective+object).

## Current state in the library
Verified ABSENT (both). No projectivity or injectivity notion exists: `rg -i 'Projective'` finds only
projective-geometry prose (`Construction/Opposite.v:27,40,43`) and a background remark on "enough
projectives" (`Structure/Abelian.v:97`); `rg -i 'Injective'` finds only the setoid-map property
`Lib/Setoid.v:117` (`Class injective`, a different notion) and the injective-resolutions essay at
`Structure/Abelian.v:98`. There is no `Structure/Projective.v` or `Structure/Injective.v`, no lifting
property beyond `Theory/Orthogonality.v:43` (`Orthogonal`, the unique-filler property, which is
stronger than the weak lifting these definitions require), and no lemma about hom-functors preserving
epis.

## Work to be done
Suggested module: `Structure/Projective.v` (with the injective dual, `Definition Injective (C) := Projective (C^op)`).

- Define `Projective p`: for every epi `g` and every arrow out of `p`, a lift — as data or as an
  ∃-statement, disclosing which — and prove the equivalent characterization that `C(p, −)` carries
  epis to epis (surjections of hom-setoids in `Sets`).
- Define `Injective` by duality on the opposite category, with covariant accessors (extension along
  any mono), and prove the `C(−, q)` characterization.
- Relate to the existing `Theory/Orthogonality.v` lifting vocabulary: orthogonality is the unique-lift
  strengthening, so projectivity is its lift-existence weakening against the class of epis; state the
  implication.
- Record the basic closure facts (retracts of projectives are projective; a coproduct of projectives
  is projective where coproducts exist).

In-tree donors: `Theory/Morphisms.v` (`Epic`, `Monic`), `Functor/Hom.v`, `Theory/Orthogonality.v`,
`Construction/Opposite.v` (for the dual).

## Definition of Done
- [ ] Statement fidelity to the book (§V.4, book p. 118 (PDF p. 127)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Projective.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Projective.
Print Assumptions Injective.
Print Assumptions projective_iff_hom_preserves_epi.
```
Reviewer: statements match Mac Lane §V.4 (book p. 118); the hom-functor characterizations must be
proved, and injectivity must be the genuine dual (not the setoid-map `injective`).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.4:def3","maclane:V.4:def4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.4: The free abelian group functor is not continuous"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.4:ex3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.4, book p. 118 (PDF p. 127)
- Items: `maclane:V.4:ex3`

## Background
The free abelian group functor from sets fails to preserve limits — a concrete non-example showing
that left adjoints need not be continuous — witnessed by its behaviour on an infinite product or a
suitable equalizer. See [Wikipedia: Free abelian group](https://en.wikipedia.org/wiki/Free_abelian_group)
and [nLab: continuous functor](https://ncatlab.org/nlab/show/continuous+functor).

## Current state in the library
Verified ABSENT. Neither the functor nor its target exists: `rg -i 'free abelian|FreeAbelian'` → 0
code hits (free groups appear only in the prose of `Theory/Universal/Arrow.v:39,45`), the tree has no
category of abelian groups (the concrete instances are `Sets`, `Coq`, `Ens`, `FinSet`, `Rel`, `CMon`,
…; `Structure/Group.v` defines group OBJECTS internal to a cartesian category, not `Ab`), and no
in-tree counterexample to continuity of any functor is recorded (`rg -i 'not continuous'` → nothing).

## Work to be done
Suggested module: `Instance/Ab/FreeNotContinuous.v`, over the category of abelian groups of #256.

- Construct the free abelian group functor `Sets ⟶ Ab` (finitely supported integer-valued functions,
  the biproduct-style free construction over `Instance/CMon/Biproduct.v`), with its universal
  property.
- Exhibit a small diagram whose limit the functor does not preserve — the standard witness is that the
  free abelian group on a countable product is not the product of the free abelian groups — and prove
  the comparison map (the §V.2 comparison issue, or an ad hoc map) fails to be an isomorphism.
- State the conclusion as `¬ Continuous FreeAb` using the continuity notion of the §V.4 definition
  issue, giving the library its first recorded discontinuity witness.

In-tree donors: #256's `Ab`, `Instance/CMon/Biproduct.v` (biproduct/free pattern),
`Theory/Universal/Arrow.v`, the §V.4 continuity definition, the §V.2 comparison arrow.

## Definition of Done
- [ ] Statement fidelity to the book (§V.4, book p. 118 (PDF p. 127)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Ab/FreeNotContinuous.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions FreeAb.
Print Assumptions FreeAb_not_continuous.
```
Reviewer: statement matches Mac Lane §V.4 Exercise 3 (book p. 118); the discontinuity must be
exhibited by a concrete diagram, not asserted.

## Dependencies
Depends on: #256

<!-- catalog: {"ids":["maclane:V.4:ex3"],"deps":["#256"]} -->
---8<---
```yaml
title: "MacLane V.5: Adjunctions and limits in functor categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.5:construction1, maclane:V.5:remark1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.5, book p. 119 (PDF p. 128)
- Items: `maclane:V.5:construction1`, `maclane:V.5:remark1`

## Background
An adjunction lifts to functor categories by postcomposition, `F ◯ −` remaining left adjoint to
`G ◯ −`, and combining this with the diagonal-limit adjunctions gives Mac Lane's sophisticated
recasting of the right-adjoints-preserve-limits theorem: taking limits commutes with a right adjoint
up to natural isomorphism. See
[nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL (both). The postcomposition functors `F ◯ − : [J, X] ⟶ [J, A]` and `G ◯ −` are not
defined anywhere — the only functor between functor categories is precomposition
`Theory/Kan/Extension.v:127` (`Induced := (− ◯ F)`), and `Instance/Cat/Bicategory.v:65`
(`Cat_Hcompose`) is a bifunctor never partially applied — so `F^J ⊣ G^J` is not expressible; the
induced unit and counit and the derivation of the triangle identities are all missing. For the remark,
`Lim` is never a functor `[J, C] ⟶ C` (`Structure/Complete.v:115` is a plain ∀-quantified function),
the general `Δ ⊣ Lim` exists only in the binary-product case (`Adjunction/Diagonal/Product.v:37`, with
the general sandwich as prose at `Functor/Diagonal.v:28`), so the square of adjoint pairs, the identity
`F^J ∘ Δ = Δ ∘ F` and the isomorphism `Lim ◯ G^J ≅ G ◯ Lim` cannot be stated.

## Work to be done
Suggested module: `Adjunction/FunctorCategory.v`.

1. Define the postcomposition functor `postcompose F : [J, X] ⟶ [J, A]` for any `F : X ⟶ A` (object
   part `F ◯ S`, arrow part `F` whiskered onto a natural transformation), with its functor laws.
2. From an adjunction `F ⊣ G`, build `postcompose F ⊣ postcompose G`: the induced unit and counit are
   the original unit/counit whiskered by the diagram, and the triangle identities follow componentwise
   from the originals.
3. Prove the remark: with the diagonal-limit adjunction `Δ ⊣ Lim` of #353, the square of adjoint pairs
   has commuting left adjoints (`postcompose F ∘ Δ = Δ ∘ F`), so by uniqueness of adjoints
   `Lim ◯ postcompose G ≅ G ◯ Lim`; conclude that a right adjoint carries a limiting cone to a
   limiting cone, the cone being the value of the `Δ ⊣ Lim` counit — recovering RAPL from the abstract
   argument.

In-tree donors: `Theory/Adjunction.v`, `Adjunction/Compose.v`, `Instance/Fun.v`, `Functor/Diagonal.v`,
`Theory/Adjunction.v:364` (`right_adjoint_iso`), #353's diagonal-limit adjunction.

## Definition of Done
- [ ] Statement fidelity to the book (§V.5, book p. 119 (PDF p. 128)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/FunctorCategory.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions postcompose_adjunction.
Print Assumptions Lim_commutes_right_adjoint.
```
Reviewer: statements match Mac Lane §V.5 (book pp. 118–119) — the induced unit/counit must be the
whiskered originals, and the remark's isomorphism must come from uniqueness of adjoints, not a
re-proof.

## Dependencies
Depends on: #353

<!-- catalog: {"ids":["maclane:V.5:construction1","maclane:V.5:remark1"],"deps":["#353"]} -->
---8<---
```yaml
title: "MacLane V.5: Non-existence of adjoints in Set and Set^op"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.5:ex1, maclane:V.5:ex4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.5, book p. 120 (PDF p. 129)
- Items: `maclane:V.5:ex1`, `maclane:V.5:ex4`

## Background
Two negative results from the preservation theorems: the functor "product with a fixed set" on sets
has no left adjoint unless the set is a point (a left adjoint would make it preserve the terminal
object), and the opposite of the category of sets is not cartesian closed. See
[nLab: continuous functor](https://ncatlab.org/nlab/show/continuous+functor) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified ABSENT (both). The library records only positive adjunction constructions — a scan of every
`⊣` site (261 hits) turns up no impossibility result, and `rg -i 'no left adjoint|no right adjoint'`
finds only the scope note at `Construction/ColouredPROP/LNL.v:53` — so the library has no idiom for
stating that a given functor lacks an adjoint. For Exercise 4, `rg -i 'not cartesian closed'` finds
only prose notes about partial-map categories (`Instance/Coq/Par.v:219`, `Instance/Coq/ParE.v:177`);
the nearest ingredient is `Structure/BiCCC.v:222` (`prod_zero_r : x × 0 ≅ 0`), the fact whose
dualization drives the Set^op argument, but it is never applied to conclude non-closure.

## Work to be done
Suggested module: `Instance/Sets/NoAdjoint.v`.

- Establish the reusable obstruction lemma: if a functor has a left adjoint it preserves limits, in
  particular the terminal object (dually for a right adjoint and colimits) — an instance of the
  present right-adjoints-preserve-limits theorem, packaged so a non-existence proof is a short
  contradiction.
- Exercise 1: `X × − : Sets ⟶ Sets` has a left adjoint only if `X` is terminal — a left adjoint would
  make `X × −` a right adjoint preserving the terminal object, forcing `X × 1 ≅ 1`, i.e. `X ≅ 1`;
  prove the converse (when `X ≅ 1` the functor is the identity, which has adjoints) so the
  characterization is exact.
- Exercise 4: `Sets^op` is not cartesian closed — if it were, `Sets` would carry the dual structure
  and `prod_zero_r` dualizes to force a degeneracy (the initial object would be terminal); prove the
  contradiction, giving the library its first non-cartesian-closedness result.

In-tree donors: `Adjunction/Continuity.v` (right adjoints preserve limits, present),
`Instance/Sets.v`, `Structure/BiCCC.v` (`prod_zero_r`), `Construction/Opposite.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.5, book p. 120 (PDF p. 129)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Sets/NoAdjoint.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions times_X_has_left_adjoint_iff_terminal.
Print Assumptions Sets_op_not_cartesian_closed.
```
Reviewer: statements match Mac Lane §V.5 Exercises 1 and 4 (book p. 120); the obstruction lemma must
be a genuine consequence of limit preservation, and Exercise 1 must prove both directions.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.5:ex1","maclane:V.5:ex4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.5: The vector-space dual functor has no right adjoint"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.5:ex2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.5, book p. 120 (PDF p. 129)
- Items: `maclane:V.5:ex2`

## Background
The dualization functor on vector spaces, self-adjoint on the right, has no right adjoint — so it is
not itself the left adjoint of its opposite — a consequence of its failure to preserve the relevant
colimits. See [Wikipedia: Dual space](https://en.wikipedia.org/wiki/Dual_space) and
[nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library
Verified ABSENT. There is no category of vector spaces in-tree (`rg -i 'Vect|vector space'` → prose
only; the nearest algebraic instance is `Instance/CMon.v`), and #359 files the self-on-the-right
adjunction of the dual-object functor as the vehicle for stating this exercise. No
non-existence-of-adjoint theorem exists anywhere (`rg -i 'no right adjoint'` → nothing usable), so the
statement has neither its subject nor its idiom today.

## Work to be done
Suggested module: alongside #359's dual-object development.

- Over the dual functor `D : Vect^op ⟶ Vect` established by #359, use the adjoint-obstruction lemma
  (a right adjoint of `D` would make `D` preserve colimits) to derive a contradiction from `D`'s
  behaviour on an infinite coproduct (the dual of a direct sum is a product, not the direct sum of
  duals), concluding `D` has no right adjoint.
- Conclude the corollary that `D` is not the left adjoint of `D^op`.
- If the underlying obstruction lemma is not yet available from another §V.5 issue, prove the instance
  needed here directly.

In-tree donors: #359's dual-object functor, `Adjunction/Continuity.v`, the adjoint-obstruction idiom
of the §V.5 non-existence issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.5, book p. 120 (PDF p. 129)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category <the file placing this over #359's development>
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions dual_functor_no_right_adjoint.
```
Reviewer: statement matches Mac Lane §V.5 Exercise 2 (book p. 120); the obstruction must be exhibited
on a concrete colimit.

## Dependencies
Depends on: #359

<!-- catalog: {"ids":["maclane:V.5:ex2"],"deps":["#359"]} -->
---8<---
```yaml
title: "MacLane V.5: A full reflective subcategory of a cocomplete category is cocomplete"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.5:ex3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.5, book p. 120 (PDF p. 129)
- Items: `maclane:V.5:ex3`

## Background
Colimits in a full reflective subcategory are computed by reflecting the ambient colimit, so a full
reflective subcategory of a cocomplete category is again cocomplete — the colimit-side companion to
"a full reflective subcategory inherits limits". See
[nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified ABSENT. The limit-side companion is #373 (a full reflective subcategory inherits limits),
whose draft explicitly leaves the colimit half optional; this exercise is that colimit half and is not
in-tree. The ingredients exist and are never combined: `Construction/Reflective.v:62` (`Reflective`,
with `reflector ⊣ Incl`), `Structure/Complete.v:119` (`Cocomplete`, with no concrete instance and only
a hypothesis use in `Theory/Adamek/Corollaries.v`), and the fact that the reflector as a left adjoint
preserves colimits (`Adjunction/Continuity.v:223`). `rg 'colimits.*subcategory'` → 0 hits.

## Work to be done
Suggested module: `Construction/Reflective/Colimit.v` (companion to #373's `Construction/Reflective/Limit.v`).

- Prove: for a full reflective subcategory of a category `D`, given a diagram in the subcategory whose
  image has a colimit in `D`, the reflection of that colimit is a colimit in the subcategory, and the
  reflector's unit exhibits the universal cocone. The proof: the reflector preserves the ambient
  colimit (left adjoint), the inclusion is full and faithful, and the counit iso
  (`reflective_counit_iso`) transports the universal property.
- State the consequence in the form the exercise asks: `Cocomplete D → Cocomplete (the subcategory)`.
- Coordinate with #373: if #373's PR already discharged the colimit half, this issue collapses to a
  cross-check; the header should note the relationship.

In-tree donors: `Construction/Reflective.v`, `Adjunction/Continuity.v`,
`Theory/Equivalence/Limit.v` (transport idiom), `Structure/Complete.v`, #373.

## Definition of Done
- [ ] Statement fidelity to the book (§V.5, book p. 120 (PDF p. 129)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Construction/Reflective/Colimit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions reflective_subcategory_cocomplete.
```
Reviewer: statement matches Mac Lane §V.5 Exercise 3 (book p. 120); confirm the colimit is the
reflection of the ambient colimit and that fullness is used.

## Dependencies
Depends on: #373

<!-- catalog: {"ids":["maclane:V.5:ex3"],"deps":["#373"]} -->
---8<---
```yaml
title: "MacLane V.6: The initial-object theorem as a characterization"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:thm1]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 120 (PDF pp. 129–130)
- Items: `maclane:V.6:thm1`

## Background
A small-complete category with small hom-sets has an initial object if and only if it satisfies the
solution set condition (a small weakly initial family); the initial object is carved out as an
equalizer of all endomorphisms of the product of the family. See
[nLab: solution set condition](https://ncatlab.org/nlab/show/solution+set+condition) and
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified PARTIAL. Only the sufficient (hard) direction is in-tree: `Theory/WeaklyInitial.v:89`
(`initial_from_weakly_initial`) builds an `Initial` from a `WeaklyInitialFamily`
(`Theory/WeaklyInitial.v:58`) by the product-and-equalizer-of-all-endomorphisms Freyd construction
(`:119` `endo_absorb`, `:154` the uniqueness chase). The necessity direction — an initial object
yields the solution set condition, via the one-element family — is nowhere in-tree: the only producers
of a `WeaklyInitialFamily` are in `Adjunction/GAFT.v` (`wif_of_sols`, from a `SolutionSet`), and
nothing builds one from an `Initial` object, so Mac Lane's Theorem 1 as a biconditional is
unavailable.

## Work to be done
Suggested module: extend `Theory/WeaklyInitial.v`.

- Prove the necessity direction: an initial object gives a weakly initial family (the singleton family
  on the initial object), hence the solution set condition; state it in the library's
  `WeaklyInitialFamily`/`SolutionSet` vocabulary.
- Package the biconditional: for a small-complete category with small hom-sets, `Initial C` is
  equivalent to the existence of a weakly initial family, combining the new direction with the
  existing `initial_from_weakly_initial`.
- Keep the endomorphism-indexed product an explicit input, as the existing development does, so
  smallness stays caller-chosen (`Theory/WeaklyInitial.v:44`).

In-tree donors: `Theory/WeaklyInitial.v`, `Adjunction/GAFT.v` (`wif_of_sols`), `Structure/Initial.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 120 (PDF pp. 129–130)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Theory/WeaklyInitial.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions weakly_initial_of_initial.
Print Assumptions initial_iff_weakly_initial_family.
```
Reviewer: statement matches Mac Lane §V.6 Theorem 1 (book p. 120) as a biconditional; the new
direction must actually use the initial object to build the family.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.6:thm1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.6: The Freyd adjoint functor theorem as a characterization"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:thm2]
deps_item_ids: [maclane:V.6:thm1, maclane:V.6:lem1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 121 (PDF pp. 130–131)
- Items: `maclane:V.6:thm2`

## Background
Freyd's general adjoint functor theorem: a functor out of a small-complete category with small
hom-sets has a left adjoint if and only if it preserves all small limits and satisfies the solution
set condition. See [nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem)
and [nLab: solution set condition](https://ncatlab.org/nlab/show/solution+set+condition).

## Current state in the library
Verified PARTIAL. The sufficient direction is fully in-tree — `Adjunction/GAFT.v:241` (`GAFT`), routed
solution-set ⇒ weakly-initial family ⇒ initial object of the comma ⇒ adjoint, with
`Construction/Comma/Limit.v:264` (`right_adjoint_PreservesImageLimit`) and
`Adjunction/Continuity.v:202` supplying the comma completeness. The necessity direction is not
packaged: nothing builds a `SolutionSet U d` from an adjunction `F ⊣ U` (the unit as a one-element
solution set), and the ONLY producers of `SolutionSet` in the tree are `Adjunction/SAFT.v:252`
(`SAFT_solution_set`) and the caller-supplied hypothesis of `GAFT`. So Mac Lane's Theorem 2 as a
CHARACTERIZATION of right adjoints is unavailable — only Freyd's sufficient condition.

## Work to be done
Suggested module: extend `Adjunction/GAFT.v`.

- Prove the necessity direction: from `F ⊣ U`, build a `SolutionSet U d` for each object (the unit
  `η_d : d ~> U (F d)` as a one-element solution set), and note that a right adjoint preserves all
  small limits (already in-tree, `right_adjoint_preserves_limits`).
- Package the biconditional `GAFT_iff`: for a small-complete domain with small hom-sets, `U` has a
  left adjoint iff it preserves all small limits and satisfies the solution set condition — combining
  the new direction with the existing `GAFT`.
- Reuse the initial-object characterization (the §V.6 Theorem 1 issue) and the comma-creation result
  (the comma-projection issue) so the proof is Mac Lane's — the solution set for `U` is the solution
  set for the comma category, which is small-complete because the projection creates limits.

In-tree donors: `Adjunction/GAFT.v`, `Adjunction/Continuity.v`, `Construction/Comma/Limit.v`,
`Theory/Adjunction.v` (unit/counit accessors).

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 121 (PDF pp. 130–131)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/GAFT.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions solution_set_of_adjunction.
Print Assumptions GAFT_iff.
```
Reviewer: statement matches Mac Lane §V.6 Theorem 2 (book p. 121) as a biconditional; the necessity
direction must construct the solution set from the unit.

## Dependencies
Depends on: maclane:V.6:thm1
Depends on: maclane:V.6:lem1

<!-- catalog: {"ids":["maclane:V.6:thm2"],"deps":["maclane:V.6:thm1","maclane:V.6:lem1"]} -->
---8<---
```yaml
title: "MacLane V.6: The representability theorem"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:thm3, maclane:V.6:def3, maclane:V.8:ex1]
deps_item_ids: [maclane:V.6:thm1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 122 (PDF pp. 131–132); §V.8, book p. 131 (PDF p. 140)
- Items: `maclane:V.6:thm3`, `maclane:V.6:def3`, `maclane:V.8:ex1`

## Background
A set-valued functor on a small-complete category with small hom-sets is representable if and only if
it preserves all small limits and satisfies the solution set condition — the special case of the
adjoint functor theorem where a representation is a universal arrow from the one-point set. A
representable functor with a domain having copowers has a left adjoint, and conversely. See
[nLab: representable functor](https://ncatlab.org/nlab/show/representable+functor) and
[nLab: solution set condition](https://ncatlab.org/nlab/show/solution+set+condition).

## Current state in the library
Verified ABSENT (Theorem 3, Exercise V.8.1) and PARTIAL (Definition 3). The bare
`Functor/Representable.v:46` (`Representable`) class exists but nothing derives an instance from
continuity plus a solution set, and `Structure/UniversalProperty.v:67-72`
(`representability_by_yoneda`) relates universal elements to representations without the existence
theorem. The element-wise solution set condition for a `Sets`-valued functor (Definition 3) is not
stated: the general hom-shaped `Adjunction/GAFT.v:159` (`SolutionSet U d`) specializes to it at the
terminal setoid, but the library never performs that instantiation nor records the
elements-vs-global-points bridge for `Sets` (no `(1 ~{Sets}~> X) ≅ carrier X` lemma). The copower
direction of Exercise V.8.1 needs the copowers of #366.

## Work to be done
Suggested module: `Adjunction/Representability.v`.

1. Definition 3: state the solution set condition element-wise for a `Sets`-valued functor `K`, and
   prove it equivalent to the general `SolutionSet` at the terminal object, via the
   global-points-are-elements bridge `(1 ~{Sets}~> X) ≅ carrier X` (prove this reusable lemma).
2. Theorem 3: a continuous `Sets`-valued functor satisfying the solution set condition is
   representable — a representation is an initial object of the comma category from the terminal set,
   supplied by the §V.6 Theorem 1 issue; conversely a representable functor is continuous (the
   hom-functor continuity of the §V.4 issue). Package as the biconditional.
3. Exercise V.8.1: if a `Sets`-valued functor has a left adjoint it is representable; conversely if
   the domain has copowers (#366) and the functor is represented by an object, the copower functor is
   its left adjoint. Prove both.

In-tree donors: `Functor/Representable.v`, `Structure/UniversalProperty.v`, `Adjunction/GAFT.v`,
`Instance/Sets.v` (`Sets_Terminal`), #366's copowers, the §V.6 Theorem 1 issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 122 (PDF pp. 131–132); §V.8, book p. 131 (PDF p. 140)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/Representability.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_global_points.
Print Assumptions representability_theorem.
Print Assumptions representable_iff_left_adjoint.
```
Reviewer: statements match Mac Lane §V.6 Theorem 3 / Definition 3 (book p. 122) and §V.8 Exercise 1
(book p. 131); the biconditional and the copower converse must both be proved.

## Dependencies
Depends on: #366
Depends on: maclane:V.6:thm1

<!-- catalog: {"ids":["maclane:V.6:thm3","maclane:V.6:def3","maclane:V.8:ex1"],"deps":["#366","maclane:V.6:thm1"]} -->
---8<---
```yaml
title: "MacLane V.6: The comma projection creates limits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:lem1, maclane:V.6:ex1, maclane:V.1:ex1]
deps_item_ids: [maclane:V.1:def3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.1, book p. 112 (PDF p. 121); §V.6, book pp. 121–125 (PDF pp. 130–134)
- Items: `maclane:V.6:lem1`, `maclane:V.6:ex1`, `maclane:V.1:ex1`

## Background
When a functor preserves all small products (respectively equalizers), the projection from a comma
category over it creates those limits; the same argument creates any limit the base functor preserves,
which is the engine of the adjoint functor theorem's comma-category step. See
[nLab: comma category](https://ncatlab.org/nlab/show/comma+category) and
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
Verified PARTIAL (both). `Construction/Comma/Limit.v` proves existence of comma limits —
`:238` (`comma_limit`), `:245` (`Comma_Complete`), with the apex data at `:159`
(`apex_obj`/`apex_leg`) — but under an all-shapes completeness oracle `@Complete C` plus all-shapes
`:110` (`PreservesImageLimit`), so the two per-shape clauses Mac Lane actually uses (preserves
products ⇒ comma has products; preserves equalizers ⇒ comma has equalizers) are not derivable. And
creation proper is not stated: the file constructs a limit lying over the chosen base limit, whereas
creation additionally asserts that for ANY base limit cone there is a unique comma cone over it, and
that it is limiting — the uniqueness/reflection clause is absent.

## Work to be done
Suggested module: `Construction/Comma/Creation.v` (or extend `Construction/Comma/Limit.v`).

- Restate `Comma_Complete` per-shape: from `PreservesImageLimit` restricted to product diagrams derive
  products in the comma category, and likewise for equalizers, so the two clauses Mac Lane's Theorem 2
  consumes are available without the all-shapes oracle.
- Prove the creation statement (the lemma and §V.6 Exercise 1): the comma projection creates all small
  limits preserved by the base functor — for any limiting cone of the projected diagram there is a
  unique cone in the comma category lying over it (using `apex_obj`/`apex_leg`), and it is limiting —
  in the sense of the creation class of the §V.1 definition issue.
- Specialize to the coslice (§V.1 Exercise 1, the base functor the identity): instantiate at `Id`
  (discharging `PreservesImageLimit` via `right_adjoint_PreservesImageLimit adj_id`) and transport
  along `Construction/Slice.v:181` (`Comma_Coslice`) to state creation for the coslice projection
  `(c ̸ C) ⟶ C`.

In-tree donors: `Construction/Comma/Limit.v`, `Construction/Slice.v`, `Instance/Adjoints.v` (`adj_id`),
the creation class from the §V.1 definition issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.1, book p. 112 (PDF p. 121); §V.6, book pp. 121–125 (PDF pp. 130–134)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level
- [ ] LIBRARY-DEFECT resolved: the header prose at `Construction/Comma.v:99-100` and `Construction/Comma/Limit.v:32-33` asserts that `comma_proj2` "creates the limits" while the files prove only existence; this issue must make that claim true by proving the creation statement, or else correct the prose to say "constructs" (the same over-claim is flagged by the V.3 discrete-inclusion verifier)

## Verification
```bash
coqc -R . Category Construction/Comma/Creation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions comma_creates_products.
Print Assumptions comma_creates_equalizers.
Print Assumptions comma_proj_creates_limits.
```
Reviewer: statements match Mac Lane §V.6 Lemma and Exercise 1 (book pp. 121, 125); creation must
include the uniqueness/reflection clause, and the per-shape forms must not depend on all-shapes
completeness.

## Dependencies
Depends on: maclane:V.1:def3

<!-- catalog: {"ids":["maclane:V.6:lem1","maclane:V.6:ex1","maclane:V.1:ex1"],"deps":["maclane:V.1:def3"]} -->
---8<---
```yaml
title: "MacLane V.6: Creation of limits is stable under pullback in Cat"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.6:ex3, maclane:V.6:ex4]
deps_item_ids: [maclane:V.1:def3, maclane:V.6:ex1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 125 (PDF p. 134)
- Items: `maclane:V.6:ex3`, `maclane:V.6:ex4`

## Background
Creation of limits is stable under pullback of categories: in a pullback square, if the bottom functor
creates limits and the right functor preserves them, the top functor creates them — yielding a second,
purely formal proof that a comma projection creates limits. See
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit) and
[nLab: Cat](https://ncatlab.org/nlab/show/Cat).

## Current state in the library
Verified ABSENT (Exercise 3) and PARTIAL (Exercise 4). There are no pullbacks in `Cat`
(`rg 'pullback' Instance/Cat*` → 0 hits; `Instance/Cat/` holds only `Bicategory`, `Cartesian`,
`Cocartesian`), which is #337's obligation, and no creation predicate (see the §V.1 definition issue),
so the stability statement of Exercise 3 has neither ingredient. For Exercise 4 (the second proof that
the comma projection creates limits, via Exercise 3 plus the fact that the coslice projection creates
limits), the coslice-projection creation is derivable — `Comma_Complete
(right_adjoint_PreservesImageLimit adj_id) HC` with `Construction/Slice.v:181` — but is not stated,
and Exercise 3 is entirely absent.

## Work to be done
Suggested module: `Instance/Cat/Creation.v` (over #337's pullbacks in `Cat`).

- Prove Exercise 3: given a pullback square in `Cat` (using #337's pullbacks), if the bottom functor
  creates limits and the right functor preserves them, the top functor creates limits — in the sense
  of the §V.1 creation class; the lift upstairs is assembled from the created lift downstairs and the
  preserved image on the right, with uniqueness from the pullback universal property.
- Prove Exercise 4: give the second proof that the comma projection over a continuous functor creates
  small limits, by exhibiting the comma category as a pullback in `Cat` (of the base functor against
  the coslice projection) and applying Exercise 3 to the coslice-projection creation result (which
  this issue also states via `Comma_Coslice` and `adj_id`).

In-tree donors: #337's `Cat` pullbacks, `Construction/Comma.v`, `Construction/Slice.v`,
`Instance/Adjoints.v` (`adj_id`), the creation class from the §V.1 definition issue, the comma-creation
issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 125 (PDF p. 134)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Cat/Creation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions creation_pullback_stable.
Print Assumptions comma_creates_limits_second_proof.
```
Reviewer: statements match Mac Lane §V.6 Exercises 3 and 4 (book p. 125); Exercise 4 must genuinely
route through the pullback-stability of Exercise 3.

## Dependencies
Depends on: #337
Depends on: maclane:V.1:def3
Depends on: maclane:V.6:ex1

<!-- catalog: {"ids":["maclane:V.6:ex3","maclane:V.6:ex4"],"deps":["#337","maclane:V.1:def3","maclane:V.6:ex1"]} -->
---8<---
```yaml
title: "MacLane V.6: The category of algebras of a variety"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:construction-variety, maclane:V.6:def-derived-operator]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 124 (PDF p. 133)
- Items: `maclane:V.6:construction-variety`, `maclane:V.6:def-derived-operator`

## Background
The algebras of a given type satisfying a set of identities, with their operation-preserving maps,
form a category — a variety or equational class (groups, rings, abelian groups, …) — and the derived
operators of the type close the given operations under composition and substitution into a clone whose
action on any algebra is determined by the basic one. See
[nLab: variety of algebras](https://ncatlab.org/nlab/show/variety+of+algebras).

## Current state in the library
Verified PARTIAL (both). The signature-and-algebra scaffolding exists but the variety category does
not: `Instance/Comp.v:151` (`Algs`) is the category of algebras of a signature WITHOUT equations, and
`Instance/Comp.v:382` (`Group := Algebra GroupOp GroupEq`) is a type of algebras, not a category — so
`⟨Ω,E⟩-Alg` is nowhere formed, and the identification of `Models T Sets`
(`Theory/Lawvere/Model.v:77`) with a presented variety is not made. The derived operators are also
missing: `Instance/Comp.v`'s `Tree` is unindexed (a term over a whole variable type, not an operator
of a specific arity), no composition or substitution operation is named, and the only arity-graded
term development, `Construction/PROP/Term.v:39` (`Term`), closes under composition, tensor and braids
but NOT under Mac Lane's substitution along an arbitrary function between finite sets.

## Work to be done
Suggested module: `Instance/Variety.v` (and `Instance/Variety/Clone.v` for the derived operators).

- The variety category: the full subcategory of `Algs` (or the analogue of `Theory/Lawvere/Model.v`'s
  `Models_sub`) cut out by the algebras satisfying a set of identities `E`, with operation-preserving
  maps; instantiate it at the group signature so `Grp := ⟨GroupOp, GroupEq⟩-Alg` is a genuine
  category (coordinate with #255).
- The derived operators (clone) `Λ` of a graded set `Ω`: the arity-graded set closed under
  composition and under substitution along an arbitrary function between finite arities
  (duplication/deletion of variables), with the theorem that every action of `Ω` on a set extends
  uniquely to an action of `Λ` — recovering `induced_hom`/`from_free_unique` as the free-algebra
  instance.
- Record the connection to `Theory/Lawvere/Model.v`: a variety's Sets-models are the Lawvere-theory
  models of the associated theory.

In-tree donors: `Instance/Comp.v`, `Theory/Lawvere/Model.v`, `Construction/Subcategory.v`,
`Construction/PROP/Term.v` (for the substitution discipline).

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 124 (PDF p. 133)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Variety.v Instance/Variety/Clone.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Variety.
Print Assumptions DerivedOperators.
Print Assumptions action_extends_to_clone.
```
Reviewer: statements match Mac Lane §V.6 (book p. 124); the variety must be a genuine `Category`, and
the clone must close under substitution along ARBITRARY functions between arities (not only braids).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.6:construction-variety","maclane:V.6:def-derived-operator"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.6: The free-algebra adjunction for a variety"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:construction-free-algebra]
deps_item_ids: [maclane:V.6:construction-variety, maclane:V.6:thm2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 124 (PDF pp. 133–134)
- Items: `maclane:V.6:construction-free-algebra`

## Background
For any variety the adjoint functor theorem produces a left adjoint to the underlying-set functor —
the free algebra on a set — the solution set being the subalgebra generated by the image; this yields
free rings, free abelian groups and free modules, but not free fields, whose partial inverse blocks
the construction. See [nLab: variety of algebras](https://ncatlab.org/nlab/show/variety+of+algebras)
and [nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified PARTIAL. The free algebra of a SIGNATURE exists — `Instance/Comp.v:92` (`Free`/`Tree`), `:108`
(`induced_hom`), with `Instance/Comp.v:209` (`Algs_Initial`) — but it is not quotiented by the
congruence generated by the equations, so no free object of a VARIETY exists; there is no underlying
functor `Variety ⟶ Sets` and no free functor, hence no adjunction; and no `SolutionSet` instance for
such a forgetful functor (the notion "subalgebra generated by the image" does not occur in the tree).
GAFT's only worked instance is `Δ ⊣ (×)` (`Adjunction/GAFT/Examples.v`); no free-algebra example
exists.

## Work to be done
Suggested module: `Instance/Variety/Free.v`.

- Construct the free `⟨Ω,E⟩`-algebra on a set: the term algebra `Instance/Comp.v:92` quotiented by the
  congruence generated by `E` (donor: `Construction/Quotient.v`), with the insertion of generators.
- Define the underlying-set functor `Variety ⟶ Sets` (from the variety category issue) and, via the
  adjoint functor theorem (the §V.6 Theorem 2 issue), the free functor left adjoint to it — supplying
  the solution set as the subalgebra generated by the image with the cardinality bound of §V.7.
- Package `Free ⊣ U` and record the named consequences (free ring, free abelian group, free module as
  instances once those varieties are available) and the field non-example (the multiplicative inverse
  is not a total operation, so fields are not a variety and free fields do not exist).

In-tree donors: `Instance/Comp.v`, `Construction/Quotient.v`, `Theory/Universal/Arrow.v`, the variety
category issue, the §V.6 Theorem 2 issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 124 (PDF pp. 133–134)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Variety/Free.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Free_Variety.
Print Assumptions Free_Variety_adjunction.
```
Reviewer: statement matches Mac Lane §V.6 (book p. 124); the free object must be the equation-quotient
of the term algebra, and the adjunction must be produced via the AFT with the generated-subalgebra
solution set.

## Dependencies
Depends on: maclane:V.6:construction-variety
Depends on: maclane:V.6:thm2

<!-- catalog: {"ids":["maclane:V.6:construction-free-algebra"],"deps":["maclane:V.6:construction-variety","maclane:V.6:thm2"]} -->
---8<---
```yaml
title: "MacLane V.6: The free group functor via the adjoint functor theorem"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:construction-free-group]
deps_item_ids: [maclane:V.6:thm2, maclane:V.1:thm3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 123 (PDF p. 132)
- Items: `maclane:V.6:construction-free-group`

## Background
Applying Freyd's theorem to the underlying-set functor of groups produces the free group functor
without any word-normal-form construction: the solution set is the family of subgroups generated by
the image of a function, and the universal arrow into the free group is injective. See
[Wikipedia: Category of groups](https://en.wikipedia.org/wiki/Category_of_groups) and
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified ABSENT. The category of groups is not in-tree (the `Grp` occurrences are prose;
`Structure/Group.v` is group OBJECTS; `Instance/Comp.v:382`'s `Group` is a type of algebras), so
neither the forgetful functor nor its free object exists; #255 files `Grp`. The free/forgetful
adjunctions that do exist — `Construction/Free/Quiver.v:550`, `Monad/Kleisli/Adjunction.v`,
`Monad/Eilenberg/Moore/Adjunction.v` — are none of them over groups, and the only worked GAFT
application is `Δ ⊣ (×)`.

## Work to be done
Suggested module: `Instance/Grp/Free.v`, over #255's `Grp`.

- Establish that the underlying-set functor of `Grp` is continuous — reuse the "Grp creates limits"
  result (the §V.1 Grp issue) so continuity is a corollary of creation.
- Build the solution set for a set `X`: the subgroups generated by the image of a function `X → UG`
  (finite products of generators and inverses), bounded in cardinality by `X`; take representatives of
  isomorphism classes. This requires a notion of generated subgroup — introduce it here (the smallest
  subgroup containing a subset) as reusable group API.
- Apply the adjoint functor theorem (the §V.6 Theorem 2 issue) to obtain the free group functor
  `Sets ⟶ Grp` left adjoint to the underlying-set functor, and prove the universal arrow
  `X → U(FX)` injective by the two-element-group separation argument.

In-tree donors: #255's `Grp`, the §V.1 Grp-creation issue, the §V.6 Theorem 2 issue,
`Theory/Universal/Arrow.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 123 (PDF p. 132)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Grp/Free.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Free_Grp.
Print Assumptions Free_Grp_adjunction.
Print Assumptions Free_Grp_unit_injective.
```
Reviewer: statement matches Mac Lane §V.6 (book p. 123); the adjoint must be produced via the AFT with
the generated-subgroup solution set, and the unit's injectivity must be proved.

## Dependencies
Depends on: #255
Depends on: maclane:V.6:thm2
Depends on: maclane:V.1:thm3

<!-- catalog: {"ids":["maclane:V.6:construction-free-group"],"deps":["#255","maclane:V.6:thm2","maclane:V.1:thm3"]} -->
---8<---
```yaml
title: "MacLane V.6: Left adjoints to forgetful functors by the adjoint functor theorem"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.6:ex2]
deps_item_ids: [maclane:V.6:thm2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 125 (PDF p. 134)
- Items: `maclane:V.6:ex2`

## Background
The adjoint functor theorem produces left adjoints for the forgetful functors from rings to sets, from
rings to abelian groups, and from categories to graphs, recovering the free ring, the tensor/monoid
ring, and the free category on a graph. See
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified PARTIAL. The graph case has an explicit free construction already —
`Construction/Free/Quiver.v:550` (`FreeForgetfulAdjunction`), `:412` (`Forgetful`), `:518`
(`UniversalArrowQuiverCat`) — but it is built by hand, not via the AFT, and it is the `StrictCat`
version (the `Cat` version is documented unavailable in the weak-equivalence setting at
`Test/Issue138.v:75`). The ring cases are entirely absent: `Rng` and `Ab` do not exist (#257, #256),
so neither the ring-side forgetful functors nor their free objects exist, and no `SolutionSet` instance
is ever built for a forgetful functor of this kind.

## Work to be done
Suggested module: `Instance/Rng/Free.v` (and a comparison lemma in `Construction/Free/Quiver.v`).

- Over #257's `Rng` and #256's `Ab`, define the forgetful functors `Rng ⟶ Sets` and `Rng ⟶ Ab`, build
  their solution sets (generated subrings, bounded in cardinality), and apply the adjoint functor
  theorem (the §V.6 Theorem 2 issue) to obtain the free ring on a set and the monoid/tensor ring on an
  abelian group.
- For the graph case, produce the left adjoint to the categories-to-graphs forgetful functor via the
  AFT and prove it isomorphic to the existing hand-built `FreeCatFunctor`, so the two constructions are
  reconciled rather than left parallel.
- State each "compare with the usual construction" clause as a proved isomorphism of the AFT-produced
  adjoint with the explicit free object.

In-tree donors: #257's `Rng`, #256's `Ab`, `Construction/Free/Quiver.v`, the §V.6 Theorem 2 issue,
`Theory/Universal/Arrow.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 125 (PDF p. 134)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Rng/Free.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Free_Rng_Set.
Print Assumptions Free_Rng_Ab.
Print Assumptions FreeCat_via_AFT_iso.
```
Reviewer: statement matches Mac Lane §V.6 Exercise 2 (book p. 125); each adjoint must be produced via
the AFT and compared to the explicit free construction.

## Dependencies
Depends on: #257
Depends on: #256
Depends on: maclane:V.6:thm2

<!-- catalog: {"ids":["maclane:V.6:ex2"],"deps":["#257","#256","maclane:V.6:thm2"]} -->
---8<---
```yaml
title: "MacLane V.6: The solution set condition is necessary (counterexamples)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:remark-ord-counterexample, maclane:V.6:remark-comp-bool]
deps_item_ids: [maclane:V.6:thm2, maclane:V.6:thm3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 123 (PDF p. 132)
- Items: `maclane:V.6:remark-ord-counterexample`, `maclane:V.6:remark-comp-bool`

## Background
The solution set condition cannot be dropped from the adjoint functor theorems: the ordered class of
small ordinals is small-complete yet the constant set-valued functor on it is continuous without being
representable, and (Solovay) there is no free complete Boolean algebra on a countable set, so the
forgetful functor from complete Boolean algebras is continuous with a small-complete domain yet has no
left adjoint. See [nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem)
and [Wikipedia: Complete Boolean algebra](https://en.wikipedia.org/wiki/Complete_Boolean_algebra).

## Current state in the library
Verified ABSENT (both). The library has no ordinals as a category (`rg -w 'Ord|OrdCat'` → a lone prose
cross-reference in `Instance/Proset.v:19`; `Instance/Omega.v` is only the ordinal ω), no smallness/
largeness machinery to make "the class of all small ordinals" a category, and it records no example of
a continuous functor without a left adjoint (`rg -i 'counterexample|no left adjoint'` → nothing of this
kind). Complete Boolean algebras and Solovay's theorem are entirely absent (`rg -i 'solovay|complete
boolean|CABA'` → 0 hits). So neither witness to the necessity of the solution set condition exists.

## Work to be done
Suggested module: `Adjunction/GAFT/Necessity.v`.

- The ordinals counterexample: build the (large, thin) category `Ord` of small ordinals — a hom is a
  proposition, `α ≤ β` — and prove `Ord^op` small-complete (a small product of ordinals is their least
  upper bound, using the preorder-limit identification of the §V.2 preorder issue). Show the constant
  one-point functor `Ord^op ⟶ Sets` is continuous but not representable (a representation would name a
  largest small ordinal), witnessing that continuity alone does not give representability (against the
  §V.6 representability issue).
- The complete-Boolean-algebra counterexample: state that the forgetful functor from complete Boolean
  algebras to sets is continuous on a small-complete domain but has no left adjoint, since no free
  complete Boolean algebra on a countable set exists (Solovay). Solovay's theorem is a deep
  set-theoretic result; the header must disclose whether it is taken as an explicit hypothesis (an
  input asserting arbitrarily large complete Boolean algebras generated by a countable set) or proved,
  and the zero-axiom rule applies to whatever is actually built.
- Present both as the sharpness companion to the §V.6 adjoint functor and representability theorems.

In-tree donors: `Instance/Proset.v`, `Instance/Omega.v`, the §V.2 preorder-limit issue, the §V.6
representability issue, `Functor/Representable.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 123 (PDF p. 132)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/GAFT/Necessity.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Ord_op_complete.
Print Assumptions Ord_constant_continuous_not_representable.
```
Reviewer: statements match Mac Lane §V.6 (book pp. 122–123); the ordinals witness must be a genuine
continuous-but-not-representable functor, and any set-theoretic input for the Boolean case disclosed in
the header.

## Dependencies
Depends on: maclane:V.6:thm2
Depends on: maclane:V.6:thm3

<!-- catalog: {"ids":["maclane:V.6:remark-ord-counterexample","maclane:V.6:remark-comp-bool"],"deps":["maclane:V.6:thm2","maclane:V.6:thm3"]} -->
---8<---
```yaml
title: "MacLane V.7: Intersections and unions of subobjects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.7:def2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book p. 126 (PDF p. 135)
- Items: `maclane:V.7:def2`

## Background
The subobjects of an object form a partial order under factorization; the pullback of two monos into
the object is their intersection (meet), a wide pullback of a family is their intersection, and unions
(joins) exist under further hypotheses — the lattice of subobjects. See
[nLab: subobject](https://ncatlab.org/nlab/show/subobject).

## Current state in the library
Verified PARTIAL. The factorization order is in-tree — `Theory/Subobject.v:59` (`sub_le`), `:62-78`
(reflexivity/transitivity/uniqueness), `:93` (`sub_equiv_iff_mutual`) — and the reindexing machinery
`Theory/Subobject/Functor.v:35` (`sub_reindex`) already packages a pulled-back mono AS a `SubObj`,
using `Theory/Morphisms/Stability.v:226` (`monic_pullback_stable`) and `Theory/Morphisms.v:212`
(`monic_compose`). What is missing: the intersection subobject itself (the composite of a pullback leg
with a mono, pushed forward to a `SubObj` of the ambient object), the two factorizations exhibiting it
below both, the greatest-lower-bound property (nothing in the tree states any glb/lub of `sub_le`),
wide/multiple pullbacks (`rg 'wide pullback|multiple pullback'` → 0 hits), and unions/joins and any
lattice structure on `SubObj` (`rg 'lattice|Heyting'` → background prose only). The
`Structure/Pullback.v:93-94` header asserts the intersection reading in words but constructs nothing.

## Work to be done
Suggested module: `Theory/Subobject/Lattice.v`.

- Binary meet: for `u v : SubObj a` and a chosen pullback of their monos, the composite
  `sub_mono u ∘ pullback_fst` as a `SubObj a` (monic by `monic_compose` + `monic_pullback_stable`,
  much of which `sub_reindex` already packages); prove the two legs `w ≤ u`, `w ≤ v` and the
  greatest-lower-bound property for `sub_le`.
- Wide intersections: introduce wide (multiple) pullbacks and define the intersection of a
  `J`-indexed family of subobjects as the wide pullback when it exists, with its glb property.
- Unions: define the join under the added hypotheses (an image-factorization of the copairing, using
  `Instance/Sets/Image.v`/`Structure/Factorization.v` where available), disclosing exactly which
  hypotheses are assumed; record the (semi)lattice structure on `SubObj a`.

In-tree donors: `Theory/Subobject.v`, `Theory/Subobject/Functor.v` (`sub_reindex`),
`Theory/Morphisms/Stability.v`, `Structure/Pullback.v`, `Structure/Factorization.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book p. 126 (PDF p. 135)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Theory/Subobject/Lattice.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions sub_meet.
Print Assumptions sub_meet_is_glb.
Print Assumptions sub_wide_intersection.
```
Reviewer: statement matches Mac Lane §V.7 (book p. 126); the intersection must be proved a greatest
lower bound for `sub_le`, and the wide-pullback (family) case must be present.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.7:def2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.7: Quotient objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.7:def3]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book p. 126 (PDF pp. 135–136)
- Items: `maclane:V.7:def3`

## Background
Dually to subobjects, the quotient objects of an object are equivalence classes of epimorphisms out of
it, partially ordered by factorization; in categories where epis are surjective they are the usual
quotients. See [nLab: quotient object](https://ncatlab.org/nlab/show/quotient+object).

## Current state in the library
Verified PARTIAL. The dual definition is one line but never written: `Theory/Subobject.v:15` (`SubObj`)
is instantiable at `C^op`, so `Definition QuotObj (x : C) := @SubObj (C^op) x` would give the notion
(the idiom the library uses for `Comonad := @Monad (C^op) (M^op)`), yet there are no covariant
accessors (quotient epi, quotient codomain), no covariant restatement of the setoid or of
`sub_le`/`sub_equiv_iff_mutual` in quotient orientation, and no lemma identifying `Monic` in `C^op`
with the `Epic` class of `Theory/Morphisms.v:104` (they are two distinct one-field records of the same
field type). Mac Lane's group illustration (quotient objects of a group are the `G/N`) is absent, the
library having no group theory of that kind.

## Work to be done
Suggested module: `Theory/Quotient.v` (or `Theory/Subobject/Quotient.v`).

- Define `QuotObj x := @SubObj (C^op) x` and provide covariant accessors — the quotient epimorphism,
  the quotient codomain — with the setoid and the order `quot_le` restated in quotient orientation
  from `sub_le`/`sub_equiv_iff_mutual`.
- Prove the conversion lemma identifying `Monic` in `C^op` with `Epic` in `C`, so the quotient
  epimorphism is genuinely an epi of `C`.
- State the "agrees with the usual notion where epis are onto" clause for `Sets` (using the present
  characterization of epis as surjections), and record the meet/join dual of the subobject-lattice
  issue by the same `C^op` transport.

In-tree donors: `Theory/Subobject.v`, `Theory/Morphisms.v` (`Epic`, with its duality note),
`Construction/Opposite.v`, `Instance/Sets.v` (epis are surjections).

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book p. 126 (PDF pp. 135–136)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Theory/Quotient.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions QuotObj.
Print Assumptions monic_op_iff_epic.
```
Reviewer: statement matches Mac Lane §V.7 (book p. 126); the covariant accessors must present a genuine
epimorphism of `C`, and the order must be the dual of `sub_le`.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.7:def3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.7: Generating (separating) sets of objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.7:def4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book p. 127 (PDF p. 136)
- Items: `maclane:V.7:def4`

## Background
A set of objects generates (better: separates) a category when maps out of them jointly distinguish
parallel arrows — equivalently, the representable functors on them are jointly faithful; the one-point
set generates sets, the integers generate abelian groups. See
[nLab: separator](https://ncatlab.org/nlab/show/separator).

## Current state in the library
Verified PARTIAL. Only the dual is in-tree: `Adjunction/SAFT.v:99` (`Cogenerator`), with the joint-
faithfulness idea stated as prose about the dual in the SAFT header (`:96`) and never proved in either
direction. A search for `Generator`/`Separator`/`SeparatingFamily`/`Generates` finds exactly that one
`Cogenerator` record. Missing: the definition itself (obtainable as
`Definition Generator (C) := Cogenerator (C^op)`, or spelled directly), the equivalence with joint
faithfulness of the representables, and every example (the terminal object generates `Sets`; the
integers generate abelian groups — the latter gated on #256's `Ab`).

## Work to be done
Suggested module: `Structure/Generator.v`.

- Define a generating (separating) family: a set `S` of objects such that for every parallel pair
  `h ≠ h'` there are `s ∈ S` and `f : s → c` with `h ∘ f ≠ h' ∘ f`; give it both directly and as the
  dual `Cogenerator (C^op)`, and prove they agree.
- Prove the equivalent characterization: `S` generates iff the family of representables `C(s, −)` for
  `s ∈ S` is jointly faithful — both directions (the dual of the header prose in `Adjunction/SAFT.v`).
- Record the `Sets` example (the terminal object is a separator, since global elements distinguish
  setoid maps) and note the algebraic examples as consequences awaiting their host categories.

In-tree donors: `Adjunction/SAFT.v` (`Cogenerator`), `Theory/Functor.v` (`Faithful`),
`Functor/Hom.v`, `Construction/Opposite.v`, `Instance/Sets.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book p. 127 (PDF p. 136)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Generator.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Generator.
Print Assumptions generator_iff_jointly_faithful.
Print Assumptions Sets_terminal_separates.
```
Reviewer: statement matches Mac Lane §V.7 (book p. 127); the joint-faithfulness characterization must
be proved both ways, and at least the `Sets` example given.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:V.7:def4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane V.7: Spanning arrows and solution sets from subobject intersections"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.7:def6, maclane:V.7:lem2, maclane:V.7:remark1]
deps_item_ids: [maclane:V.7:def2, maclane:V.6:construction-variety]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book pp. 127–128 (PDF pp. 136–137)
- Items: `maclane:V.7:def6`, `maclane:V.7:lem2`, `maclane:V.7:remark1`

## Background
An arrow spans an object when it factors through no proper subobject; when a functor preserves
intersections of subobjects, every arrow factors through a spanning one, and the spanning arrows out of
each object form a solution set — the subobject-theoretic route to the adjoint functor theorem, applied
to varieties via generated subalgebras. See [nLab: subobject](https://ncatlab.org/nlab/show/subobject)
and [nLab: solution set condition](https://ncatlab.org/nlab/show/solution+set+condition).

## Current state in the library
Verified ABSENT (all three). There is no spanning-arrow notion (`rg -i 'spanning'` finds only the
span/cospan limit shape), no "proper subobject" (`sub_le` carries no strict order and there is no top
subobject; `rg 'proper mono|proper subobject'` → 0 hits), and no generated subobject/subalgebra
(`rg 'generated subalgebra|generated subobject'` → 0 hits). The intersection of subobjects the lemma's
proof takes is itself missing (the §V.7 subobject-lattice issue), and `SolutionSet`
(`Adjunction/GAFT.v:159`) is manufactured only in `Adjunction/SAFT.v:252`, never from spanning arrows.

## Work to be done
Suggested module: `Adjunction/SpanningArrow.v`.

- Define a proper subobject (strictly below the top subobject `id`) and a spanning arrow for a functor
  `G` (an arrow `x → Ga` factoring through no proper subobject of `a`), reusing the subobject order and
  the intersection meet of the §V.7 subobject-lattice issue.
- Prove Lemma (V.7): when every family of subobjects has an intersection and `G` preserves these
  intersections, every arrow `x → Ga` factors through a spanning arrow (the intersection of all
  subobjects it factors through), so the spanning arrows out of `x` form a solution set for `G`.
- Prove Remark (V.7): for the underlying-set functor of a variety, the subalgebra generated by the
  image of a function gives such a spanning factorization, with the cardinality bound, delivering the
  solution set used by the free-algebra construction.

In-tree donors: the §V.7 subobject-lattice issue, `Theory/Subobject.v`, `Adjunction/GAFT.v`
(`SolutionSet`), the variety category issue, `Structure/Factorization.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book pp. 127–128 (PDF pp. 136–137)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/SpanningArrow.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions spanning_arrow.
Print Assumptions factors_through_spanning.
Print Assumptions spanning_solution_set.
```
Reviewer: statements match Mac Lane §V.7 (book pp. 127–128); the lemma must use preservation of
subobject intersections, and the remark must produce a genuine solution set for a variety.

## Dependencies
Depends on: maclane:V.7:def2
Depends on: maclane:V.6:construction-variety

<!-- catalog: {"ids":["maclane:V.7:def6","maclane:V.7:lem2","maclane:V.7:remark1"],"deps":["maclane:V.7:def2","maclane:V.6:construction-variety"]} -->
---8<---
```yaml
title: "MacLane V.7: Tensor products of modules via the adjoint functor theorem"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.7:construction1, maclane:V.7:ex3]
deps_item_ids: [maclane:V.6:thm2, maclane:V.7:def6]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book p. 128 (PDF p. 137)
- Items: `maclane:V.7:construction1`, `maclane:V.7:ex3`

## Background
The tensor product of modules is obtained categorically as a universal element of the bilinear-maps
functor: the adjoint functor theorem supplies it once the solution set is cut down to bilinear maps
that span their target, so no generators-and-relations construction is needed; over a noncommutative
ring the balanced tensor product arises the same way. See
[Wikipedia: Tensor product of modules](https://en.wikipedia.org/wiki/Tensor_product_of_modules) and
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified ABSENT (both). There is no bilinear-maps notion (`rg -i 'bilinear|Bilin'` → background prose
only), no tensor product of modules (`rg 'tensor product of modules'` → 0 hits), and no module
category (#258); every in-tree "tensor" is the abstract monoidal `⨂` or the Day/PROP/funny tensors.
The universal-arrow machinery `Theory/Universal/Arrow.v` exists but is never applied to a bilinear-maps
functor, and the spanning-arrow solution-set route (the §V.7 spanning issue) is likewise absent.

## Work to be done
Suggested module: `Instance/Module/Tensor.v`, over #258's module categories.

- Define bilinear (and, over a noncommutative ring, balanced) maps and the functor
  `Bilin(A, B; −) : Mod ⟶ Sets`.
- Construct the tensor product as a universal element of that functor via the adjoint functor theorem
  (the §V.6 Theorem 2 issue), with the solution set given by the bilinear maps that span their target
  (the spanning-arrow route of the §V.7 spanning issue) — emphasizing that all properties follow from
  the universal property, with no explicit generators-and-relations construction.
- Prove it spanned by the elementary tensors, and for a ring map examine the base-change relation
  between the tensor products over the two rings.

In-tree donors: #258's modules, `Theory/Universal/Arrow.v`, the §V.6 Theorem 2 issue, the §V.7
spanning-arrow issue, `Instance/Sets/Coend.v` (setoid-quotient idiom, if a direct model is wanted).

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book p. 128 (PDF p. 137)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Module/Tensor.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Bilin.
Print Assumptions module_tensor_universal.
```
Reviewer: statements match Mac Lane §V.7 (book p. 128) and Exercise 3; the tensor product must be
produced as a universal element via the AFT, not by generators and relations.

## Dependencies
Depends on: #258
Depends on: maclane:V.6:thm2
Depends on: maclane:V.7:def6

<!-- catalog: {"ids":["maclane:V.7:construction1","maclane:V.7:ex3"],"deps":["#258","maclane:V.6:thm2","maclane:V.7:def6"]} -->
---8<---
```yaml
title: "MacLane V.7: Colimits in algebraic categories via the adjoint functor theorem"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.7:ex1, maclane:V.7:ex2, maclane:V.7:ex4]
deps_item_ids: [maclane:V.6:thm2, maclane:V.6:construction-variety]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.7, book p. 128 (PDF p. 137)
- Items: `maclane:V.7:ex1`, `maclane:V.7:ex2`, `maclane:V.7:ex4`

## Background
The adjoint functor theorem builds colimits in algebraic categories: the coproduct (free product) of
groups, the coproduct of rings, and coequalizers in any variety, each as a solution to the appropriate
universal problem. See [Wikipedia: Category of groups](https://en.wikipedia.org/wiki/Category_of_groups)
and [nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem).

## Current state in the library
Verified ABSENT (all three). Free products of groups are prose only (`rg -i 'free product'` →
background comments such as `Construction/Funny.v:113`), there is no `Grp` (#255) and no `Rng` (#257),
and `Instance/Comp.v`'s `Algs_Cocartesian` (the generic coproduct of algebras) is COMMENTED OUT
(`:223-233`, bodies left as `_`). The coequalizer classes `Structure/Coequalizer.v:68`
(`HasCoequalizers`) and `Structure/Coequalizer/Reflexive.v:54` exist but are never instantiated in any
concrete algebraic category (`rg 'coequalizer' Instance/` → prose only), and the sole end-to-end AFT
application is `Δ ⊣ (×)`.

## Work to be done
Suggested module: `Instance/Grp/Coproduct.v`, `Instance/Rng/Coproduct.v`, `Instance/Variety/Coequalizer.v`.

- Free product of groups (Exercise 1): construct the coproduct in `Grp` (#255) as a universal object
  via the adjoint functor theorem (the §V.6 Theorem 2 issue), and prove the two injections monic with
  images meeting in the trivial subgroup (needs generated subgroups and the subobject intersection of
  the §V.7 subobject-lattice issue).
- Coproduct of rings (Exercise 2): the analogous construction in `Rng` (#257).
- Coequalizers in a variety (Exercise 4): construct coequalizers in the variety category (the variety
  issue) by the adjoint functor theorem, giving the variety its first colimits.

In-tree donors: #255's `Grp`, #257's `Rng`, the variety category issue, the §V.6 Theorem 2 issue,
`Structure/Coequalizer.v`, `Structure/Cocartesian.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.7, book p. 128 (PDF p. 137)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Grp/Coproduct.v Instance/Rng/Coproduct.v Instance/Variety/Coequalizer.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Grp_free_product.
Print Assumptions Rng_coproduct.
Print Assumptions Variety_coequalizers.
```
Reviewer: statements match Mac Lane §V.7 Exercises 1, 2, 4 (book p. 128); each colimit must be produced
via the AFT, and the group-injection monicity/intersection claim proved.

## Dependencies
Depends on: #255
Depends on: #257
Depends on: maclane:V.6:thm2
Depends on: maclane:V.6:construction-variety

<!-- catalog: {"ids":["maclane:V.7:ex1","maclane:V.7:ex2","maclane:V.7:ex4"],"deps":["#255","#257","maclane:V.6:thm2","maclane:V.6:construction-variety"]} -->
---8<---
```yaml
title: "MacLane V.8: Well-powered and co-well-powered categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.8:def1]
deps_item_ids: [maclane:V.7:def2, maclane:V.7:def3]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.8, book p. 130 (PDF p. 139)
- Items: `maclane:V.8:def1`

## Background
A category is well-powered when the subobjects of each object form a small set and co-well-powered when
the quotient objects do; a well-powered small-complete category automatically has all intersections of
subobjects, formed by pullback, making the extra hypotheses of the special theorems automatic. See
[nLab: well-powered category](https://ncatlab.org/nlab/show/well-powered+category) and
[nLab: subobject](https://ncatlab.org/nlab/show/subobject).

## Current state in the library
Verified PARTIAL. `Adjunction/SAFT.v:119` (`SubobjectIndex`) supplies a per-object small index of
subobjects but with NO exhaustiveness clause — nothing states that the index enumerates ALL subobjects
of the object, so it is strictly weaker than well-poweredness (and trivially satisfiable, as its header
at `:63` and `:117` acknowledges). The dual (co-well-powered, over quotient objects) does not exist,
and the recorded consequence — well-powered + small-complete ⇒ every set of subobjects has an
intersection — is absent, since no intersection/wide-pullback construction exists (the §V.7
subobject-lattice issue).

## Work to be done
Suggested module: `Structure/WellPowered.v`.

- Define `WellPowered C`: for each object a small index together with a bijection onto the setoid of
  ALL its subobjects (the exhaustiveness clause `SubobjectIndex` lacks) — strengthen or wrap
  `Adjunction/SAFT.v:119` accordingly.
- Define `CoWellPowered C := WellPowered (C^op)` over the quotient objects of the §V.7 quotient issue.
- Prove the consequence: a well-powered small-complete category has all intersections of families of
  subobjects, formed as the wide pullback of the §V.7 subobject-lattice issue over the (now small)
  index — so the intersection hypothesis of the special theorems is automatic.

In-tree donors: `Adjunction/SAFT.v` (`SubobjectIndex`), `Theory/Subobject.v`, the §V.7 subobject-lattice
and quotient issues, `Structure/Complete.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.8, book p. 130 (PDF p. 139)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/WellPowered.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions WellPowered.
Print Assumptions CoWellPowered.
Print Assumptions wellpowered_complete_has_intersections.
```
Reviewer: statement matches Mac Lane §V.8 (book p. 130); well-poweredness must carry the exhaustiveness
clause (a bijection onto ALL subobjects), and the intersection consequence must be proved.

## Dependencies
Depends on: maclane:V.7:def2
Depends on: maclane:V.7:def3

<!-- catalog: {"ids":["maclane:V.8:def1"],"deps":["maclane:V.7:def2","maclane:V.7:def3"]} -->
---8<---
```yaml
title: "MacLane V.8: The special initial-object theorem"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.8:thm1]
deps_item_ids: [maclane:V.7:def2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.8, book p. 128 (PDF pp. 137–138)
- Items: `maclane:V.8:thm1`

## Background
A small-complete category with small hom-sets, a small cogenerating set, and all intersections of
subobjects has an initial object: the intersection of all subobjects of the product of the cogenerating
set. See [nLab: complete category](https://ncatlab.org/nlab/show/complete+category) and
[nLab: separator](https://ncatlab.org/nlab/show/separator).

## Current state in the library
Verified PARTIAL. The theorem is unstated. In-tree SAFT (`Adjunction/SAFT.v:274`) deliberately bypasses
it, routing through GAFT's solution-set/weakly-initial machinery instead, and the supporting pieces are
present only in that guise — `Adjunction/SAFT.v:223` (`cogenerator_canonical_monic`), `:99`
(`Cogenerator`), `Theory/WeaklyInitial.v:89` (`initial_from_weakly_initial`), `:119`
(`SubobjectIndex`). Missing: the intersection of a FAMILY of subobjects (the §V.7 subobject-lattice
issue), the uniqueness half (two distinct arrows out of the candidate would have an equalizer that is a
strictly smaller subobject of the product), and the conclusion `Initial` from completeness + a
cogenerating set + intersections.

## Work to be done
Suggested module: `Adjunction/SAFT/InitialObject.v`.

- State and prove the special initial-object theorem: from `Complete C`, a `Cogenerator`, and all
  subobject intersections (the §V.7 subobject-lattice issue), the initial object is the intersection of
  all subobjects of the product of the cogenerating family.
- Prove existence of an arrow from it to any object by pulling a mono into the product back along the
  canonical map (using `cogenerator_canonical_monic`), and uniqueness by the equalizer-subobject
  argument (two arrows would give an equalizer strictly below the intersection, contradiction).
- Relate to the existing `initial_from_weakly_initial`: this is Mac Lane's alternative, cogenerator-
  based route to the same initial object, and the header should state that relationship.

In-tree donors: `Adjunction/SAFT.v` (`Cogenerator`, `cogenerator_canonical_monic`, `SubobjectIndex`),
`Theory/WeaklyInitial.v`, the §V.7 subobject-lattice issue, `Structure/Equalizer/Fork.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.8, book p. 128 (PDF pp. 137–138)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/SAFT/InitialObject.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions special_initial_object.
```
Reviewer: statement matches Mac Lane §V.8 Theorem 1 (book p. 128); the initial object must be the
subobject intersection, and both existence and the equalizer-based uniqueness proved.

## Dependencies
Depends on: maclane:V.7:def2

<!-- catalog: {"ids":["maclane:V.8:thm1"],"deps":["maclane:V.7:def2"]} -->
---8<---
```yaml
title: "MacLane V.8: The special adjoint functor theorem as a characterization"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.8:thm2, maclane:V.8:lem1, maclane:V.8:cor1]
deps_item_ids: [maclane:V.8:thm1, maclane:V.8:def1, maclane:V.7:def2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.8, book pp. 129–130 (PDF pp. 138–139)
- Items: `maclane:V.8:thm2`, `maclane:V.8:lem1`, `maclane:V.8:cor1`

## Background
The special adjoint functor theorem: from a small-complete, well-powered domain with small hom-sets and
a small cogenerating set, a functor has a left adjoint if and only if it preserves all small limits and
all pullbacks of families of monos — and its corollary, that every continuous functor into sets on such
a domain is representable. See
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem) and
[nLab: well-powered category](https://ncatlab.org/nlab/show/well-powered+category).

## Current state in the library
Verified PARTIAL (theorem and corollary) and ABSENT (the monos lemma). In-tree SAFT
(`Adjunction/SAFT.v:274`) is the sufficient direction routed through a caller-supplied
`SubobjectCover` (`:240`) hypothesis; `docs/INHABITATION.md:54` records that none of its three data is
inhabited and SAFT is never applied. Missing: the necessity direction packaged as an iff; the
derivation of the covering/image-factorization step from well-poweredness + `cogenerator_canonical_monic`
+ intersections; the comma-category verification — Mac Lane's Lemma that an arrow of the comma
`(x ↓ G)` is monic iff its underlying arrow is (via the comma projection creating kernel pairs), the
cogenerating set of the comma, and intersections in the comma pulled back from `A`; and the weaker
preservation hypothesis "small limits + pullbacks of families of monics". The classical corollary
form (well-powered + cogenerating set ⇒ the SAFT hypotheses) and the representability half are also
absent.

## Work to be done
Suggested module: `Adjunction/SAFT/Characterization.v`.

1. Prove the monos lemma (V.8): an arrow of the comma category `(x ↓ G)` is monic iff its underlying
   arrow in `A` is — via the comma projection creating limits (the §V.6 comma-creation issue), hence
   kernel pairs, which `A` has and `G` preserves. This makes the comma projection reflect monos.
2. Prove SAFT as a biconditional over `Complete` + `WellPowered` (the §V.8 well-powered issue) + a
   `Cogenerator`: build the left adjoint via the special initial-object theorem (the §V.8 Theorem 1
   issue) in each comma category, whose cogenerating set and intersections are obtained by the monos
   lemma and preservation of the pullbacks; necessity because right adjoints preserve limits.
3. Derive the classical corollary: well-powered + small-complete makes the intersection hypothesis
   automatic (the §V.8 well-powered issue), and every continuous `Sets`-valued functor on such a domain
   is representable.

In-tree donors: `Adjunction/SAFT.v`, `Construction/Comma/Limit.v`, the §V.6 comma-creation issue, the
§V.8 Theorem 1 and well-powered issues, `Functor/Representable.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.8, book pp. 129–130 (PDF pp. 138–139)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Adjunction/SAFT/Characterization.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions comma_monic_iff_underlying_monic.
Print Assumptions SAFT_iff.
Print Assumptions continuous_Set_functor_representable.
```
Reviewer: statements match Mac Lane §V.8 Theorem 2 and Corollary (book pp. 129–130); the monos lemma
and the representability corollary must both be proved, and SAFT stated as a biconditional.

## Dependencies
Depends on: maclane:V.8:thm1
Depends on: maclane:V.8:def1
Depends on: maclane:V.7:def2

<!-- catalog: {"ids":["maclane:V.8:thm2","maclane:V.8:lem1","maclane:V.8:cor1"],"deps":["maclane:V.8:thm1","maclane:V.8:def1","maclane:V.7:def2"]} -->
---8<---
```yaml
title: "MacLane V.8: Watt's theorem on representable additive functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.8:thm-watt, maclane:V.8:ex2, maclane:V.8:ex3]
deps_item_ids: [maclane:V.8:thm2, maclane:V.4:def4]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.8, book pp. 131–132 (PDF pp. 140–141)
- Items: `maclane:V.8:thm-watt`, `maclane:V.8:ex2`, `maclane:V.8:ex3`

## Background
Watt's theorem: a continuous additive functor on a module category is representable, since the ring is
a generator; the proof rests on the hom-tensor adjunctions and the injective cogenerator of the
rationals modulo one. See [nLab: Eilenberg-Watts theorem](https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem)
and [Wikipedia: Tensor product of modules](https://en.wikipedia.org/wiki/Tensor_product_of_modules).

## Current state in the library
Verified ABSENT (all three). There is no module or abelian-group category (#258, #256), no additive
functor notion (`rg -i 'additive functor'` → 0 definitional hits; `Structure/Additive.v` is a class on
CATEGORIES), no injective cogenerator (`rg -i 'injective'` finds only the setoid-map property; the
`nLab` "injective cogenerator" page does not resolve), and no Watt statement (`rg -i 'Watt'` → 0 hits).
The `Representable` class exists but nothing derives an instance from continuity plus additivity.

## Work to be done
Suggested module: `Instance/Module/Watts.v`, over #258's module categories.

- Establish the hom-tensor adjunctions (Exercise 2a): the natural isomorphisms among
  `hom_R(A, hom_Z(B, G))`, `hom_Z(B ⊗_R A, G)` and `hom_R(B, hom_Z(A, G))`, with the induced module
  structures — reusing the module tensor product of the §V.7 tensor issue.
- Prove `hom_Z(R, Q/Z)` is an injective cogenerator of the module category (Exercise 2b), using the
  injective-object notion of the §V.4 projective/injective issue and the divisibility of the rationals
  modulo one.
- Prove Watt's theorem (Exercise 3): a continuous additive functor on modules is representable — via
  the special adjoint functor theorem (the §V.8 characterization issue) applied to the functor, using
  that the ring is a generator; conclude the natural isomorphism with a hom-functor.

In-tree donors: #258's modules, the §V.7 tensor issue, the §V.4 injective-object issue, the §V.8 SAFT
characterization issue, `Functor/Representable.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.8, book pp. 131–132 (PDF pp. 140–141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Module/Watts.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions hom_tensor_adjunction.
Print Assumptions QZ_injective_cogenerator.
Print Assumptions watts_theorem.
```
Reviewer: statements match Mac Lane §V.8 Exercises 2–3 and the Watt theorem (book pp. 131–132); the
representability must be derived from SAFT plus additivity.

## Dependencies
Depends on: #258
Depends on: maclane:V.8:thm2
Depends on: maclane:V.4:def4

<!-- catalog: {"ids":["maclane:V.8:thm-watt","maclane:V.8:ex2","maclane:V.8:ex3"],"deps":["#258","maclane:V.8:thm2","maclane:V.4:def4"]} -->
---8<---
```yaml
title: "MacLane V.6/V.8: The Stone-Cech compactification via the adjoint functor theorems"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:construction-stone-cech-discrete, maclane:V.8:construction1, maclane:V.8:ex4]
deps_item_ids: [maclane:V.6:thm2, maclane:V.8:thm2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.6, book p. 125 (PDF p. 134); §V.8, book pp. 131–132 (PDF pp. 140–141)
- Items: `maclane:V.6:construction-stone-cech-discrete`, `maclane:V.8:construction1`, `maclane:V.8:ex4`

## Background
The Stone-Cech compactification arises as a left adjoint from the adjoint functor theorems: applied to
the underlying-set functor of compact Hausdorff spaces it compactifies a discrete set, and applied via
the special theorem to the inclusion of compact Hausdorff spaces into all spaces (with the unit
interval as cogenerator) it compactifies any space, injectively on completely regular ones. See
[nLab: Stone-Cech compactification](https://ncatlab.org/nlab/show/Stone-Cech+compactification) and
[Wikipedia: Urysohn's lemma](https://en.wikipedia.org/wiki/Urysohn%27s_lemma).

## Current state in the library
Verified ABSENT (all three). No topological categories exist — no `Top`, no `CompHaus`
(`rg -i 'Stone|Cech|compactif|Tychonoff|Urysohn|completely regular'` → prose only, e.g.
`Theory/Universal/Arrow.v:40,46`), so neither functor of the constructions can be named; #259 files
`Top` and the §V.1 CompHaus issue files `CompHaus`. SAFT itself is never applied to any concrete
category (`docs/INHABITATION.md:54`).

## Work to be done
Suggested module: `Instance/Top/StoneCech.v`.

- Discrete case (§V.6): apply the adjoint functor theorem (the §V.6 Theorem 2 issue) to the
  underlying-set functor of `CompHaus` (the §V.1 CompHaus issue) — which creates limits, so `CompHaus`
  is complete — with the double-power-set solution set Mac Lane describes, obtaining a left adjoint that
  sends a set to the Stone-Cech compactification of its discrete topology.
- General case (§V.8): apply the special adjoint functor theorem (the §V.8 characterization issue) to
  the inclusion `CompHaus ⟶ Top` (#259), with the unit interval as a cogenerator (Urysohn), obtaining
  the Stone-Cech compactification as a left adjoint, subsuming the discrete case.
- Injectivity (Exercise 4): for a completely regular space the universal arrow into its compactification
  is injective, by Urysohn's lemma in the point-separating form; note that the classical restriction to
  completely regular spaces is unnecessary at the level of universal arrows.

In-tree donors: #259's `Top`, the §V.1 CompHaus issue, the §V.6 Theorem 2 and §V.8 characterization
issues, `Construction/Reflective.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.6, book p. 125 (PDF p. 134); §V.8, book pp. 131–132 (PDF pp. 140–141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/StoneCech.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions StoneCech_discrete.
Print Assumptions StoneCech.
Print Assumptions StoneCech_unit_injective_completely_regular.
```
Reviewer: statements match Mac Lane §V.6 (book p. 125) and §V.8 (book pp. 131–132); the general
construction must go through SAFT with the interval cogenerator, and subsume the discrete case.

## Dependencies
Depends on: #259
Depends on: maclane:V.6:thm2
Depends on: maclane:V.8:thm2

<!-- catalog: {"ids":["maclane:V.6:construction-stone-cech-discrete","maclane:V.8:construction1","maclane:V.8:ex4"],"deps":["#259","maclane:V.6:thm2","maclane:V.8:thm2"]} -->
---8<---
```yaml
title: "MacLane V.9: The underlying-set functor of Top and its adjoint triple"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:construction1, maclane:V.9:ex2]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book pp. 132–135 (PDF pp. 141–144)
- Items: `maclane:V.9:construction1`, `maclane:V.9:ex2`

## Background
The underlying-set functor on spaces is faithful and sits in an adjoint triple: the discrete-topology
functor is its left adjoint and the indiscrete-topology functor its right adjoint, so it preserves both
limits and colimits; the indiscrete functor in turn has no right adjoint. See
[nLab: Top](https://ncatlab.org/nlab/show/Top) and
[nLab: adjoint triple](https://ncatlab.org/nlab/show/adjoint+triple).

## Current state in the library
Verified ABSENT (both). No category of spaces exists (`rg -i 'topolog'` → Grothendieck-topology prose
and background essays only; the instance layer has no `Top`), so the forgetful functor, its two
adjoints, and the discrete/indiscrete constructions cannot be named (`rg -i 'discrete topology|
indiscrete'` → comment-only hits). `Adjunction/Continuity.v:223` supplies the positive
left-adjoint-preserves-colimits direction that the "indiscrete functor has no right adjoint" exercise
contradicts, but no non-existence result is stated.

## Work to be done
Suggested module: `Instance/Top/Forgetful.v`, over #259's `Top`.

- Define the underlying-set functor `Top ⟶ Sets` and prove it faithful.
- Construct its left adjoint (the discrete-topology functor, all subsets open) and right adjoint (the
  indiscrete-topology functor, only the improper subsets open), proving both adjunctions; conclude the
  forgetful functor preserves all limits and all colimits.
- Exercise 2: the indiscrete functor has no right adjoint — exhibit its failure to preserve a coproduct
  (using the adjoint-obstruction idiom of the §V.5 non-existence issue).

In-tree donors: #259's `Top`, `Theory/Adjunction.v`, `Adjunction/Continuity.v`, the §V.5 non-existence
idiom.

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book pp. 132–135 (PDF pp. 141–144)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Forgetful.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Top_Forget.
Print Assumptions discrete_forget_indiscrete_triple.
Print Assumptions indiscrete_no_right_adjoint.
```
Reviewer: statements match Mac Lane §V.9 (book p. 132) and Exercise 2 (book p. 135); the adjoint triple
must be proved, and the non-existence exhibited on a concrete colimit.

## Dependencies
Depends on: #259

<!-- catalog: {"ids":["maclane:V.9:construction1","maclane:V.9:ex2"],"deps":["#259"]} -->
---8<---
```yaml
title: "MacLane V.9: Subspace and quotient topologies as sliced adjoint inverses"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:construction2, maclane:V.9:construction3, maclane:V.9:prop1]
deps_item_ids: [maclane:V.9:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book pp. 132–133 (PDF pp. 141–143)
- Items: `maclane:V.9:construction2`, `maclane:V.9:construction3`, `maclane:V.9:prop1`

## Background
The subspace topology is a right-adjoint-right-inverse to the underlying-set functor sliced over a
space, and the quotient topology a left-adjoint-right-inverse to it sliced under a space; from such
sliced inverses over a faithful functor with equalizers downstairs, one gets equalizers upstairs — the
element-free account of why the subspace topology is the right choice for equalizers in spaces. See
[nLab: Top](https://ncatlab.org/nlab/show/Top) and
[Wikipedia: Quotient space (topology)](https://en.wikipedia.org/wiki/Quotient_space_(topology)).

## Current state in the library
Verified ABSENT (all three). None of the vocabulary exists: `rg -i 'subspace|quotient topology|initial
topology|final topology'` → 0 hits, and `rg -i 'right-adjoint-right-inverse|RARI|LARI'` → 0 hits, so
the sliced-inverse notions have no in-tree name. Slices exist — `Construction/Slice.v:123` (`Slice`),
`:169` (`Coslice`) — but the only functors between slices in the tree are the base-change
`Bang_Functor` of `Construction/Slice/Pullback.v`, and there is no induced sliced functor from a
functor between the ambient categories (`rg 'Comma_Functor'` finds only Huq's section functor). `Top`
itself is absent (#259).

## Work to be done
Suggested module: `Instance/Top/Subspace.v` and `Structure/SlicedInverse.v` (the abstract Proposition).

- Define the sliced functor induced by the underlying-set functor over a fixed space
  (`(Top ↓ X) ⟶ (Sets ↓ GX)`), and its dual under a fixed space; introduce the
  right-adjoint-right-inverse and left-adjoint-right-inverse vocabulary (a functor with the named
  adjoint whose composite with it is the identity).
- Construct the subspace topology as the RARI (open sets are preimages of opens) and the quotient
  topology as the LARI (open sets are those with open preimage), proving the adjunction and the
  inverse identity in each case.
- Prove Proposition 1 abstractly: a faithful functor with equalizers in the codomain and sliced RARIs
  yields equalizers in the domain (built as the RARI of the downstairs equalizer), and note the dual
  (coequalizers from sliced LARIs) for the §V.9 cocompleteness issue.

In-tree donors: #259's `Top`, `Construction/Slice.v`, `Theory/Functor.v` (`Faithful`),
`Structure/Equalizer/Fork.v`, `Theory/Adjunction.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book pp. 132–133 (PDF pp. 141–143)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Subspace.v Structure/SlicedInverse.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions subspace_RARI.
Print Assumptions quotient_LARI.
Print Assumptions equalizers_from_sliced_RARI.
```
Reviewer: statements match Mac Lane §V.9 (book pp. 132–133) and Proposition 1; the universal property
must be over ARBITRARY spaces mapping in, not only subspaces.

## Dependencies
Depends on: #259
Depends on: maclane:V.9:construction1

<!-- catalog: {"ids":["maclane:V.9:construction2","maclane:V.9:construction3","maclane:V.9:prop1"],"deps":["#259","maclane:V.9:construction1"]} -->
---8<---
```yaml
title: "MacLane V.9: Top is complete and cocomplete"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:remark1, maclane:V.9:remark2, maclane:V.9:ex3]
deps_item_ids: [maclane:V.9:prop1, maclane:V.9:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book pp. 133–135 (PDF pp. 142–145)
- Items: `maclane:V.9:remark1`, `maclane:V.9:remark2`, `maclane:V.9:ex3`

## Background
The category of spaces is complete and cocomplete: products carry the initial (weakest) topology making
the projections continuous and equalizers the subspace topology, dually for colimits; the product
construction has a categorical formulation through cone-comma adjoints. See
[nLab: Top](https://ncatlab.org/nlab/show/Top) and
[nLab: complete category](https://ncatlab.org/nlab/show/complete+category).

## Current state in the library
Verified ABSENT (all three). With no `Top` in the tree (#259), "Top is complete" has no subject; the
initial-topology construction (`rg -i 'initial topology|weakest topology|product topology'` → 0 hits)
and the cone-comma formulation of products (Exercise 3) are absent. The general apparatus is present in
the abstract — `Structure/Complete.v`, `Structure/Equalizer/Fork.v`, `Structure/Limit/Product.v`,
`Instance/Cones/Comma.v:73` (`Cones_...` scaffolding) — but never applied to spaces.

## Work to be done
Suggested module: `Instance/Top/Complete.v`.

- Products in `Top`: the product of underlying sets with the initial topology for the projections;
  prove limiting. Equalizers: the subspace topology on the set-equalizer (the §V.9 sliced-inverse
  issue). Conclude `Complete Top` (Remark 1), via the products-and-equalizers theorem (the §V.2 issue)
  or directly.
- Colimits dually: coproducts as disjoint unions and coequalizers as quotient topologies, giving
  `Cocomplete Top` (Remark 2) by the dual of Proposition 1.
- Exercise 3: the categorical construction of products via cone-comma adjoints — for the forgetful
  functor and a discrete shape, a left adjoint to the induced functor on cone-comma categories puts the
  weakest topology making a family of maps continuous, transporting a terminal object of the downstairs
  cone-comma to a limit upstairs; conclude that `Top` has all products.

In-tree donors: #259's `Top`, the §V.9 sliced-inverse issue, `Structure/Limit/Product.v`,
`Instance/Cones/Comma.v`, the §V.2 products-and-equalizers issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book pp. 133–135 (PDF pp. 142–145)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Complete.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Top_Complete.
Print Assumptions Top_Cocomplete.
Print Assumptions Top_products_via_cone_comma.
```
Reviewer: statements match Mac Lane §V.9 Remarks and Exercise 3 (book pp. 133–135); products must carry
the initial topology and equalizers the subspace topology.

## Dependencies
Depends on: #259
Depends on: maclane:V.9:prop1
Depends on: maclane:V.9:construction1

<!-- catalog: {"ids":["maclane:V.9:remark1","maclane:V.9:remark2","maclane:V.9:ex3"],"deps":["#259","maclane:V.9:prop1","maclane:V.9:construction1"]} -->
---8<---
```yaml
title: "MacLane V.9: Collapsing a subset and the category of pairs"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:construction5, maclane:V.9:construction6]
deps_item_ids: [maclane:V.9:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book p. 134 (PDF pp. 143–144)
- Items: `maclane:V.9:construction5`, `maclane:V.9:construction6`

## Background
Collapsing a subset of a space to a point is a coequalizer of the family of point-inclusions, and the
resulting quotient functor from the category of space-subset pairs is left adjoint to the functor
sending a pointed space to its underlying pair — the homotopy-theoretic quotient as an adjunction. See
[Wikipedia: Quotient space (topology)](https://en.wikipedia.org/wiki/Quotient_space_(topology)) and
[nLab: Top](https://ncatlab.org/nlab/show/Top).

## Current state in the library
Verified ABSENT (both). With no `Top` (#259) there is no space to collapse; `rg -i 'collapse|quotient
by'` finds only coherence/comonad prose, and the "wide coequalizer of a family" needed for the
collapse is not in-tree (`Structure/Coequalizer.v:52,68` give only the binary parallel-pair notion;
`rg 'coequalizer of a family'` → a lone prose hit at `Theory/WeaklyInitial.v:39`). The category of
pairs and the pointed-space category are also absent (`Instance/Fun.v:230`'s `Pointed` is a POINTED
ENDOFUNCTOR notion, unrelated).

## Work to be done
Suggested module: `Instance/Top/Quotient.v`.

- Introduce wide coequalizers (coequalizers of a family of parallel arrows with common domain and
  codomain), dualizing the wide-pullback vocabulary; a modest addition to
  `Structure/Coequalizer.v`.
- Construction 5: `X/A`, the space obtained by collapsing a subset to a point, as the wide coequalizer
  of the family of point-inclusions of `A`; prove the universal property.
- Construction 6: the category of pairs (a space with a chosen subset, arrows the maps carrying subset
  into subset) and the pointed-space category; prove the quotient functor `⟨X,A⟩ ↦ X/A` left adjoint to
  the functor sending a pointed space to its underlying pair.

In-tree donors: #259's `Top`, the §V.9 Top-cocompleteness issue (for the quotient/coequalizer topology),
`Structure/Coequalizer.v`, `Theory/Adjunction.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book p. 134 (PDF pp. 143–144)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Quotient.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions collapse_coequalizer.
Print Assumptions pairs_quotient_adjunction.
```
Reviewer: statements match Mac Lane §V.9 (book p. 134); `X/A` must be the coequalizer of the
point-inclusion family, and the adjunction to the pointed-space embedding proved.

## Dependencies
Depends on: #259
Depends on: maclane:V.9:construction1

<!-- catalog: {"ids":["maclane:V.9:construction5","maclane:V.9:construction6"],"deps":["#259","maclane:V.9:construction1"]} -->
---8<---
```yaml
title: "MacLane V.9: Gluing along an open cover and the sheaf condition"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:construction4]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book p. 134 (PDF p. 143)
- Items: `maclane:V.9:construction4`

## Background
Continuous maps out of a space glue along an open cover: the restriction diagram over a cover is an
equalizer of hom-sets for every target, equivalently the space is the colimit of the cover diagram of
opens and their pairwise intersections — the sheaf condition satisfied by the representables. See
[nLab: sheaf](https://ncatlab.org/nlab/show/sheaf) and [nLab: Top](https://ncatlab.org/nlab/show/Top).

## Current state in the library
Verified PARTIAL. The abstract gluing predicate exists — `Theory/Sheaf.v:192` (`Sheaf`) over
`Theory/Sheaf.v:159` (`Site`) and the sheaf category `Theory/Sheaf/Category.v:81` — but its scope note
(`:33`) discloses the inherited predicate is per-leg and vacuous beyond subsingleton fibres. Missing:
any category of spaces (#259); the site of opens of a space with covers by open covers; the equalizer
formulation `F(X) → ∏ F(U_i) ⇉ ∏ F(U_i ∩ U_j)` (never formed; `IsEqualizer` never applied to a
restriction fork); the statement that the representable `Top(−, Y)` satisfies it; and the colimit half
— the two-level index category of singletons and pairs, the diagram of opens and intersections, and
that the space is its colimit.

## Work to be done
Suggested module: `Instance/Top/Cover.v`.

- Over #259's `Top`, build the poset/site of open subsets of a space with covering families the open
  covers, and the restriction diagram of a presheaf over a cover.
- Prove the equalizer formulation: for every target `Y`, the fork `Top(X, Y) → ∏ Top(U_i, Y) ⇉
  ∏ Top(U_i ∩ U_j, Y)` of restrictions is an equalizer in `Sets` — i.e. the representable `Top(−, Y)`
  satisfies the gluing condition — using the honest matching-family sheaf condition (strengthening
  `Theory/Sheaf.v` per its scope note where necessary).
- Prove the colimit half: the two-level index category of the cover (objects the indices and the index
  pairs, arrows the two inclusions), the diagram of opens and intersections, and that `X` with the
  inclusion cocone is its colimit.

In-tree donors: #259's `Top`, `Theory/Sheaf.v`, `Theory/Sheaf/Category.v`, `Structure/Equalizer/Fork.v`,
`Structure/Limit.v` (colimits).

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book p. 134 (PDF p. 143)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Cover.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions cover_restriction_equalizer.
Print Assumptions representable_satisfies_gluing.
Print Assumptions space_is_colimit_of_cover.
```
Reviewer: statement matches Mac Lane §V.9 (book p. 134); both the equalizer and the colimit
formulations must be proved, and the representable shown to satisfy the gluing condition.

## Dependencies
Depends on: #259

<!-- catalog: {"ids":["maclane:V.9:construction4"],"deps":["#259"]} -->
---8<---
```yaml
title: "MacLane V.9: Hausdorff spaces, reflection, and the separation axioms"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.9:prop2, maclane:V.9:ex4, maclane:V.9:ex5]
deps_item_ids: [maclane:V.6:thm2]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book pp. 135–136 (PDF pp. 144–145)
- Items: `maclane:V.9:prop2`, `maclane:V.9:ex4`, `maclane:V.9:ex5`

## Background
Hausdorff spaces form a complete and cocomplete reflective subcategory of all spaces — the reflector is
the largest Hausdorff quotient — and the inclusions between successive separation-axiom subcategories
each have a left adjoint, while the inclusion of Hausdorff spaces has no right adjoint. See
[Wikipedia: Separation axiom](https://en.wikipedia.org/wiki/Separation_axiom) and
[nLab: Hausdorff space](https://ncatlab.org/nlab/show/Hausdorff+space).

## Current state in the library
Verified ABSENT (all three). With no `Top` (#259) there is no `Haus` and no separation-axiom
subcategories (`rg -i 'hausdorff|separation axiom|regular space|normal space'` → bibliographic prose
only). The general reflective-subcategory vocabulary exists (`Construction/Reflective.v:60`) and the
adjoint functor theorem is in-tree, but neither is applied to spaces, and no non-existence-of-adjoint
result exists for the Hausdorff inclusion.

## Work to be done
Suggested module: `Instance/Top/Hausdorff.v`, over #259's `Top`.

- Define the separation-axiom full subcategories (at least T0 through T2/Hausdorff) of `Top`.
- Proposition 2: `Haus` is complete and cocomplete, and the inclusion `Haus ⟶ Top` has a left adjoint
  (the largest Hausdorff quotient) — construct it via the adjoint functor theorem (the §V.6 Theorem 2
  issue), with the solution set the small set of Hausdorff surjective quotients; also give the left
  adjoint of `Haus ⟶ Sets`. Conclude colimits in `Haus` from the reflector (a left adjoint), with the
  coequalizer the largest Hausdorff quotient of the `Top`-coequalizer.
- Exercise 4: each inclusion between successive separation-axiom subcategories has a left adjoint
  (reflection), by the same AFT argument.
- Exercise 5: the inclusion `Haus ⟶ Top` has no right adjoint (a `Top`-coequalizer of Hausdorff spaces
  need not be Hausdorff), and neither does `Haus ⟶ Sets`.

In-tree donors: #259's `Top`, `Construction/Reflective.v`, the §V.6 Theorem 2 issue, the §V.5
non-existence idiom, the §V.9 Top-completeness issue.

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book pp. 135–136 (PDF pp. 144–145)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Hausdorff.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Haus_reflective.
Print Assumptions separation_axiom_reflections.
Print Assumptions Haus_inclusion_no_right_adjoint.
```
Reviewer: statements match Mac Lane §V.9 Proposition 2 and Exercises 4–5 (book pp. 135–136); the
reflector must be produced via the AFT, and the non-existence exhibited on a concrete coequalizer.

## Dependencies
Depends on: #259
Depends on: maclane:V.6:thm2

<!-- catalog: {"ids":["maclane:V.9:prop2","maclane:V.9:ex4","maclane:V.9:ex5"],"deps":["#259","maclane:V.6:thm2"]} -->
---8<---
```yaml
title: "MacLane V.9: The connected-components functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:V.9:ex1]
deps_item_ids: [maclane:V.9:construction1]
deps_pending: []
```

## Source
- Book: Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5)
- Section: §V.9, book p. 135 (PDF p. 144)
- Items: `maclane:V.9:ex1`

## Background
On locally connected spaces the connected-components functor is left adjoint to the discrete-space
functor, but it has no left adjoint of its own because it fails to preserve equalizers. See
[Wikipedia: Locally connected space](https://en.wikipedia.org/wiki/Locally_connected_space) and
[nLab: Top](https://ncatlab.org/nlab/show/Top).

## Current state in the library
Verified ABSENT. There is no `Top` and no locally-connected subcategory (#259); `rg -i 'connected'`
finds a genuine mathematical use only in `Instance/FinSet/Pushout.v` (a union-find connected-components
computation for finite sets), and `rg -i 'π₀|components functor|locally connected'` → 0 hits. The
discrete-space functor of the exercise does not exist (it is the left adjoint of the §V.9 forgetful
issue).

## Work to be done
Suggested module: `Instance/Top/Components.v`.

- Define local connectedness and the full subcategory of locally connected spaces in `Top` (#259).
- Construct the connected-components functor to `Sets` and prove it left adjoint to the discrete-space
  functor (the left adjoint of the §V.9 forgetful issue restricted to locally connected spaces).
- Prove it has no left adjoint of its own, by exhibiting an equalizer it fails to preserve (using the
  adjoint-obstruction idiom of the §V.5 non-existence issue).

In-tree donors: #259's `Top`, the §V.9 forgetful issue, the §V.5 non-existence idiom,
`Instance/FinSet/Pushout.v` (connected-components computation, as a proof-pattern reference).

## Definition of Done
- [ ] Statement fidelity to the book (§V.9, book p. 135 (PDF p. 144)); setoid discipline — `≈` on morphisms, never `=`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Components.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions components_functor.
Print Assumptions components_left_adjoint_discrete.
Print Assumptions components_no_left_adjoint.
```
Reviewer: statement matches Mac Lane §V.9 Exercise 1 (book p. 135); the adjunction must be proved and
the failure of a left adjoint exhibited on a concrete equalizer.

## Dependencies
Depends on: #259
Depends on: maclane:V.9:construction1

<!-- catalog: {"ids":["maclane:V.9:ex1"],"deps":["#259","maclane:V.9:construction1"]} -->

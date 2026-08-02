```yaml
title: "Riehl 3.1: Essential uniqueness of limits and colimits"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.1:prop7]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.1, printed p. 84 (PDF p. 104)
- Items: `riehl:3.1:prop7`

## Background
Any two limit cones over a common diagram are related by a unique isomorphism of apexes commuting
with the legs, because both are terminal objects of the category of cones and terminal objects form a
contractible groupoid; the apex may still have non-trivial automorphisms, but only the identity
commutes with a fixed limit cone. See [nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified PARTIAL. **Phase D overturned the Phase-C reading of PRESENT**: the classifier had recorded
this as present "by instantiation rather than as a stand-alone limit theorem", and the verifier
established that the instantiation is never performed, so under the campaign's frozen definitions
this is a gap and not a presentation difference.

- `Structure/UniversalProperty.v:175` (`univ_property_unique_up_to_unique_iso`) is the generic
  representability theorem, and `Structure/UniversalProperty/Limit.v:141`
  (`LimitIsUniversalProperty`) certifies that "is a limit of `F` at `c`" is such a property — but the
  verifier enumerated every occurrence of the former and found exactly two: its definition site and a
  header mention in `Theory/Isomorphism.v:80`. The composite is never formed, so no term of the shape
  `IsALimit F c → IsALimit F d → ∃! iso c ≅ d` exists anywhere.
- The verifier further enumerated every `Lemma`/`Theorem`/`Definition` in `Structure/Limit.v`,
  `Structure/Limit/Preservation.v`, `Structure/Cone.v`, `Instance/Cones.v`,
  `Instance/Cones/Limit.v` and `Structure/UniversalProperty/Limit.v`, and grepped every file that
  mentions both `≅` and `IsALimit`/`limit_cone`: nothing states that two limits of a common diagram
  are isomorphic.
- Riehl's clause "commuting with the legs of the two limit cones" is **not** available even on the
  generic route: the transport in `Structure/UniversalProperty.v:159`
  (`univ_property_respects_iso`) is defined through the Yoneda round trip, and no lemma identifies
  that transport with precomposing the limit legs by the isomorphism.
- The accompanying remark — the only endomorphism of the apex commuting with a fixed limit cone is
  the identity — is unstated; it is one line from `Structure/Limit/Preservation.v:82`
  (`limit_med_unique`).
- The two shape-specific results that do exist are hand-rolled and strictly weaker:
  `Structure/Equalizer/Fork.v:106` (`equalizer_unique`) and `Structure/Pullback.v:182`
  (`pullback_unique`) each conclude a bare `≅` with no uniqueness clause and no commutation with the
  legs/projections.
- The colimit dual is likewise unstated.

## Work to be done
Suggested module: `Structure/Limit/Unique.v`.

1. Prove the leg-level statement directly from `limit_med`/`limit_med_commutes`/`limit_med_unique`
   (`Structure/Limit/Preservation.v:74-82`) rather than through the Yoneda round trip: given
   `IsALimit F c` and `IsALimit F d` with their cones, build the mutually inverse mediators, prove
   each composite is the identity by `limit_med_unique`, and package the result as an
   `Isomorphism c d` **together with** the equations `leg_d x ∘ to ≈ leg_c x` and
   `leg_c x ∘ from ≈ leg_d x` for every index `x`.
2. Prove the uniqueness clause: any morphism commuting with the two families of legs equals that
   isomorphism (again `limit_med_unique`), and derive the remark's corollary — an endomorphism of the
   apex commuting with a fixed limit cone is the identity.
3. Give the colimit dual. `Colimit F := Limit (F^op)` (`Structure/Limit.v:158`) with the covariant
   accessors `colimit_inj`/`colimit_med`/`colimit_med_unique` of
   `Structure/Limit/Preservation.v:135-152`, so the dual should be a short covariant re-reading, not
   a second proof.
4. Reconcile with the generic route: prove that the new isomorphism agrees with the one produced by
   `univ_property_unique_up_to_unique_iso` at `LimitIsUniversalProperty`, so the two developments stop
   being unrelated, and retire the hand-rolled `equalizer_unique` / `pullback_unique` in favour of
   instances of the general result (or prove them equal to it).

In-tree donors: `Structure/Limit.v`, `Structure/Limit/Preservation.v`, `Structure/Cone.v`,
`Structure/UniversalProperty.v`, `Structure/UniversalProperty/Limit.v`, `Instance/Cones/Limit.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.1, printed p. 84 (PDF p. 104)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The isomorphism carries the leg-commutation equations, not merely a bare `≅`
- [ ] The uniqueness clause is proved (a morphism commuting with both leg families is that isomorphism), and the automorphism corollary is stated
- [ ] The colimit dual is stated and proved
- [ ] `equalizer_unique` (`Structure/Equalizer/Fork.v:106`) and `pullback_unique` (`Structure/Pullback.v:182`) are derived from, or proved to agree with, the general result
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Unique.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions limit_unique_iso.
Print Assumptions limit_unique_iso_legs.
Print Assumptions colimit_unique_iso.
```
Reviewer: statement matches Riehl §3.1 Proposition 3.1.7 (printed p. 84) — the isomorphism must be
shown unique *among morphisms commuting with the legs*, which is the whole content; a bare `≅` does
not close this issue.

## Dependencies
None.

<!-- catalog: {"ids":["riehl:3.1:prop7"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 3.1: The fiber of a morphism over a global element"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.1:eq17]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.1, printed p. 87 (PDF p. 107), numbered display (3.1.17)
- Items: `riehl:3.1:eq17`

## Background
In a category with a terminal object, the fiber of a morphism over a global element is the pullback of
that morphism along the element; it is the categorical rendering of the preimage of a point, and it is
the notion the theory of bundles and fiber spaces is phrased in. See
[nLab: fiber](https://ncatlab.org/nlab/show/fiber) and
[nLab: generalized element](https://ncatlab.org/nlab/show/generalized+element).

## Current state in the library
Verified PARTIAL. The ambient pullback machinery is fully in force and the library even *uses* a
pullback along a global element without naming the construction:

- `Structure/Pullback.v:161` (`Pullback` with `ump_pullbacks`) and `:215` (`Class HasPullbacks`) give
  the general pullback with its unique-mediator universal property; `Structure/Terminal.v` gives the
  terminal object, and `Structure/Terminal.v:60-61` and `Structure/Constant.v:12-15` already carry
  the global-element vocabulary `1 ~> x` in prose.
- `Structure/SubobjectClassifier.v:52` (`char_pullback : IsPullback (char m M) truth u m one`, with
  `truth : 1 ~> Ω` at `:46`) is a genuine in-tree pullback along a global element — the classifying
  square — so the pattern is in use but unabstracted.
- Missing: any definition, notation or lemma for the fiber `B_a` of `f : B ~> A` over `a : 1 ~> A`. A
  user must instantiate `HasPullbacks` at the cospan `(f, a)` by hand; no in-tree constant
  abbreviates that, and no property of fibers is stated in fiber vocabulary. The verifier confirmed
  the negative: every `fiber`/`fibre` hit in the tree (21 files) belongs to the
  fibration/displayed/Grothendieck development, a different notion.

## Work to be done
Suggested module: `Structure/Pullback/Fiber.v`.

1. Define `fiber` for `f : b ~> a` and a global element `x : 1 ~> a` in a category with a terminal
   object and pullbacks: the apex of `pullback f x`, with the projection `fiber f x ~> b` and the
   canonical map `fiber f x ~> 1`. Provide a scoped notation (Riehl writes `B_a`).
2. State the universal property in fiber form: a morphism `z ~> fiber f x` is exactly a morphism
   `h : z ~> b` with `f ∘ h ≈ x ∘ one`, uniquely. This is `ump_pullbacks` specialized, but it is the
   form every downstream consumer wants.
3. Prove the two facts Riehl's surrounding prose uses:
   (a) the projection `fiber f x ~> b` is monic whenever `f` is monic — an instance of
       `Theory/Morphisms/Stability.v`'s pullback-stability of monos, so a one-liner;
   (b) functoriality of the fiber in the global element along an isomorphism of the base, via
       `Theory/Morphisms/Stability.v:329` (`pullback_transport`).
4. Record `char_pullback` (`Structure/SubobjectClassifier.v:52`) as an instance of the new
   vocabulary, so the classifying square is visibly "the fiber of a mono over `truth`".

In-tree donors: `Structure/Pullback.v`, `Structure/Terminal.v`, `Structure/Constant.v`,
`Theory/Morphisms/Stability.v`, `Structure/SubobjectClassifier.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.1, printed p. 87 (PDF p. 107), display (3.1.17)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The fiber notation and the fiber-form universal property are provided (not only the raw pullback)
- [ ] Pullback-stability of monos is instantiated for fibers
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Pullback/Fiber.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions fiber.
Print Assumptions fiber_ump.
Print Assumptions fiber_proj_monic.
```
Reviewer: statement matches Riehl §3.1 display (3.1.17) (printed p. 87) — the fiber is the pullback
along a *global element*, not along an arbitrary morphism.

## Dependencies
None.

<!-- catalog: {"ids":["riehl:3.1:eq17"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 3.1: The least common multiple as a pullback in Ab, and the sign ambiguity of its cone"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.1:example19, riehl:3.1:exviii]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.1, printed pp. 87–88 and p. 92 (PDF pp. 107–108 and p. 112), including numbered display (3.1.20)
- Items: `riehl:3.1:example19`, `riehl:3.1:exviii`

## Background
Because the integers represent the underlying-set functor on abelian groups, endomorphisms of `ℤ`
are integers, and the pullback of two multiplication maps computes their least common multiple; the
exercise then observes that negating both legs gives another cone with the same universal property,
which is not a defect but exactly the essential uniqueness of limits. See
[nLab: pullback](https://ncatlab.org/nlab/show/pullback) and
[Wikipedia: Least common multiple](https://en.wikipedia.org/wiki/Least_common_multiple).

## Current state in the library
Verified ABSENT (the example) and PARTIAL (the exercise).

- There is no category of abelian groups: the only algebraic concrete instance is
  `Instance/CMon.v` (commutative monoids over setoids), and `Structure/Group.v:109`
  (`GroupObject`) is a group *object* internal to a cartesian monoidal category, not `Ab`. A
  whole-tree search for `lcm`/`gcd`/`divisib`/`least common multiple` returns 0 hits, so display
  (3.1.20) has no in-tree counterpart at all.
- The exercise's *general principle* is present in full and at exactly the pullback level:
  `Structure/SubobjectClassifier.v:108` (`is_pullback_precompose_iso` — precomposing a pullback's
  projections with an isomorphism of the apex again yields a pullback),
  `Theory/Morphisms/Stability.v:329` (`pullback_transport` — any two pullbacks of one cospan are
  related by an isomorphism commuting with both projections) and
  `Structure/UniversalProperty.v:163` (`univ_property_respects_iso`). The verifier performed an
  adversarial check on the first: although it is declared inside a section whose `Context` carries
  `Terminal`, `HasPullbacks` and even `SubobjectClassifier`, its statement and proof mention none of
  them, so Coq discharges only `C` and the exported lemma is as general as quoted — there is no
  hidden topos hypothesis.
- What is missing is the concrete object the exercise turns on: an ambient category carrying a
  non-identity isomorphism `a ≅ −a`, so that the "unique" pullback apex genuinely has distinct
  representatives.

## Work to be done
Suggested module: `Instance/Ab/Lcm.v` (over the `Ab` instance of #256).

1. Over `Ab`, prove that `ℤ` represents the underlying-set functor and hence that
   `Ab(ℤ, ℤ) ≅ ℤ` as a set, identifying the endomorphism `n · (−)` with the integer `n`.
2. Construct the pullback of `ℤ --m--> ℤ <--n-- ℤ` for `m, n` not both zero: the subgroup of pairs
   `(x, y)` with `n·x = m·y`, show it isomorphic to `ℤ`, and identify the legs `(a, b)` of the
   pullback cone as the unique pair with `m·a = n·b = lcm(m, n)`. Prove the lcm characterization
   itself (least among common multiples) rather than asserting it.
3. Exercise 3.1.viii: show `(−a, −b)` also satisfies the universal property, by instantiating
   `is_pullback_precompose_iso` (`Structure/SubobjectClassifier.v:108`) at the negation automorphism
   of `ℤ`; and explain the non-ambiguity by `pullback_transport`
   (`Theory/Morphisms/Stability.v:329`) — the pullback is well defined up to a canonical isomorphism
   commuting with both projections, which is precisely what the two sign choices exhibit. Keep this
   as a *proof*, not a comment: the deliverable is a term of the form
   `IsPullback p₁ p₂ … → IsPullback (neg ∘ p₁) (neg ∘ p₂) …` plus the transport relating them.
4. If the essential-uniqueness result of `riehl:3.1:prop7` has landed by then, phrase step 3 through
   it rather than re-deriving the transport.

In-tree donors: `Structure/Pullback.v`, `Theory/Morphisms/Stability.v`,
`Structure/SubobjectClassifier.v` (`is_pullback_precompose_iso`), `Structure/UniversalProperty.v`,
`Instance/CMon.v` (the setoid-algebra pattern to imitate for `Ab`).

## Definition of Done
- [ ] Statement fidelity to the book (§3.1, printed pp. 87–88, 92 (PDF pp. 107–108, 112)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The pullback apex is proved isomorphic to `ℤ` and its legs identified with the lcm, with the lcm's own least-common-multiple property proved
- [ ] The sign-ambiguity half is a proved term (both `(a,b)` and `(−a,−b)` satisfy the UMP) plus the transport explaining why the pullback is still well defined
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond those `Instance/` layers already use per docs/AXIOMS.md
- [ ] `Print Assumptions` closed (or the axiom use documented against docs/AXIOMS.md) for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Ab/Lcm.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Ab_lcm_pullback.
Print Assumptions Ab_lcm_pullback_sign.
```
Reviewer: statements match Riehl §3.1 Example 3.1.19 with display (3.1.20) (printed pp. 87–88) and
Exercise 3.1.viii (printed p. 92); the "why this is not ill-defined" half must be a transport lemma,
not prose.

## Dependencies
Depends on: #256

<!-- catalog: {"ids":["riehl:3.1:example19","riehl:3.1:exviii"],"deps":["#256"]} -->

---8<---

```yaml
title: "Riehl 3.1: Concrete limits and colimits in Top — the fiber of the exponential covering map, and the wedge of circles and the torus as pushouts"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.1:example18, riehl:3.1:example24]
deps_item_ids: [riehl:3.1:eq17]
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.1, printed p. 87 and p. 89 (PDF p. 107 and p. 109)
- Items: `riehl:3.1:example18`, `riehl:3.1:example24`

## Background
Two standard computations that exhibit limits and colimits of spaces: the fiber of the exponential
covering map of the circle over the basepoint is the discrete space of integers, and the figure eight
and the torus are pushouts in `Top` — the figure eight of a span of circles under a point, the torus
by attaching a disk along the commutator loop. See
[nLab: covering space](https://ncatlab.org/nlab/show/covering+space),
[nLab: pushout](https://ncatlab.org/nlab/show/pushout) and
[Wikipedia: Wedge sum](https://en.wikipedia.org/wiki/Wedge_sum).

## Current state in the library
Verified ABSENT (both), independently reproduced by the Phase-D verifier.

- There is no category of topological spaces. `ls Instance/` yields Adj, Adjoints, AST, Cat, CMon,
  Comp, Cones, Coq, Discrete, Ens, Fact, FinSet, Fun, Lambda, Omega, One, Parallel, Poset, Props,
  Proset, Rel, Roof, Sets, Shapes, StrictCat, Two, Zero, ZX — no `Top`; and every
  `topological`/`continuous map` hit is background-essay prose. There is no `ℝ`, no `S¹`, no disk, no
  covering map, no torus.
- The generic pushout machinery *is* available (`Structure/Pushout.v`, plus the concrete
  `Instance/Sets/Pushout.v:185` and `Instance/FinSet/Pushout.v:513`), so what is missing is
  exclusively the spaces to apply it to.
- Disambiguation the verifier asks to be preserved in the issue: `Structure/Wedge.v` is the
  (co)end wedge / dinaturality notion and has **nothing** to do with the topological wedge sum; do
  not reuse the name.
- The follow-on prose of Example 3.1.18 (pullback-stability of monomorphisms) is *not* part of this
  gap — it is in-tree at `Theory/Morphisms/Stability.v` and is recorded separately under Riehl
  Exercise 3.1.v, which is PRESENT.

## Work to be done
Suggested module: `Instance/Top/Examples.v`, over the `Top` instance of #259 and the
(co)completeness work of #458.

1. Build the minimum point-set apparatus these two examples need: the real line with its standard
   topology, the circle as the quotient `ℝ/ℤ` (or as the subspace of `ℂ`, whichever the `Top`
   instance makes cheapest), the closed disk, and the exponential map `ρ : ℝ → S¹`. Disclose in the
   header whichever construction of `ℝ` the library adopts and its axiom footprint against
   docs/AXIOMS.md — this is an `Instance/` layer, so stdlib axioms are permitted but must be
   enumerated.
2. Example 3.1.18: prove the fiber of `ρ` over the basepoint — the pullback of `ρ` along the global
   element `1 : * → S¹`, in the fiber vocabulary of `riehl:3.1:eq17` — is the discrete subspace `ℤ`
   of `ℝ`, i.e. exhibit the pullback square and prove its universal property.
3. Example 3.1.24: prove `S¹ ∨ S¹` is the pushout of the span `S¹ ← * → S¹` in unbased spaces, and
   that it is the binary coproduct of `S¹` with itself in based spaces; then present the torus as the
   pushout of `D² ← S¹ → S¹ ∨ S¹` along the boundary inclusion and the commutator attaching map, and
   prove it homeomorphic to `S¹ × S¹`. If the homeomorphism proof is out of reach, state the pushout
   square as the *definition* of the torus and disclose the missing identification in the file
   header rather than admitting it.
4. Name the wedge sum something that does not collide with `Structure/Wedge.v`.

In-tree donors: #259's `Top`, #458's (co)completeness of `Top`, `Structure/Pushout.v`,
`Structure/Pullback.v`, the fiber vocabulary of `riehl:3.1:eq17`, `Instance/Sets/Pushout.v` (the
quotient-by-a-generated-equivalence pattern).

## Definition of Done
- [ ] Statement fidelity to the book (§3.1, printed pp. 87, 89 (PDF pp. 107, 109)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The fiber of `ρ` is proved to be the *discrete* space `ℤ`, not merely the underlying set
- [ ] Both pushout squares are proved (universal property), not asserted
- [ ] The wedge-sum construction does not collide with the (co)end `Structure/Wedge.v`
- [ ] Any use of a stdlib axiom (e.g. for `ℝ`) is enumerated in the file header and reconciled with docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory sense
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Examples.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions exp_fiber_discrete.
Print Assumptions figure_eight_pushout.
Print Assumptions torus_pushout.
```
Reviewer: statements match Riehl §3.1 Examples 3.1.18 and 3.1.24 (printed pp. 87, 89); check that the
attaching map really is the commutator loop and that the fiber statement is about the *space*, not
the underlying set.

## Dependencies
Depends on: #259
Depends on: #458
Depends on: riehl:3.1:eq17

<!-- catalog: {"ids":["riehl:3.1:example18","riehl:3.1:example24"],"deps":["#259","#458","riehl:3.1:eq17"]} -->

---8<---

```yaml
title: "Riehl 3.2/3.3/3.6: Limits and colimits of G-sets — fixed points, orbits, and objectwise versus natural isomorphism"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.2:example10, riehl:3.3:example4, riehl:3.6:exi]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.2, printed p. 95 (PDF p. 115); §3.3, printed p. 100 (PDF p. 120); §3.6, printed p. 121 (PDF p. 141)
- Items: `riehl:3.2:example10`, `riehl:3.3:example4`, `riehl:3.6:exi`

## Background
A left `G`-set is a functor from the delooping `BG` into sets; the limit of that functor is the set of
`G`-fixed points and the colimit is the set of orbits. The pair also supplies the standard
counterexample separating objectwise isomorphism from natural isomorphism of diagrams. See
[nLab: action](https://ncatlab.org/nlab/show/action) and
[nLab: delooping](https://ncatlab.org/nlab/show/delooping).

## Current state in the library
Verified ABSENT (all three), independently reproduced by the Phase-D verifier.

- **No delooping exists.** `delooping` occurs only in `Theory/Bicategory.v` and
  `Theory/Bicategory/OneObject.v`, and there it deloops a *monoidal category* into a one-object
  *bicategory* — one level up, a different construction. `Structure/Group.v:109` (`GroupObject`) is
  an internal group object with no action and no invariants. `Construction/Groupoid.v` is the core
  groupoid of a category, not `BG`. So the diagram `X : BG ⟶ Set` cannot be written.
- **No orbit or equivariance vocabulary.** `rg -i 'orbit'` → 0 hits; every `equivariant` hit is the
  symmetric-group action on multicategory arities (`Theory/Multicategory/Endomorphism.v:796,853,889`,
  `Theory/Multicategory/Representable.v:687`); every `fixed point` hit is an idempotent fixed point
  (`Instance/Sets/Karoubi.v`) or an endofunctor fixed point (`Theory/Lambek.v`,
  `Theory/Recursion.v`).
- **No (co)limits in `Sets` to compute with.** `rg -n 'Colimit|HasColimits|Cocomplete' Instance/` → 0
  hits, and there is no `Complete Sets`; the concrete colimit-shaped constructions that do exist
  (`Instance/Sets/Pushout.v`, `Instance/Sets/Coend.v`) go through their own universal properties and
  are never phrased as `Colimit`.

## Work to be done
Suggested module: `Instance/GSet/Limit.v`, over the delooping of #220 and the `G`-action categories
of #278.

1. With `BG` from #220 and `[BG, Sets]` from #278, prove **Example 3.2.10**: for `X : BG ⟶ Sets`,
   the limit of `X` is the fixed-point sub-setoid `{x | ∀ g, g · x ≈ x}` with the evident leg, i.e.
   construct the cone and discharge `IsALimit`. Use the `Sets` cone-set limit of #407 to identify the
   apex, or build the sub-setoid directly (funext-free, in the style of `Instance/Sets/End.v:59`).
2. Prove **Exercise 3.6.i** dually: the colimit of `X : BG ⟶ Sets` is the orbit setoid — the quotient
   of the carrier by the equivalence relation generated by `x ∼ g · x` — with the quotient map as the
   colimit injection. The inductive setoid-quotient technique of `Instance/Sets/Coend.v:69-93`
   (`coend_sum`/`coend_eq`/`coend_apex_setoid`) is the right donor; it is the same
   quotient-by-a-generated-relation pattern.
3. Prove **Example 3.3.4**: two `G`-sets are objectwise isomorphic exactly when their carriers are
   isomorphic, and naturally isomorphic exactly when there is a `G`-equivariant bijection; then build
   the `ℤ/2` witness — the two-element set with the trivial action and the two-element set with the
   swap action — and *compute* all four (co)limits from steps 1–2: the fixed points are `2` and `∅`,
   the orbits are `2` and `1`. Conclude that objectwise isomorphism does not suffice in Riehl's
   Corollary 3.3.3 (filed as #353's transport result).
4. Keep the `ℤ/2` witness decidable and axiom-free so its four (co)limit computations can be checked
   by `vm_compute`/`eq_refl` where possible, in the spirit of `Instance/FinSet/Topos.v`'s sanity
   examples.

In-tree donors: #220 (`BG`), #278 (`[BG, Sets]` and equivariant maps), #407 (`Sets` completeness),
#329 (`Sets` cocompleteness), `Instance/Sets/Coend.v`, `Instance/Sets/End.v`, `Structure/Limit.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.2 printed p. 95, §3.3 printed p. 100, §3.6 printed p. 121 (PDF pp. 115, 120, 141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `lim X ≅ X^G` and `colim X ≅ X/G` are both proved as genuine `Limit`/`Colimit` witnesses, not as bare bijections
- [ ] The objectwise-versus-natural distinction is stated as an iff, and the `ℤ/2` counterexample is exhibited with all four (co)limits computed
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond those the `Instance/` layer already uses per docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/GSet/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions gset_limit_fixed_points.
Print Assumptions gset_colimit_orbits.
Print Assumptions gset_objectwise_not_natural.
```
Reviewer: statements match Riehl §3.2 Example 3.2.10, §3.3 Example 3.3.4 and §3.6 Exercise 3.6.i; the
counterexample must actually compute the four (co)limits, not merely assert them.

## Dependencies
Depends on: #220
Depends on: #278
Depends on: #407
Depends on: #329

<!-- catalog: {"ids":["riehl:3.2:example10","riehl:3.3:example4","riehl:3.6:exi"],"deps":["#220","#278","#407","#329"]} -->

---8<---

```yaml
title: "Riehl 3.3: Associativity of binary products up to unique natural isomorphism, and a chosen product whose associator is not the identity"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.3:lem6, riehl:3.3:exii, riehl:3.3:example7]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.3, printed pp. 101–102 (PDF pp. 121–122)
- Items: `riehl:3.3:lem6`, `riehl:3.3:exii`, `riehl:3.3:example7`

## Background
In a category with binary products there is a *unique* natural isomorphism between the two bracketings
of a triple product commuting with the three projections; uniqueness is what makes iterated binary
products a legitimate definition of the n-ary product. Isbell's example, refined by clingman, shows
the associator need not be the identity even when the two bracketings are literally the same object.
See [nLab: associator](https://ncatlab.org/nlab/show/associator) and
[nLab: cartesian monoidal category](https://ncatlab.org/nlab/show/cartesian+monoidal+category).

## Current state in the library
Verified PARTIAL (the lemma and the exercise) and ABSENT (the example).

- `Structure/Cartesian.v:485` (`prod_assoc : (x × y) × z ≅ x × (y × z)`) is the explicit associator,
  and `Structure/Monoidal/Internal/Product.v:54` (`CC_Monoidal`) instantiates the whole `Monoidal`
  class at `(tensor := ×, I := 1)`, so `to_tensor_assoc_natural`/`from_tensor_assoc_natural` and
  `Structure/Monoidal.v:167` (`pentagon_identity`) are discharged for the cartesian associator. The
  naturality and pentagon halves of Riehl's exercise are therefore already in force.
- **Uniqueness is nowhere stated.** `rg -i 'unique natural isomorphism'` → 0 hits; no lemma says an
  isomorphism commuting with the three projections must be `prod_assoc`, and even the
  projection-compatibility equations for `prod_assoc` itself (`exl ∘ to prod_assoc ≈ exl ∘ exl`, …)
  are never recorded — they hold by construction but are not asserted. The tool exists
  (`Structure/Cartesian.v:136`, `ump_products`) and is never applied to the associator.
- **The associator carries an extra hypothesis.** The verifier's sharpest catch: `Context {@Terminal C}`
  is opened at `Structure/Cartesian.v:449`, ahead of `prod_comm` (`:479`), `prod_assoc` (`:485`) and
  `toggle` (`:492`), so the in-tree associator is unavailable in a category with binary products but
  no terminal object — Riehl's lemma needs only products.
- **Verifier caveat on the `CC_Monoidal` evidence** (fold this into the work, it changes how step 1
  is done): the parenthetical "at `tensor_assoc := prod_assoc`" is *not* lexically checkable.
  `CC_Monoidal` supplies only `{ tensor := InternalProductFunctor C; I := 1 }`; `unit_left`,
  `unit_right` and `tensor_assoc` are left to the global `Obligation Tactic` (`Lib/Tactics.v:225`),
  whose `program_simpl` leaf runs `eauto with typeclass_instances` and picks up the `#[export]`
  instances, and `Structure/Monoidal/Internal/Product.glob` records no reference to `prod_assoc`.
  The identification is corroborated only by the library's own header
  (`Structure/Monoidal/Cartesian.v:24`). Making that identification explicit is part of this work.
- Isbell's example is entirely absent: `rg -i subterminal` → 0, `rg -i clingman` → 0, and
  `Instance/Sets.v` never builds a bijection `C ≅ C × C` for an infinite carrier.

## Work to be done
Suggested module: `Structure/Cartesian/Assoc.v`, plus a witness file under `Instance/Sets/`.

1. Restate the associator under `Cartesian C` **alone**, without `Terminal C`: either move
   `prod_assoc` above the `Terminal` context in `Structure/Cartesian.v` or introduce
   `prod_assoc'` in the new file and prove the two agree where both are available. Record the
   projection-compatibility equations as named lemmas.
2. Prove Lemma 3.3.6: there is a *unique* morphism (hence a unique isomorphism)
   `x × (y × z) ~> (x × y) × z` commuting with the three projections to `x`, `y`, `z`, and it is the
   associator — by `ump_products` (`Structure/Cartesian.v:136`) applied twice.
3. Prove Exercise 3.3.ii's second half as an explicit statement: the associators satisfy the pentagon
   for any quadruple. Rather than re-deriving it, prove the identification `tensor_assoc CC_Monoidal ≈
   prod_assoc` and cite `pentagon_identity`, closing the lexical gap the verifier flagged.
4. State and prove the two consequences Riehl draws: iterated binary products define n-ary products
   (delegate the construction to #335 and state only the coherence consequence here), and the
   associator is the identity **iff** the projections from the two iterated products agree.
5. Example 3.3.7 (a chosen product with a non-identity associator): in `Sets`, take a countably
   infinite setoid `C` with a chosen isomorphism `C ≅ C × C`, use it to equip `C` with a *chosen*
   binary product structure whose apex is `C` itself, exhibit the common section `δ` of the two
   projections, and prove by the displayed argument that the induced comparison between the two
   ternary bracketings is not the identity (if it were, `π₁ = π₂ = id`, contradicting that the
   identity span is not a product cone). Cite clingman's refinement — the comparison is an identity
   exactly when `C(−, C)` is subterminal — in the header as background, not as an obligation.

In-tree donors: `Structure/Cartesian.v`, `Structure/Monoidal.v`,
`Structure/Monoidal/Internal/Product.v`, `Structure/Monoidal/Cartesian.v`, `Instance/Sets.v`,
`Instance/Sets/Cartesian.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.3, printed pp. 101–102 (PDF pp. 121–122)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The associator is available under `Cartesian` alone, with no `Terminal` hypothesis
- [ ] Uniqueness among morphisms commuting with the three projections is proved
- [ ] `tensor_assoc CC_Monoidal ≈ prod_assoc` is proved, so the pentagon citation is lexically justified rather than tactic-inferred
- [ ] The `Sets` witness with a non-identity associator compiles and its non-identity claim is proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping) in `Structure/`
- [ ] `Print Assumptions` closed under the global context for every principal artifact in `Structure/`
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Cartesian/Assoc.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions prod_assoc_unique.
Print Assumptions tensor_assoc_is_prod_assoc.
```
Reviewer: statements match Riehl §3.3 Lemma 3.3.6, Exercise 3.3.ii and Example 3.3.7 (printed
pp. 101–102); the uniqueness clause and the removal of the `Terminal` hypothesis are the substance —
naturality and the pentagon are already in-tree.

## Dependencies
Depends on: #335

<!-- catalog: {"ids":["riehl:3.3:lem6","riehl:3.3:exii","riehl:3.3:example7"],"deps":["#335"]} -->

---8<---

```yaml
title: "Riehl 3.3: Species — permutations versus total orderings, and unlabeled structures as colimits over the automorphism groupoid"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.3:example5]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.3, printed pp. 100–101 (PDF pp. 120–121)
- Items: `riehl:3.3:example5`

## Background
A species (Joyal) is a functor from the groupoid of finite sets and bijections to finite sets; the set
of unlabeled structures on `n` is the colimit of the restriction along the symmetric group regarded as
the automorphisms of `n`. Permutations and total orderings give equinumerous but non-naturally
isomorphic species, and their unlabeled structures differ — conjugacy classes versus a single point.
See [nLab: species](https://ncatlab.org/nlab/show/species) and
[nLab: action](https://ncatlab.org/nlab/show/action).

## Current state in the library
Verified ABSENT. The Phase-D verifier reproduced the negatives and corrected the Phase-C log's file
list (the `Joyal` hits are `Adjunction/GAFT.v:121`, `Structure/Monoidal/Symmetric.v:45`,
`Structure/Monoidal/CompactClosed.v:103`, `Structure/Monoidal/Braided.v:53,56`, not the PROP files
the classifier named) — the conclusion is unchanged: every hit is Joyal–Street on braided monoidal
categories or Joyal's product counterexample in GAFT, and none is Joyal on species.

- There is no groupoid of finite sets and bijections: `rg -i 'Fin_iso'` → 0 hits, and
  `Instance/FinSet.v` is skeletal `FinSet` with *all* functions between `Fin.t`s, carving out no
  bijections-only wide subcategory (`ls Instance/FinSet/` gives Classifier, Closed, Lawvere, Product,
  Pushout, Topos — none restricts the morphisms).
- `rg -i species` returns only the ordinary English word (`Theory/Functor.v:19`,
  `Monad/Transformer.v:59,179`, `Structure/Initial.v:25`).
- There is no delooping of a group into a one-object category, so `BS_n` cannot be written (see #220).

## Work to be done
Suggested module: `Instance/FinSet/Groupoid.v` and `Construction/Species.v`.

1. Build the core groupoid of skeletal `FinSet` — objects the natural numbers, morphisms the
   bijections of `Fin.t n` — either as a wide subcategory carved out by invertibility
   (`Construction/Subcategory.v`) or through `Construction/Groupoid.v`, whichever keeps the
   decidability of `Instance/FinSet.v` intact. Prove `Aut(n)` is the symmetric group.
2. Define `Species := Fin_iso ⟶ FinSet` (or into `Sets`, if the codomain needs to be large) and
   construct the two examples: `Sym`, acting by conjugation, and `Ord`, acting by translation.
3. Prove they are objectwise isomorphic (both have `n!` elements) but **not** naturally isomorphic —
   the counterexample is the point of the item and must be a proved negation, not a remark.
4. Define the unlabeled structures on `n` as the colimit of the restriction along
   `BS_n ⟶ Fin_iso --F--> FinSet` (the delooping of #220), and compute both cases: unlabeled
   `Sym`-structures are the conjugacy classes of permutations of `n`, unlabeled `Ord`-structures form
   a singleton. If #220's delooping is not yet available, express `BS_n ⟶ Fin_iso` as the inclusion
   of the automorphism group of `n` and use the orbit description of `riehl:3.6:exi` once it lands.
5. Header: cite Joyal 1981 for the notion and record explicitly that this file does *not* develop the
   generating-function calculus.

In-tree donors: `Instance/FinSet.v`, `Construction/Groupoid.v`, `Construction/Subcategory.v`,
`Theory/Multicategory/Endomorphism.v` (the in-tree symmetric-group action on arities, and its
axiom-free UIP normalization), #220 (delooping).

## Definition of Done
- [ ] Statement fidelity to the book (§3.3, printed pp. 100–101 (PDF pp. 120–121)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `Sym` and `Ord` are both built as functors on the bijections groupoid, and the non-existence of a natural isomorphism between them is *proved*
- [ ] Unlabeled structures are defined as a colimit and both computations (conjugacy classes; a singleton) are proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (the skeletal `FinSet` layer is axiom-free by design — keep it so)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/FinSet/Groupoid.v Construction/Species.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Fin_iso.
Print Assumptions Sym_Ord_not_naturally_isomorphic.
Print Assumptions unlabeled_Sym_conjugacy_classes.
```
Reviewer: statements match Riehl §3.3 Example 3.3.5 (printed pp. 100–101); the non-naturality claim
must be proved, and the two unlabeled computations must be theorems.

## Dependencies
Depends on: #220
Depends on: riehl:3.6:exi

<!-- catalog: {"ids":["riehl:3.3:example5"],"deps":["#220","riehl:3.6:exi"]} -->

---8<---

```yaml
title: "Riehl 3.2/3.4/3.8: Split idempotents as absolute limits and colimits"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.4:exvi, riehl:3.2:example14, riehl:3.8:exi]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.2, printed pp. 96–97 (PDF pp. 116–117); §3.4, printed pp. 108–109 (PDF pp. 128–129); §3.8, printed p. 129 (PDF p. 149)
- Items: `riehl:3.4:exvi`, `riehl:3.2:example14`, `riehl:3.8:exi`

## Background
A retract exhibits its idempotent as both an equalizer and a coequalizer, so the retract is
simultaneously the limit and the colimit of the walking-idempotent diagram; these (co)limits are
absolute — preserved by every functor — which is why splitting idempotents commutes with all limits
and colimits. See [nLab: split idempotent](https://ncatlab.org/nlab/show/split+idempotent) and
[nLab: absolute colimit](https://ncatlab.org/nlab/show/absolute+colimit).

## Current state in the library
Verified PARTIAL (Exercise 3.4.vi and Example 3.2.14), ABSENT (Exercise 3.8.i — **Phase D overturned**
the Phase-C PARTIAL here: the split-coequalizer evidence is real but belongs to Exercise 3.4.vi, and
zero of Exercise 3.8.i's own commutation content is in-tree).

- The **general** split-coequalizer theory exists and subsumes the exercise's coequalizer half:
  `Structure/Coequalizer/Split.v:90` (`split_coequalizer_is_coequalizer`), `:104`
  (`functor_preserves_split`) and `:132` (`split_coequalizer_preserved`, the `∀ F : C ⟶ D`
  preservation statement that *is* absoluteness, instantiated once).
- **But the instance is never taken.** The verifier checked the arithmetic and confirms it is three
  lines away: for a `SplitIdempotent` (`Theory/Morphisms.v:85`, carrying `split_idem_sr : s ∘ r ≈ e`
  and `split_idem_rs : r ∘ s ≈ id`), the witness `f := id[A]`, `g := s ∘ r`, `scoeq_e := r`,
  `scoeq_s := s`, `scoeq_t := id[A]` satisfies all four `SplitCoequalizer` laws. This is the cheapest
  item in the chapter.
- **The equalizer half is entirely absent.** There is no `SplitEqualizer`/split-fork record dual to
  `Structure/Coequalizer/Split.v`; `rg -ni 'SplitEqualizer|split equalizer|split fork'` returns three
  prose hits only (`Comonad/Coalgebra.v:89`, `Monad/Monadicity/BeckObjects.v:19,54`). So "split
  equalizers are absolute" is unproved.
- **Clause (ii) is absent**: there is no walking-idempotent shape category and no (co)limit statement
  over an endomorphism diagram.
- On the `Sets` side (Example 3.2.14) the *splitting* half is present at full strength:
  `Instance/Sets/Karoubi.v:41` (`sets_split_obj e`, carrier `∃ a : X, e a ≈ a`), `:80` (`sets_split`),
  `:101` (`Sets_IdempotentsSplit`), `:113` (`Sets_Cauchy`). What is missing is the identification of
  `A^e` with a limit/equalizer, and the converse direction (from a retraction, `s ∘ r` is idempotent
  and `B ↣ A ⇉ A` is an equalizer diagram).
- **Verifier correction to the Phase-C gap for Example 3.2.14**: the clause "the section
  `s : A^e ↣ A` is not shown monic" is overstated — `Theory/Morphisms.v:179` proves
  `sections_are_monic : Section f → Monic f`, and `split_idem_rs` exhibits `sets_split_s` as a
  `Section`, so monicity is a one-line instantiation of existing API. Treat it as a one-liner, not as
  missing content.
- **Verifier calibration on `Construction/Karoubi.v:67-70`**: it is a background-essay sentence
  explicitly attributed to nLab ("Cauchy complete category"), not a claim the tree proves absoluteness
  — do not describe it as an unsupported assertion.

## Work to be done
Suggested module: `Structure/Equalizer/Split.v` and `Construction/Karoubi/Absolute.v`.

1. **Split equalizers.** Dualize `Structure/Coequalizer/Split.v` in full: the `SplitEqualizer`
   record, `split_equalizer_is_equalizer`, `functor_preserves_split_equalizer` and
   `split_equalizer_preserved`. If the `C^op` route is cheaper than a fresh development, take it, but
   expose covariant accessors so consumers do not have to reason under `^op`.
2. **The instance.** From a `SplitIdempotent A B r s`, build the `SplitCoequalizer id[A] (s ∘ r)` with
   `scoeq_e := r` (the witness above) and the dual `SplitEqualizer id[A] (s ∘ r)` with the fork
   `s : B ↣ A`. Conclude Exercise 3.4.vi clause (i): both fork and cofork are (co)equalizer diagrams.
3. **Clause (ii).** Introduce the walking-idempotent index category (one object, one non-identity
   idempotent endomorphism) alongside `Instance/Parallel.v` and `Instance/Two.v`, and prove that `B`
   is both a `Limit` and a `Colimit` of the corresponding diagram, with the cone/cocone legs `s` and
   `r`.
4. **Clause (iii) / Exercise 3.8.i.** Instantiate the absolute-(co)limit predicate of #477 at these two witnesses, and state the consequence
   Exercise 3.8.i asks for: splitting an idempotent commutes with limits and colimits of *every*
   shape — i.e. for any `F : J ⟶ C` valued in split idempotents, the splitting of a pointwise
   idempotent computes the splitting of the limit/colimit. State the commutation precisely (which
   diagram, which canonical map) rather than as a slogan.
5. **Example 3.2.14 in `Sets`.** Show `sets_split_obj e` is the equalizer of `(id, e)` and the limit
   of the walking-idempotent diagram; add the one-line monicity of `sets_split_s` via
   `sections_are_monic`; and prove the converse leg — `Retraction r s → Idempotent (s ∘ r)` — which
   currently has no lemma (`Idempotent` producers in-tree are only `id_idem` and
   `karoubi_idem_splits`).

In-tree donors: `Structure/Coequalizer/Split.v`, `Theory/Morphisms.v` (`Idempotent`,
`SplitIdempotent`, `sections_are_monic`), `Construction/Karoubi.v`, `Instance/Sets/Karoubi.v`,
`Instance/Parallel.v`, `Structure/Equalizer/Fork.v`, #477.

## Definition of Done
- [ ] Statement fidelity to the book (§3.2 printed pp. 96–97, §3.4 printed pp. 108–109, §3.8 printed p. 129 (PDF pp. 116–117, 128–129, 149)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `SplitEqualizer` exists with the full dual API, including preservation by an arbitrary functor
- [ ] The `SplitIdempotent → SplitCoequalizer` and `SplitIdempotent → SplitEqualizer` instances are constructed
- [ ] The walking-idempotent shape exists and `B` is proved both its limit and its colimit
- [ ] Exercise 3.8.i is stated as a precise commutation statement (named canonical map), not a slogan, and proved
- [ ] `Retraction r s → Idempotent (s ∘ r)` is added, and `sets_split_obj e` is identified with the equalizer of `(id, e)`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Equalizer/Split.v Construction/Karoubi/Absolute.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions split_equalizer_preserved.
Print Assumptions idempotent_split_coequalizer.
Print Assumptions idempotent_splitting_absolute.
```
Reviewer: statements match Riehl §3.4 Exercise 3.4.vi (all three parts), §3.2 Example 3.2.14 and
§3.8 Exercise 3.8.i; the equalizer half must be a real development, not a `^op` alias with no
covariant accessors.

## Dependencies
Depends on: #477

<!-- catalog: {"ids":["riehl:3.4:exvi","riehl:3.2:example14","riehl:3.8:exi"],"deps":["#477"]} -->

---8<---

```yaml
title: "Riehl 3.4/3.6: Connected colimits — the coslice and category-of-elements projections create them, and slices of a bicomplete category are bicomplete"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.4:prop8, riehl:3.4:exii, riehl:3.4:exiv, riehl:3.6:prop5]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.4, printed p. 106 and p. 108 (PDF p. 126 and p. 128); §3.6, printed p. 117 (PDF p. 137)
- Items: `riehl:3.4:prop8` (the connected-colimit half; the limit half is filed on #438),
  `riehl:3.4:exii`, `riehl:3.4:exiv`, `riehl:3.6:prop5`
- Note: `riehl:3.4:prop8` is a genuinely two-part item. Its limit half — the coslice projection
  strictly creates limits — is recorded against #438. This issue is the connected-colimit half.

## Background
The projection from a coslice creates limits unconditionally, but creates colimits only over
*connected* index categories; the connectedness hypothesis is exactly what lets the apex object be
defined independently of the chosen index. Coproducts in a coslice must therefore be built separately,
as wide pushouts under the base object. See
[nLab: connected category](https://ncatlab.org/nlab/show/connected+category) and
[nLab: created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
Verified PARTIAL (all four).

- The limit side of the comma/coslice story is real: `Construction/Comma/Limit.v:238`
  (`comma_limit`), `:245` (`Comma_Complete`), `:264` (`right_adjoint_PreservesImageLimit`), `:271`
  (`Comma_Complete_right_adjoint`), with `Construction/Slice.v:181` (`Comma_Coslice`) identifying the
  coslice with `=(c) ↓ Id`. The verifier confirmed the coslice specialization is a one-liner, not
  missing machinery: `Instance/Adjoints.v:42` (`adj_id : Id -| Id`) plus
  `right_adjoint_PreservesImageLimit` already make
  `Comma_Complete_right_adjoint Adjunction_Id c HC : Complete (=(c) ↓ Id)` type-check; only the
  transport along `Comma_Coslice` and the statement are absent. That leg is #438's obligation.
- **The colimit half is doubly blocked.** There is no colimit analogue of `Comma_Complete` anywhere,
  and there is no notion of a connected category in the tree at all:
  `rg -riE 'connected colimit|wide pushout|wide colimit'` → 0 hits, and every `connected` hit is
  prose or `Instance/FinSet/Pushout.v`'s connected-components labelling of a finite edge relation
  (a set-level union-find, unrelated to the categorical predicate).
- **Verifier calibration correction, important for scoping**: `Construction/Comma/Limit.v` does *not*
  prove strict creation. What it proves is strict *lifting* plus limit-ness — a limit of `K` exists
  whose `comma_proj2`-image is the given `C`-limit cone on the nose (`apex_obj` at `:159`,
  `apex_leg` at `:163`) — while the **uniqueness of the lift**, the other half of creation, is
  nowhere stated, and no creation predicate exists in the tree. Do not cite
  `Construction/Comma/Limit.v` as an in-tree instance of "strictly creates".
- The category of elements does not exist (`rg -i 'category of elements'` → exactly one hit,
  `Construction/Grothendieck.v:108`, inside a background essay), so Exercise 3.4.ii's subject is
  unavailable; `Construction/Grothendieck.v` builds `∫` only for an `IndexedCat`, never for a
  `Sets`-valued functor.
- Exercise 3.4.iv has no statable form: there is no `Set_*` and no `Top`, and
  `Construction/Slice.v:82`'s pointed-sets remark is an essay line, never instantiated.
- For Proposition 3.6.5 the slice `C/c` is uncovered even on the limit side: `Comma_Complete` is
  stated only for the coslice-shaped comma `=(d) ↓ U`, and completeness of a slice is *not* the
  formal dual of completeness of a coslice (dualizing swaps `Complete` for `Cocomplete`);
  `Construction/Slice/Pullback.v` contains only `Bang_Functor` (`:50`) and `Star_Functor` (`:67`).

## Work to be done
Suggested module: `Construction/Comma/Colimit.v`, plus `Construction/Slice/Limit.v`.

1. With the connected-category predicate of #352, prove the
   colimit half of Proposition 3.4.8: for connected `J`, the coslice projection `Π : c/C ⟶ C` creates
   colimits — given a colimit cocone `μ : K ⟹ Δp` in `C`, the lifted object is `μ_j ∘ κ_j : c ~> p`,
   well defined precisely by connectedness, and the lift is unique and colimiting. State creation in
   the sense of the creation class of #406, i.e. with the uniqueness clause the comma-limit file
   currently lacks.
2. Prove Exercise 3.4.ii, the generalization to the category of elements: for `F : C ⟶ Set`, the
   projection `Π : ∫F ⟶ C` (a) strictly creates all limits `C` admits **and** `F` preserves, and
   (b) strictly creates all connected colimits `C` admits. Phrase both **per class of diagrams**, not
   with the wholesale `@Complete C` + all-shapes `PreservesImageLimit` hypothesis pack that
   `Comma_Complete` uses — the verifier confirmed `PreservesImageLimit`
   (`Construction/Comma/Limit.v:110`) is quantified over all `J` and `G`, so the wholesale form does
   not specialize.
3. Prove Proposition 3.6.5: if `C` is complete and cocomplete then so are `c/C` and `C/c`. Complete
   the coslice by transporting #438's limit creation along `Comma_Coslice`; cocomplete it by step 1
   for connected shapes plus coproducts, which must be built separately as **wide pushouts under
   `c`** (the dual of Riehl's Lemma 3.5.15, filed on #326) with `id_c` as the empty coproduct. Then
   handle the slice `C/c` explicitly rather than by an appeal to duality, since the dual of "coslice
   complete" is "slice cocomplete".
4. Prove Exercise 3.4.iv, the necessity of connectedness: the forgetful functor `Set_* ⟶ Set` (over
   #261, or `Coslice Sets 1`) fails to preserve binary coproducts, exhibiting a non-connected shape
   over which the coslice projection does not create colimits. A witness suffices; a general theory of
   pointed spaces is not required.
5. While in the file, introduce the wide pushout / wide colimit vocabulary the coproduct construction
   needs, coordinating with #326 so the wide *pullback* dual lands in the same vocabulary.

In-tree donors: `Construction/Comma/Limit.v`, `Construction/Slice.v`, `Construction/Slice/Pullback.v`,
`Instance/Adjoints.v` (`adj_id`), `Structure/Limit.v`, #352, #406, #438, #345, #261.

## Definition of Done
- [ ] Statement fidelity to the book (§3.4 printed pp. 106, 108; §3.6 printed p. 117 (PDF pp. 126, 128, 137)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Creation is stated with the uniqueness-of-lift clause, not merely lifting-plus-universality
- [ ] The connected-colimit statement is per class of diagrams, not under a wholesale completeness oracle
- [ ] The slice `C/c` is treated explicitly, not by an incorrect appeal to duality from the coslice
- [ ] Wide pushouts (and the coproduct-as-wide-pushout construction in a coslice) are defined and used
- [ ] The Exercise 3.4.iv counterexample is a compiled witness showing coproducts are not preserved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Construction/Comma/Colimit.v Construction/Slice/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions coslice_creates_connected_colimits.
Print Assumptions elements_proj_creates_connected_colimits.
Print Assumptions Slice_Bicomplete.
Print Assumptions Coslice_Bicomplete.
```
Reviewer: statements match Riehl §3.4 Proposition 3.4.8 (colimit half), Exercises 3.4.ii and 3.4.iv,
and §3.6 Proposition 3.6.5; check that connectedness is genuinely consumed in the colimit proof and
that the slice case is not smuggled in by duality.

## Dependencies
Depends on: #352
Depends on: #406
Depends on: #438
Depends on: #345
Depends on: #261
Depends on: #326

<!-- catalog: {"ids":["riehl:3.4:prop8","riehl:3.4:exii","riehl:3.4:exiv","riehl:3.6:prop5"],"deps":["#352","#406","#438","#345","#261","#326"]} -->

---8<---

```yaml
title: "Riehl 3.5: The Yoneda embedding preserves and reflects limits but does not create them"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.5:thm5, riehl:3.5:thm10, riehl:3.5:exii, riehl:3.5:remark14]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.5, printed pp. 110–115 (PDF pp. 130–135)
- Items: `riehl:3.5:thm5`, `riehl:3.5:thm10`, `riehl:3.5:exii`, `riehl:3.5:remark14`

## Background
The Yoneda embedding both preserves and reflects limits — preservation because limits in a presheaf
category are pointwise and representables are continuous, reflection because the embedding is full and
faithful — but it does not create them, since a diagram may have a limit downstairs with no counterpart
upstairs. Lawvere's generalized-element philosophy is the same fact read informally: an object is
determined by its generalized elements, so a cone is limiting exactly when it is limiting after
probing by every shape. See [nLab: Yoneda embedding](https://ncatlab.org/nlab/show/Yoneda+embedding),
[nLab: preserved limit](https://ncatlab.org/nlab/show/preserved+limit) and
[nLab: generalized element](https://ncatlab.org/nlab/show/generalized+element).

## Current state in the library
Verified PARTIAL (all four). The two halves exist separately and are never composed.

- **Reflection is available only as an uncomposed pair.** `Theory/Equivalence/Limit.v:401`
  (`ff_reflects_limit`) proves that a full and faithful functor reflects limits, and `Functor/Hom.v:85`
  (`Yoneda_Faithful`) and `:96` (`Yoneda_Full`) prove `Curried_Hom C` is full and faithful — but
  `rg -i 'yoneda' --glob '*.v' | grep -iE 'limit|colimit|preserv|reflect'` returns exactly ONE hit, a
  `Require` line at `Structure/UniversalProperty/Limit.v:13`. No in-tree constant connects Yoneda to
  (co)limits. The verifier flags that this instantiation is **real work, not a one-liner**:
  `ff_reflects_limit` carries the extra leg-identification hypothesis `Hlegs`
  (`Theory/Equivalence/Limit.v:353`), which must be discharged at the Yoneda embedding.
- **Preservation is entirely missing, and so is its prerequisite.** `Instance/Fun/` contains exactly
  one file (`Cartesian.v`), whose sole result is `Functor_Category_Cartesian` (`:111`) for binary
  products; there is no theorem that limits in `[C^op, Sets]` are pointwise. The verifier identifies
  this as the real prerequisite: the issue should depend on the pointwise-limits work (#425) rather
  than on Riehl's Theorem 3.5.5 directly.
- **Non-creation is literally unstatable.** `rg -n 'Creates'` returns only
  `Monad/Monadicity/Beck.v:164` (`CreatesUSplitCoequalizers`), `:911` (`monadic_creates`),
  `Monad/Monadicity/BeckObjects.v`, and `Theory/Equivalence/Limit.v:486`
  (`equivalence_creates_limits`) — no general creation class, so "`y` does not create limits" cannot
  be written and no counterexample exists.
- **The contravariant half** (Theorem 3.5.10) has the same shape: reflection available generically,
  preservation absent, and `Structure/Limit/Preservation.v:147` (`ump_colimit`) supplies only the
  elementwise cocone universal property.
- **Generalized elements** (Remark 3.5.14): clause (a) — a parallel pair agreeing on all generalized
  elements is equal — *is* `Yoneda_Faithful` read at `C^op`, whose own proof specializes the
  hypothesis at the identity, i.e. Riehl's argument verbatim. Clause (b) — a cone is limiting if its
  image under every probe is limiting in `Set` — is available only in the representability form
  `Structure/UniversalProperty/Limit.v:141` (`LimitIsUniversalProperty`). The verifier additionally
  checked `Structure/UniversalProperty/Limit.v:104` (`cone_equiv_to_morphism_equiv`) and confirms it
  is the *uniqueness* half only, so it does not close the gap. The vocabulary itself is absent:
  `generalized element` occurs only in prose at `Structure/Terminal.v:60-61` and
  `Structure/Constant.v:15`.

## Work to be done
Suggested module: `Functor/Hom/Yoneda/Limit.v`.

1. **Reflection.** Instantiate `ff_reflects_limit` at `Curried_Hom C` and discharge the `Hlegs`
   leg-identification hypothesis explicitly; state `yoneda_reflects_limits` and, at `C^op`, its
   colimit twin `yoneda_reflects_colimits` for the contravariant embedding
   `Curried_CoHom` (`Functor/Hom.v:146`). The reflection half of Theorem 3.5.10 depends on the
   fully-faithful **colimit** reflection lemma, which is itself missing (recorded against #481) —
   depend on it rather than re-deriving.
2. **Preservation.** Over the pointwise-limit theorem for functor categories (#425) and the
   continuity of representables (#428), prove Theorem 3.5.5 clause (ii): `y : C ⟶ [C^op, Sets]`
   preserves all limits existing in `C`. Give the contravariant form (Theorem 3.5.10 clause (ii)) at
   `C^op`.
3. **Non-creation.** With the creation class of #406, prove `y` does not create limits, and supply
   Riehl's requested explicit counterexample — a diagram in some `C` whose image under `y` has a limit
   in `[C^op, Sets]` while the diagram has none in `C` (a small `C` lacking the relevant limit will
   do; keep it decidable and compiled, not sketched).
4. **Generalized elements.** Introduce the vocabulary — an `X`-shaped generalized element of `a` is a
   morphism `X ~> a`, with the action of `f : a ~> b` by postcomposition — and state Riehl's two
   consequences as named lemmas: (a) `f ≈ g` iff they agree on generalized elements of every shape
   (from `Yoneda_Faithful`); (b) a cone is limiting iff its image under every `C(X, −)` is limiting in
   `Sets` (the composite of steps 1 and 2). Coordinate the definition with #671, which introduces
   local membership of generalized elements in a subobject, so the two do not diverge.

In-tree donors: `Functor/Hom.v`, `Theory/Equivalence/Limit.v`, `Structure/Limit/Preservation.v`,
`Structure/UniversalProperty/Limit.v`, `Structure/Limit/Weighted.v`, `Instance/Fun.v`, #425, #428,
#720, #481, #406, #671.

## Definition of Done
- [ ] Statement fidelity to the book (§3.5, printed pp. 110–115 (PDF pp. 130–135)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `ff_reflects_limit`'s `Hlegs` hypothesis is genuinely discharged at the Yoneda embedding
- [ ] Preservation is proved for **all** limits, not only products (#720 covers products and exponentials)
- [ ] Both variances are covered: covariant `y` on limits, contravariant `y` on colimits
- [ ] Non-creation is stated against a real creation class, with a compiled explicit counterexample
- [ ] Generalized elements are defined, and both of Riehl's consequences are named lemmas
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Functor/Hom/Yoneda/Limit.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions yoneda_preserves_limits.
Print Assumptions yoneda_reflects_limits.
Print Assumptions yoneda_not_creates_limits.
Print Assumptions limit_iff_pointwise_generalized_elements.
```
Reviewer: statements match Riehl §3.5 Theorems 3.5.5 and 3.5.10, Exercise 3.5.ii and Remark 3.5.14
(printed pp. 110–115); a proof of preservation that only covers products does not close this issue.

## Dependencies
Depends on: #425
Depends on: #428
Depends on: #720
Depends on: #481
Depends on: #406
Depends on: #671

<!-- catalog: {"ids":["riehl:3.5:thm5","riehl:3.5:thm10","riehl:3.5:exii","riehl:3.5:remark14"],"deps":["#425","#428","#720","#481","#406","#671"]} -->

---8<---

```yaml
title: "Riehl 3.6: Internal equivalence relations — the kernel pair as a relation, and effective quotients"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.6:example11]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.6, printed pp. 119–121 (PDF pp. 139–141)
- Items: `riehl:3.6:example11`

## Background
The kernel pair of a morphism is a subobject of the square of its domain — a relation — and it carries
reflexivity, symmetry and transitivity maps making it an internal equivalence relation (a congruence);
the coequalizer of such a relation is the quotient, and the induced comparison is the image
factorization. See [nLab: kernel pair](https://ncatlab.org/nlab/show/kernel+pair) and
[nLab: congruence](https://ncatlab.org/nlab/show/congruence).

## Current state in the library
Verified PARTIAL. The *back half* of the example is present, and in one respect stronger than the
book, while the relational front half is entirely absent.

- Present, and stronger than Riehl's "in good situations" phrasing: `Structure/Regular.v:46`
  (`kernel_pair f := pullback f f`), `Structure/Regular/Factorization.v:128` (`image_kernel_pair`),
  `:132` (`image_obj`), `:140` (`image_is_coeq` — the image is the coequalizer of the kernel pair),
  `:155` (`image_mor`), `:175` (`image_comparison_monic`, proved by the Freyd/Borceux double-cover
  chase), `:270` (`regular_factorization`), `:282` (`Regular_OFS`) — a full orthogonal factorization
  system, plus the concrete `Instance/Sets/Image.v:75` (`Sets_Image`) and `:143`
  (`Sets_Image_Factorization`).
- Absent, clause by clause:
  (a) nothing proves the kernel-pair pairing `(s,t) : R → X × X` is monic, so `R` is never exhibited
      as a subobject/relation on `X`, and the generalized-element reading ("`x, x' : Z ⇒ X` are
      identified exactly when `f x = f x'`") is unstated. The verifier confirms `rg -i 'jointly monic'`
      has a single hit, `Construction/Cospan/Double.v:45`, which is prose about pushout legs.
  (b) the three structure maps — `ρ` a common section of `s` and `t` factoring the diagonal, `σ` with
      `t σ = s` and `s σ = t`, `τ` on the pullback of `t` along `s` with `s τ = s s̄`, `t τ = t t̄` —
      are nowhere constructed for a kernel pair.
  (c) **there is no internal-equivalence-relation class in the library at all.**
      `rg -riE 'equivalence relation|internal relation'` over `Structure/ Theory/ Construction/
      Instance/` returns only setoid-level equivalence relations and header prose
      (`Structure/Topos.v:92` mentions effectivity as part of the Giraud-axiom discussion without
      formalizing it). `Structure/Coequalizer/Reflexive.v`'s `ReflexivePair` captures only clause (i).
      Effectiveness — every internal equivalence relation is a kernel pair — is therefore also absent.
- **Verifier refinement**: the Phase-C strength comparison is slightly generous about clause (d);
  treat the quotient/comparison story as covered by `Regular_OFS` only under a `Regular` hypothesis,
  not in an arbitrary finitely (co)complete category as the example states.

## Work to be done
Suggested module: `Structure/Relation/Internal.v` (with the effectivity results in
`Structure/Regular/Effective.v`).

1. Prove the pairing `⟨s, t⟩ : R ~> X × X` of a kernel pair is monic, in a category with binary
   products and pullbacks, and package `R` as a `SubObj (X × X)` using `Theory/Subobject.v`; state
   the generalized-element characterization (`⟨s,t⟩ ∘ − ` identifies `x, x' : Z ⇒ X` exactly when
   `f ∘ x ≈ f ∘ x'`).
2. Define `InternalEquivalenceRelation` (congruence): a subobject `⟨s,t⟩ : R ↣ X × X` together with
   `ρ`, `σ`, `τ` satisfying Riehl's three clauses, `τ` defined on the pullback of `t` along `s`.
   Prove the laws are property-like (proof-irrelevant given the mono) so the record is well behaved.
3. Prove every kernel pair carries this structure — construct `ρ`, `σ`, `τ` from the pullback
   universal property — which is the example's clause (b).
4. Define the quotient of an internal equivalence relation as the coequalizer of `s, t` when it
   exists, and define `Effective`: the relation is the kernel pair of its own quotient map. Prove the
   two standard directions available in-tree: in a `Regular` category (`Structure/Regular.v`) the
   kernel pair of any morphism is effective, and the image factorization of
   `Structure/Regular/Factorization.v` realizes Riehl's clause (e).
5. Instantiate at `Sets` over `Instance/Sets/Image.v` so the abstract development has a witness, and
   record the result against docs/INHABITATION.md.

In-tree donors: `Structure/Regular.v`, `Structure/Regular/Factorization.v`, `Structure/Pullback.v`,
`Theory/Morphisms/Stability.v`, `Theory/Subobject.v`, `Structure/Coequalizer.v`,
`Structure/Coequalizer/Reflexive.v`, `Instance/Sets/Image.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.6, printed pp. 119–121 (PDF pp. 139–141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The kernel-pair pairing is proved monic and packaged as a subobject of `X × X`
- [ ] `InternalEquivalenceRelation` exists with all three structure maps and their equations
- [ ] Every kernel pair is proved to be an internal equivalence relation
- [ ] Effectivity is defined, and the regular-category direction is proved
- [ ] The `Sets` witness compiles and is recorded in docs/INHABITATION.md
- [ ] `Structure/Topos.v:92`'s effectivity remark is updated to point at the new definition
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Relation/Internal.v Structure/Regular/Effective.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions kernel_pair_monic.
Print Assumptions kernel_pair_is_equivalence_relation.
Print Assumptions regular_kernel_pair_effective.
```
Reviewer: statement matches Riehl §3.6 Example 3.6.11 (printed pp. 119–121); all three structure maps
must be constructed, and `τ` must live on the pullback of `t` along `s`, not on a product.

## Dependencies
Depends on: #333
Depends on: #326

<!-- catalog: {"ids":["riehl:3.6:example11"],"deps":["#333","#326"]} -->

---8<---

```yaml
title: "Riehl 3.1/3.6: Cone-shape index categories, and pushouts in Cat computing the free monoid and free group on one generator"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.1:remark8, riehl:3.6:example8, riehl:3.6:exvi]
deps_item_ids: []
deps_pending: [riehl:4.6:cor15]
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.1, printed p. 85 (PDF p. 105); §3.6, printed p. 118 and p. 122 (PDF p. 138 and p. 142)
- Items: `riehl:3.1:remark8`, `riehl:3.6:example8`, `riehl:3.6:exvi`

## Background
A diagram together with a cone over it is the same thing as a diagram indexed by the shape obtained
from the index category by freely adjoining an initial object; dually for cocones. Those augmented
shapes are themselves pushouts in `Cat`, and the same pushout technique computes the delooped monoid
of natural numbers and the delooped group of integers. See
[nLab: join of categories](https://ncatlab.org/nlab/show/join+of+categories) and
[nLab: Cat](https://ncatlab.org/nlab/show/Cat).

## Current state in the library
Verified ABSENT (all three), independently reproduced by the Phase-D verifier.

- No shape augmentation exists. `rg -ni 'limit diagram|colimit diagram'` → 0 hits; there is no
  `J^◁`/`J^▷`, no cone-shape or cocone-shape category, and no `adjoin`/`augment` construction (the
  only such hits are `Theory/Coq/Maybe.v`'s freely adjoined monoid unit and `Instance/Coq/Par.v`'s
  basepoint). The in-tree shape categories are `Zero`, `One`, `Two`/`Two_Discrete`, `Parallel`,
  `Roof`, `DiscreteCat` — none is an augmented shape.
- The two cone reformulations that *do* exist — `Cone_Natural_Transform`/`Cone_Comma`
  (`Structure/Cone/Const.v`) and `Cones_Comma` (`Instance/Cones/Comma.v`) — are the
  Δ-natural-transformation and comma-category readings, which are different statements;
  Phase C correctly refused to count them, and the verifier endorses that.
- **`Cat` has no pushouts.** `ls Instance/Cat/*.v` is exactly `Bicategory.v`, `Cartesian.v`,
  `Cocartesian.v` — products, coproducts and the bicategory structure, no pushout and no general
  colimit. The only `HasPushouts` instances in-tree are `Instance/Sets/Pushout.v:185` and
  `Instance/FinSet/Pushout.v:513`.
- There is no delooping of a monoid or group into a category, so `BN` and `BZ` have no names; and
  there is no walking-isomorphism category (`Instance/Two.v:134` gives the walking arrow `_2`; `I`
  appears only in the Funny-tensor prose). `Construction/Free.v:118` (`Free`) is the path category
  on the underlying quiver of an *existing* category, not the free category on an abstract one-vertex
  one-loop graph, so it does not give `BN` either.
- Riehl defers the general cocompleteness of `Cat` to her Corollary 4.6.15, which is outside this
  chapter; it is recorded as a pending dependency rather than absorbed here.

## Work to be done
Suggested module: `Instance/Cat/Pushout.v` and `Construction/Cone/Shape.v`.

1. **Pushouts in `Cat`.** Construct binary pushouts of small categories (the pushout of the underlying
   quivers, followed by the quotient by the generated congruence — donors:
   `Construction/Free/Quiver.v`, `Construction/Quotient.v`, `Instance/Sets/Pushout.v`), and register
   `HasPushouts Cat`. Mind the `Instance/Cat.v:142-145` hom-setoid: `Cat`'s hom-equivalence is natural
   isomorphism, so state the universal property in the form that setoid supports and disclose the
   deviation from the strict 1-categorical `Cat` in the header, exactly as
   `Instance/Cat/Cartesian.v:26-30` does for products.
2. **Example 3.6.8.** Compute the pushout of `1 ← 1 + 1 → 2` and prove it is the delooping `BN` of
   the additive monoid of naturals (over #220), i.e. the free category on one object and one
   non-identity endomorphism. Then replace the walking arrow `2` by the walking isomorphism `I`
   (over #666) and prove the pushout is `BZ`.
3. **Exercise 3.6.vi.** Define `i₀, i₁ : J ⇉ J × 2` and construct the cone-shape and cocone-shape
   categories as the pushouts of `J → 1` along `i₀` and `i₁`; prove the object picked out by the
   functor out of `1` is initial in the first and terminal in the second.
4. **Remark 3.1.8.** Prove the identification: a `J`-indexed diagram together with a cone over it is
   the same thing as a diagram indexed by the cone shape (an isomorphism, or at least an equivalence,
   of the relevant categories), and dually for cocones; and introduce the terminology "limit diagram"
   / "colimit diagram" for a diagram bundled with its limiting (co)cone. Relate the new shapes to
   `Structure/Cone/Const.v`'s existing Δ-transformation reading, so the library has one cone notion
   and two presentations, not two notions.

In-tree donors: `Instance/Cat.v`, `Instance/Cat/Cartesian.v`, `Instance/Cat/Cocartesian.v`,
`Construction/Free/Quiver.v`, `Construction/Quotient.v`, `Structure/Pushout.v`,
`Structure/Cone/Const.v`, `Instance/Cones/Comma.v`, `Instance/Two.v`, #220, #666, #414.

## Definition of Done
- [ ] Statement fidelity to the book (§3.1 printed p. 85; §3.6 printed pp. 118, 122 (PDF pp. 105, 138, 142)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `HasPushouts Cat` is constructed, with the natural-isomorphism hom-setoid caveat disclosed in the header
- [ ] `BN` and `BZ` are computed as pushouts and identified with the deloopings of `(ℕ, +)` and `(ℤ, +)`
- [ ] The cone-shape and cocone-shape categories are built as pushouts, with the initial/terminal object identified
- [ ] Remark 3.1.8's identification (diagram-with-a-cone = diagram on the augmented shape) is a proved equivalence, and is related to `Structure/Cone/Const.v` rather than duplicating it
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Cat/Pushout.v Construction/Cone/Shape.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Cat_HasPushouts.
Print Assumptions pushout_is_BN.
Print Assumptions cone_shape_initial.
Print Assumptions diagram_with_cone_equiv.
```
Reviewer: statements match Riehl §3.1 Remark 3.1.8, §3.6 Example 3.6.8 and Exercise 3.6.vi (printed
pp. 85, 118, 122); check that the `Cat` pushout universal property is stated against `Cat`'s actual
hom-setoid and that the deviation is disclosed.

## Dependencies
Depends on: #220
Depends on: #666
Depends on: #414

<!-- catalog: {"ids":["riehl:3.1:remark8","riehl:3.6:example8","riehl:3.6:exvi"],"deps":["#220","#666","#414"]} -->

---8<---

```yaml
title: "Riehl 3.6: Completeness and cocompleteness of Quiver and rQuiver, and the failure for Graph"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:3.6:exiv]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.6, printed p. 121 (PDF p. 141)
- Items: `riehl:3.6:exiv`

## Background
Quivers and reflexive quivers are presheaf categories, hence complete and cocomplete with limits and
colimits computed pointwise; undirected simple graphs are not, and the product of the walking edge
with itself exhibits the failure. See [nLab: quiver](https://ncatlab.org/nlab/show/quiver) and
[nLab: category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves).

## Current state in the library
Verified ABSENT. **Phase D considered PARTIAL and withdrew it**: the ambient category exists but not
one of the exercise's three claims does, and the ambient is a prerequisite of the claims rather than a
part of them.

- `Construction/Free/Quiver.v:358` (`#[export] Instance QuiverCategory : Category`) and `:205`
  (`Class QuiverHomomorphism`) give the category of quivers, verified line-exact by the verifier, who
  also re-derived the file's full symbol list.
- No limit or colimit fact about quivers exists anywhere: no completeness, no cocompleteness, no
  computed product, and no presentation of `Quiver` as a presheaf category on the two-object walking-arrow
  shape.
- There is no category of reflexive quivers (`rQuiver`) — the reflexive-quiver notion is itself filed
  as #906 — and no category of undirected simple graphs.

## Work to be done
Suggested module: `Construction/Free/Quiver/Complete.v`. Two module-path notes are recorded under
Dependencies below and must be read before writing any file: one path is already claimed by another
issue, and the category of graphs this exercise needs is supplied by an existing issue rather than
introduced here.

1. Present `Quiver` as a presheaf category: build the two-object index category with two parallel
   arrows (`Instance/Parallel.v` is the shape), give the equivalence
   `QuiverCategory ≃ [Parallel^op, Sets]` (or an isomorphism if the encodings line up), and conclude
   completeness and cocompleteness from the pointwise-limits theorem (#425) and its colimit dual
   (#715). Describe the resulting limits and colimits concretely — vertices and edges computed
   separately — as the exercise asks.
2. Do the same for reflexive quivers over #906: the index category acquires the degeneracy, and the
   same argument gives `rQuiver` complete and cocomplete. Compute the product of the walking arrow
   with itself in **both** categories and exhibit the difference — this is the point of part (ii) and
   must be a computed object, not a remark.
3. Part (iii): over the category of undirected simple graphs supplied by #926, prove it is neither
   complete nor cocomplete by
   exhibiting the concrete failures Riehl asks for — either compute the product of the walking edge
   with itself or prove no such product exists. A proved non-existence is the stronger and preferred
   deliverable; if the argument turns on loops, disclose the exact definition of `Graph` adopted in
   the header, since the answer depends on whether loops are permitted.

In-tree donors: `Construction/Free/Quiver.v`, `Instance/Parallel.v`, `Instance/Fun.v`,
`Instance/Fun/Cartesian.v`, `Instance/Sets.v`, #906, #425, #715, #926.

## Definition of Done
- [ ] Statement fidelity to the book (§3.6, printed p. 121 (PDF p. 141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `Quiver` is identified with a presheaf category and its (co)completeness derived, not assumed
- [ ] `rQuiver` is constructed and its (co)completeness proved
- [ ] The product of the walking arrow with itself is computed in both `Quiver` and `rQuiver`, and the two answers are shown to differ
- [ ] The `Graph` failure is a proved statement (ideally a proved non-existence), stated against the category of graphs of #926 rather than a second, rival one, with the definition's treatment of loops disclosed in the header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Construction/Free/Quiver/Complete.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Quiver_Complete.
Print Assumptions rQuiver_Complete.
Print Assumptions Graph_not_Complete.
```
Reviewer: statements match Riehl §3.6 Exercise 3.6.iv (printed p. 121); parts (ii) and (iii) require
computed objects and a proved failure, not descriptions.

## Dependencies
Depends on: #906
Depends on: #425
Depends on: #715
Depends on: #926

Module-path notes (read before creating any file):
- #332 already claims `Construction/Free/Quiver/Limit.v` for cones over a quiver-shaped diagram — a
  different obligation. Use `Construction/Free/Quiver/Complete.v` here, and cross-link the two.
- #926 already claims `Instance/Graph.v` for the category of graphs. Part (iii) must build on that
  category rather than introducing a rival one.

<!-- catalog: {"ids":["riehl:3.6:exiv"],"deps":["#906","#425","#715","#926"]} -->

---8<---

```yaml
title: "Riehl 3.6: Configuration spaces of n points — the ordered configuration space, its symmetric-group action, and functoriality in finite sets and injections"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.6:example4, riehl:3.6:exviii]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.6, printed pp. 116–117 and p. 122 (PDF pp. 136–137 and p. 142)
- Items: `riehl:3.6:example4`, `riehl:3.6:exviii`

## Background
The ordered configuration space of `n` points in a space is the complement of the fat diagonal in the
`n`-fold power; the symmetric group permutes coordinates, and the unordered configuration space is the
colimit of that action. Ordered configurations are contravariantly functorial in finite sets and
injections, while unordered ones are not. See
[nLab: configuration space](https://ncatlab.org/nlab/show/configuration+space) and
[nLab: action](https://ncatlab.org/nlab/show/action).

## Current state in the library
Verified ABSENT (both), independently reproduced by the Phase-D verifier.

- `rg -i 'configuration|fat diagonal|PConf|Conf_'` finds nothing relevant (the single `configuration`
  hit is an unrelated English use in `Construction/Cospan/SCFA.v`).
- The sharper obstruction: **the diagram shape `BS_n` cannot even be written**, because nothing in-tree
  deloops a group or monoid into a one-object category — `rg -i 'one-object|deloop'` finds only
  `Structure/Monoidal.v:109-110` and `Theory/Bicategory/OneObject.v`, which deloop a *monoidal
  category* into a one-object *bicategory*, a different construction. `Structure/Monoid.v` is monoid
  *objects* in a monoidal category.
- There is no category of topological spaces (see #259), so the codomain of `PConf_•(X)` does not
  exist; `rg -in 'Topological|category Top|Instance Top'` returns only prose.
- The `Fin_mono` half is genuinely absent too: `Instance/FinSet.v` is skeletal `FinSet` with **all**
  functions between `Fin.t`s and carries no injections-only wide subcategory (`ls Instance/FinSet/`
  gives Classifier, Closed, Lawvere, Product, Pushout, Topos).
- The library is universe-polymorphic, so this is a genuine content gap, not an unformalizable one.

## Work to be done
Suggested module: `Instance/Top/Configuration.v`, over #259's `Top` and #220's delooping.

1. Build the wide subcategory `Fin_mono` of skeletal `FinSet` on the injections (donor:
   `Construction/Subcategory.v`; keep the decidability of `Instance/FinSet.v` intact), and the
   groupoid `Fin_iso` if the species work of `riehl:3.3:example5` has not already supplied it.
2. Define the fat diagonal in `X^n` and the ordered configuration space `PConf_n(X)` as its
   complement, with the subspace topology; prove it is a subspace, i.e. that the inclusion is the
   equalizer/subobject `Top` provides.
3. Define the `S_n`-action on `X^n` by permuting coordinates, prove it restricts to `PConf_n(X)`, and
   present it as a diagram `BS_n ⟶ Top`; define `Conf_n(X)` as its colimit. Cite `riehl:3.6:exi`'s
   orbit description for the underlying set, as Riehl's cross-reference does.
4. Exercise 3.6.viii: build the contravariant functor `PConf_•(X) : Fin_mono^op ⟶ Top` (an injection
   induces the corresponding coordinate projection between configuration spaces) and prove
   functoriality; then prove the negative half — this does **not** descend to a functor sending an
   `n`-element set to `Conf_n(X)` — by exhibiting the obstruction rather than describing it.

In-tree donors: #259's `Top`, #220's delooping, `Instance/FinSet.v`, `Construction/Subcategory.v`,
`Structure/Limit.v`, `Structure/Colimit`-side accessors in `Structure/Limit/Preservation.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.6, printed pp. 116–117, 122 (PDF pp. 136–137, 142)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `Fin_mono` is constructed as a wide subcategory of skeletal `FinSet`
- [ ] `PConf_n(X)` is built as a genuine subspace, and `Conf_n(X)` as a genuine `Colimit`
- [ ] The contravariant functoriality on injections is proved, and the failure to descend to unordered configurations is a proved obstruction, not prose
- [ ] Any use of a stdlib axiom in the `Top` layer is enumerated in the file header per docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory sense
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/Configuration.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Fin_mono.
Print Assumptions PConf.
Print Assumptions Conf_colimit.
Print Assumptions PConf_functorial.
```
Reviewer: statements match Riehl §3.6 Example 3.6.4 and Exercise 3.6.viii (printed pp. 116–117, 122);
the unordered configuration space must be a colimit over `BS_n`, not a hand-built quotient.

## Dependencies
Depends on: #259
Depends on: #220
Depends on: riehl:3.6:exi

<!-- catalog: {"ids":["riehl:3.6:example4","riehl:3.6:exviii"],"deps":["#259","#220","riehl:3.6:exi"]} -->

---8<---

```yaml
title: "Riehl 3.6: Fiber spaces, trivial fiber spaces, and the sections functors"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:3.6:exix]
deps_item_ids: [riehl:3.1:eq17]
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.6, printed p. 122 (PDF pp. 142–143)
- Items: `riehl:3.6:exix`

## Background
Following Grothendieck, a fiber space over a base is just a morphism into it; maps of fiber spaces are
commutative squares, so fiber spaces form the arrow category, and the fiber over a point is functorial
along such maps. Taking continuous sections defines a functor on the slice, and restricting to pullback
squares makes sections contravariantly functorial. See
[nLab: bundle](https://ncatlab.org/nlab/show/bundle) and
[Wikipedia: Fiber bundle](https://en.wikipedia.org/wiki/Fiber_bundle).

## Current state in the library
Verified ABSENT. The abstract shells exist; not one of the seven claims does.

- `Construction/Arrow.v:110` (`Arrow {C} := (Id[C] ↓ Id[C])`) is the arrow category, and its header
  already draws the commuting square that Riehl's "map of fiber spaces" is;
  `Construction/Slice.v` gives the slice. So the *shapes* are real.
- There is no `Top`, so none of the seven parts can be stated in the book's setting;
  `rg -in 'fiber space|fibre space|continuous section'` → 0 hits.
- **Same-name trap the verifier checked and confirmed**: `Theory/Morphisms.v:179`
  (`sections_are_monic : Section f → Monic f`) means "`Section`" in-tree is a *split monomorphism*,
  not a section of a bundle. Any new sections functor must avoid that name or qualify it.
- The fiber over a point is itself unformalized; it is filed as `riehl:3.1:eq17`.

## Work to be done
Suggested module: `Instance/Top/FiberSpace.v`, over #259's `Top`.

1. Set up the vocabulary over `Construction/Arrow.v` and `Construction/Slice.v`: a fiber space is an
   object of `Top^2`; `Top/B` is the (non-full) subcategory of maps over `B` with identity codomain
   component. Pick a name for bundle sections that does not collide with `Theory/Morphisms.v`'s
   `Section`.
2. Part (i): a map of fiber spaces `(g, f)` induces a canonical map from the fiber over `b ∈ B'` to
   the fiber over `f(b)`, in the fiber vocabulary of `riehl:3.1:eq17`; prove functoriality of that
   assignment.
3. Part (ii): the fibers of a product of fiber spaces are the products of the fibers. Part (iii): the
   fiber of a trivial fiber space `B × F → B` is isomorphic to `F`.
4. Part (iv): characterize the isomorphisms in `Top/B` between two trivial fiber spaces with a priori
   distinct fibers.
5. Parts (v)–(vii): prove that continuous sections define a functor `Π_B : Top/B ⟶ Set`; that on the
   non-full subcategory `Top^2_pb` of pullback squares the section assignment is contravariantly
   functorial; and the remaining clause of the exercise as printed. Each part must be a compiled
   statement; if the last clause proves out of reach, split it into a follow-up issue rather than
   admitting it.

In-tree donors: #259's `Top`, `Construction/Arrow.v`, `Construction/Slice.v`,
`Structure/Pullback.v`, `Theory/Morphisms/Stability.v`, the fiber vocabulary of `riehl:3.1:eq17`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.6, printed p. 122 (PDF pp. 142–143)); setoid discipline — `≈` on morphisms, never `=`
- [ ] All seven parts are compiled statements, or the residue is split into a follow-up issue with nothing admitted
- [ ] The bundle-section name does not collide with `Theory/Morphisms.v`'s split-mono `Section`
- [ ] Both sections functors are proved functorial (covariant on `Top/B`, contravariant on pullback squares)
- [ ] Any stdlib axiom used by the `Top` layer is enumerated in the header per docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory sense
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/Top/FiberSpace.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions fiber_space_fiber_map.
Print Assumptions trivial_fiber_space_fiber.
Print Assumptions sections_functor.
```
Reviewer: statements match Riehl §3.6 Exercise 3.6.ix (printed p. 122); confirm the sections functor
is on the *slice*, and the contravariant one on the *pullback-square* subcategory.

## Dependencies
Depends on: #259
Depends on: riehl:3.1:eq17

<!-- catalog: {"ids":["riehl:3.6:exix"],"deps":["#259","riehl:3.1:eq17"]} -->

---8<---

```yaml
title: "Riehl 3.6/3.7: Size obstructions — the large products Set does and does not admit, and the failure of cocompleteness for CAT"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.7:example4, riehl:3.6:remark9]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.6, printed pp. 118–119 (PDF pp. 138–139); §3.7, printed p. 124 (PDF p. 144)
- Items: `riehl:3.7:example4`, `riehl:3.6:remark9`

## Background
Completeness beyond small diagrams is delicate: `Set` has a product of *all* its objects (the empty
set forces the apex to be empty) but no product of all *non-empty* sets, by Cantor diagonalization;
and `CAT` has coproducts yet fails to be cocomplete, because a pushout can create a proper class of
morphisms between two objects. See [nLab: large category](https://ncatlab.org/nlab/show/large+category)
and [Wikipedia: Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem).

## Current state in the library
Verified ABSENT (both), independently reproduced by the Phase-D verifier, who explicitly considered
and **rejected** `OUT_OF_SCOPE`: the library is universe-polymorphic and already formalizes size
obstructions elsewhere (`Instance/Sets/Classifier.v`'s cross-universe treatment of the truth-value
setoid; `Structure/Complete.v:64-77` on Freyd's thinness theorem), so a universe-indexed `Cat_i`/`Cat_j`
pair and a failure-of-colimit statement are formalizable in principle.

- `rg -in 'product of all|large product|global choice|Cantor|diagonaliz'` yields only two prose
  mentions of Cantor (`Structure/Limit.v:109` on Scott domains, `Structure/Complete.v:69` inside the
  Freyd paragraph); no in-tree statement says which large families of sets admit products.
- The verifier checked the one route that could have made this PARTIAL: `Structure/Limit/Product.v`
  supplies `iprod` over a `DiscreteCat`, but `Complete`/`Cocomplete` occur **only** as hypothesis
  binders tree-wide (`Adjunction/SAFT.v:145-275`, `Adjunction/GAFT.v:193`,
  `Construction/Comma/Limit.v`, `Theory/Adamek/Corollaries.v`) and no category carries an instance, so
  no large product over `Sets` is ever formed, let alone shown to exist or fail.
- Local smallness is never a predicate: `rg -i 'locally small'` gives four background-prose hits
  (`Functor/Hom.v:18`, `Functor/Representable.v:29`, `Construction/Enriched.v:26`,
  `Structure/Complete.v:83`), so the *subject* of Remark 3.6.9 — a category of locally small
  categories, distinguished from `Cat` — cannot be named; `Instance/Cat.v:142` is a single
  universe-polymorphic `Cat`. Its *claim* is unavailable too: no `Cocomplete Cat`, no pushouts in
  `Cat`. `Instance/Cat.v:22` ("Cat is a large category, and so cannot be an object of itself") is the
  closest in-tree remark and is prose.

## Work to be done
Suggested module: `Structure/Complete/Size.v` and `Instance/Sets/LargeProduct.v`.

1. Fix the size vocabulary this needs, coordinating with #253: a `LocallySmall` predicate on a
   category (hom-setoids at the lower universe level), and the universe-indexed distinction between
   `Cat` at level `i` and `CAT` at level `j > i`. Disclose the universe discipline in the header the
   way `Structure/Complete.v:30-40` does.
2. Example 3.7.4, positive half: prove `Sets` admits the product of the family of *all* its objects —
   the apex is the initial (empty) setoid, and the cone is unique because a map into the empty setoid
   forces the domain empty. This is a genuine limit statement, so it must be an `IsALimit` witness
   over the discrete diagram, not a remark.
3. Example 3.7.4, negative half: prove the product of all *non-empty* sets does not exist. Riehl's
   argument uses Cantor diagonalization on `P(P)` together with global choice; formalize what the
   library can support and **disclose the choice principle used** in the header and against
   docs/AXIOMS.md — this is an `Instance/` layer result, so a documented use of stdlib choice is
   acceptable, an undocumented one is not.
4. Remark 3.6.9: build Riehl's counterexample — a locally small category `E` with a proper class of
   objects, each carrying a generating non-identity endomorphism and no morphisms between distinct
   objects — and prove that the pushout of `ob E → 1` along `ob E → E` would have a non-small
   endomorphism collection, so `CAT` does not contain that pushout. State the conclusion as the
   precise negative it is (no object of `CAT` satisfies the pushout universal property for this
   cospan), and record the coproducts-do-exist half separately.

In-tree donors: `Structure/Complete.v`, `Structure/Limit/Product.v`, `Instance/Discrete.v`,
`Instance/Sets.v`, `Instance/Sets/Classifier.v` (the in-tree cross-universe precedent),
`Instance/Cat.v`, #253, #423.

## Definition of Done
- [ ] Statement fidelity to the book (§3.6 printed pp. 118–119, §3.7 printed p. 124 (PDF pp. 138–139, 144)); setoid discipline — `≈` on morphisms, never `=`
- [ ] A `LocallySmall` predicate exists and the `Cat`/`CAT` universe distinction is expressible
- [ ] The positive half (a product of all sets exists) is an `IsALimit` witness
- [ ] The negative halves are proved negations, with the choice principle used disclosed and reconciled with docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory sense; any `Instance/`-layer axiom use is enumerated
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Complete/Size.v Instance/Sets/LargeProduct.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Sets_product_of_all.
Print Assumptions Sets_no_product_of_all_nonempty.
Print Assumptions CAT_not_cocomplete.
```
Reviewer: statements match Riehl §3.7 Example 3.7.4 and §3.6 Remark 3.6.9 (printed pp. 124, 118–119);
the negative results must be proved negations and their use of choice must be disclosed.

## Dependencies
Depends on: #253
Depends on: #423

<!-- catalog: {"ids":["riehl:3.7:example4","riehl:3.6:remark9"],"deps":["#253","#423"]} -->

---8<---

```yaml
title: "Riehl 3.7: The limit of the identity functor is the initial object"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.7:lem1, riehl:3.7:exi]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.7, printed p. 123 and p. 125 (PDF pp. 143–144 and p. 145)
- Items: `riehl:3.7:lem1`, `riehl:3.7:exi`

## Background
The summit of any cone over the identity functor is weakly initial, and if the leg indexed by the
summit is the identity then the cone is limiting and the summit is initial; conversely the identity
functor has a limit exactly when the category has an initial object. This is a naturally occurring
*large* limit, and its existence explains why a functor can preserve all limits without preserving
initial objects. See [nLab: initial object](https://ncatlab.org/nlab/show/initial+object) and
[nLab: limit](https://ncatlab.org/nlab/show/limit).

## Current state in the library
Verified ABSENT (both), independently reproduced by the Phase-D verifier.

- `rg -in 'limit of the identity|identity functor.*limit|weakly initial|WeaklyInitial'` and
  `rg -n 'Diagonal.*Id'` find nothing stating either clause.
- **Same-name trap, checked at source.** `Theory/WeaklyInitial.v:58`'s `WeaklyInitialFamily` is a
  *family* (`wif_index`, `wif_obj`, `wif_cover`), and `:89`'s `initial_from_weakly_initial` is
  Freyd's product-and-equalizer construction, taking three extra hypotheses that Riehl's Lemma 3.7.1
  does not need and never mentioning `Id`. There is no single-object `WeaklyInitial` predicate in-tree
  at all.
- Clause (ii) is an **iff**, and the in-tree material provides neither direction.
- For Exercise 3.7.i the verifier corrected the Phase-C log: the claim that "the library has no
  statement that any functor does or does not preserve initial/terminal objects" is too strong —
  `Functor/Structure/Terminal.v:43` defines `TerminalFunctor` and `:59-62` the notation
  `InitialFunctor F := @TerminalFunctor _ _ (F^op) _ _`, and that property *is* consumed as a
  hypothesis at `Theory/Lawvere/Model.v:57,72`. So the vocabulary for "preserves the initial object"
  exists; what is missing is the relation to limit preservation and any exhibited counterexample.
- A second naming defect worth fixing while in the area: the in-tree `InitialFunctor` notation
  (`Functor/Structure/Terminal.v:59`) collides with the standard meaning of "initial functor"
  (= cofinal), which #567/#568 will introduce.

## Work to be done
Suggested module: `Structure/Limit/Identity.v`.

1. Define a single-object `WeaklyInitial` predicate (at least one morphism to every object),
   distinct from `Theory/WeaklyInitial.v`'s family, and relate the two.
2. Prove clause (i): the summit of any cone `λ : Δl ⟹ Id_C` is weakly initial; and if `λ_l ≈ id_l`
   then the cone is limiting and `l` is initial. The argument is two lines from the cone equation
   `f ∘ λ_l ≈ λ_c`.
3. Prove clause (ii) as a genuine iff: `Limit Id_C` exists **iff** `C` has an initial object. Forward:
   apply the cone condition to `λ_l` as a morphism of the diagram to get `λ_c ∘ λ_l ≈ λ_c`, then use
   uniqueness of factorizations to force `λ_l ≈ id_l` and appeal to clause (i). Backward: the unique
   maps out of an initial object assemble into a cone whose component at the initial object is the
   identity, and any cone factors through it uniquely.
4. Exercise 3.7.i: state precisely why "there are functors preserving all limits without size
   restriction that do not preserve initial objects" does not contradict Lemma 3.7.1 — namely that
   the lemma's conclusion depends on the *identity* diagram of the source, which the functor does not
   carry to the identity diagram of the target. Give the explanation as a compiled statement about
   the two `Limit Id` witnesses, not as a comment. Riehl's own witnesses come from her Theorem 4.6.2,
   which is outside this chapter; if no in-tree witness is available, state the general obstruction
   and record the missing example in the file header rather than admitting anything.
5. While in the file, resolve the `InitialFunctor` naming collision at
   `Functor/Structure/Terminal.v:59` — either rename it (e.g. `PreservesInitial`) or add a header note
   reserving "initial functor" for the cofinality sense of #567.

In-tree donors: `Structure/Limit.v`, `Structure/Cone.v`, `Structure/Limit/Preservation.v`,
`Structure/Initial.v`, `Functor/Diagonal.v`, `Functor/Structure/Terminal.v`, `Theory/WeaklyInitial.v`.

## Definition of Done
- [ ] Statement fidelity to the book (§3.7, printed pp. 123, 125 (PDF pp. 143–145)); setoid discipline — `≈` on morphisms, never `=`
- [ ] A single-object `WeaklyInitial` predicate exists and is related to `Theory/WeaklyInitial.v`'s family
- [ ] Clause (ii) is proved in **both** directions
- [ ] Exercise 3.7.i's reconciliation is a compiled statement, or the missing witness is disclosed in the header with nothing admitted
- [ ] The `InitialFunctor` naming collision (`Functor/Structure/Terminal.v:59`) is resolved or explicitly reserved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Structure/Limit/Identity.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions cone_over_id_weakly_initial.
Print Assumptions limit_id_iff_initial.
```
Reviewer: statement matches Riehl §3.7 Lemma 3.7.1 and Exercise 3.7.i (printed pp. 123, 125); clause
(ii) is an iff and both directions must be present.

## Dependencies
None.

<!-- catalog: {"ids":["riehl:3.7:lem1","riehl:3.7:exi"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 3.8: The extended real line as a bicomplete poset — lim inf, lim sup, and sup-inf at most inf-sup"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:3.8:cor4, riehl:3.8:example6, riehl:3.8:remark5]
deps_item_ids: []
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.8, printed pp. 127–128 (PDF pp. 147–148)
- Items: `riehl:3.8:cor4`, `riehl:3.8:example6`, `riehl:3.8:remark5`

## Background
The extended real line is a complete lattice, hence a bicomplete thin category in which limits are
infima and colimits suprema; the canonical map from a colimit of limits to a limit of colimits then
specializes to the familiar analytic inequality, and lim inf and lim sup are iterated colimits and
limits of a doubly indexed sequence. See
[Wikipedia: Extended real number line](https://en.wikipedia.org/wiki/Extended_real_number_line),
[Wikipedia: Limit inferior and limit superior](https://en.wikipedia.org/wiki/Limit_inferior_and_limit_superior)
and [nLab: complete lattice](https://ncatlab.org/nlab/show/complete+lattice).

## Current state in the library
Verified ABSENT (all three), independently reproduced by the Phase-D verifier.

- The library imports no real numbers: `rg -ln 'Reals|R_scope|Rle'` returns only
  `Construction/Enriched.v`, and there only in header prose about Lawvere metric spaces (enrichment in
  `[0, ∞]`).
- There is no order-theoretic supremum or infimum: `rg -ni '\bsup\b|\binf\b'` returns only the journal
  abbreviation "Inf. Comput." and the identifier `Sup` in
  `Construction/{PROP,ColouredPROP}/Signature.v` (`SubSig`/`CSubSig`, signature inclusion).
- `Instance/Poset.v` and `Instance/Proset.v` contain only `Proset`, `Poset` and
  `LessThanEqualTo_Category` — no (co)limit is ever computed in a thin category, so even the
  "limits in a poset are meets" dictionary is prose (`Instance/Poset.v:50-51`).
- **Verifier log correction** (does not change the verdict): the Phase-C claim that
  `Structure/Complete.v`'s header "explicitly notes no concrete inhabitant is constructed in-tree" is
  false — the header discusses Freyd's thinness collapse, the universe ledger and the in-tree
  consumers. The underlying claim is nevertheless true and was independently re-verified: `Complete`
  and `Cocomplete` occur only as hypothesis binders anywhere in the tree, so no poset (or any other
  category) carries an instance.
- The canonical map `κ : colim lim → lim colim` that Corollary 3.8.4 specializes is itself absent; it
  is filed on #563.
- **Not out of scope**: the library has posets and universe polymorphism, so a poset-level
  `sup-inf ≤ inf-sup` is formalizable once `κ` exists.

## Work to be done
Suggested module: `Instance/ExtReal.v` (with the poset limit dictionary supplied by #422).

1. Construct the extended real line as a poset: either over Coq's `Reals` (documenting the stdlib
   axioms it drags in, per docs/AXIOMS.md — this is an `Instance/` layer) or over a
   constructively-friendlier carrier if the library prefers one. Adjoin `±∞` and prove the order is a
   complete lattice: every subset has an infimum and a supremum. Disclose the choice in the header.
2. Using the poset dictionary of #422 (limits are greatest lower bounds, colimits least upper
   bounds), conclude `Complete` and `Cocomplete` for the induced thin category — the library's first
   concrete bicompleteness witness for a poset; record it in docs/INHABITATION.md.
3. Corollary 3.8.4: instantiate the canonical map `κ` of #563 at this poset and read off
   `sup_{x∈X} inf_{y∈Y} f(x,y) ≤ inf_{y∈Y} sup_{x∈X} f(x,y)` for `f : X × Y → ℝ̄`. In a thin category
   the existence of `κ` *is* the inequality, so the deliverable is the specialization plus the
   readable corollary, not a new proof.
4. Example 3.8.6: define, for a sequence `x : ℕ → ℝ̄` regarded as a diagram on the discrete
   `ℕ × ℕ`, `lim inf` and `lim sup` as the two iterated (co)limits
   `colim_n lim_m x_{n+m}` and `lim_n colim_m x_{n+m}`; prove they agree with the classical formulas
   `sup_n inf_{m≥n} x_m` and `inf_n sup_{m≥n} x_m`, and derive `lim inf ≤ lim sup` from step 3.
   Prove the convergence criterion Riehl states: the sequence has a limit exactly when the inequality
   is an equality.
5. Remark 3.8.5: record, as a header note attached to the step-3 proof, that unwinding the categorical
   argument in the thin case gives exactly the analyst's proof (transitivity is composition). This is
   the one clause with no separate proof obligation.

In-tree donors: `Instance/Poset.v`, `Instance/Proset.v`, `Structure/Limit.v`, `Structure/Complete.v`,
#422, #563, #684 (order-theoretic completeness vocabulary).

## Definition of Done
- [ ] Statement fidelity to the book (§3.8, printed pp. 127–128 (PDF pp. 147–148)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The extended real line is proved a complete lattice, and `Complete`/`Cocomplete` for its thin category are actual instances
- [ ] `sup-inf ≤ inf-sup` is obtained by specializing `κ`, not by an independent analytic proof
- [ ] `lim inf` / `lim sup` are defined as iterated (co)limits and proved equal to the classical formulas, with the convergence criterion
- [ ] Any stdlib axiom pulled in by the real numbers is enumerated in the header and reconciled with docs/AXIOMS.md
- [ ] docs/INHABITATION.md updated with the first concrete bicomplete poset
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory sense
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/ExtReal.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions ExtReal_Complete.
Print Assumptions sup_inf_le_inf_sup.
Print Assumptions liminf_le_limsup.
```
Reviewer: statements match Riehl §3.8 Corollary 3.8.4, Example 3.8.6 and Remark 3.8.5 (printed
pp. 127–128); the inequality must be derived from the categorical `κ`, which is the whole point of the
corollary.

## Dependencies
Depends on: #422
Depends on: #563
Depends on: #684

<!-- catalog: {"ids":["riehl:3.8:cor4","riehl:3.8:example6","riehl:3.8:remark5"],"deps":["#422","#563","#684"]} -->

---8<---

```yaml
title: "Riehl 3.8: Coprime group orders — BG-indexed limits commute with BH-indexed colimits in Set"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:3.8:exii]
deps_item_ids: [riehl:3.2:example10, riehl:3.6:exi]
deps_pending: []
```

## Source
- Book: Emily Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy; folios are NOT the Dover/AMS print pagination)
- Section: §3.8, printed p. 129 (PDF p. 149)
- Items: `riehl:3.8:exii`

## Background
Limits and colimits rarely commute, but for groups of coprime order the fixed-point construction and
the orbit construction do: `BG`-indexed limits commute with `BH`-indexed colimits in sets whenever
`|G|` and `|H|` are coprime. See
[nLab: commutativity of limits and colimits](https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits)
and [nLab: action](https://ncatlab.org/nlab/show/action).

## Current state in the library
Verified ABSENT, doubly so, and independently reproduced by the Phase-D verifier.

- **No delooping.** The verifier enumerated every `Definition/Program Definition … : Category` in
  `Instance/` and `Construction/` (Adjoints, Cones, Tries, Vectors, Rel, Fun, `_0`, Adj, Free,
  FreeSyntax, ZX_Cat, Ens, EnsT, FinSet, Algs, Comp, Lambda, Sets, Fact, FAlg, Roof, Karoubi,
  DiscreteCat, Omega, Arrow, Product, Quotient, CMon, LessThanEqualTo_Category) and none is the
  one-object category `BG` of a group or monoid. `Construction/Cayley.v` is the Yoneda image of a
  category, not a delooping.
- No `G`-sets, no orbits or fixed points as (co)limits, and no arithmetic on group orders
  (`rg 'coprime|gcd|orbit|G-set'` → 0 hits).
- The ambient vocabulary this exercise instantiates — "shape-`I` limits commute with shape-`J`
  colimits" and the canonical map `κ` — is itself absent and is filed on #563.

## Work to be done
Suggested module: `Instance/GSet/Commutation.v`.

1. Over the fixed-point and orbit computations of `riehl:3.2:example10` and `riehl:3.6:exi`, and the
   canonical map `κ : colim_j lim_i F(i,j) ⟶ lim_i colim_j F(i,j)` of #563, state the commutation
   claim precisely for `I := BG`, `J := BH`, `C := Sets`: `κ` is an isomorphism for every
   `F : BG × BH ⟶ Sets`.
2. Formalize the coprimality hypothesis — finite `G`, `H` with `gcd(|G|, |H|) = 1` — with whatever
   finite-group cardinality machinery the `Instance/` layer adopts (this is the main non-categorical
   ingredient; keep it separate and reusable).
3. Prove the theorem. The standard argument averages over the coprime orders: for a `G × H`-set, the
   `H`-orbit map restricted to `G`-fixed points is a bijection onto the `G`-fixed points of the orbit
   set, because the two group actions can be separated using invertibility of `|H|` modulo `|G|`.
   Whatever route is taken, the deliverable is `IsIsomorphism κ` under the coprimality hypothesis, not
   a description.
4. Record in the header that this is an instance of a general phenomenon (Bergner–Joachimi–Lesh–…, the
   reference Riehl cites) and that only the coprime case is in scope here.

In-tree donors: the `G`-set (co)limit computations of `riehl:3.2:example10` and `riehl:3.6:exi`,
#563's `κ`, #220's delooping, `Instance/Sets.v`, `Instance/Sets/Coend.v` (quotient technique).

## Definition of Done
- [ ] Statement fidelity to the book (§3.8, printed p. 129 (PDF p. 149)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The commutation is stated as invertibility of the canonical map `κ` of #563, not as a bijection between two independently defined sets
- [ ] The coprimality hypothesis is a real hypothesis on the two group orders, and is genuinely consumed by the proof
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond documented `Instance/`-layer use per docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification
```bash
coqc -R . Category Instance/GSet/Commutation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions coprime_BG_BH_commute.
```
Reviewer: statement matches Riehl §3.8 Exercise 3.8.ii (printed p. 129); check that coprimality is
used, and that the conclusion is about the canonical comparison map.

## Dependencies
Depends on: #563
Depends on: riehl:3.2:example10
Depends on: riehl:3.6:exi

<!-- catalog: {"ids":["riehl:3.8:exii"],"deps":["#563","riehl:3.2:example10","riehl:3.6:exi"]} -->

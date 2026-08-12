title: "Awodey 6.2: Pos is cartesian closed — the componentwise product and the pointwise-ordered monotone function space"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.2:example4]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.2 "Cartesian closed categories", Example 6.4, printed pages 131–132 (PDF pages 140–141). Item covered: `awodey:6.2:example4`.

## Background

The category of posets and monotone maps is cartesian closed: the product carries the componentwise order, and the exponential is the set of monotone maps ordered pointwise, with evaluation and transposition inherited from the underlying functions. See [nLab: Pos](https://ncatlab.org/nlab/show/Pos) and [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

Nothing of this example exists, and its carrier is itself an open gap.

- The category of posets and monotone maps does not exist in-tree; it is the already-filed #641. `Instance/Poset.v:116` — `Definition Poset ... : Category := Proset P` — is a *single* poset read as a thin category (Awodey's other use of the word), and `Instance/Proset.v:33` likewise for preorders.
- Monotone maps exist only as `Record MonotoneMap (P Q : TwoPreorder)` at `Construction/Enriched/Two.v:175`, used solely by `EnrichedFunctor_Two_monotone` (`:183`); no `Category` is built on it, and no product or exponential of those preorders is ever formed.
- The two order-instance headers point at the missing object by name: `Instance/Poset.v:21` refers to `[Pos]` and `Instance/Proset.v:19` to `[Ord]` in the library's bracketed-identifier convention, and neither identifier exists anywhere in the tree (this dangling reference is already recorded as a library defect riding on #641).
- An enumeration of every `Closed` instance in the tree (`grep -rn 'exponent_obj' --include=*.v .`) yields `Sets`, `Coq`, `FinSet`, `Cat`, `Props`, `Rel`, `Comp`, `Lambda`, `AST` and the internal-product monoidal instance — none of them a category of ordered sets. Neither the componentwise product order nor the pointwise order on a monotone function space appears anywhere (`grep -rniE 'pointwise order'` → 0 hits).

## Work to be done

Suggested module: `Instance/Pos/Closed.v` (with the cartesian half in `Instance/Pos/Cartesian.v` if that keeps the files small), building on the `Pos` delivered by #641.

1. Give `Pos` a terminal object (the one-point poset) and binary products: the carrier is the set-level product, the order is componentwise, the projections are monotone, and the pairing of two monotone maps is monotone. Assemble `@Cartesian Pos` and `@Terminal Pos`, keeping `≈` on morphisms (equality of the underlying monotone maps, not of their monotonicity proofs).
2. Build the exponential: for posets `P`, `Q`, the carrier is the type of monotone maps `P → Q` with the pointwise order, which must be shown reflexive, transitive and antisymmetric — antisymmetry is where the poset (rather than preorder) hypothesis is used, and the file header should say so.
3. Prove evaluation `Q^P × P ⟶ Q` monotone. This is the first of the two checks Awodey singles out, and it is the one that genuinely uses both coordinates of the componentwise order.
4. Prove that the transpose of a monotone `f : X × P ⟶ Q` is monotone as a map `X ⟶ Q^P` (the second check), then discharge the exponential universal property and assemble `@Closed Pos _`. The equations themselves are inherited from the underlying functions, so the mathematical content is exactly the two monotonicity checks.
5. Record in the header that the exponential's carrier is a *sub*-order of the function space (only monotone maps), so that the §6.2 example and the ω-CPO refinement of §6.2 Example 6.5 share one shape.

In-tree donors: the `Pos` of #641, `Instance/Poset.v`, `Instance/Proset.v`, `Construction/Enriched/Two.v` (`MonotoneMap`), `Structure/Cartesian.v`, `Structure/Cartesian/Closed.v`, `Instance/Sets/Cartesian/Closed.v` (the closest existing template for a closed structure over a structured-set category).

## Definition of Done

- [ ] Statement fidelity to the book (§6.2 Example 6.4, printed pp. 131–132 (PDF pp. 140–141)); setoid discipline — `≈` on morphisms, never `=`
- [ ] `@Cartesian Pos` and `@Terminal Pos` proved, with the product order componentwise
- [ ] The exponential carrier is the monotone function space under the *pointwise* order, with antisymmetry proved (not merely assumed)
- [ ] Evaluation is proved monotone, and the transpose of a monotone map is proved monotone — the two checks the book isolates
- [ ] `@Closed Pos _` assembled and the exponential universal property discharged
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Pos/Closed.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Pos_Cartesian.
Print Assumptions Pos_Closed.
```
Reviewer: statement matches Awodey §6.2 Example 6.4 — the product order must be componentwise and the exponential order pointwise; check that the two monotonicity lemmas (evaluation, transpose) are proved rather than obtained by `Program` obligations left to a tactic that silently uses the wrong order.

## Dependencies

- Depends on: #641

<!-- catalog: {"ids":["awodey:6.2:example4"],"deps":["#641"]} -->

---8<---

title: "Awodey 6.2/6.6 Ex 4: ω-CPOs are cartesian closed, and strict ω-CPOs are not"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.2:example5, awodey:6:ex4]
deps_item_ids: [awodey:6.2:example4]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.2 Example 6.5, printed page 132 (PDF page 141), together with §6.6 Exercise 4, printed page 149 (PDF page 158) — the example states the result and explicitly defers its three verifications to the exercise, which additionally asks for the negative half. Items covered: `awodey:6.2:example5`, `awodey:6:ex4`.

## Background

Restricting the poset exponential to maps that are both monotone and ω-continuous gives a cartesian closed category of ω-CPOs, the basic function-space construction of denotational semantics; the strict variant, where maps must preserve the least element, is not cartesian closed. See [nLab: dcpo](https://ncatlab.org/nlab/show/dcpo) and [Wikipedia: Complete partial order](https://en.wikipedia.org/wiki/Complete_partial_order).

## Current state in the library

Absent, with the strongest possible negative evidence, and its two prerequisites are themselves open.

- `grep -rniE 'cpo' --include=*.v .` returns two hits, both prose in `Structure/Monoidal/Traced.v:66,93` ("pointed cpos" cited as an example of a traced category). `dcpo`, `directed complete`, `chain.complete`, `omega.continuous`, `Scott.continuous`, `least upper bound`, `supremum` and `lub` each return zero code hits; no file in the tree has `cpo` or `domain` in its name.
- The ω-CPO objects and the continuity predicate are the already-filed #675, which also builds the category and its forgetful functor to the category of posets.
- The ambient category of ordered sets is #641, and its cartesian closed structure is the companion issue for §6.2 Example 6.4 — the present example is a *restriction* of that one, so it should reuse its exponential rather than rebuild it.
- The chain shape exists (`Instance/Omega.v:72`, `Omega` on `nat` with the `le_t` order), and the preservation vocabulary exists (`Structure/Limit/Preservation.v`), but nothing connects "preserves ω-colimits" to "preserves chain suprema".

## Work to be done

Suggested module: `Instance/CPO/Closed.v`, plus a short `Instance/CPO/Strict.v` for the negative half.

1. Products: the componentwise order on a product of ω-CPOs is again an ω-CPO (suprema are computed coordinatewise), the projections and pairings are continuous; assemble `@Cartesian ωCPO` and `@Terminal ωCPO`.
2. Exponential carrier: the monotone *and* continuous maps `P → Q` with the pointwise order. Prove the three facts Awodey leaves to the reader, each stated as its own lemma: (a) that carrier is an ω-CPO (the supremum of a chain of continuous maps is the pointwise supremum, and it is continuous — the interchange-of-suprema argument); (b) evaluation is continuous; (c) the transpose of a continuous map is continuous.
3. Assemble `@Closed ωCPO _`. Because the underlying equations are those of the poset exponential, the file should *import* the §6.2 Example 6.4 structure and add only the continuity layer, disclosing that split in the header.
4. Negative half: define strict ω-CPOs (a least element as data, with maps required to preserve it) and prove the category is not cartesian closed. The cleanest in-tree route is the structural obstruction rather than an ad-hoc counterexample: in a strict setting the one-point ω-CPO is both initial and terminal, and a cartesian closed category with a zero object is trivial (every object is isomorphic to the initial one, via `Structure/BiCCC.v:208` `prod_zero_l`), while two non-isomorphic strict ω-CPOs plainly exist. State the conclusion as a proved negation, not a remark.
5. Keep all suprema as *data* (an operation plus the upper-bound and least-upper-bound clauses), matching the choice-free convention that #675 adopts.

In-tree donors: the ω-CPO development of #675, the `Pos` cartesian closed structure of §6.2 Example 6.4, `Instance/Omega.v`, `Structure/Cartesian/Closed.v`, `Structure/BiCCC.v` (`prod_zero_l`, `prod_zero_r`), `Structure/Initial.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.2 Example 6.5, printed p. 132 (PDF p. 141); §6.6 Exercise 4, printed p. 149 (PDF p. 158)); setoid discipline — `≈` on morphisms, never `=`
- [ ] All three verifications the book defers are proved as separate named lemmas: the function space is an ω-CPO, evaluation is continuous, the transpose is continuous
- [ ] `@Cartesian ωCPO`, `@Terminal ωCPO` and `@Closed ωCPO _` assembled
- [ ] The strict variant is defined and its failure of cartesian closure is a *proved theorem*, not a comment
- [ ] Suprema are data, so no choice principle is introduced
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/CPO/Closed.v Instance/CPO/Strict.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CPO_Closed.
Print Assumptions CPO_exp_is_CPO.
Print Assumptions CPO_eval_continuous.
Print Assumptions StrictCPO_not_Closed.
```
Reviewer: statement matches Awodey §6.2 Example 6.5 and §6.6 Exercise 4 — the exponential must contain only the continuous maps (not all monotone maps), and the negative half must be a proved impossibility with the non-triviality hypothesis exhibited concretely.

## Dependencies

- Depends on: #675
- Depends on: awodey:6.2:example4

<!-- catalog: {"ids":["awodey:6.2:example5","awodey:6:ex4"],"deps":["#675","awodey:6.2:example4"]} -->

---8<---

title: "Awodey 6.2/6.6 Ex 3: The unit of the currying adjunction (− × B) ⊣ (−)^B, and the global points of an exponential"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.2:construction-eta, awodey:6:ex3]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.2, the unnumbered construction of the arrow η as the transpose of an identity and the resulting formula for computing transposes, printed pages 135–136 (PDF pages 144–145); together with §6.6 Exercise 3, printed page 149 (PDF page 158). Items covered: `awodey:6.2:construction-eta`, `awodey:6:ex3`.

## Background

The transpose of the identity on a product is the unit of the adjunction between product and exponential, and every transpose factors through it via the exponentiation functor; the same adjunction, evaluated at the terminal object, identifies the global points of an exponential with arrows out of the exponent. See [nLab: exponential object](https://ncatlab.org/nlab/show/exponential+object) and [Wikipedia: Currying](https://en.wikipedia.org/wiki/Currying).

## Current state in the library

The *equations* are in-tree in a stronger form than the book states them; the *packaging* is not.

- `Structure/Cartesian/Closed.v:177` — `Corollary curry_comp {x y z w} (f : z ~> w) (g : x × y ~> z) : curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g`. Instantiating `g := id[x × y]` gives exactly the book's factorisation of a transpose through the exponentiation functor, so that half is a special case of what is already proved.
- `Structure/Cartesian/Closed.v:201` — `Theorem curry_id {x y z} (f : x ~> y) : curry (@id _ (y × z)) ∘ f ≈ curry (first f)`. This is the only occurrence of the arrow in question anywhere in the tree, and it occurs as the anonymous subterm `curry (@id _ (y × z))`: no definition, no name, no notation (`grep -rnE 'curry id|curry \(id|curry \(@id' --include=*.v .` returns only that line).
- The counit *is* a named definition — `eval {x y} : y^x × x ~> y := uncurry id` at `Structure/Cartesian/Closed.v:75` — so the asymmetry is purely one of packaging.
- No `Adjunction` instance for the product/exponential pair exists: neither `(− × y)` nor `(−)^y` is built as a `Functor` object anywhere, so `Theory/Adjunction.v`'s unit is unavailable here, and searches for a closed-structure adjunction return only prose. `Functor/Hom/Internal.v:40` supplies the two-variable internal-hom bifunctor, not the one-variable right adjoint.
- Exercise 3's bijection is not stated: `Structure/Cartesian/Closed.v:51` gives `exp_iso {x y z} : x × y ~> z ≊ x ~> z^y`, which at `x := 1` yields `(1 × x ~> y) ≊ (1 ~> y^x)`, and `Structure/Cartesian.v:451` gives `prod_one_l : 1 × x ≅ x`; transporting one along the other — and the naturality of the resulting bijection — is never carried out, and no lemma in-tree names the global points of an exponential.

## Work to be done

Suggested module: `Structure/Cartesian/Closed/Adjunction.v`.

1. Name the arrow: `Definition exp_unit {x y} : x ~> (x × y)^y := curry id`, with a `Proper` instance if needed, and prove the book's computation rule in the shape it states it — the transpose of `f : z × y ~> w` equals `fmap` of `f` under the exponentiation functor composed with the unit. This requires identifying `curry (f ∘ eval)` with the functorial action, an `≈`-rewrite (not a definitional equality) that should be its own lemma.
2. Build the two functors `(− × y) : C ⟶ C` and `(−)^y : C ⟶ C` as `Functor` objects (the second is the one-variable restriction of `Functor/Hom/Internal.v:40`), and assemble the genuine `Adjunction` witness for the pair, exhibiting the named unit and `eval` as counit and proving both triangle identities. This is the reusable artifact the rest of the chapter's material leans on.
3. Prove the exercise: a bijection between arrows `x ~> y` and global points `1 ~> y^x`, natural in both arguments, obtained by transporting `exp_iso` along `prod_one_l`. State it as an isomorphism of hom-setoids so that the naturality is available to callers, and check it against the in-tree representability vocabulary (`Tools/Represented.v:31`).
4. Add the `Sets` sanity computation the book gives for the unit (its value at a point is the pairing map), so the abstract arrow has a concrete reading.

In-tree donors: `Structure/Cartesian/Closed.v` (`curry`, `uncurry`, `eval`, `curry_comp`, `curry_id`, `ump_exponents`), `Structure/Cartesian.v` (`first`, `second_id`, `prod_one_l`), `Functor/Hom/Internal.v`, `Theory/Adjunction.v`, `Instance/Sets/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.2, printed pp. 135–136 (PDF pp. 144–145); §6.6 Exercise 3, printed p. 149 (PDF p. 158)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The unit is a *named definition*, and the book's factorisation of a transpose through it is proved in that shape
- [ ] A real `Adjunction` witness for the product/exponential pair exists, with both functors built as `Functor` objects and both triangle identities proved
- [ ] The global-points bijection is proved and shown natural in both arguments
- [ ] LIBRARY DEFECT: `Structure/Cartesian/Closed.v:34` and `:47`–`:50` assert that the class field `exp_iso` is "natural in x, y and z" and that "naturality recovers the substitution laws below", but the class carries no naturality requirement at all — which is precisely why `ump_exponents'` (`:61`) has to be an asserted field rather than a derived lemma. Either supply the naturality (it now follows from the adjunction built here) or correct those comments to say that the class asserts the beta law separately
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a real product/exponential adjunction is flagship-level for the cartesian-closed spine)

## Verification

```bash
coqc -R . Category Structure/Cartesian/Closed/Adjunction.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions exp_unit.
Print Assumptions curry_via_unit.
Print Assumptions Product_Exponential_Adjunction.
Print Assumptions exp_global_points.
```
Reviewer: statement matches Awodey §6.2's construction — the unit must be *defined* (not inlined), the factorisation must go through the exponentiation functor's action, and the Exercise 3 bijection must be natural, not merely pointwise.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:6.2:construction-eta","awodey:6:ex3"],"deps":[]} -->

---8<---

title: "Awodey 6.3: Heyting algebras — the class, the poset exponential UMP, and negation"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:def7, awodey:6.3:remark-ha-ump-equivalence, awodey:6.3:def-heyting-negation]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3 "Heyting algebras", Definition 6.7 and the two remarks that immediately follow it — the equivalence of the Heyting condition with the exponential universal property in the poset case, and the definition of negation as implication into the bottom element — printed pages 137–138 (PDF pages 146–147). Items covered: `awodey:6.3:def7`, `awodey:6.3:remark-ha-ump-equivalence`, `awodey:6.3:def-heyting-negation`.

## Background

A Heyting algebra is a bounded lattice in which each pair of elements has a relative pseudo-complement, equivalently a poset that is bicartesian closed when read as a thin category; negation is implication into the bottom element. See [nLab: Heyting algebra](https://ncatlab.org/nlab/show/Heyting+algebra) and [Wikipedia: Heyting algebra](https://en.wikipedia.org/wiki/Heyting_algebra).

## Current state in the library

The categorical *target* of the definition is fully present; the order-theoretic notion, the bridge, and negation are not.

- There is no `HeytingAlgebra` class: `grep -rniI --include='*.v' 'Heyting'` returns seven hits, every one of them prose (`Structure/Topos.v:81`, `Theory/Sheaf.v:85`, `Theory/Lawvere.v:87`, `Instance/Two.v:86`, and the `Instance/Props.v` header at `:15`, `:17`, `:27`).
- The structure is available only unbundled, as the simultaneous assumption of `@Terminal C`, `@Initial C`, `@Cartesian C`, `@Cocartesian C` and `@Closed C _` — the pattern `Structure/Bicartesian.v:24` and `Structure/BiCCC.v:26` each adopt deliberately, both headers stating that the file introduces no class of its own.
- It is instantiated exactly once at a thin category: `Instance/Props.v:39` (`Props`), `:69` (`Props_Cartesian`), `:94` (`Props_Closed`, with `exponent_obj := Basics.impl`) plus the terminal and initial instances. The file's own header at `:27` calls the result a Heyting **pre**algebra — its hom-setoid is the trivial `equiv _ _ := True`, so antisymmetry is never imposed and the objects are not a poset.
- The bridge Awodey's remark asserts is missing in both directions. Thinness is not available as a hypothesis anywhere: there is no `Thin` class or subsingleton-homset predicate (`rg -n "Definition .*[Tt]hin|Class .*Thin"` → 0 hits); it exists only as the per-instance `Lemma two_thin {x y : TwoObj} (f g : TwoHom x y) : f = g` (`Instance/Two/Monoidal.v:26`, used at `:87` and `:102`) for the walking arrow, which carries no `Closed` instance, and definitionally as the trivial hom-setoids of `Instance/Proset.v:38` and `Instance/Props.v:45`. So "a family of two-sided entailments yields a `Closed` instance" is re-done ad hoc inside `Props_Closed` and is invisible there: the trivial setoid silently discharges every obligation.
- `Instance/Poset.v:116` defines a poset as a thin category but nothing in the tree connects it to `Cartesian`/`Cocartesian`/`Closed` (the file requires only `Lib`, `Theory.Category` and `Instance.Proset`).
- Negation is absent: the only exponential-with-bottom symbol in the tree is `Structure/BiCCC.v:236`, `exp_zero : x^0 ≅ 1`, which is the exponential *out of* the initial object — the opposite of the object the book names. All `negation`/`neg` hits are `pneg`, the additive inverse on hom commutative monoids (`Structure/Additive.v:41`), or prose.

## Work to be done

Suggested modules: `Structure/HeytingAlgebra.v` for the class and its theory, `Structure/Thin.v` (or a section of the former) for the thinness bridge.

1. Introduce a `Thin` predicate on a category — any two parallel arrows are `≈` — and prove the enabling lemma the whole section rests on: given a thin category with binary products, supplying only the two directions of the transposition condition yields a full `@Closed` instance, with `ump_exponents'` discharged automatically. This is the content of the book's remark, and it turns the ad-hoc collapse inside `Props_Closed` into a reusable constructor.
2. Define `HeytingAlgebra` as a poset (reflexive, transitive, antisymmetric order) with top, binary meet, bottom, binary join and a relative pseudo-complement satisfying the two-sided condition, in the order-theoretic surface syntax rather than as five separate categorical class assumptions.
3. Prove the round trip against the categorical presentation: a Heyting algebra, read as a thin category, carries `Terminal`, `Initial`, `Cartesian`, `Cocartesian` and `Closed`; conversely a thin category with all five, and with antisymmetry, is a Heyting algebra. This is where the deliberate non-bundling of `Structure/BiCCC.v` is respected — the class lives on the order side, and the theorem is the bridge.
4. Define negation as implication into the bottom element, and prove the always-valid intuitionistic facts: `a ≤ ¬¬a`, `a ∧ ¬a = 0`, and the contrapositive monotonicity of negation. The *failure* of the converse inequality and of excluded middle needs a counterexample and is deliberately deferred to the companion issue for §6.3 Example 6.10.
5. Re-found `Instance/Props.v` on the new vocabulary where it is honest to do so, or add a header note recording precisely why it is a Heyting *pre*algebra (its hom-setoid is trivial, so antisymmetry is vacuous) and how it relates to the class introduced here.

In-tree donors: `Instance/Props.v`, `Instance/Poset.v`, `Instance/Proset.v`, `Instance/Two/Monoidal.v` (`two_thin` as the pattern to generalise), `Structure/Cartesian/Closed.v`, `Structure/Bicartesian.v`, `Structure/BiCCC.v`, `Structure/Distributive.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.3 Definition 6.7 and the following two remarks, printed pp. 137–138 (PDF pp. 146–147)); setoid discipline — `≈` on morphisms, never `=`
- [ ] A `Thin` predicate exists, and the constructor "thin + products + two-sided transposition ⇒ `Closed`" is proved as a reusable lemma, not re-done per instance
- [ ] `HeytingAlgebra` is a named class stated in order-theoretic syntax, with antisymmetry present (a poset, not a preorder)
- [ ] Both directions of the bridge to the bicartesian-closed thin-category presentation are proved
- [ ] Negation is defined as implication into the bottom element, with `a ≤ ¬¬a` proved
- [ ] `Instance/Props.v` is either re-founded on the new class or its prealgebra status is documented against it
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a Heyting-algebra spine is flagship-level: the topos and sheaf headers already promise it in prose)

## Verification

```bash
coqc -R . Category Structure/HeytingAlgebra.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions HeytingAlgebra.
Print Assumptions thin_closed_of_transposition.
Print Assumptions HeytingAlgebra_BiCCC.
Print Assumptions BiCCC_thin_HeytingAlgebra.
Print Assumptions hey_not_not.
```
Reviewer: statement matches Awodey §6.3 Definition 6.7 — all three clauses (finite meets, finite joins, exponentials) must be present, the exponential clause must be the two-sided condition, and the poset (antisymmetry) hypothesis must be genuinely used in the bridge rather than quietly dropped to a preorder.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:6.3:def7","awodey:6.3:remark-ha-ump-equivalence","awodey:6.3:def-heyting-negation"],"deps":[]} -->

---8<---

title: "Awodey 6.3: Complete lattices — meets give joins, and the infinite distributive law as the Heyting criterion"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:remark-complete-iff-cocomplete, awodey:6.3:prop9]
deps_item_ids: [awodey:6.3:def7]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3, Definition 6.8 with the remark inside it that completeness and cocompleteness coincide for posets (left to the reader), and Proposition 6.9, printed pages 137–138 (PDF pages 146–147). Items covered: `awodey:6.3:remark-complete-iff-cocomplete`, `awodey:6.3:prop9`.

## Background

A poset with all set-indexed meets automatically has all set-indexed joins (a join is the meet of the upper bounds), and a complete lattice is a Heyting algebra exactly when meet distributes over arbitrary joins — the frame condition, with implication defined as the join of everything whose meet with the antecedent is below the consequent. See [nLab: complete lattice](https://ncatlab.org/nlab/show/complete+lattice) and [nLab: frame](https://ncatlab.org/nlab/show/frame).

## Current state in the library

Neither statement, nor the order-theoretic vocabulary either needs.

- `Cocomplete` occurs six times tree-wide: `Structure/Complete.v:22,32,99,119` (the definition and its header, which records only the definitional duality `Cocomplete C = Complete C^op`) and `Theory/Adamek/Corollaries.v:51,61` (a hypothesis consumed at the ordinal ω). Nothing relates `Complete` to `Cocomplete` in either direction, and the duality that *is* recorded is not this remark — Awodey's claim is the non-dual poset fact that all meets yield all joins in the *same* poset.
- No order-theoretic completeness exists: `upper bound`/`lower bound` has one prose hit (`Instance/Poset.v:51`), `complete lattice` two prose hits (`Instance/Poset.v:93`, `Structure/Complete.v:71`), and `supremum`/`infimum`/`lub` none. No join is ever constructed as a meet of upper bounds.
- No infinitary distributivity: `infinite distributive` returns zero hits, and the only distributivity in-tree is finite — `Structure/Distributive.v:44`–`:49` (`distr_prod_coprod` binary and `distr_zero` nullary) and `Structure/BiCCC.v:46,90`.
- No frame or locale notion: `locale` returns zero hits and every `frame` hit is either the evaluation-context datatype of `Instance/Lambda/Full.v` or the English word.
- The forward direction is not even available as an instance of the library's adjoint-preservation machinery: `Adjunction/Continuity.v:222` has `left_adjoint_preserves_colimits`, but no adjunction is ever built from a `Closed` instance (`Structure/Cartesian/Closed.v:34,47` mentions the adjunction only in prose — a real witness is the deliverable of the §6.2 currying-adjunction issue). The converse construction, implication as a join over a comprehension, has no in-tree counterpart at all.

## Work to be done

Suggested module: `Structure/Lattice/Complete.v` (with the frame material in `Structure/Frame.v` if it grows).

1. Define a complete poset order-theoretically: an operation taking an arbitrary indexed family to its meet, together with the lower-bound and greatest-lower-bound clauses as data (no choice principle). Do the same for joins, and keep both notions available so the equivalence below is a theorem rather than a definition.
2. Prove the deferred remark: a poset with all set-indexed meets has all set-indexed joins, constructing a join as the meet of the family of upper bounds, and the dual. State it as a construction (the join operation is produced), not merely as an existence claim, so downstream code can compute with it.
3. Prove Proposition 6.9 forward: in a complete lattice that is a Heyting algebra, meet distributes over arbitrary joins. The clean argument is that meeting with a fixed element is a left adjoint, so it preserves joins — this is where the currying adjunction of the §6.2 issue pays off, and the proof should be routed through the general preservation result rather than redone by hand if that adjunction has landed.
4. Prove the converse: given the infinite distributive law, define implication as the join of all elements whose meet with the antecedent lies below the consequent, and verify the two-sided Heyting condition. Both halves of Awodey's chain of inequalities are short once the distributive law is available as a rewrite.
5. Name the resulting structure (a frame / complete Heyting algebra) and record in the header that this is the point-free counterpart of a topology, so the companion issue for §6.3 Example 6.10 can instantiate it.
6. Optionally connect to the categorical reading — meets in a poset are products in its thin category — reusing the dictionary of #422 rather than restating it.

In-tree donors: the Heyting-algebra class of the §6.3 Definition 6.7 issue, `Instance/Poset.v`, `Instance/Proset.v`, `Structure/Complete.v`, `Structure/Distributive.v`, `Adjunction/Continuity.v`, `Structure/Limit/Product.v` (`iprod` as the indexed-product precedent for arbitrary index types).

## Definition of Done

- [ ] Statement fidelity to the book (§6.3 Definition 6.8's remark and Proposition 6.9, printed pp. 137–138 (PDF pp. 146–147)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Completeness and cocompleteness of a poset are proved equivalent, with the join *constructed* from meets and dually
- [ ] Both directions of the Heyting-iff-infinitely-distributive criterion are proved
- [ ] The implication of the converse direction is defined by the join over the comprehension, and the two-sided condition is verified
- [ ] Suprema/infima are data, so no choice principle is introduced
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Lattice/Complete.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions complete_iff_cocomplete.
Print Assumptions frame_of_complete_heyting.
Print Assumptions complete_heyting_of_frame.
```
Reviewer: statement matches Awodey §6.3 Proposition 6.9 — the distributive law must be the infinitary one (over an arbitrary index type, not a finite fold), and the converse must *define* implication by the stated join rather than assume it.

## Dependencies

- Depends on: awodey:6.3:def7

<!-- catalog: {"ids":["awodey:6.3:remark-complete-iff-cocomplete","awodey:6.3:prop9"],"deps":["awodey:6.3:def7"]} -->

---8<---

title: "Awodey 6.3: Powersets and open-set lattices as complete Heyting algebras, and the failure of the Boolean laws"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:example10, awodey:6.3:remark-ha-not-boolean]
deps_item_ids: [awodey:6.3:def7, awodey:6.3:prop9]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3, Example 6.10 and the remark that follows it on the intuitionistic character of Heyting algebras, printed page 138 (PDF page 147). Items covered: `awodey:6.3:example10`, `awodey:6.3:remark-ha-not-boolean`.

## Background

Powersets and the open-set lattice of a topological space are the motivating complete Heyting algebras, and the latter is where intuitionism becomes visible: negation is the interior of the complement, so double negation and excluded middle both fail. See [nLab: locale](https://ncatlab.org/nlab/show/locale) and [Wikipedia: Heyting algebra](https://en.wikipedia.org/wiki/Heyting_algebra).

## Current state in the library

Nothing of either example, and no topology at all.

- The powerset is never constructed as an ordered structure. The nearest candidate is a same-name trap: `Instance/Ens.v:65` defines `EnsT (T : Type)` with objects `Ensemble T` but homs `{ f : T → T | ∀ x, x ∈ A ↔ f x ∈ B }` — endofunctions with `A = f⁻¹(B)`, not inclusions — so it is neither thin nor the inclusion order and carries no cartesian or closed structure. `Structure/Topos.v:75` and `Instance/FinSet/Topos.v` supply the internal power *object* `Pow a := Ω ^ a`, which carries no order structure. The powerset-as-cartesian-closed-lattice half is the already-filed #389.
- No topological space is ever defined: `open subset` returns zero hits, and every `topolog` hit is Grothendieck-topology or algebraic-topology prose. The category of topological spaces is the already-filed #259.
- The subobject reading is prose only: `Theory/Subobject.v` carries the setoid (`:33`) and the factorisation preorder `sub_le` (`:59`) with reflexivity and transitivity, and `grep -n 'meet\|join\|lattice\|Heyting' Theory/Subobject.v` returns zero hits, so `Structure/Topos.v:81`'s sentence that subobjects form a Heyting algebra is background prose, not a construction.
- The failure statements are not expressible today: `double negation`, `not not` and `tertium` all return zero hits; the single `excluded middle` hit is `Structure/Topos.v:82`, inside a header essay, with no formal statement, independence witness or counterexample; there is no topological interior operator (`interior` has two unrelated hits) and no Boolean-algebra class against which the non-implication could be phrased (the class itself is the already-filed #653).

## Work to be done

Suggested modules: `Instance/Powerset/Heyting.v` and `Instance/Top/Opens.v`.

1. Powerset: build the powerset of a type as a poset under inclusion, exhibit arbitrary meets and joins (intersections and unions), verify the infinite distributive law, and obtain the complete Heyting algebra by the criterion of the §6.3 Proposition 6.9 issue rather than by re-deriving implication by hand. Reconcile with #389, which delivers the same carrier's cartesian closed structure: one of the two should be derived from the other, not duplicated.
2. Open sets: given a topological space (from #259), build the lattice of opens — closed under finite intersections and arbitrary unions — and obtain the frame structure the same way. Note in the header that the meet of an infinite family of opens is *not* the intersection, which is exactly why the lattice is a frame rather than a complete Boolean algebra.
3. Negation as interior: prove that in the open-set lattice, the negation supplied by the Heyting structure is the interior of the set-theoretic complement. This is the identification that makes the counterexample legible.
4. The failure: exhibit a concrete space and an open set for which double-negation elimination fails, and one for which excluded middle fails, as *proved negations*. Awodey's witness is an interval with a punctured open subinterval; any space with a non-regular open works, and the reviewer should be able to see the chosen witness computed.
5. Record the resulting general statement — every Boolean algebra is a Heyting algebra, but not conversely — with the forward direction pointing at #389/#653 and the converse being the counterexample proved here.

In-tree donors: the Heyting class and negation of the §6.3 Definition 6.7 issue, the frame criterion of the §6.3 Proposition 6.9 issue, `Instance/Ens.v` (for the `Ensemble` carrier only), `Theory/Subobject.v`, `Structure/Topos.v`, plus `Top` from #259 and the Boolean algebras of #653.

## Definition of Done

- [ ] Statement fidelity to the book (§6.3 Example 6.10 and the following remark, printed p. 138 (PDF p. 147)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The powerset is a complete Heyting algebra, obtained through the infinite-distributivity criterion, and reconciled with the cartesian closed structure of #389 (no duplicate construction)
- [ ] The open-set lattice of a topological space is a frame, with the header disclosing that infinite meets are interiors of intersections
- [ ] Negation in the open-set lattice is proved to be the interior of the complement
- [ ] The failure of double-negation elimination and of excluded middle is proved on a concrete witness, not asserted
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md; any classical assumption used for the topological witness is confined and enumerated
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Powerset/Heyting.v Instance/Top/Opens.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Powerset_CompleteHeyting.
Print Assumptions Opens_Frame.
Print Assumptions opens_neg_is_interior_complement.
Print Assumptions opens_not_not_fails.
```
Reviewer: statement matches Awodey §6.3 Example 6.10 — the powerset claim is *completeness*, not merely cartesian closure, and the counterexample must be a proved failure on an exhibited space, with the interior identification available to justify it.

## Dependencies

- Depends on: #389
- Depends on: #259
- Depends on: awodey:6.3:def7
- Depends on: awodey:6.3:prop9

<!-- catalog: {"ids":["awodey:6.3:example10","awodey:6.3:remark-ha-not-boolean"],"deps":["#389","#259","awodey:6.3:def7","awodey:6.3:prop9"]} -->

---8<---

title: "Awodey 6.3: The full IPC entailment calculus and the Lindenbaum–Tarski Heyting algebra"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:def-ipc, awodey:6.3:construction-lindenbaum-tarski, awodey:6.3:prop11, awodey:6.3:remark-positive-fragment]
deps_item_ids: [awodey:6.3:def7]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3: the six-rule entailment system for intuitionistic propositional calculus (printed pp. 138–139, PDF pp. 147–148); the statement that the positive fragment corresponds to cartesian closed posets and full IPC to Heyting algebras (printed p. 140, PDF pp. 149–150); the Lindenbaum–Tarski algebra of a calculus (printed p. 141, PDF pp. 150–151); and Proposition 6.11, the completeness of IPC for Heyting-algebra models (printed p. 141, PDF p. 150). Items covered: `awodey:6.3:def-ipc`, `awodey:6.3:construction-lindenbaum-tarski`, `awodey:6.3:prop11`, `awodey:6.3:remark-positive-fragment`.

## Background

Intuitionistic propositional logic can be presented by entailments closed under six rules, and quotienting formulas by interderivability yields the Lindenbaum–Tarski algebra — the Heyting algebra in which a formula is provable exactly when its class is the top element, whence completeness. See [nLab: Lindenbaum-Tarski algebra](https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra) and [Wikipedia: Lindenbaum–Tarski algebra](https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra).

## Current state in the library

The positive fragment of this development — a propositional syntax with a derivability relation, presented as a thin cartesian closed category — is already filed as #390 for Mac Lane §IV.6 Exercise 2, whose scope is explicitly the conjunction/implication/truth fragment. Everything this section adds beyond that fragment is missing:

- No entailment relation at all. The six rules exist in-tree only as *constructors of a proof-relevant term calculus*: `Instance/AST.v:72` declares `Hom : Obj → Obj → Set` over the formula formers of `:45`, with `Id`/`Compose` (`:73`–`:74`) as reflexivity and transitivity, `One'` (`:76`) and `Zero'` (`:85`) as the two unit rules, `Fork`/`Exl`/`Exr` (`:78`–`:80`) as the meet rule, `Merge`/`Inl`/`Inr` (`:87`–`:89`) as the join rule and `Curry`/`Uncurry` (`:82`–`:83`) as the implication rule, assembled as `AST : Category` at `:127`. That is the Curry–Howard proof-term version, not a relation between formulas.
- The equational theory of that calculus is not generated by the rules: `AST`'s hom-setoid (`Instance/AST.v:131`–`:141`) identifies two terms when they agree under *every* interpretation into a bicartesian closed category, i.e. semantically. So no quotient by interderivability exists anywhere.
- No falsum/disjunction entailment layer, no Lindenbaum–Tarski quotient, no completeness statement: `IPC`, `turnstile`, `modus ponens` and `sequent` all return zero hits; `entailment` has two prose hits (`Instance/Poset.v:104,107`); `propositional calculus` one prose hit (`Instance/Coq.v:57`); every `Hilbert` hit is a Hilbert *space*.
- `Instance/Props.v:39`–`:99` is a single fixed model (the ambient meta-logic), not a calculus parameterised by axioms; `Instance/Lambda.v` is the simply-typed λ-calculus with only the top/and/implies fragment and a denotational morphism equality.

## Work to be done

Suggested module: `Instance/IPC/Lindenbaum.v` (extending, not duplicating, whatever #390 lands as its positive fragment).

1. Extend the propositional syntax of #390 with falsum and disjunction, and extend the derivability relation with the two missing primitive rules (falsum entails everything; the join rule as a two-sided condition). Keep the relation proof-irrelevant — a `Prop`-valued inductive on formulas — which is the distinguishing feature of this item against the proof-relevant term calculus already in-tree.
2. Build the Lindenbaum–Tarski algebra: quotient formulas by interderivability, show the induced order is well defined on classes and antisymmetric by construction, and show each connective descends to the corresponding Heyting operation. The library's setoid discipline makes this a hom-setoid quotient rather than a set-theoretic one; `Construction/Quotient.v` is the in-tree precedent.
3. Instantiate the Heyting-algebra class of the §6.3 Definition 6.7 issue at that quotient, and prove the key property: a formula is provable in the calculus exactly when its class is the top element.
4. Prove Proposition 6.11 as the immediate corollary: a formula true in every Heyting-algebra model is provable, by evaluating the hypothesis at the calculus's own Lindenbaum–Tarski algebra. Both the soundness direction (the interpretation of a derivation) and the completeness direction should be present, since soundness is what makes the statement non-vacuous.
5. State the correspondence the section is organised around, in both directions: from a calculus to its algebra (delivered by step 2) and from a Heyting algebra back to a calculus whose Lindenbaum–Tarski algebra recovers it. Awodey develops only the first and leaves the second to the reader; if the second is too large, scope it out explicitly in the header rather than silently.
6. Record how the new relation sits against `Instance/AST.v`: the term calculus there is the proof-relevant refinement, and a truncation map from its homs into the new entailment relation is a cheap, useful sanity lemma.

In-tree donors: the syntax and derivability of #390, the Heyting-algebra class of the §6.3 Definition 6.7 issue, `Instance/AST.v`, `Instance/Props.v`, `Construction/Quotient.v`, `Instance/Poset.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.3, printed pp. 138–141 (PDF pp. 147–151)); setoid discipline — `≈` on morphisms, never `=`
- [ ] All six primitive rules are present, including the falsum and disjunction rules that #390's positive fragment excludes, with the relation proof-irrelevant
- [ ] The Lindenbaum–Tarski quotient is constructed and shown to be a Heyting algebra by instantiating the class, not by re-proving the laws inline
- [ ] "Provable iff the class is the top element" is proved
- [ ] Proposition 6.11 is proved, with soundness as well as completeness
- [ ] The algebra-to-calculus direction of the correspondence is either delivered or explicitly scoped out in the file header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a Lindenbaum–Tarski construction is flagship-level for the logic spine)

## Verification

```bash
coqc -R . Category Instance/IPC/Lindenbaum.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions IPC_entails.
Print Assumptions LT_HeytingAlgebra.
Print Assumptions LT_provable_iff_top.
Print Assumptions IPC_complete.
```
Reviewer: statement matches Awodey §6.3 — the entailment relation must carry all six rules (the two involving falsum and disjunction are exactly what distinguishes this from #390), and the algebra must be the quotient by interderivability, not the preorder itself.

## Dependencies

- Depends on: #390
- Depends on: awodey:6.3:def7

<!-- catalog: {"ids":["awodey:6.3:def-ipc","awodey:6.3:construction-lindenbaum-tarski","awodey:6.3:prop11","awodey:6.3:remark-positive-fragment"],"deps":["#390","awodey:6.3:def7"]} -->

---8<---

title: "Awodey 6.3/6.6 Ex 5: Derived entailment rules and the three implication axioms of positive IPC"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:remark-ipc-derived-rules, awodey:6.3:remark-positive-ipc-axioms, awodey:6:ex5]
deps_item_ids: [awodey:6.3:def7, awodey:6.3:def-ipc]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3: the derived rules obtained from the six primitive entailment rules (printed p. 139, PDF p. 148) and the three implication axioms of positive propositional logic (printed p. 139, PDF pp. 148–149), together with §6.6 Exercise 5, which asks for the third axiom (printed p. 149, PDF p. 158). Items covered: `awodey:6.3:remark-ipc-derived-rules`, `awodey:6.3:remark-positive-ipc-axioms`, `awodey:6:ex5`.

## Background

The standard Hilbert axioms for implication, and the usual derived rules (evaluation, modus ponens, projections), are consequences of the meet/implication adjunctions, so they hold in any cartesian closed poset. See [nLab: intuitionistic logic](https://ncatlab.org/nlab/show/intuitionistic+logic) and [Wikipedia: Intuitionistic logic](https://en.wikipedia.org/wiki/Intuitionistic_logic).

## Current state in the library

Three of the derived rules exist as named constructions valid in *every* cartesian closed category — stronger than the book needs — while the remainder, and the entire axiom list, do not exist in either the entailment or the global-element phrasing.

- Present in the categorical form: `Structure/Cartesian/Closed.v:75` (`eval`), with `eval_first` at `:141`; `Structure/Cartesian.v:127` (`exl`, `exr`); `Structure/Cartesian.v:451` (`prod_one_l : 1 × x ≅ x`, the interderivability of a proposition with its conjunction with truth). `Instance/Props.v:94` supplies one cartesian closed poset in which they read as entailments.
- Missing: the modus-ponens rule and the internalised projection, both of which the book phrases through global elements `1 ~> −`; neither is stated or named anywhere.
- Missing: all three implication axioms, in either phrasing. Only the first has any witness at all, and only incidentally — the identity morphism at `Instance/Lambda.v:137` is a proof term of self-implication in one particular model. The second and third are absent outright. `Structure/Cartesian/Closed.v:310` (`exp_prod_r : (y × z)^x ≅ y^x × z^x`) is the distribution of implication over conjunction that the book uses in deriving the third axiom, so one ingredient is in place.
- Missing: any entailment phrasing at all, since no entailment calculus exists in-tree (the calculus is the companion issue for §6.3's rule system, extending #390).

## Work to be done

Suggested module: `Structure/Cartesian/Closed/Logic.v` for the categorical statements, with the entailment-level corollaries in whatever file the IPC calculus lands in.

1. State and prove the three implication axioms as global elements in an arbitrary cartesian closed category with a terminal object: self-implication; the constant-function axiom; and the distribution axiom of Exercise 5. The third is the substantive one — derive it from the distribution of implication over conjunction (`exp_prod_r`) together with monotonicity of implication in its right argument, as the book does, rather than by an opaque tactic.
2. State and prove the derived rules the book lists: evaluation, modus ponens (from two global elements to a third), the two projections, the interderivability of a proposition with its conjunction with truth, and the internalised projection.
3. Specialise all of them to the thin case, so that each reads as an entailment: this is where the thinness bridge of the §6.3 Definition 6.7 issue is consumed, and where Exercise 5's actual statement ("in any cartesian closed poset") is discharged.
4. Once the entailment calculus exists, restate each as a *derived rule* of that calculus — the book's own framing — and prove them from the six primitives, so the file records both the semantic and the syntactic derivations and the two are visibly the same content.
5. Keep the file free of new structure: it should consist entirely of consequences of `Cartesian`, `Closed` and `Terminal`, which makes it a useful general-purpose lemma library rather than a logic-specific one.

In-tree donors: `Structure/Cartesian/Closed.v` (`curry`, `eval`, `curry_comp`, `exp_prod_r`), `Structure/Cartesian.v` (`exl`, `exr`, `first`, `prod_one_l`), `Structure/Terminal.v`, `Instance/Props.v` (as the thin witness), the thinness bridge of the §6.3 Definition 6.7 issue, the calculus of the §6.3 IPC issue.

## Definition of Done

- [ ] Statement fidelity to the book (§6.3, printed p. 139 (PDF pp. 148–149); §6.6 Exercise 5, printed p. 149 (PDF p. 158)); setoid discipline — `≈` on morphisms, never `=`
- [ ] All three implication axioms are proved, the third (Exercise 5) by the book's route through distribution and monotonicity
- [ ] All five derived rules are proved and named, including modus ponens and the internalised projection in their global-element form
- [ ] Each statement is available in the thin/entailment reading, not only the categorical one
- [ ] Once the IPC calculus is available, the same statements are also derived syntactically from the six primitive rules
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Cartesian/Closed/Logic.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions ccc_axiom_K.
Print Assumptions ccc_axiom_S.
Print Assumptions ccc_modus_ponens.
Print Assumptions ccc_internal_proj.
```
Reviewer: statement matches Awodey §6.3 and §6.6 Exercise 5 — the axioms must be global elements (or entailments from the top element), not merely arrows of the corresponding hom-sets, and the third axiom's derivation must be visible rather than discharged by automation.

## Dependencies

- Depends on: awodey:6.3:def7
- Depends on: awodey:6.3:def-ipc

<!-- catalog: {"ids":["awodey:6.3:remark-ipc-derived-rules","awodey:6.3:remark-positive-ipc-axioms","awodey:6:ex5"],"deps":["awodey:6.3:def7","awodey:6.3:def-ipc"]} -->

---8<---

title: "Awodey 6.3: Heyting algebras presented by generators and relations — the universal property of HA(L)"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.3:remark-ha-presentation-ump]
deps_item_ids: [awodey:6.3:def7, awodey:6.3:construction-lindenbaum-tarski]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.3, the remark that a propositional calculus is a presentation by generators and relations of its Lindenbaum–Tarski algebra, with the two-generator worked illustration, printed page 142 (PDF page 151). Item covered: `awodey:6.3:remark-ha-presentation-ump`.

## Background

The Lindenbaum–Tarski algebra of a calculus is the Heyting algebra presented by the propositional variables as generators and the extra axioms as relations: any assignment of the generators in another Heyting algebra that satisfies the relations extends to a unique homomorphism. See [nLab: Lindenbaum-Tarski algebra](https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra) and [Wikipedia: Heyting algebra](https://en.wikipedia.org/wiki/Heyting_algebra).

## Current state in the library

Absent in every component, though the shape of the missing theorem exists one structural level away.

- No Heyting-algebra structure at all (see the §6.3 Definition 6.7 issue), hence no Heyting homomorphisms and no category of Heyting algebras. `grep -rniI --include='*.v' 'HeytingAlgebra'` → 0 hits.
- No presentation machinery for order structures: the in-tree presentation vocabulary is `Construction/PROP/Presentation.v:48` (`PresentedCat`, generators and equations for PROPs), with its universal property at `Construction/PROP/Universal.v:603` (`interp_unique`), and `Construction/Quotient.v` for hom-congruence quotients. Neither is instantiated at a poset or lattice.
- `Instance/Comp.v:240` has `EqSignature`/`OpSignature`/`Algebra`, an equational-signature layer for ordinary algebras, which is the closest existing template but is unrelated to order structures and is not connected to any universal property.
- The claim itself appears nowhere, not even as prose.

## Work to be done

Suggested module: `Structure/HeytingAlgebra/Presentation.v`.

1. Define Heyting homomorphisms (preserving top, bottom, meet, join and implication) and assemble the category of Heyting algebras; prove identities and composites are homomorphisms. This is a prerequisite the whole item rests on and it does not exist today.
2. Define a presentation: a set of generators together with a set of relations between formulas built from them, and the induced calculus. Reuse the syntax and derivability of the Lindenbaum–Tarski issue rather than introducing a second copy.
3. Prove the universal property: for any Heyting algebra with a valuation of the generators satisfying every relation, there is a unique homomorphism from the presented algebra commuting with the valuation. Existence is the induced map on interderivability classes; uniqueness is generator-wise, exactly as in the PROP development.
4. Discharge the book's worked illustration as a test: two generators subject to a single relation, with the promised unique homomorphism into any algebra carrying two elements satisfying that relation. Keeping this as an executable sanity check is what distinguishes a presentation theorem from an abstract restatement.
5. Note in the header the parallel with the λ-theory presentation of §6.5 — the two universal properties have the same shape one level up — so a later reader can see the section's organising analogy.

In-tree donors: the Heyting-algebra class of the §6.3 Definition 6.7 issue, the calculus and quotient of the §6.3 Lindenbaum–Tarski issue, `Construction/PROP/Presentation.v`, `Construction/PROP/Presentation/Universal.v`, `Construction/PROP/Universal.v`, `Construction/Quotient.v`, `Instance/Comp.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.3, printed p. 142 (PDF p. 151)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Heyting homomorphisms and the category of Heyting algebras are defined and proved to be one
- [ ] The presented algebra's universal property is proved with *both* existence and uniqueness
- [ ] The book's two-generator, one-relation illustration is discharged as a concrete instance
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/HeytingAlgebra/Presentation.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions HeytingHom.
Print Assumptions HA_presented.
Print Assumptions HA_presented_ump.
Print Assumptions HA_two_generator_example.
```
Reviewer: statement matches Awodey §6.3's presentation remark — uniqueness of the extending homomorphism must be proved (not just existence), and the worked example must be an instance of the general theorem rather than a separate hand construction.

## Dependencies

- Depends on: awodey:6.3:def7
- Depends on: awodey:6.3:construction-lindenbaum-tarski

<!-- catalog: {"ids":["awodey:6.3:remark-ha-presentation-ump"],"deps":["awodey:6.3:def7","awodey:6.3:construction-lindenbaum-tarski"]} -->

---8<---

title: "Awodey 6.4: The equational characterization of cartesian closed categories"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.4:prop12]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.4 "Equational definition", Proposition 6.12, printed page 142 (PDF pages 151–152). Item covered: `awodey:6.4:prop12`.

## Background

Cartesian closure can be presented purely equationally — operations for the terminal object, products with pairing, and exponentials with transposition, subject to a short list of equations — which is often easier to verify than the universal properties directly, and is the presentation used when building syntactic models. See [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category) and [Wikipedia: Cartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category).

## Current state in the library

Every operation and every equation of the list exists, but the proposition's *biconditional* content does not, because the library has only one definition to compare.

- `Structure/Terminal.v:107` — `Class Terminal` with the distinguished object, the arrow to it and the uniqueness law: Awodey's clause (1) verbatim.
- `Structure/Cartesian.v:121` — `Class Cartesian` with `product_obj`, the projections and the pairing, and `Structure/Cartesian.v:211` — `exl_fork`, `exr_fork`, `fork_exl_exr`: Awodey's clause (2) verbatim, already an equational presentation. `Structure/Cartesian.v:172` supplies `first`, the `g × 1` of the book's third clause.
- `Structure/Cartesian/Closed.v:43` — `Class Closed`, whose exponential clause is *not* equational: it is the hom-setoid isomorphism `exp_iso {x y z} : x × y ~> z ≊ x ~> z^y` (`:51`) together with the separately asserted beta law `ump_exponents'` (`:61`). The two equations Awodey lists are available as `ump_exponents` (`:78`) and `curry_uncurry` (`:101`), but they are consequences of the packaged iso rather than the primitive data.
- No second, universal-property-only definition of cartesian closure exists to compare against, so "a category is cartesian closed iff it carries this structure" is definitional in-tree rather than a theorem. The one place the library does prove an equational-vs-universal equivalence is the binary product: `Structure/UniversalProperty/Cartesian.v:60`, `CartesianProductIsUniversalProperty`, via representability. Nothing analogous exists for the terminal object or the exponential, and the adjunction formulation of the exponential is not built as an in-tree `Adjunction` at all.

## Work to be done

Suggested module: `Structure/Cartesian/Closed/Equational.v`.

1. Introduce the equational presentation as its own record: the three clauses exactly as the book lists them, with the exponential given by an object, an evaluation arrow, a transposition *operation*, and the two equations (beta, and the eta-style law recovering an arrow from the transpose of its uncurrying).
2. Prove the biconditional. From the equational data, construct the hom-setoid isomorphism of the `Closed` class — the two equations are precisely the two round trips — and hence a `Closed` instance; conversely, read the equational data off an existing `Closed` instance. Both directions must respect `≈`, and the transposition operation must be shown `Proper`.
3. Ship the result as a smart constructor (`Build_Closed'` or similar) so that new instances can be built from curry plus two equations instead of an isomorphism of setoids. This is the practical payoff Awodey advertises, and it is what makes the issue worth a PR beyond the biconditional itself.
4. Extend the universal-property bridge already present for binary products to the terminal object and the exponential, so `Structure/UniversalProperty/` covers all three clauses uniformly.
5. Retrofit at least one existing instance through the smart constructor as a regression check that it is genuinely usable.

In-tree donors: `Structure/Terminal.v`, `Structure/Cartesian.v`, `Structure/Cartesian/Closed.v`, `Structure/UniversalProperty/Cartesian.v`, `Instance/Lambda.v` and `Instance/AST.v` (the two syntactic instances that would most benefit from the constructor).

## Definition of Done

- [ ] Statement fidelity to the book (§6.4 Proposition 6.12, printed p. 142 (PDF pp. 151–152)), including all three clauses and both exponential equations; setoid discipline — `≈` on morphisms, never `=`
- [ ] Both directions of the equivalence are proved against the existing `Closed` class
- [ ] A smart constructor building `Closed` from curry plus the two equations is exported, and at least one existing instance is rebuilt through it
- [ ] The universal-property bridge covers the terminal object and the exponential, not only binary products
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Cartesian/Closed/Equational.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Closed_of_equational.
Print Assumptions equational_of_Closed.
Print Assumptions Build_Closed'.
```
Reviewer: statement matches Awodey §6.4 Proposition 6.12 — the second exponential equation (recovering an arrow from the transpose of its uncurrying) must be present as primitive data in the equational record, not silently obtained from the isomorphism.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:6.4:prop12"],"deps":[]} -->

---8<---

title: "Awodey 6.5: The typed λ-calculus over a signature, and λ-theories with a provable-equality judgement"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:def-typed-lambda-calculus, awodey:6.5:def-lambda-theory]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5 "λ-calculus": the recollection of the typed λ-calculus — types, terms and the five equations (the two projection laws, surjective pairing, beta and eta) — printed page 144 (PDF page 153); and the definition of a *theory* in the λ-calculus as basic types, basic terms and equations, printed page 146 (PDF page 155). Items covered: `awodey:6.5:def-typed-lambda-calculus`, `awodey:6.5:def-lambda-theory`.

## Background

A λ-theory is a simply-typed λ-calculus over a signature of basic types and typed constants, together with a set of equations between terms and the derivability judgement they generate; this is the syntactic side of the correspondence with cartesian closed categories. See [nLab: simple type theory](https://ncatlab.org/nlab/show/simply+typed+lambda-calculus) and [Wikipedia: Simply typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus).

## Current state in the library

The library has a simply-typed λ-calculus, but it is the *closed* one — a single ground type, no constants, and no equational theory.

- `Instance/Lambda/Ty.v:33` — `Ty`, the type grammar. Its header at `:20` records that there is exactly one ground type and no typed constants, so the parameterisation over a signature that both items require is absent by design.
- `Instance/Lambda/Exp.v:67` — `Exp`, the term grammar, matching Awodey's formation rules (pairing, projections, application, abstraction) but with no constant constructor.
- No provable-equality judgement. What exists instead is (a) an operational relation, `Instance/Lambda/Step.v:71` (`Step`), which is call-by-value: the projection and beta rules fire only at values, and surjective pairing and eta are absent entirely; and (b) a denotational hom-equality, `Instance/Lambda.v:154` (`Exp_Setoid`), which the file's own header (`:92`–`:97`) records as identifying strictly more terms than βη. So "the equation `a = b` is provable in the theory" has no in-tree meaning.
- The equational-signature vocabulary that would serve as a template lives elsewhere and is not connected: `Instance/Comp.v:240` (`EqSignature`, `OpSignature`, `Algebra`) for first-order algebras, and `Construction/PROP/Presentation.v:48` (`PresentedCat`) for PROPs by generators and relations.
- `Instance/AST.v:45`,`:72` is the combinator presentation of the same content, likewise with no signature parameter and with a semantic (not derivational) equality.

## Work to be done

Suggested modules: `Instance/Lambda/Signature.v` and `Instance/Lambda/Theory.v`.

1. Parameterise the type grammar by a set of basic types, keeping the existing product and arrow formers, and parameterise the term grammar by a set of typed constants. The existing files are the donor; the work is turning two closed inductives into families over a signature without disturbing the downstream development that uses the closed instance.
2. Define the provable-equality judgement inductively: a congruence containing the two projection laws, surjective pairing, beta and eta, closed under the term formers, and extended by the equations of a given theory. Substitution must be defined and shown to respect the judgement — this is the technical core, and the file header should be explicit that capture-avoidance is handled by whatever representation is chosen (the existing development's convention is the obvious donor).
3. Package a `LambdaTheory` record: basic types, basic terms with their typings, and a set of equations, together with the generated derivability relation.
4. Prove the sanity facts that make the judgement usable downstream: it is an equivalence relation on terms of each type; it is closed under substitution; and at the empty theory it contains βη.
5. Record the relationship to what exists: the call-by-value step relation is *not* the equational theory (its closure is strictly coarser in one direction and finer in another), and the denotational setoid is strictly coarser than βη. Both facts belong in the header so nobody mistakes the new judgement for either.

In-tree donors: `Instance/Lambda/Ty.v`, `Instance/Lambda/Exp.v`, `Instance/Lambda/Sub.v` and the rest of `Instance/Lambda/`, `Instance/AST.v`, `Instance/Comp.v` (`EqSignature`), `Construction/PROP/Presentation.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5, printed pp. 144 and 146 (PDF pp. 153, 155)); all five equations present, including surjective pairing and eta
- [ ] Types and terms are parameterised by a signature of basic types and typed constants
- [ ] A provable-equality judgement exists, is a congruence, and is closed under substitution — proved, not assumed
- [ ] A `LambdaTheory` record packages signature plus equations, and the generated judgement is defined from it
- [ ] The header records how the new judgement differs from the existing operational step relation and from the denotational hom-setoid
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a λ-theory layer is flagship-level for the `Instance/Lambda/` development)

## Verification

```bash
coqc -R . Category Instance/Lambda/Signature.v Instance/Lambda/Theory.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions LambdaTheory.
Print Assumptions Provable.
Print Assumptions Provable_subst.
Print Assumptions Provable_beta_eta.
```
Reviewer: statement matches Awodey §6.5 — all five equations must be primitive rules of the judgement (surjective pairing and eta are exactly what the existing step relation omits), and the signature parameterisation must be real (instantiating at two different signatures gives two different calculi).

## Dependencies

None.

<!-- catalog: {"ids":["awodey:6.5:def-typed-lambda-calculus","awodey:6.5:def-lambda-theory"],"deps":[]} -->

---8<---

title: "Awodey 6.5: The category of types C(L) of a λ-theory, and its cartesian closed structure"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:construction-category-of-types, awodey:6.5:prop-category-of-types-ccc]
deps_item_ids: [awodey:6.5:def-typed-lambda-calculus, awodey:6.4:prop12]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5: the construction of the category of types of a λ-calculus, whose arrows are provable-equality classes of closed terms of function type (printed p. 144, PDF pp. 153–154), and the proposition that it is cartesian closed, with the function type as exponential and the explicit evaluation and transposition terms (printed p. 145, PDF pp. 154–155). Items covered: `awodey:6.5:construction-category-of-types`, `awodey:6.5:prop-category-of-types-ccc`.

## Background

The syntactic category of a λ-theory has the types as objects and provable-equality classes of terms as arrows; it is cartesian closed, which is the syntactic half of the correspondence between λ-calculi and cartesian closed categories. See [nLab: syntactic category](https://ncatlab.org/nlab/show/syntactic+category) and [nLab: relationship between type theory and category theory](https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory).

## Current state in the library

A category of types exists and is proved cartesian closed — but over the wrong hom-equality, so the theorem proved is about a model rather than about the syntax.

- `Instance/Lambda.v:226` — `Lambda Γ : Category` with `obj := Ty`, identity and composition given by the expected λ-terms (`:137`), and `Lambda_Terminal`/`Lambda_Cartesian` at `:242`.
- `Instance/Lambda.v:291` — `Lambda_Closed Γ : @Closed (Lambda Γ) _` with `exponent_obj := TyArrow` and the book's curry/uncurry terms at `:282`. So the cartesian closed structure is genuinely constructed and proved.
- The defect is the hom-equality. `Instance/Lambda.v:154` (`Exp_Setoid`) defines two arrows to be equal when they agree denotationally in the standard model, and the file's own header (`:92`–`:97`) records that this identifies strictly more terms than βη — so, in its own words, the object built is the image of the syntactic category inside the standard model, not the free cartesian closed category. Awodey's quotient is by *provable equality*, which is the missing judgement of the §6.5 λ-theory issue.
- Two secondary divergences: homs are open terms in a fixed context, which is a parameter never instantiated to the empty context, so "closed terms of function type" is not what is being quotiented; and the verification at `:291` is model-theoretic (rewriting the denotation, with functional extensionality used in two obligations) rather than the λ-calculus computation Awodey performs.
- The other in-tree syntactic cartesian closed category, `Instance/AST.v:127` with `Hom_Closed` at `:177`, has the same problem in combinator form: its hom-setoid is agreement under every bicartesian-closed interpretation.

## Work to be done

Suggested module: `Instance/Lambda/Syntactic.v`.

1. Build the category of types over a λ-theory: objects the types, arrows the provable-equality classes of closed terms of the corresponding function type, identity and composition as the book's terms. The hom-setoid must be the derivability judgement of the λ-theory issue — this is the whole point of the item, and it is what distinguishes the new object from `Lambda Γ`.
2. Prove the category laws *syntactically*, from beta, eta and the congruence rules, so that no appeal to a model is made anywhere in the file.
3. Prove the terminal object and binary products from the product types and the pairing/projection terms, using surjective pairing where the book does.
4. Prove cartesian closure with the function type as exponential and the book's explicit evaluation and transposition terms, verifying the two equations of the equational characterization (which is the companion §6.4 issue's deliverable — use its smart constructor if it has landed, which is exactly the route Awodey takes).
5. Relate the new object to the existing one: exhibit the canonical functor from the syntactic category to the existing denotational category and show it is the identity on objects and full, with its failure of faithfulness being precisely the header's disclosure. That comparison is what upgrades a documented limitation into a theorem.

In-tree donors: the λ-theory and derivability judgement of the §6.5 λ-theory issue, `Instance/Lambda.v` (the construction to be re-founded), `Instance/Lambda/Sem.v`, `Instance/AST.v`, the equational characterization of the §6.4 issue, `Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5, printed pp. 144–145 (PDF pp. 153–155)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The hom-setoid is the provable-equality judgement, not denotational agreement, and no proof in the file appeals to a model
- [ ] Objects are the types and arrows are classes of *closed* terms of function type (the context parameter instantiated, or its absence justified in the header)
- [ ] Terminal object, binary products and cartesian closure all proved, with the book's evaluation and transposition terms
- [ ] The comparison functor to the existing denotational category is constructed, and the failure of faithfulness is stated
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md; in particular the syntactic proofs must not import functional extensionality
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a genuine syntactic cartesian closed category is flagship-level)

## Verification

```bash
coqc -R . Category Instance/Lambda/Syntactic.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CL.
Print Assumptions CL_Cartesian.
Print Assumptions CL_Closed.
Print Assumptions CL_to_Lambda.
```
Reviewer: statement matches Awodey §6.5 — check that `Print Assumptions CL_Closed` is closed (the existing denotational instance uses functional extensionality; the syntactic one must not), and that the exponential's evaluation and transposition are the book's terms.

## Dependencies

- Depends on: awodey:6.5:def-typed-lambda-calculus
- Depends on: awodey:6.4:prop12

<!-- catalog: {"ids":["awodey:6.5:construction-category-of-types","awodey:6.5:prop-category-of-types-ccc"],"deps":["awodey:6.5:def-typed-lambda-calculus","awodey:6.4:prop12"]} -->

---8<---

title: "Awodey 6.5: Models of a λ-theory in a cartesian closed category, and the λ-theory of monoids"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:def-model-in-ccc, awodey:6.5:example-monoid-theory]
deps_item_ids: [awodey:6.5:def-typed-lambda-calculus]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5: the definition of a model of a λ-theory in a cartesian closed category, including the requirement that every equation of the theory be satisfied by the interpretation, and the worked example identifying the models of the λ-theory of monoids with monoid objects, printed page 146 (PDF pages 155–156). Items covered: `awodey:6.5:def-model-in-ccc`, `awodey:6.5:example-monoid-theory`.

## Background

A model of a λ-theory interprets basic types as objects and basic terms as arrows of a cartesian closed category, sending products to products, application to evaluation and abstraction to transposition, and validating the theory's equations; the theory with one type, a constant and a binary operation subject to the monoid laws has exactly the monoid objects as models. See [nLab: categorical semantics](https://ncatlab.org/nlab/show/categorical+semantics) and [nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

Interpretation exists only for the *empty* theory, and only in two hard-wired forms; the notion of a model of a theory does not exist.

- `Instance/AST.v:94` — `interp`, a `Program Fixpoint` sending the combinator syntax into any bicartesian closed category, with `interp_proper` at `:221`. It has no valuation parameter (there are no basic types or constants to value) and no equation-satisfaction requirement, and it is never packaged as a `Functor`, so it carries no `CartesianFunctor`/`ClosedFunctor` witnesses.
- `Instance/Lambda/Sem.v:46` — `SemTy`/`SemExp`, the interpretation of the λ-syntax, hard-wired to Coq's `Type` rather than to an abstract cartesian closed category.
- `Functor/Structure/Cartesian/Closed.v:49` — `ClosedFunctor`, the structure-preservation vocabulary that a model ought to carry, exists but is never used for either interpretation.
- The nearest existing model notion is at a different level of generality: `Theory/Lawvere/Model.v:50` — `Record Model` with `model_fun`, `model_cartesian`, `model_terminal` — models of a Lawvere theory as product-preserving functors. It is the right template but is not about λ-theories and does not reach exponentials.
- The monoid half of the example is fully present: `Structure/Monoid.v:124` (`MonoidObject` with unit and multiplication), `:173`, `:290`, and `Theory/Algebra/Monoid/Hom.v:83` (`Mon`, the category of internal monoids). What is missing is the *theory* whose models they are: no signature with one basic type and two basic terms, no equation set, and no bijection theorem.

## Work to be done

Suggested modules: `Instance/Lambda/Model.v` and `Instance/Lambda/Model/Monoid.v`.

1. Define a model of a λ-theory in a cartesian closed category as a record: a valuation of basic types as objects and of basic terms as arrows, the structural extension to all types and terms (products to products, pairing to pairing, application to evaluation, abstraction to transposition), and the soundness requirement that the interpretation identifies the two sides of every equation of the theory.
2. Prove soundness in the strong form: if two terms are provably equal in the theory then their interpretations are `≈`. This is the induction over the derivability judgement of the λ-theory issue, and it is what makes the definition non-vacuous.
3. Package the interpretation as structure-preserving data: exhibit the `CartesianFunctor` and `ClosedFunctor` witnesses so a model is manifestly a structure-preserving interpretation, and retrofit the existing combinator interpretation through the same interface where that is cheap.
4. Define the λ-theory of monoids — one basic type, a constant and a binary operation, subject to the two unit laws and associativity — and prove the example: models of it in a cartesian closed category correspond to monoid objects, in both directions and with the round trips proved, using the existing monoid-object class as the target rather than a fresh copy.
5. Note in the header that a model in this sense is the λ-level analogue of the Lawvere-theory models already in-tree, so a reader can navigate between the two.

In-tree donors: the λ-theory of the §6.5 λ-theory issue, `Instance/AST.v` (`interp`), `Instance/Lambda/Sem.v`, `Functor/Structure/Cartesian/Closed.v`, `Theory/Lawvere/Model.v`, `Structure/Monoid.v`, `Theory/Algebra/Monoid/Hom.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5, printed p. 146 (PDF pp. 155–156)); setoid discipline — `≈` on morphisms, never `=`
- [ ] A model is parameterised by a theory and carries a valuation of basic types and basic terms
- [ ] The equation-satisfaction requirement is part of the definition, and soundness (provable equality implies `≈` of interpretations) is proved
- [ ] The interpretation is packaged with its `CartesianFunctor`/`ClosedFunctor` witnesses
- [ ] The λ-theory of monoids is defined, and its models are proved to correspond to monoid objects in both directions
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Lambda/Model.v Instance/Lambda/Model/Monoid.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions LambdaModel.
Print Assumptions model_sound.
Print Assumptions monoid_theory.
Print Assumptions monoid_model_iff_monoid_object.
```
Reviewer: statement matches Awodey §6.5 — the equation clause must be a *requirement* on the model (not a derived remark), and the monoid correspondence must be proved in both directions with the round trips, against the existing monoid-object class.

## Dependencies

- Depends on: awodey:6.5:def-typed-lambda-calculus

<!-- catalog: {"ids":["awodey:6.5:def-model-in-ccc","awodey:6.5:example-monoid-theory"],"deps":["awodey:6.5:def-typed-lambda-calculus"]} -->

---8<---

title: "Awodey 6.5: The universal property of C(L) — the free cartesian closed category on a λ-theory"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:prop-cl-universal-property]
deps_item_ids: [awodey:6.5:construction-category-of-types, awodey:6.5:def-model-in-ccc]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5, the proposition that the category of types has the universal property of an algebra presented by generators and relations: every model of the theory in a cartesian closed category extends to a unique structure-preserving functor out of it, printed page 147 (PDF page 156). Item covered: `awodey:6.5:prop-cl-universal-property`.

## Background

The syntactic category of a λ-theory is the free cartesian closed category on that theory: models correspond bijectively to cartesian-closed-structure-preserving functors out of it. See [nLab: syntactic category](https://ncatlab.org/nlab/show/syntactic+category) and [Wikipedia: Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence).

## Current state in the library

Neither half exists, though the analogous theorem is fully proved one structural level down.

- For the closed calculus, the interpretation exists as a plain function: `Instance/AST.v:94` (`interp`) with `interp_proper` at `:221`. It is never packaged as a `Functor`, carries no `CartesianFunctor`/`ClosedFunctor` witnesses, and no uniqueness theorem accompanies it — the file's declarations end at `interp_proper`.
- For a general theory the statement is not even expressible, since there is no notion of λ-theory or of model of one (those are the companion §6.5 issues).
- The shape of the missing theorem is in-tree for PROPs: `Construction/PROP/Universal.v:603` (`interp_unique`) proves exactly this kind of uniqueness for the free PROP on a signature, with the presentation variant in `Construction/PROP/Presentation/Universal.v`. That development is the model to imitate, including its handling of the transport bookkeeping that object-level equalities force.

## Work to be done

Suggested module: `Instance/Lambda/Universal.v`.

1. Build the interpretation as a `Functor` from the syntactic category into the target cartesian closed category, induced by a model, and equip it with `CartesianFunctor` and `ClosedFunctor` witnesses. Well-definedness on hom-setoids is exactly the soundness lemma of the models issue, so this step should consume it rather than repeat it.
2. Prove it extends the model on basic types and basic terms — the "commutes with the generators" half of the universal property.
3. Prove uniqueness: any structure-preserving functor agreeing with the model on the generators is naturally isomorphic (or, given the syntactic category's strictness, equal up to `≈` on homs) to the induced one. Follow the PROP development's induction over the term structure; the exponential case is the one the PROP proof does not have to handle.
4. State the resulting bijection explicitly — models of the theory in a category correspond to structure-preserving functors out of the syntactic category — since that is the form downstream results consume.
5. LIBRARY DEFECT to discharge on the way: `Instance/AST.v:31`–`:37` advertises the combinator category as the *free* bicartesian closed category, but nothing in the file proves initiality, and its hom-setoid is defined semantically (agreement under every interpretation), which makes the freeness claim circular as stated. Either prove the corresponding statement for that category or rewrite the header to say that freeness is asserted, not proved.

In-tree donors: the syntactic category of the §6.5 category-of-types issue, the models of the §6.5 models issue, `Construction/PROP/Universal.v`, `Construction/PROP/Presentation/Universal.v`, `Functor/Structure/Cartesian/Closed.v`, `Instance/AST.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5, printed p. 147 (PDF p. 156)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The induced interpretation is a `Functor` with `CartesianFunctor` and `ClosedFunctor` witnesses
- [ ] Existence (extends the model on generators) and uniqueness are both proved
- [ ] The bijection between models and structure-preserving functors is stated as such
- [ ] LIBRARY DEFECT: `Instance/AST.v:31`–`:37` claims freeness among bicartesian closed categories with no proof in the file, and with a hom-setoid defined by quantifying over all interpretations — either prove it or correct the header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the free cartesian closed category on a theory is flagship-level)

## Verification

```bash
coqc -R . Category Instance/Lambda/Universal.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions CL_interp.
Print Assumptions CL_interp_extends.
Print Assumptions CL_interp_unique.
Print Assumptions CL_models_iff_functors.
```
Reviewer: statement matches Awodey §6.5 — uniqueness must be proved (this is what "presented by generators and relations" means), and the induced functor must carry genuine structure-preservation witnesses, not merely commute with the operations pointwise.

## Dependencies

- Depends on: awodey:6.5:construction-category-of-types
- Depends on: awodey:6.5:def-model-in-ccc

<!-- catalog: {"ids":["awodey:6.5:prop-cl-universal-property"],"deps":["awodey:6.5:construction-category-of-types","awodey:6.5:def-model-in-ccc"]} -->

---8<---

title: "Awodey 6.5/6.6 Ex 6: Completeness of the λ-calculus for cartesian closed models, and the degeneracy of Sets-models"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:prop13, awodey:6.5:remark-sets-incomplete, awodey:6:ex6]
deps_item_ids: [awodey:6.5:construction-category-of-types, awodey:6.5:def-model-in-ccc]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5 Proposition 6.13 (an equation is provable in a λ-theory exactly when it holds in every model in every cartesian closed category) and the following remark that quantifying over all cartesian closed categories is essential — models in sets alone do not suffice — printed page 147 (PDF page 156); together with §6.6 Exercise 6, the reflexive-domain theory whose only model in sets is degenerate, printed page 149 (PDF page 158). Items covered: `awodey:6.5:prop13`, `awodey:6.5:remark-sets-incomplete`, `awodey:6:ex6`.

## Background

The λ-calculus is deductively complete for models in cartesian closed categories, the generic model being the syntactic category itself; the completeness genuinely needs all such categories, as the theory of a reflexive domain shows — in sets its only model is a one-element one, in which every equation holds. See [nLab: categorical semantics](https://ncatlab.org/nlab/show/categorical+semantics) and [nLab: reflexive object](https://ncatlab.org/nlab/show/reflexive+object).

## Current state in the library

Absent in all three parts, and the vocabulary each needs is itself missing.

- No completeness statement of any kind for the λ-calculus: there is no notion of "provable in a theory" (the derivability judgement is the §6.5 λ-theory issue) and no notion of "model of a theory" (the §6.5 models issue), so neither side of the biconditional is expressible today.
- The generic model does not exist either: the syntactic category over provable equality is the §6.5 category-of-types issue; the two existing candidates, `Instance/Lambda.v:226` and `Instance/AST.v:127`, both carry semantically-defined hom-setoids, which makes them unusable as generic models — using them would make the completeness statement circular.
- Nothing in the tree discusses the inadequacy of set models, and no reflexive object appears anywhere: an object isomorphic to its own function space is never constructed or refuted, and the library's cardinality-free universe-polymorphic setting means the classical "no set is isomorphic to its own function space" argument has to be made explicitly rather than assumed.
- The one nearby in-tree fact is the general triviality mechanism the exercise's degeneracy argument uses: `Structure/BiCCC.v:208`,`:221` (`prod_zero_l`, `prod_zero_r`) and `:236` (`exp_zero`).

## Work to be done

Suggested modules: `Instance/Lambda/Completeness.v` and `Instance/Lambda/Reflexive.v`.

1. Prove soundness and completeness: two terms are provably equal in a theory exactly when every model in every cartesian closed category identifies their interpretations. Soundness is the models issue's lemma; completeness is the evaluation of the hypothesis at the generic model — the syntactic category with its tautological model — where interpretation-equality is provable equality by construction.
2. Make the generic model explicit as a named artifact, since it is the entire content of the completeness direction and is reusable.
3. Formalize the reflexive-domain theory of the exercise: one basic type with two constants exhibiting it as isomorphic to its own function space, subject to the two round-trip equations.
4. Prove the exercise's two claims for models in the library's category of setoids: up to isomorphism there is exactly one model, and in it every equation of the calculus holds. The argument is a cardinality/triviality one — a set isomorphic to its own function space must be a singleton — and the file header must state precisely which classical principle, if any, that argument uses in this constructive setting, confining it.
5. Conclude the remark as a theorem: there is a λ-theory and an equation that holds in every model in sets yet is not provable, so completeness fails when restricted to sets. This is the payoff that makes the exercise more than a curiosity, and it should be stated as such rather than left implicit.

In-tree donors: the λ-theory, models and syntactic category of the three companion §6.5 issues, `Instance/Sets.v`, `Instance/Sets/Cartesian/Closed.v`, `Structure/BiCCC.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5 Proposition 6.13 and the following remark, printed p. 147 (PDF p. 156); §6.6 Exercise 6, printed p. 149 (PDF p. 158)); setoid discipline — `≈` on morphisms, never `=`
- [ ] Both directions of the completeness biconditional are proved, with the generic model exposed as a named artifact
- [ ] The reflexive-domain theory is formalized with both round-trip equations
- [ ] Its uniqueness-up-to-isomorphism of set models and the degeneracy (every equation holds) are proved
- [ ] The failure of completeness for set models alone is stated as a theorem
- [ ] Any classical principle used in the cardinality argument is confined, enumerated in the header, and visible in `Print Assumptions`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Lambda/Completeness.v Instance/Lambda/Reflexive.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions lambda_sound.
Print Assumptions lambda_complete.
Print Assumptions generic_model.
Print Assumptions reflexive_domain_sets_model_unique.
Print Assumptions sets_not_complete.
```
Reviewer: statement matches Awodey §6.5 Proposition 6.13 and §6.6 Exercise 6 — completeness must quantify over *all* cartesian closed categories, the generic model must be the provable-equality syntactic category (not a denotational one, which would make the argument circular), and the degeneracy claim must be proved rather than asserted.

## Dependencies

- Depends on: awodey:6.5:construction-category-of-types
- Depends on: awodey:6.5:def-model-in-ccc

<!-- catalog: {"ids":["awodey:6.5:prop13","awodey:6.5:remark-sets-incomplete","awodey:6:ex6"],"deps":["awodey:6.5:construction-category-of-types","awodey:6.5:def-model-in-ccc"]} -->

---8<---

title: "Awodey 6.5: The internal language L(C) of a cartesian closed category, and the isomorphism C(L(C)) ≅ C"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:6.5:construction-internal-language, awodey:6.5:prop-lambda-ccc-equivalence]
deps_item_ids: [awodey:6.5:def-typed-lambda-calculus, awodey:6.5:construction-category-of-types]
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.5: the construction of the λ-theory of a cartesian closed category — objects as basic types, arrows as basic terms, and the equations identifying the λ-operations with the categorical structure (printed p. 147, PDF pp. 156–157); and the statement that the category of types of that theory is *isomorphic* (not merely equivalent) to the original category, with the reverse round trip an equivalence of theories (printed p. 148, PDF p. 157). Items covered: `awodey:6.5:construction-internal-language`, `awodey:6.5:prop-lambda-ccc-equivalence`.

## Background

Every cartesian closed category has an internal language: a λ-theory whose types are its objects and whose constants are its arrows, and passing to the category of types of that theory recovers the category on the nose — the precise sense in which λ-calculus and cartesian closed categories are the same notion. See [nLab: internal logic](https://ncatlab.org/nlab/show/internal+language) and [nLab: relationship between type theory and category theory](https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory).

## Current state in the library

Absent, in both directions and in all supporting vocabulary.

- No internal-language construction exists: nothing in the tree builds a syntax out of a category's objects and arrows. `internal language` returns no code hits, and the only related in-tree object is the interpretation going the *other* way (`Instance/AST.v:94`).
- No round-trip statement of any kind between a syntactic category and its internal language exists; nor does the notion of λ-theory that the construction must produce (the companion §6.5 issue).
- The nearest in-tree round trip is at a different level and is a useful template rather than a donor: `Construction/Grothendieck/RoundTrip.v` builds the indexed-category-of-a-fibration comparison with its equivalence, and its file header is the model for how to disclose which direction is strict and which is only up to iso.
- The claim that the comparison is an *isomorphism of categories* rather than an equivalence deserves particular care in this library: object equality is the strict notion the tree usually avoids, and the existing strictness idioms (`Construction/Grothendieck/Strict.v`, `Instance/StrictCat`) are the precedent for stating it honestly.

## Work to be done

Suggested module: `Instance/Lambda/InternalLanguage.v`.

1. Construct the internal language of a cartesian closed category: basic types are its objects, basic terms are its arrows, and the equations are those identifying pairing/projections with the categorical product, abstraction with transposition, application with evaluation, composition of terms with composition of arrows, and the identity term with the identity arrow — exactly the list the book gives.
2. Prove it is a well-formed λ-theory in the sense of the companion §6.5 issue, i.e. that its equation set is a set of equations between well-typed terms.
3. Construct the comparison functor from the category of types of that theory back to the original category and prove it an isomorphism of categories: bijective on objects (by construction, since the basic types *are* the objects) and bijective on hom-setoids. Where strict object equality is unavoidable, follow the library's existing strictness idiom and disclose it in the header.
4. Handle the other round trip honestly: the book states only that a theory and the internal language of its category of types are "equivalent in a suitable sense" and refers the reader elsewhere. Either prove a precise comparison (an interpretation in each direction whose composites are provably-equal to the identity on generators) or scope it out explicitly in the header with the reason — silence is the failure mode to avoid.
5. As a payoff, note in the header that the internal language gives a term-level notation for reasoning inside any cartesian closed category in-tree, which is the practical reason the construction is worth having.

In-tree donors: the λ-theory of the §6.5 λ-theory issue, the syntactic category of the §6.5 category-of-types issue, `Instance/AST.v`, `Construction/Grothendieck/RoundTrip.v` (as the round-trip template), `Theory/Equivalence.v`, `Functor/Structure/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.5, printed pp. 147–148 (PDF pp. 156–157)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The internal language is constructed with every equation the book lists
- [ ] The comparison is proved to be an isomorphism of categories, with any strict object-level equality disclosed in the header
- [ ] The reverse round trip is either proved in a stated precise sense or explicitly scoped out with its reason
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the internal-language round trip is flagship-level)

## Verification

```bash
coqc -R . Category Instance/Lambda/InternalLanguage.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions internal_language.
Print Assumptions CL_of_internal_language_iso.
```
Reviewer: statement matches Awodey §6.5 — the comparison must be an isomorphism of categories (bijective on objects and hom-setoids), not merely an equivalence, and any place where the formalization can only deliver an equivalence must say so in the header rather than quietly weakening the theorem.

## Dependencies

- Depends on: awodey:6.5:def-typed-lambda-calculus
- Depends on: awodey:6.5:construction-category-of-types

<!-- catalog: {"ids":["awodey:6.5:construction-internal-language","awodey:6.5:prop-lambda-ccc-equivalence"],"deps":["awodey:6.5:def-typed-lambda-calculus","awodey:6.5:construction-category-of-types"]} -->

---8<---

title: "Awodey 6.6 Ex 2: The category of monoids is not cartesian closed"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:6:ex2]
deps_item_ids: []
deps_pending: []

## Source

Awodey, *Category Theory* (2nd ed.), §6.6 Exercise 2, printed page 149 (PDF page 158): decide, with justification, whether the category of monoids and monoid homomorphisms is cartesian closed. Item covered: `awodey:6:ex2`.

## Background

The category of monoids has finite products but is not cartesian closed: the trivial monoid is both initial and terminal, and a cartesian closed category with a zero object is trivial. See [nLab: category of monoids](https://ncatlab.org/nlab/show/Mon) and [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

The category exists; the exercise's content does not.

- `Theory/Algebra/Monoid/Hom.v:83` — `Mon : Category`, internal monoids in an ambient monoidal category, with `Structure/Monoid.v:124` (`MonoidObject`) as the object structure and a forgetful functor to the ambient category. Instantiated at the cartesian monoidal structure on setoids this is Awodey's category of monoids.
- No cartesian, terminal, initial or closed structure is ever put on it: searches for a `Closed` instance turn up only `Sets`, `Coq`, `FinSet`, `Cat`, `Props`, `Rel`, `Comp`, `Lambda`, `AST` and the internal-product monoidal instance. In particular the trivial monoid is never exhibited as a zero object.
- The general obstruction is likewise unstated. The two ingredients exist — `Structure/BiCCC.v:208`,`:221` (`prod_zero_l : 0 × x ≅ 0`, `prod_zero_r`) — but no theorem anywhere says that a cartesian closed category with a zero object is trivial, and there is no in-tree example of a "this category is *not* cartesian closed" theorem to imitate (the two nearby remarks, `Instance/Coq/Par.v:219` and `Instance/Coq/ParE.v:177`, are prose about partiality Kleisli categories).

## Work to be done

Suggested modules: `Structure/Cartesian/Closed/Triviality.v` for the general lemma, `Instance/Mon/NotClosed.v` for the instance.

1. Prove the general obstruction first, since it is the reusable half: in a category with a terminal object, an initial object and cartesian closed structure, if the initial and terminal objects are isomorphic then every object is isomorphic to the terminal one. The proof is the composite of the zero-product isomorphism with the unit isomorphism, both already in-tree.
2. Give the category of monoids its finite products (the pointwise monoid structure on a product) and its terminal object (the one-element monoid), and prove the one-element monoid is also initial — so it is a zero object.
3. Exhibit two non-isomorphic monoids (any monoid with more than one element, against the trivial one), which is the non-triviality hypothesis the obstruction needs.
4. Conclude the exercise as a proved negation: the category of monoids admits no cartesian closed structure. State it in the form "there is no `Closed` instance", i.e. as an impossibility, not as an unproved remark.
5. Record in the header that the same argument applies verbatim to any category with a zero object and non-isomorphic objects (abelian groups, modules, pointed sets), which is what makes the general lemma worth extracting.

In-tree donors: `Theory/Algebra/Monoid/Hom.v`, `Structure/Monoid.v`, `Structure/BiCCC.v` (`prod_zero_l`, `prod_zero_r`), `Structure/Terminal.v`, `Structure/Initial.v`, `Structure/Cartesian/Closed.v`, `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to the book (§6.6 Exercise 2, printed p. 149 (PDF p. 158)): the answer is a proved negation with its justification, not a remark; setoid discipline — `≈` on morphisms, never `=`
- [ ] The general lemma "cartesian closed plus a zero object implies trivial" is proved and stated separately from the instance
- [ ] The category of monoids is given finite products and a zero object, and two non-isomorphic monoids are exhibited
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the documented `Instance/` stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for every principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Cartesian/Closed/Triviality.v Instance/Mon/NotClosed.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions closed_zero_object_trivial.
Print Assumptions Mon_Zero.
Print Assumptions Mon_not_Closed.
```
Reviewer: statement matches Awodey §6.6 Exercise 2 — the conclusion must be an impossibility theorem, and the non-triviality witness (two non-isomorphic monoids) must be exhibited concretely rather than assumed.

## Dependencies

None.

<!-- catalog: {"ids":["awodey:6:ex2"],"deps":[]} -->

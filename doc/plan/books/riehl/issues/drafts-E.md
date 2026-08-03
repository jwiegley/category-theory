```yaml
title: "Riehl E.2: The symmetric monoidal structure on chain complexes and its sign conventions"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.2:example-symmetric-monoidal]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (locally recompiled author's copy; printed folio = PDF page − 20).
- Section: Epilogue §E.2 ("Monoidal categories"), the roster of examples of symmetric monoidal categories, printed p. 253 (PDF pp. 273–274).
- Item: `riehl:E.2:example-symmetric-monoidal` — **clause (d) only** (unbounded chain complexes over a commutative ring with the graded tensor product). The roster's other clauses are recorded elsewhere: clause (b), the coproduct/initial-object structure, on #490; clause (c), `R`-Mod under `⊗_R`, on #388; clause (e), a commutative monoid as a discrete symmetric monoidal category, on #772; clause (a), finite products, is already in force in-tree.

## Background

For a commutative ring `R`, the unbounded chain complexes of `R`-modules carry a tensor product whose degree-`n` component is the direct sum of the `R`-module tensor products `A_p ⊗ B_q` over `p + q = n`, with the differential given by the graded Leibniz rule; the unit is `R` concentrated in degree zero. The symmetry interchanges tensor factors with a sign in odd degrees, and there are two conventions for that sign which differ by a sign in odd–odd degree, so the *choice* is part of the data. See [nLab: tensor product of chain complexes](https://ncatlab.org/nlab/show/tensor+product+of+chain+complexes), [nLab: chain complex](https://ncatlab.org/nlab/show/chain+complex), and [Wikipedia: Chain complex](https://en.wikipedia.org/wiki/Chain_complex).

## Current state in the library

Verified ABSENT for this clause, and absent at the level of its ingredients as well.

- There are no chain complexes. `Construction/Chain.v` is the initial-algebra ω-chain `Chain F : Omega ⟶ C` of an endofunctor, with no `∂ ∘ ∂ ≈ 0` condition; every occurrence of "chain complex", "homology" or "differential graded" in the tree is background-essay prose (`Construction/Enriched.v:47,71`; `Structure/Abelian.v:69-70,111`; `Theory/Equivalence.v:79`). Chain complexes and homology objects are already a filed obligation (#557).
- There is no category of modules over a ring, and no ring: the verifier independently re-ran `rg 'Class Ring|Record Ring|Ring :'` (0 hits) and listed `Instance/` in full (Adj, AST, Cat, CMon, Comp, Coq, Discrete, Ens, Fact, FinSet, Fun, Lambda, Omega, One, Parallel, Poset, Props, Proset, Rel, Roof, Sets, Shapes, StrictCat, Two, Zero, ZX — no `Ab`, no `Mod`, no `Ring`). `R`-Mod and its `⊗_R` symmetric monoidal structure are filed as #258 and #388.
- The generic monoidal spine is in good order and is the target to hit: `Structure/Monoidal.v` (pentagon/triangle), `Structure/Monoidal/Braided.v`, `Structure/Monoidal/Symmetric.v` with `braid_invol`. The only fully general symmetric monoidal *construction* in-tree is `CC_SymmetricMonoidal` (`Structure/Monoidal/Internal/Product.v:314`), i.e. the cartesian one, concretely witnessed only by `Coq_Monoidal` (`Instance/Coq.v:159`). A genuinely non-cartesian symmetric monoidal category does not exist anywhere in the tree, so this issue (with #388) would supply one of the first.

## Work to be done

Suggested modules: `Instance/Module/Complex.v` (the category of chain complexes over a commutative ring), `Instance/Module/Complex/Tensor.v` (the graded tensor and its symmetry).

1. Over the chain complexes of #557 and the module category of #258/#388, define the graded tensor product: `(A ⊗ B)_n := ⨁_{p+q=n} A_p ⊗_R B_q`, with differential `∂(a ⊗ b) = ∂a ⊗ b + (−1)^{|a|} a ⊗ ∂b`. Prove `∂ ∘ ∂ ≈ 0` for the result, so the construction lands back in chain complexes.
2. Prove bifunctoriality (action on chain maps, respecting `≈`), and construct the unitors and associator from the module-level ones of #388, discharging the triangle and pentagon.
3. Construct the symmetry `A ⊗ B ≅ B ⊗ A` carrying the Koszul sign `(−1)^{pq}` on the `(p,q)` summand, prove it a chain map, prove the hexagon, and prove `braid_invol` — the involutivity is where the sign convention has to be pinned down.
4. Record **both** sign conventions Riehl mentions as two named instances (or one instance parameterized by the convention) together with a proof that they are related by the evident sign twist, and state in the file header which one the library takes as canonical. The point of the example in the book is precisely that the choice is real and must be made explicitly.
5. Register the resulting `SymmetricMonoidal` instance and update `docs/INHABITATION.md`: a non-cartesian symmetric monoidal witness is exactly what several parametric results in the monoidal spine currently await.

In-tree donors: `Structure/Monoidal.v`, `Structure/Monoidal/Braided.v`, `Structure/Monoidal/Symmetric.v`, `Structure/Monoidal/Internal/Product.v` (the cartesian template), `Structure/Biproduct.v` / `Structure/Limit/Product.v` (for the degreewise direct sum), plus the chain complexes of #557 and the module tensor of #388.

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.2, printed p. 253, PDF pp. 273–274, clause (d)); setoid discipline — `≈` on morphisms, never `=`
- [ ] The graded tensor is proved to land in chain complexes (`∂ ∘ ∂ ≈ 0`) and to be a bifunctor
- [ ] Unitors, associator, triangle and pentagon discharged; the symmetry proved a chain map with the hexagon and `braid_invol`
- [ ] Both sign conventions are recorded, with the relation between them proved and the canonical choice stated in the file header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping; any stdlib axioms inherited from the module layer confined to `Instance/` and enumerated in docs/AXIOMS.md)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level
- [ ] `docs/INHABITATION.md` updated — this is a non-cartesian symmetric monoidal witness

## Verification

```bash
coqc -R . Category Instance/Module/Complex.v
coqc -R . Category Instance/Module/Complex/Tensor.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Complex_Tensor.
Print Assumptions Complex_SymmetricMonoidal.
```
Reviewer: statement matches Riehl §E.2 clause (d) (printed p. 253) — the differential is the graded Leibniz rule, the symmetry carries the degree-dependent sign, and the two conventions are both present with their relation proved rather than one silently chosen.

## Dependencies

Depends on: #557 — chain complexes (this issue tensors them).
Depends on: #388 — the module category and its `⊗_R` symmetric monoidal structure (the degreewise input).

<!-- catalog: {"ids":["riehl:E.2:example-symmetric-monoidal"],"deps":["#557","#388"]} -->

---8<---

```yaml
title: "Riehl E.3: The universal property of the unit interval — bipointed spaces and Freyd's terminal coalgebra"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.3:def-bipointed-space, riehl:E.3:thm1, riehl:E.3:remark-terminal-coalgebra]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (printed folio = PDF page − 20).
- Section: Epilogue §E.3 ("Freyd's characterization of the unit interval"), printed pp. 255–256 (PDF pp. 275–276).
- Items: `riehl:E.3:def-bipointed-space` (bipointed spaces, their maps, and the wedge `X ∨ X`), `riehl:E.3:thm1` (Theorem E.3.1, the universal property of `I`, after Freyd and Leinster), `riehl:E.3:remark-terminal-coalgebra` (the reformulation of that theorem as a terminal coalgebra, together with the appeal to Lambek's theorem).

## Background

A bipointed space carries two distinguished distinct points; gluing the second point of one copy to the first point of another gives the wedge `X ∨ X`, and `X ↦ X ∨ X` is an endofunctor of bipointed spaces. Freyd's observation is that the unit interval with its endpoints is the terminal coalgebra for that endofunctor — the halving map `I → I ∨ I` being the structure map — so the interval is characterized by a universal property rather than constructed from the reals. See [nLab: interval object](https://ncatlab.org/nlab/show/interval+object), [nLab: terminal coalgebra](https://ncatlab.org/nlab/show/terminal+coalgebra), and [Wikipedia: Unit interval](https://en.wikipedia.org/wiki/Unit_interval).

## Current state in the library

Verified ABSENT for the bipointed/topological content, PARTIAL for the remark (its Lambek half is fully present). The split matters, because it determines what actually has to be built.

- **The coalgebraic framework is complete and inhabited.** `Theory/Lambek.v:78` reads

  ```coq
  Theorem lambek_final `(F : C ⟶ C) (T : @Terminal (FCoalg F)) :
    `1 (@terminal_obj (FCoalg F) T) ≅ F (`1 (@terminal_obj (FCoalg F) T)).
  ```

  — an arbitrary endofunctor on an arbitrary category, no completeness or size side conditions, proved by duality from `lambek` (`Theory/Lambek.v:40`) with no axioms. `Construction/FCoalg.v` supplies the category of coalgebras, `Theory/Recursion.v:99` the anamorphism API, and `Instance/Sets/Streams.v:231` (`Stream_final`) is a concrete inhabitant of `@Terminal (FCoalg _)`. So Riehl's appeal to Lambek is already discharged in-tree at full generality; what is missing is only the interval half.
- **The topological input does not exist.** There is no category of topological spaces, no continuous map and no homeomorphism (`rg -i 'continuous function|homeomorph'` → 0 hits); the library never imports the reals (`rg 'Require.*Reals|Rdefinitions'` → 0 hits); and every `interval` hit is the interval *category* `_2` (`Instance/Two.v`), the factorization category (`Instance/Fact.v`) or the ordinal `ω` (`Instance/Omega.v`). `bipointed` has 0 hits; the near-misses are `Pointed`/`WellPointed` **endofunctors** (`Instance/Fun.v:230,240`) and the dinatural `Structure/Wedge.v` (ends/coends), neither related.
- **The colimit side is ready.** The verifier's sharpening: `Structure/Pushout.v` supplies general pushouts and `Construction/Slice.v` supplies coslices, so the wedge `X ∨ X` and the bipointed-*object* category `(1 + 1)/C` are expressible in any cocartesian category the moment a category of spaces exists — the missing ingredient is the space, not the colimit. What is *not* expressible at object level is the space-level requirement that the two points be **distinct closed points**; that clause needs the topology.

## Work to be done

Suggested modules: `Instance/Top/Bipointed.v` (the category and the wedge endofunctor), `Instance/Top/Interval.v` (the theorem).

1. Over the category `Top` of #259 and the unit interval infrastructure of #249, define bipointed spaces (a space with two distinguished distinct points) and their maps (continuous and preserving both points, in order). Do it in two layers so the reusable part is reusable: first the bipointed-**object** category of an arbitrary cocartesian category as the coslice `(1 + 1)/C` (`Construction/Slice.v` + `Structure/Cocartesian.v`), then the topological refinement adding distinctness/closedness.
2. Define the wedge `X ∨ X` as the pushout gluing the second point of the first copy to the first point of the second (`Structure/Pushout.v`), with its induced bipointing, and prove `X ↦ X ∨ X` is an endofunctor of bipointed spaces.
3. State and prove Theorem E.3.1: `(I, 0, 1)` with the halving map is terminal among bipointed spaces equipped with a map to their own wedge — i.e. exhibit `@Terminal (FCoalg Wedge)` at it, in the `Construction/FCoalg.v` packaging so that the existing API applies.
4. Derive the remark's content **by instantiation, not by re-proof**: apply `Theory/Lambek.v:78` `lambek_final` to conclude that the structure map is an isomorphism (the halving homeomorphism), and record in the file header that this is Lambek's general theorem specialized, exactly as Riehl presents it.
5. Disclose in the file header whichever construction of `[0,1]` is used (stdlib `Reals` in the instance layer, or a constructive/synthetic substitute) and its axiom cost, per the same discipline #249 imposes; enumerate any stdlib axioms in docs/AXIOMS.md.

In-tree donors: `Theory/Lambek.v` (`lambek_final`), `Construction/FCoalg.v`, `Theory/Recursion.v` (`ana`), `Instance/Sets/Streams.v` (the precedent for building a terminal coalgebra concretely), `Structure/Pushout.v`, `Construction/Slice.v`, `Structure/Cocartesian.v`, plus `Top` (#259) and the interval (#249).

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.3, Theorem E.3.1 and the following remark, printed pp. 255–256, PDF pp. 275–276); setoid discipline — `≈` on morphisms, never `=`
- [ ] Bipointed spaces and their maps defined, with the reusable bipointed-object layer `(1 + 1)/C` separated from the topological refinement
- [ ] The wedge is constructed as a genuine pushout and proved functorial
- [ ] The interval is exhibited as `@Terminal (FCoalg Wedge)`, and the invertibility of the halving map is obtained by applying `lambek_final`, not re-proved
- [ ] The construction of `[0,1]` and its axiom cost are disclosed in the file header and enumerated in docs/AXIOMS.md if stdlib axioms are used (instance layer only)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` in the core-theory files touched (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` run on each principal artifact, with output matching the AXIOMS.md enumeration
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated — this would be the second concrete terminal coalgebra in-tree after `Stream_final`

## Verification

```bash
coqc -R . Category Instance/Top/Bipointed.v
coqc -R . Category Instance/Top/Interval.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions Bipointed_Wedge.
Print Assumptions interval_terminal_coalgebra.
```
Reviewer: statement matches Riehl §E.3 Theorem E.3.1 (printed p. 255) — terminality is among bipointed spaces with a map to their own wedge, the two basepoints are required distinct, and the halving map's invertibility is a corollary of `lambek_final` rather than an independent argument.

## Dependencies

Depends on: #259 — `Top`, the category of topological spaces.
Depends on: #249 — the unit interval infrastructure and paths (that issue's "workable `[0,1]`" is this issue's object).

- Related (NOT blocking): **#901** also creates `Instance/Top/Interval.v`. It builds the interval
  DOMAIN — the space whose points are closed intervals `[d,u]`, for the topos of behavior types —
  whereas this issue builds the unit interval itself as a bipointed space with its universal
  property. Different objects in one module; neither is derivable from the other, though both need
  the same numeric substrate decision (see #901's Work item 1, which discloses the options). No
  dependency edge is asserted; they must not be worked in the same parallel wave.

<!-- catalog: {"ids":["riehl:E.3:def-bipointed-space","riehl:E.3:thm1","riehl:E.3:remark-terminal-coalgebra"],"deps":["#259","#249"]} -->

---8<---

```yaml
title: "Riehl E.4: Finite-limit-preserving functors and the definition of a Grothendieck topos"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.4:def-grothendieck-topos]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (printed folio = PDF page − 20).
- Section: Epilogue §E.4 ("Grothendieck toposes"), the definition, printed p. 256 (PDF p. 276).
- Item: `riehl:E.4:def-grothendieck-topos`.

## Background

A Grothendieck topos is a reflective full subcategory of a presheaf category on a small category whose reflector preserves finite limits — a *left-exact* localization of presheaves. The left-exactness clause is the whole content of the definition beyond reflectivity, so the finite-limit-preservation predicate has to exist before the definition can be stated. See [nLab: Grothendieck topos](https://ncatlab.org/nlab/show/Grothendieck+topos) and [nLab: exact functor](https://ncatlab.org/nlab/show/left+exact+functor).

## Current state in the library

Verified PARTIAL: the two structural ingredients are each in force, their conjunction is not, and one Phase-C claim about the third ingredient was **overturned by the verifier** — the corrected reading is the one an implementer should work from.

- Reflectivity is present: `Construction/Reflective.v:60` is `Record Reflective {C : Category} (S : Subcategory C) := { reflective_full : Full C S; reflector : C ⟶ Sub C S; reflective_adj : reflector ⊣ Incl C S }`.
- A full subcategory of a presheaf category is present as a worked case: `Theory/Sheaf/Category.v:81` defines `Sheaves := Sub (@Presheaves C Sets) Sheaves_sub`, with `Sheaves_Full` (`:94`), `Sheaves_Faithful` (`:103`) and repleteness `sheaf_iso_closed` (`:119`).
- Nothing bundles them: `rg 'GrothendieckTopos|Grothendieck_Topos'` → 0 hits, and the only two occurrences of the phrase "Grothendieck topos" are prose (`Theory/Sheaf.v:83`, `Structure/Topos.v:54`).
- **Verifier correction, which supersedes the Phase-C text.** The coverage record originally said left-exactness has no in-tree counterpart and is not expressible. That is overstated and must not be repeated in the implementation. Finite-limit preservation is partly bundled and wholly assemblable today: `Functor/Structure/Terminal.v:43` `Class TerminalFunctor` (the comparison iso `1 ≅ F 1` plus `fmap_one`) and `Functor/Structure/Cartesian.v:49` `Class CartesianFunctor` (the comparison iso `F (x × y) ≅ F x × F y` plus `fmap_exl`/`fmap_exr`/`fmap_fork`) *are* preservation of the nullary and binary products, and preservation of pullbacks is statable as `PreservesLimit` (`Structure/Limit/Preservation.v:48`) at cospan-shaped diagrams over `Instance/Roof.v` (cf. `Structure/Pullback/Limit.v`). Since `Structure/Topos.v:20-25` itself *defines* "finite limits", for topos purposes, as terminal + binary products + pullbacks, a lex predicate is a conjunction of pieces that already exist. What is genuinely missing is that no such predicate is **named or bundled**, and there is no finiteness condition on an arbitrary shape category `J` (`rg 'PreservesFinite|FiniteLimits|left exact'` → 0 code hits; the 5 "finite limits" hits are all comment headers).
- No instance: the one candidate reflective subcategory of presheaves has no reflector, because sheafification is an explicitly named in-tree deferral (`Theory/Sheaf/Category.v:47,49-51`, ledger entry 1). So `Reflective Sheaves_sub` is never inhabited, and this issue does not need it to be — the definition is what is being supplied here.
- A shape mismatch to plan around: `Reflective` is stated for a `Subcategory S of C` (a selected-objects/selected-morphisms record, `Construction/Subcategory.v`), so an arbitrary category `E` with a fully faithful embedding into presheaves must first be presented as such a `Subcategory`, or the class must be restated over a fully faithful functor.

## Work to be done

Suggested modules: `Structure/Limit/Finite.v` (the finite-limit vocabulary and the preservation predicate), `Structure/Topos/Grothendieck.v` (the definition).

1. Name and bundle the finite-limit-preservation predicate. Follow `Structure/Topos.v:20-25`'s own reading of "finite limits": define `PreservesFiniteLimits F` as the conjunction of `TerminalFunctor F`, `CartesianFunctor F` and preservation of cospan-shaped limits (`PreservesLimit` at `Instance/Roof.v`-indexed diagrams). Do **not** invent a rival notion of finite shape category; if a genuine finiteness predicate on `J` is wanted, add it separately and prove the two agree for the three shapes above.
2. Define `GrothendieckTopos`: a small category `C`, a full subcategory `S` of `@Presheaves C Sets`, a `Reflective S`, and `PreservesFiniteLimits (reflector …)`. Provide accessors so consumers never destructure the record, and state the smallness of `C` the way the library states smallness elsewhere — as data, per `Adjunction/SAFT.v`'s `SubobjectIndex` idiom — or record explicitly in the header that universe polymorphism carries it.
3. Provide the trivial witness so the class is not vacuously stated: the identity reflection exhibits any presheaf category `[C^op, Sets]` as a Grothendieck topos over itself (the reflector is the identity, which preserves everything). This is the cheapest possible inhabitant and it makes the definition demonstrably satisfiable.
4. Repoint the prose: `Theory/Sheaf.v:83` and `Structure/Topos.v:54` currently describe Grothendieck toposes in words; they should cite the new definition.

In-tree donors: `Construction/Reflective.v`, `Construction/Subcategory.v`, `Functor/Structure/Terminal.v`, `Functor/Structure/Cartesian.v`, `Structure/Limit/Preservation.v`, `Structure/Pullback/Limit.v`, `Instance/Roof.v`, `Theory/Sheaf/Category.v` (the worked full-subcategory-of-presheaves case), `Structure/Topos.v`.

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.4, printed p. 256, PDF p. 276); setoid discipline — `≈` on morphisms, never `=`
- [ ] `PreservesFiniteLimits` is a named, reusable predicate, assembled from the existing `TerminalFunctor`/`CartesianFunctor`/cospan-`PreservesLimit` pieces rather than from a new rival notion
- [ ] `GrothendieckTopos` defined with reflectivity **and** left-exactness of the reflector, with accessors
- [ ] At least one inhabitant exists (the identity reflection of a presheaf category), so the class is demonstrably satisfiable
- [ ] The prose at `Theory/Sheaf.v:83` and `Structure/Topos.v:54` cites the definition instead of describing it
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated — the `Structure/Topos.v` entry should record that the Grothendieck side now exists

## Verification

```bash
coqc -R . Category Structure/Limit/Finite.v
coqc -R . Category Structure/Topos/Grothendieck.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions PreservesFiniteLimits.
Print Assumptions GrothendieckTopos.
Print Assumptions Presheaves_GrothendieckTopos.
```
Reviewer: statement matches Riehl §E.4 (printed p. 256) — the subcategory is full, the inclusion has a left adjoint, and that left adjoint is required to preserve finite limits (the clause that distinguishes a Grothendieck topos from an arbitrary reflective subcategory of presheaves).

## Dependencies

None blocking.

Coordination (not a blocking dependency): #546 already promises `ExactFunctor`/`LeftExactFunctor` for **additive** functors between **abelian** categories, and to prove those equivalent to preservation of finite (co)limits. The predicate defined here is the general, non-additive one for an arbitrary functor between finitely complete categories. Whichever lands first should be the definition the other consumes — the two must not become rival predicates.

- Depends on: #417 — it defines finiteness for an index category and `FinitelyComplete` in the same
  `Structure/Limit/Finite.v` this issue targets. Finite-limit preservation cannot be stated before
  that vocabulary exists, so this is a genuine prerequisite, not merely a shared file.

<!-- catalog: {"ids":["riehl:E.4:def-grothendieck-topos"],"deps":["#417"]} -->

---8<---

```yaml
title: "Riehl E.4: Every Grothendieck topos is a cocomplete elementary topos, and Fin is not one"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.4:remark-cocomplete-and-elementary]
deps_item_ids: [riehl:E.4:def-grothendieck-topos]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (printed folio = PDF page − 20).
- Section: Epilogue §E.4 ("Grothendieck toposes"), the remark following the definition, printed p. 256 (PDF p. 276).
- Item: `riehl:E.4:remark-cocomplete-and-elementary` — three claims: (1) a Grothendieck topos is cocomplete, so its defining adjunction can be produced instead from the composite of the reflector with the Yoneda embedding, the reflector being the left Kan extension of that composite along Yoneda; (2) every Grothendieck topos is an elementary topos; (3) the converse fails — the category of finite sets is an elementary topos that is not a Grothendieck topos, one reason being that it is neither complete nor cocomplete.

## Background

Grothendieck toposes sit strictly inside elementary toposes: they inherit all small colimits from presheaves through the reflection, and they inherit the classifier and exponentials, but they additionally carry a smallness/cocompleteness that the elementary axioms do not force. Finite sets are the standard separating example. See [nLab: Grothendieck topos](https://ncatlab.org/nlab/show/Grothendieck+topos) and [nLab: topos](https://ncatlab.org/nlab/show/elementary+topos).

## Current state in the library

Verified PARTIAL, on the strength of the *positive* half of claim (3) only.

- Present: `Instance/FinSet/Topos.v:38` `Definition FinSet_Topos : ElementaryTopos FinSet := {| topos_terminal := FinSet_Terminal; topos_cartesian := FinSet_Cartesian; topos_pullbacks := FinSet_Pullbacks; topos_closed := FinSet_Closed; topos_classifier := FinSet_Classifier |}`, with computing sanity checks at `:52` (`@Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl`). So "finite sets form an elementary topos" is in force, with a witness that computes. `Structure/Topos.v:112` is `Class ElementaryTopos` with those five fields, and its header at `:20-25` discloses that finite limits are carried explicitly as terminal + binary products + pullbacks because the pullback-from-equalizer reduction is not formalized.
- Claim (1) is **unstatable** as things stand, and the verifier confirmed the sharpest form of that: `Cocomplete` (`Structure/Complete.v:119`, `∀ (D : Category) (F : D ⟶ C), Colimit F`) has **no inhabitant anywhere in the tree** — its only other occurrences are prose at `Theory/Adamek/Corollaries.v:51` and a hypothesis binder at `:61`. The reformulation via Kan extensions is likewise unavailable: `Theory/Kan/Extension.v:222` has the `LeftKan` class but nothing connects `Lan` to the Yoneda embedding of `Functor/Hom/Yoneda.v`, and "free cocompletion" occurs exactly once, as prose (`Theory/Sheaf.v:117`).
- Claim (2) has no antecedent notion (see the Grothendieck-topos definition issue) and no proof route in-tree: `ElementaryTopos` has exactly one witness tree-wide, `FinSet_Topos`; presheaf categories are not yet toposes (#404) and no structure is transported along a reflection.
- The negative half of claim (3) is absent: `FinSet` is shown to have finite products, chosen pullbacks, exponentials, coproducts and pushouts, but no in-tree statement denies it infinite (co)products or any other property, so "not a Grothendieck topos" cannot be concluded.

## Work to be done

Suggested modules: `Structure/Topos/Grothendieck/Colimits.v` (claim 1), `Structure/Topos/Grothendieck/Elementary.v` (claim 2), `Instance/FinSet/NotGrothendieck.v` (claim 3).

1. **Cocompleteness.** Prove that a Grothendieck topos is cocomplete: presheaf categories are cocomplete (#715), and colimits descend through a reflection by applying the reflector to the presheaf colimit. Then state the reformulation Riehl highlights — that the reflector is recovered as the left Kan extension along the Yoneda embedding of its restriction to representables — over the Kan-extension existence theorem of #590, and connect `Theory/Kan/Extension.v`'s `LeftKan` to `Functor/Hom/Yoneda.v`'s embedding for the first time. Producing an actual inhabitant of `Cocomplete` is itself an increment: today the class has none.
2. **Every Grothendieck topos is elementary.** Transport the five `ElementaryTopos` fields (`Structure/Topos.v:112`) along the lex reflection from a presheaf topos (#404): the terminal object, binary products and pullbacks come from left-exactness of the reflector plus fullness of the inclusion; the exponentials and the classifier are the standard reflective-subcategory arguments. Disclose in the header any clause that is left conditional.
3. **`FinSet` is not a Grothendieck topos.** Prove the negative half honestly: exhibit a small diagram in `FinSet` with no colimit (equivalently, show a countable coproduct cannot exist because the coproduct injections would be jointly monic into a finite set), hence `¬ Cocomplete FinSet`, hence — with claim (1) — that `FinSet_Topos` is not a Grothendieck topos. State precisely which logical principles the non-existence argument uses; a constructive counting argument should be possible over the skeletal `Instance/FinSet.v` encoding, and if it is not, say so.

In-tree donors: `Structure/Topos.v`, `Instance/FinSet/Topos.v`, `Instance/FinSet.v`, `Construction/Reflective.v`, `Structure/Complete.v`, `Theory/Kan/Extension.v`, `Functor/Hom/Yoneda.v`, `Structure/Limit/Preservation.v`, plus #715 (presheaf cocompleteness), #404 (presheaf toposes) and #590 (Kan existence).

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.4, the remark on printed p. 256, PDF p. 276); setoid discipline — `≈` on morphisms, never `=`
- [ ] Cocompleteness of a Grothendieck topos is proved, producing the **first inhabitant of `Cocomplete`** in the tree
- [ ] The reflector-as-left-Kan-extension-along-Yoneda reformulation is stated and proved, tying `LeftKan` to the Yoneda embedding
- [ ] `ElementaryTopos` is constructed for every Grothendieck topos, with any conditional clause disclosed in the file header
- [ ] `¬ Cocomplete FinSet` is proved, and the conclusion that `FinSet` is an elementary topos which is not a Grothendieck topos is drawn explicitly
- [ ] Any classical principle used in the negative half is disclosed (the zero-axiom rule applies)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship-level) and `docs/INHABITATION.md` updated with the first `Cocomplete` witness

## Verification

```bash
coqc -R . Category Structure/Topos/Grothendieck/Colimits.v
coqc -R . Category Structure/Topos/Grothendieck/Elementary.v
coqc -R . Category Instance/FinSet/NotGrothendieck.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions grothendieck_cocomplete.
Print Assumptions grothendieck_reflector_is_lan.
Print Assumptions grothendieck_is_elementary.
Print Assumptions FinSet_not_cocomplete.
```
Reviewer: statement matches Riehl §E.4's remark (printed p. 256) — all three claims are addressed, and the third is a genuine negative result about `FinSet`, not a restatement of the positive half.

## Dependencies

Depends on: riehl:E.4:def-grothendieck-topos
Depends on: #715 — colimits in a functor category are pointwise, and presheaf categories are cocomplete.
Depends on: #404 — presheaf categories are elementary toposes (the structure this issue transports along the reflection).
Depends on: #590 — existence of Kan extensions and the global adjoint to precomposition (the reflector-as-`Lan` reformulation).


<!-- catalog: {"ids":["riehl:E.4:remark-cocomplete-and-elementary"],"deps":["riehl:E.4:def-grothendieck-topos","#715","#404","#590"]} -->

---8<---

```yaml
title: "Riehl E.4: Disjoint coproducts and universal (pullback-stable) colimits"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.4:def-disjoint-coproduct, riehl:E.4:def-universal-colimit]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (printed folio = PDF page − 20).
- Section: Epilogue §E.4 ("Grothendieck toposes"), the exactness vocabulary introduced for Giraud's theorem, printed p. 257 (PDF p. 277).
- Items: `riehl:E.4:def-disjoint-coproduct`, `riehl:E.4:def-universal-colimit`.

## Background

A coproduct is *disjoint* when its injections are monic and the pullback of two distinct injections is initial; a colimit cone is *universal* (pullback-stable) when pulling every leg back along an arbitrary map again yields a colimit cone over the pulled-back diagram. Together these are the exactness half of Giraud's characterization of Grothendieck toposes, and they are the defining conditions of extensive and of infinitary-pretopos-style categories. See [nLab: extensive category](https://ncatlab.org/nlab/show/extensive+category) and [nLab: pullback-stable colimit](https://ncatlab.org/nlab/show/pullback-stable+colimit).

## Current state in the library

Verified ABSENT for both, though — as the verifier stressed — every ambient ingredient exists, so this is a "not yet written" gap and not a "not derivable" one.

- Disjointness: `Structure/Cocartesian.v` defines `Coprod`, `merge`, `inl`, `inr`, `left`, `right`, `cover`, `paws` and their calculus, and contains **zero** occurrences of `monic` (verified by count); there is no `Monic inl`, no `inl_monic`, and nothing anywhere pulls one coproduct injection back against another (checked in `Structure/Pullback.v`, `Theory/Morphisms/Stability.v`, and every `Instance/`). There is no strict-initial-object statement. `extensive` occurs twice, both prose — `Structure/Initial.v:29` is the unrelated adverb and `Structure/Cocartesian.v:103` is a bare Lack–Walters citation with no definition following.
- Universality: `rg -i 'universal colimit|stable colimit|van Kampen colimit'` → 0 hits. The verifier independently confirmed that **every** "stable under pullback" hit concerns a *morphism class*, never a colimit cone: `Theory/Morphisms/Stability.v:226` `monic_pullback_stable`, `:264` `iso_pullback_stable`, and `Structure/Regular.v:79` `regular_stable {x y z} (f : x ~> z) (g : y ~> z) : RegularEpi f → RegularEpi (pullback_snd f g (pullback f g))`. That last one is the nearest miss and is strictly weaker: it says the pulled-back map coequalizes *some* pair, not that the pullbacks of a given colimit cone's legs form a colimit cone over the pulled-back diagram.
- Base change is half-built: `Construction/Slice/Pullback.v` defines only `Bang_Functor` (`:50`, `Σ_f`) and `Star_Functor` (`:67`, `f*`), with the would-be adjunction **commented out** at `:114-121`, so no cocontinuity of base change is available either.
- `descent` has 89 hits, every one the elementary sense of a map descending through an epi or coequalizer (`Structure/Regular.v`, `Structure/Coequalizer.v`); no descent condition for colimits.

## Work to be done

Suggested modules: `Structure/Cocartesian/Disjoint.v`, `Structure/Colimit/Universal.v`.

1. Define a disjoint binary coproduct: `Monic inl`, `Monic inr`, and the pullback of `inl` against `inr` is an initial object. State it over the existing `Structure/Cocartesian.v` API and `Structure/Pullback.v`'s `IsPullback`, in the apex-pinned form `Theory/Morphisms/Stability.v` already uses so the pasting toolkit applies. Add the indexed/infinitary version over `Structure/Limit/Product.v`'s discrete-diagram encoding (`Instance/Discrete.v`), since Giraud's condition is about arbitrary small coproducts.
2. Prove the standard consequences that make the definition usable: a disjoint coproduct has a strict initial object, and disjointness is inherited by the slices — each is a small lemma but each is what downstream proofs actually call.
3. Define a universal (pullback-stable) colimit cone: given a colimit cone over `F : J ⟶ C` with apex `c` and any `g : b ~> c`, the pullbacks of the legs along `g` form a colimit cone over the pulled-back diagram. State it cone-level, following the precedent set by `Construction/Comma/Limit.v`'s `PreservesImageLimit` — the apex-only reading is genuinely insufficient here for the same reason it is there, since the legs would be unconstrained.
4. Prove the two closure lemmas Giraud's proof needs: universal colimits are stable under composition of base changes, and a colimit that is universal is preserved by every `Star_Functor f*` (`Construction/Slice/Pullback.v:67`), which is the formulation "base change is cocontinuous".
5. Record the relation to the classes already in the tree: `Structure/Regular.v:79` `regular_stable` is the morphism-class shadow of universality, and `Structure/Distributive.v` is a genuinely different and weaker condition. Say so in the file header so a reader does not mistake either for this.

In-tree donors: `Structure/Cocartesian.v`, `Structure/Initial.v`, `Structure/Pullback.v`, `Theory/Morphisms/Stability.v` (the apex-pinned `IsPullback` and its pasting lemmas), `Structure/Colimit.v`, `Structure/Limit/Preservation.v`, `Construction/Slice/Pullback.v`, `Instance/Discrete.v`.

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.4, printed p. 257, PDF p. 277); setoid discipline — `≈` on morphisms, never `=`
- [ ] Disjointness defined for binary **and** small-indexed coproducts, with strict initiality derived
- [ ] Universality defined **cone-level** (not apex-only), with the reason recorded in the file header
- [ ] Base change preserves universal colimits, proved over `Star_Functor`
- [ ] The header distinguishes these notions from `regular_stable` (`Structure/Regular.v:79`) and from `Structure/Distributive.v`, both of which are weaker and unrelated
- [ ] At least one witness: coproducts in `Sets` (or `FinSet`) are disjoint, so neither predicate is stated vacuously
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Structure/Cocartesian/Disjoint.v
coqc -R . Category Structure/Colimit/Universal.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions DisjointCoproduct.
Print Assumptions disjoint_strict_initial.
Print Assumptions UniversalColimit.
Print Assumptions universal_colimit_base_change.
```
Reviewer: statements match Riehl §E.4 (printed p. 257) — disjointness requires monic injections *and* an initial pullback, and universality is quantified over a colimit *cone*, with the pulled-back legs required to be colimiting, not merely the apex.

## Dependencies

None blocking.

Coordination (not a blocking dependency): #566 proves that coproducts commute with pullback **in `Set`** (`Instance/Sets/Extensive.v`). That is the concrete instance of the universality condition defined here; the two should share this definition rather than each spelling out its own.

<!-- catalog: {"ids":["riehl:E.4:def-disjoint-coproduct","riehl:E.4:def-universal-colimit"],"deps":[]} -->

---8<---

```yaml
title: "Riehl E.4: Giraud's theorem"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:E.4:thm1]
deps_item_ids: [riehl:E.4:def-grothendieck-topos, riehl:E.4:def-disjoint-coproduct, riehl:E.4:def-universal-colimit]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition (printed folio = PDF page − 20).
- Section: Epilogue §E.4 ("Grothendieck toposes"), Theorem E.4.1, printed p. 257 (PDF p. 277).
- Item: `riehl:E.4:thm1`.

## Background

Giraud's theorem characterizes Grothendieck toposes intrinsically: a category is (equivalent to) a category of sheaves on a small site exactly when it is locally small with finite limits and all small colimits, its coproducts are disjoint and universal, its colimits are universal, its equivalence relations are effective, and it has a small separating set. It is the bridge between the site-theoretic and the exactness-theoretic descriptions of a topos. See [nLab: Giraud's theorem](https://ncatlab.org/nlab/show/Giraud%27s+theorem) and [nLab: Grothendieck topos](https://ncatlab.org/nlab/show/Grothendieck+topos).

## Current state in the library

Verified ABSENT, and absent in an over-determined way: neither side of the biconditional is currently expressible.

- The word occurs twice in `.v` files and both are prose: `Structure/Topos.v:90-93` ("an elementary topos with a small generating set, all small colimits, coproducts disjoint and universal, and equivalence relations effective is exactly a category of sheaves on a small site") and `Construction/Grothendieck.v:72` (the historical Jean Giraud, on fibrations). Neither is a Coq statement, and `Structure/Topos.v` contains no biconditional of any kind — its only topos definition is `Class ElementaryTopos` at `:112`.
- Every technical term of the hypothesis list is separately missing or only half-present, which is why this issue depends on so much: no Grothendieck-topos definition; no disjointness and no universality of colimits; no internal equivalence relation, hence no effectiveness (the one adjacent construct is `Structure/Regular.v:46` `kernel_pair`, and the verifier singles it out as the piece to build on); the separating-set notion exists only as its dual, `Adjunction/SAFT.v:99` `Cogenerator`; and `Cocomplete` (`Structure/Complete.v:119`) has no inhabitant anywhere.
- One hypothesis has **no statable counterpart at all** and this must be planned for rather than discovered mid-proof: local smallness. The verifier confirmed that "locally small" occurs 4 times, all prose, and that the library handles size by universe polymorphism instead of a smallness predicate. Clause (i) of the theorem therefore has to be either carried as data (the `Adjunction/SAFT.v` idiom, where smallness is a supplied index `Type`) or explicitly scoped out in the file header. That choice is part of this issue's work, not a detail.

## Work to be done

Suggested module: `Structure/Topos/Giraud.v`.

1. State the theorem over the vocabulary this chapter's other issues supply: the Giraud axioms as a record (`GiraudAxioms C`) bundling finite limits, small colimits, disjoint and universal coproducts, universal colimits, effective equivalence relations, and a small separating set, with smallness supplied as data in the `SubobjectIndex` style and the decision disclosed in the header.
2. Prove the easy direction first and land it independently: **every Grothendieck topos satisfies the Giraud axioms**. Each clause is a transport along the lex reflection from presheaves, where the corresponding property is either already available or straightforward, so this half is a genuine, reviewable deliverable even if the converse is deferred.
3. The converse — Giraud axioms ⇒ equivalent to sheaves on a small site — is the flagship half. Build the canonical site on the separating set with the coverage generated by jointly-epimorphic families, the comparison functor into presheaves on it, and prove the comparison an equivalence onto the sheaves. This consumes the re-founded sheaf/site development of #890 (whose current `Site` class is single-family and finitary, and whose `Sheaf` predicate is disclosed-degenerate), so it cannot honestly be attempted before that lands.
4. If the converse is not completed in one pass, ship the easy direction plus the axiom record and record the converse in `docs/INHABITATION.md` as a parametric/conditional target, per the convention the library already uses for GAFT and SAFT. Do **not** state it as an axiom.
5. Repoint `Structure/Topos.v:90-93` at whatever is actually proved, so the header stops describing an external theorem as though it were context-free background.

In-tree donors: `Structure/Topos.v`, `Theory/Sheaf.v`, `Theory/Sheaf/Category.v`, `Construction/Reflective.v`, `Structure/Regular.v` (`kernel_pair`), `Adjunction/SAFT.v` (the smallness-as-data idiom and `Cogenerator`), `Construction/Subcategory.v`, `Functor/Hom/Yoneda.v`.

## Definition of Done

- [ ] Statement fidelity to the book (Riehl §E.4 Theorem E.4.1, printed p. 257, PDF p. 277); setoid discipline — `≈` on morphisms, never `=`
- [ ] The Giraud axioms are recorded as a single named structure over the definitions this chapter supplies, not re-spelled inline
- [ ] The local-smallness clause is either carried as data or explicitly scoped out, with the decision stated in the file header
- [ ] The direction "Grothendieck topos ⇒ Giraud axioms" is **proved**
- [ ] The converse is either proved or recorded in `docs/INHABITATION.md` as a conditional target — never asserted as an axiom or left `Admitted`
- [ ] `Structure/Topos.v:90-93`'s prose is repointed at the in-tree statement
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (flagship-level)

## Verification

```bash
coqc -R . Category Structure/Topos/Giraud.v
make && make todo
nix build .#category-theory_8_19 && nix build .#category-theory_8_20
```
```coq
Print Assumptions GiraudAxioms.
Print Assumptions grothendieck_satisfies_giraud.
(* and, if the converse is proved: *)
Print Assumptions giraud_theorem.
```
Reviewer: statement matches Riehl §E.4 Theorem E.4.1 (printed p. 257) — all six clauses appear, the coproduct conditions are both disjointness and universality, equivalence relations are required *effective* (not merely internal), and any clause carried as an assumption rather than derived is disclosed in the file header.

## Dependencies

Depends on: riehl:E.4:def-grothendieck-topos
Depends on: riehl:E.4:def-disjoint-coproduct
Depends on: riehl:E.4:def-universal-colimit
Depends on: #960 — internal equivalence relations, kernel pairs, and effective quotients.
Depends on: #447 — generating (separating) sets of objects.
Depends on: #890 — the re-founded sheaf/site development (the target of the converse).

<!-- catalog: {"ids":["riehl:E.4:thm1"],"deps":["riehl:E.4:def-grothendieck-topos","riehl:E.4:def-disjoint-coproduct","riehl:E.4:def-universal-colimit","#960","#447","#890"]} -->

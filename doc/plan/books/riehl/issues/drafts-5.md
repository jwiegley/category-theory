title: "Riehl 5.1: The maybe monad on Sets — its Kleisli category of partial functions, its pointed-set algebras, and monadicity"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.3:example2, riehl:5.2:example6]
deps_item_ids: []
deps_pending: []

## Source
Emily Riehl, *Category Theory in Context*, 2nd edition (the author's recompiled copy; printed page = PDF page − 20). §5.2 Example 5.2.6 (printed p. 189, PDF pp. 209–210) and §5.3 Example 5.3.2 (printed p. 196, PDF p. 216). Items: `riehl:5.2:example6`, `riehl:5.3:example2`.

This issue also formalizes clause (i) of §5.1 Example 5.1.4 (printed p. 183, PDF p. 203) and clause (i) of §5.2 Example 5.2.11 (printed p. 191, PDF p. 211) — the maybe monad as the monad of the free-pointed-set adjunction, and its Kleisli category as partial functions. Those two catalogue rows are carried by sibling issues (§5.1's self-adjoint-exponential issue for Example 5.1.4, §5.2's writer/state issue for Example 5.2.11), which cross-reference this one.

Example 5.2.6 is a four-clause catalogue and only clause (i) is worked here; clause (ii) is recorded on #465, clause (iii) on #471 and clause (iv) on #463.

## Background
Adjoining a disjoint basepoint is left adjoint to forgetting it, so `(−) + 1` carries a monad structure — the [maybe monad](https://ncatlab.org/nlab/show/maybe+monad) — whose Kleisli morphisms are exactly the [partial functions](https://ncatlab.org/nlab/show/partial+function) and whose algebras are the pointed sets. Because every algebra is free up to isomorphism, that Kleisli adjunction is itself monadic.

## Current state in the library
The Kleisli category is built, but the monad it is the Kleisli category *of* is not. `Instance/Sets/Par.v:27` defines `Part : Category` with `hom x y := SetoidMorphism x (option y)`, identity `Some` and composition by `option`-bind, and `Instance/Coq/Par.v:53` defines the `Type`-level `Par` the same way; both files assert in header prose (`Instance/Sets/Par.v:16-19` and `:108`, `Instance/Coq/Par.v:34`) that this *is* the Kleisli category of the maybe monad and that it is equivalent to pointed sets — neither claim is a theorem anywhere. `Theory/Coq/Maybe.v:94` `Maybe_Monad` is an instance of the deliberately law-free applied-layer class `Theory/Coq/Monad.v:32` (whose header at lines 28-30 states the laws are not recorded as fields), and `Theory/Coq/Monad/Proofs.v` proves the `IsMonad` lawfulness bridge only for `Identity` (`:57`), the reader (`:63`) and `Compose` (`:90`) — never for `Maybe`; `Theory/Coq/Maybe/Proofs.v` contains no monad-law lemma at all. Consequently the generic `Kleisli` construction (`Monad/Kleisli.v:38`) is never instantiated at the maybe monad, `Theory/Coq/Maybe.v:29`'s comment "its algebras are the pointed objects" is unproved, no category of pointed sets exists, and `Monadic` (`Monad/Comparison.v:273`) has exactly one inhabitant tree-wide, `Identity_Monadic` (`Monad/Monadicity/Examples.v:155`).

Two further facts recorded by the Phase-D verifier and worth carrying into the work: `Instance/Sets/Par.v` contains `admit` at lines 263 and 265, but both sit inside *Aborted* scratch lemmas (`from_to`, `to_from`) rather than in `Part` or the `Qed`-closed `to_from_impossible`/`from_to_impossible`; and Riehl's generalisation of clause (i) — adjoining a *fixed object* in any category with coproducts — has no in-tree counterpart either.

## Work to be done
- Build `Maybe : Sets ⟶ Sets` (`x ↦ x + 1` over the in-tree coproduct, `Instance/Sets/Cocartesian.v:28`) and equip it with a genuine `@Monad Sets Maybe` (`Theory/Monad.v`): unit the left injection, multiplication the codiagonal on the two adjoined points. Do the same at the level of generality Riehl states: for a fixed object `s` of any category with binary coproducts, `(−) + s` is a monad.
- Prove `Kleisli Maybe ≅ Part` (`Monad/Kleisli.v`, `Instance/Sets/Par.v`) — an isomorphism of categories is available here because both sides have `Sets` as objects and the same hom-setoids; state it as such and record where it degrades to an equivalence at the `Coq` level (`Instance/Coq/Par.v`).
- Construct the category of pointed sets (either directly or as the coslice `Construction/Slice.v:169` under the terminal setoid — the route already named in that file's prose at `:82`), and prove `EilenbergMoore Maybe ≅ Sets_*`, matching a `TAlgebra` structure map to the choice of basepoint and algebra homomorphisms to basepoint-preserving maps.
- Prove Example 5.3.2: the Kleisli adjunction `Kleisli_Free ⊣ Kleisli_Forget` (`Monad/Kleisli/Adjunction.v`) for the maybe monad is monadic, i.e. `Monadic Kleisli_Forget`, by composing the previous two identifications with the partial-maps/pointed-sets equivalence of #708.
- Suggested modules: `Monad/Instance/Maybe.v` (the monad), `Instance/Sets/Par/Kleisli.v` (the `Part` identification and the monadicity). Donors: `Instance/Sets/Par.v`, `Instance/Coq/Par.v`, `Monad/Kleisli.v`, `Monad/Kleisli/Adjunction.v`, `Monad/Eilenberg/Moore.v`, `Monad/Comparison.v`, `Construction/Slice.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Ex. 5.1.4(i), §5.2 Ex. 5.2.6(i)/5.2.11(i) and §5.3 Ex. 5.3.2 (paraphrased above); setoid `≈` discipline on morphisms, never `=`.
- [ ] `@Monad Sets Maybe` proved (not merely an ops-only `Theory/Coq/Monad.v` instance), together with the coproduct-with-a-fixed-object generalisation.
- [ ] `Kleisli Maybe ≅ Part` and `EilenbergMoore Maybe ≅ Sets_*` proved.
- [ ] `Monadic Kleisli_Forget` proved for the maybe monad — the library's second inhabited `Monadic` witness after `Identity_Monadic`.
- [ ] Library hygiene while here: the prose claims at `Instance/Sets/Par.v:16-19`, `:108`, `Instance/Coq/Par.v:34` and `Theory/Coq/Maybe.v:29` are pointed at the new theorems instead of asserting them, and the two `admit`s in the Aborted scratch lemmas at `Instance/Sets/Par.v:263,265` are removed or the whole scratch block is deleted.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (core theory stays axiom-free per docs/AXIOMS.md scoping; any stdlib axiom used in `Instance/` is enumerated there).
- [ ] `Print Assumptions` closed for the monad, both identifications, and the monadicity witness.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`).
- [ ] `make todo` adds no new hits.
- [ ] docs/INHABITATION.md updated: a concrete non-trivial monadic adjunction is a first in-tree witness.

## Verification
- `coqc -R . Category Monad/Instance/Maybe.v` and `coqc -R . Category Instance/Sets/Par/Kleisli.v` compile after their dependencies.
- `Print Assumptions` on the `@Monad Sets Maybe` instance, on the `Kleisli Maybe ≅ Part` isomorphism, on the `EilenbergMoore Maybe ≅ Sets_*` comparison and on the `Monadic` witness.
- `rg -n 'admit' Instance/Sets/Par.v` returns nothing.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer confirms the statements match Riehl §5.2 Example 5.2.11(i) and §5.3 Example 5.3.2.

## Dependencies
Depends on: #261 (`Set_*`, the category of pointed sets)
Depends on: #708 (the category of partial maps is equivalent to the category of pointed sets)

<!-- catalog: {"ids":["riehl:5.3:example2","riehl:5.2:example6"],"deps":["#261","#708"]} -->

---8<---
title: "Riehl 5.1/5.5: The free-category monad on quivers, and the monadicity of Cat over Quiver"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:example7]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20). §5.5 Example 5.5.7 clause (iv) (printed p. 205, PDF pp. 225–226). Item: `riehl:5.5:example7`.

This issue also formalizes clause (vi) of §5.1 Example 5.1.4 (printed p. 184, PDF p. 204) — the free-category monad on quivers — whose catalogue row is carried by §5.1's self-adjoint-exponential issue. Of Example 5.5.7's four clauses, clause (i) is recorded on #465, clause (ii) on #474 and clause (iii) is the subject of §5.5's restriction-functor issue; only clause (iv) is worked here.

## Background
The [free category](https://ncatlab.org/nlab/show/free+category) on a [quiver](https://ncatlab.org/nlab/show/quiver) is left adjoint to the underlying-quiver functor; the induced monad sends a quiver to its quiver of finite directed paths, and the forgetful functor is [monadic](https://ncatlab.org/nlab/show/monadic+functor), factoring through the category of reflexive quivers.

## Current state in the library
The generating adjunction exists and is registered: `Construction/Free/Quiver.v:412` defines `Forgetful : StrictCat ⟶ QuiverCategory` and `:550` defines `FreeForgetfulAdjunction : Adjunction FreeCatFunctor Forgetful`, built from the universal arrows `UniversalArrowQuiverCat` (`_CoqProject:72`). What is missing is everything on top of it. The induced monad is never formed, even though `Adjunction_Induced_Monad` would produce it in one application — `Test/Issue138.v:65` only `Check`s that `Forgetful ◯ FreeCatFunctor` is an endofunctor of `QuiverCategory`, which asserts endofunctoriality, not monadhood. Monadicity is asserted only in prose, at `Construction/Free.v:75-78` (citing Leinster, Thm. 6.5.2), and never proved; `Monadic` (`Monad/Comparison.v:273`) has one inhabitant tree-wide, `Identity_Monadic` (`Monad/Monadicity/Examples.v:155`). There is no category of reflexive quivers (`rg -i 'reflexive quiver|rQuiver'` → 0 hits), so the factorisation has no target.

A deliberate deviation must be preserved rather than "fixed": the adjunction is stated over `StrictCat`, not the weak `Cat`, because a category's underlying quiver is not invariant under natural isomorphism. `Construction/Free/Quiver.v:41-46` explains this and `Test/Issue138.v:67-76` `Fail`-checks that `Forgetful` is *not* typable as `Cat ⟶ QuiverCategory`. The monadicity statement therefore has to be made about `StrictCat`, with the discrepancy from Riehl's `Cat` disclosed in the file header.

## Work to be done
- Form the path monad `Forgetful ◯ FreeCatFunctor` on `QuiverCategory` as an `Adjunction_Induced_Monad` of `FreeForgetfulAdjunction`, and spell out what its unit and multiplication compute (inclusion of unary paths; concatenation of paths of paths).
- Build the category `rQuiver` of reflexive quivers (a quiver with a chosen endo-arrow at each vertex) and reflexive-quiver morphisms, together with the underlying-reflexive-quiver functor `StrictCat ⟶ rQuiver` and the forgetful `rQuiver ⟶ QuiverCategory`, and prove the factorisation of `Forgetful`.
- Prove `Monadic Forgetful` for `StrictCat ⟶ QuiverCategory` by Beck's theorem (`Monad/Monadicity/Beck.v:739` `beck_monadicity` needs `CreatesUSplitCoequalizers`), and likewise for `StrictCat ⟶ rQuiver`; state clearly in the header which of Riehl's two monadic functors is obtained over `StrictCat` rather than `Cat` and why.
- Suggested modules: `Monad/Instance/Path.v` (the monad), `Construction/Free/Quiver/Monadicity.v` (the two monadicity proofs). Donors: `Construction/Free/Quiver.v`, `Monad/Adjunction.v` (`Adjunction_Induced_Monad`), `Monad/Monadicity/Beck.v`, `Instance/StrictCat.v`.
- **Module coordination:** do *not* introduce a second reflexive-quiver module. `Instance/RQuiver.v` is already proposed by #979, and the reflexive-quiver notion together with the underlying-reflexive-quiver functor is the deliverable of #906; consume both rather than redefining, and add only the factorisation and monadicity here.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Ex. 5.1.4(vi) and §5.5 Ex. 5.5.7(iv); setoid `≈` on morphisms, never `=`.
- [ ] The path monad on `QuiverCategory` is an in-tree `@Monad`, obtained from the existing adjunction rather than re-built by hand.
- [ ] `rQuiver` exists with the factorisation `StrictCat ⟶ rQuiver ⟶ QuiverCategory` proved, reusing the `Instance/RQuiver.v` carrier of #979/#906 rather than introducing a second one.
- [ ] Monadicity proved for both forgetful functors, via `beck_monadicity`.
- [ ] Library defect fixed while here: `Construction/Free.v:75-78` currently asserts this monadicity as established fact with a bibliographic citation; repoint it at the new theorem (or soften it to a forward reference) so the essay stops overclaiming in-tree content.
- [ ] The `StrictCat`-versus-`Cat` deviation is disclosed in the new file's header, cross-referencing `Construction/Free/Quiver.v:41-46` and `Test/Issue138.v:67-76`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the path monad and both monadicity witnesses.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (a second concrete monadicity witness is index-worthy).

## Verification
- `coqc -R . Category Monad/Instance/Path.v`, `coqc -R . Category Instance/RQuiver.v`, `coqc -R . Category Construction/Free/Quiver/Monadicity.v` compile after their dependencies.
- `Print Assumptions` on the path monad and on each `Monadic` witness.
- `rg -n 'Leinster' Construction/Free.v` shows the prose now cites the in-tree theorem.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the statements against Riehl §5.5 Example 5.5.7(iv), including the `StrictCat` caveat.

## Dependencies
Depends on: #906 (reflexive quivers and the underlying reflexive quiver of a category)
Depends on: #979 (which already proposes the `Instance/RQuiver.v` module — coordinate the layout, do not duplicate it)
Depends on: #484 (the completed Beck monadicity theorem — the general converse and creation criterion)

<!-- catalog: {"ids":["riehl:5.5:example7"],"deps":["#906","#979","#484"]} -->

---8<---
title: "Riehl 5.1: The self-adjoint exponential S^(−) and its continuation monad (double power set, double dual)"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.1:example4]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.1 Example 5.1.4, clauses (vii) and (viii) (printed p. 185, PDF p. 205). Item: `riehl:5.1:example4`.

Example 5.1.4 is an eight-clause catalogue of monads induced by familiar adjunctions; this issue carries its catalogue row and works clauses (vii)–(viii). Its other clauses are distributed as follows and each of the issues below cross-references this one: (i) the maybe monad — §5.1's maybe-monad issue; (ii) the free monoid / list monad — #471; (iii) the free `R`-module monad — #472; (iv) the free group monad — #442; (v) the ultrafilter monad — §5.1's ultrafilter-monad issue; (vi) the free-category monad on quivers — §5.1/§5.5's quiver issue.

## Background
In a cartesian closed category the functor `S^(−) : C^op ⟶ C` is right adjoint to its own opposite, since `C(a, S^b) ≅ C(a × b, S) ≅ C(b, S^a)`; the induced monad `S^{S^(−)}` is the [continuation monad](https://ncatlab.org/nlab/show/continuation+monad). Taking `C = Set` and `S = 2` recovers the double [power set](https://ncatlab.org/nlab/show/power+set) monad, and `C = Vect_k`, `S = k` the double-dual monad.

## Current state in the library
Nothing of this exists. `rg -i 'self-adjoint|mutually right adjoint'` returns two hits, both saying the *identity* functor is self-adjoint (`Adjunction/Compose.v:29`, `Instance/Adjoints.v:17`); `rg -i 'continuation'` returns only header prose (`Monad/Thunkable.v:105`, `Theory/Lawvere.v:98`, `Theory/Coq.v`), and `rg -i 'double power'` returns nothing. The one in-tree double-dual construction assumes what is to be built: `Structure/Monoidal/StarAutonomous.v:252` defines `double_dual d := dual d ◯ (dual d)^op` and `:261`'s `Class StarAutonomous` *posits* `star_double_dual : x ≅ double_dual dualizer x` as a field — an isomorphism, which the continuation unit is precisely not. The exponential itself is available (`Structure/Cartesian/Closed.v`, with `Instance/Sets/Cartesian/Closed.v` for `Sets`), so the adjunction is expressible; it is simply never formed, and no monad is derived from it.

## Work to be done
- In a cartesian closed `C`, define `Exp_op S : C^op ⟶ C` (object part `x ↦ S^x`, morphism part the precomposition transpose) and its opposite, and prove the hom-set adjunction `C^op(x, S^(−) y) ≅ C(y, S^x)` natural in both variables — i.e. `(S^(−))^op ⊣ S^(−)` — using the currying adjunction of #239.
- Form the induced continuation monad `S^{S^(−)} : C ⟶ C` by `Adjunction_Induced_Monad`, and identify its unit (double transpose of evaluation) and multiplication concretely.
- Instantiate at `Sets` with `S` the two-element setoid, obtaining the double power set monad, and record in the header the `Vect_k`/`k` double-dual instance as a consequence available once a vector-space category exists (#258).
- Suggested module: `Monad/Instance/Continuation.v`. Donors: `Structure/Cartesian/Closed.v`, `Instance/Sets/Cartesian/Closed.v`, `Construction/Opposite.v`, `Monad/Adjunction.v`, `Theory/Adjunction.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Example 5.1.4(vii)–(viii); setoid `≈` on morphisms, never `=`.
- [ ] The self-adjunction `(S^(−))^op ⊣ S^(−)` is proved from the cartesian closed structure, with naturality in both variables.
- [ ] The continuation monad is obtained as `Adjunction_Induced_Monad` of that adjunction, not re-derived.
- [ ] The `Sets`/`S = 2` instance is exhibited and identified with the double power set monad.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the adjunction, the monad, and the `Sets` instance.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is deemed flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/Continuation.v` compiles after its dependencies.
- `Print Assumptions` on the self-adjunction and on the continuation monad.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the hom-set bijection against Riehl §5.1 Example 5.1.4(vii).

## Dependencies
Depends on: #239 (the currying adjunction and naturality of evaluation)
Depends on: #704 (the contravariant powerset functor on Sets and the double-powerset unit)

<!-- catalog: {"ids":["riehl:5.1:example4"],"deps":["#239","#704"]} -->

---8<---
title: "Riehl 5.1/5.2: The writer monad of a monoid object and the state monad of the currying adjunction"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.2:example11]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.2 Example 5.2.11, clause (iii) (printed p. 191, PDF pp. 211–212). Item: `riehl:5.2:example11`.

This issue also formalizes clause (iii) of §5.1 Example 5.1.5 (printed p. 185, PDF pp. 205–206) — the monad `(−) × ℕ` and its monoid-object generalization — whose catalogue row is carried by §5.1's Giry-monad issue. Example 5.2.11 is a four-clause catalogue whose row this issue carries: clause (i) is worked in §5.1's maybe-monad issue, clause (ii) is recorded on #471, clause (iv) in §5.1's Giry-monad issue, and clause (iii) here.

## Background
A monoid object `m` in a monoidal category makes `m ⊗ (−)` a monad — the [writer monad](https://ncatlab.org/nlab/show/writer+monad), whose unit inserts the monoid unit and whose multiplication multiplies the two accumulated values. Dually to the reader, the currying adjunction `S × (−) ⊣ (−)^S` induces the [state monad](https://ncatlab.org/nlab/show/state+monad) `(S × (−))^S`, whose Kleisli morphisms `a → b` are exactly the maps `a × S → b × S`.

## Current state in the library
Both monads exist only as law-free applied-layer instances or as duals. `Theory/Coq/Tuple.v:104` gives `Instance Tuple_Monad x `{Monoid x} : Monad (Tuple x)` — the writer over an arbitrary monoid — but it inhabits `Theory/Coq/Monad.v:32`, the ops-only class whose header (lines 28-30) states the laws are *not* fields, and `Theory/Coq/Monad/Proofs.v` supplies the `IsMonad` bridge only for `Identity`, the reader and `Compose`, never for `Tuple`. Riehl's generalisation — a monoid object in a monoidal category yields the monad `m ⊗ (−)` — is nowhere proved, despite both `MonoidObject` (`Structure/Monoid.v`) and `Monoidal` (`Structure/Monoidal.v`) being in force. `Monad/Graded.v:356`'s `GradedWriter (W : GradeMonoid) : @GradedMonad Coq W (fun _ => Id[Coq])` is a different object (a constant identity family with the log living in the grades), not this monad.

For the state monad there is nothing at all: `rg -i 'state monad'` returns three comments (`Comonad/Duality.v:96`, `:99`, `Instance/Coq/Comonad/Store.v:31`), and `Instance/Coq/Comonad/Store.v:363` builds only the dual `Store` *comonad* via `Build_Monad` on `Sets^op`. No `S × (−) ⊣ (−)^S` adjunction is formed at `Sets` (the cartesian closed structure is present at `Instance/Sets/Cartesian/Closed.v`, whose `:24` mentions the adjunction only in a remark), and the generic `Kleisli` (`Monad/Kleisli.v:38`) is never instantiated at a state monad.

## Work to be done
- Prove: for a monoid object `m` in a monoidal category `V`, `m ⊗ (−) : V ⟶ V` is a monad, with unit `λ⁻¹` followed by `unit ⊗ id` and multiplication built from the associator and the monoid multiplication. Instantiate at `(Sets, ×)` with a monoid on the natural numbers to recover Riehl's `(−) × ℕ`, and use it to give `Theory/Coq/Tuple.v:104`'s `Tuple_Monad` its missing `IsMonad` witness.
- Build the adjunction `S × (−) ⊣ (−)^S` at a cartesian closed category from #239, form the state monad `(S × (−))^S` by `Adjunction_Induced_Monad`, and prove the Kleisli hom-set identification `Kleisli(state)(a, b) ≅ Sets(a × S, b × S)` naturally, which is Riehl's clause (iii) of Example 5.2.11.
- Suggested modules: `Monad/Instance/Writer.v`, `Monad/Instance/State.v`. Donors: `Structure/Monoid.v`, `Structure/Monoidal.v`, `Structure/Cartesian/Closed.v`, `Monad/Adjunction.v`, `Monad/Kleisli.v`, `Theory/Coq/Tuple.v`, `Theory/Coq/Monad/Proofs.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Example 5.1.5(iii) and §5.2 Example 5.2.11(iii); setoid `≈` on morphisms, never `=`.
- [ ] `m ⊗ (−)` proved a monad for a monoid object in an arbitrary monoidal category, with the `(Sets, ×)` instance exhibited.
- [ ] `Theory/Coq/Tuple.v`'s `Tuple_Monad` given an `IsMonad` lawfulness witness in `Theory/Coq/Monad/Proofs.v`, closing a gap that file's existing coverage (Identity / reader / Compose) leaves open.
- [ ] The state monad built from the currying adjunction, with the Kleisli hom-set identification proved natural.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the writer monad, the `IsMonad` bridge, the state monad, and the Kleisli identification.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/Writer.v` and `coqc -R . Category Monad/Instance/State.v` compile after their dependencies.
- `Print Assumptions` on each principal artifact, including the `IsMonad` witness for `Tuple`.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the Kleisli identification against Riehl §5.2 Example 5.2.11(iii).

## Dependencies
Depends on: #239 (the currying adjunction and naturality of evaluation)

<!-- catalog: {"ids":["riehl:5.2:example11"],"deps":["#239"]} -->

---8<---
title: "Riehl 5.1/5.2: The Giry monad on measurable spaces, and its Kleisli category of Markov kernels"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.1:example5]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.1 Example 5.1.5, clause (iv) (printed p. 185, PDF pp. 205–206). Item: `riehl:5.1:example5`.

This issue also formalizes clause (iv) of §5.2 Example 5.2.11 (printed p. 192, PDF p. 212) — the Kleisli category of the Giry monad as measurable spaces and Markov kernels — whose catalogue row is carried by §5.2's writer/state issue. Example 5.1.5 is a four-clause catalogue of monads *not* presented via an adjunction, and this issue carries its row: clause (i), the covariant power set monad, is recorded on #466; clause (ii), the free commutative monoid (multiset) monad, on #471; clause (iii), the monad `(−) × ℕ`, is worked in §5.2's writer/state issue; clause (iv) here.

## Background
The [Giry monad](https://ncatlab.org/nlab/show/Giry+monad) sends a measurable space to the space of probability measures on it, carrying the smallest σ-algebra making every evaluation measurable; its unit is the Dirac measure and its multiplication is integration. Its Kleisli morphisms are exactly the [Markov kernels](https://ncatlab.org/nlab/show/Markov+kernel), so a Kleisli endomorphism of a finite discrete space is a Markov chain.

## Current state in the library
Nothing concrete. The library axiomatises the *abstract* setting instead: `Structure/Monoidal/Markov.v` defines Markov categories synthetically (copy/discard plus semicartesian) and cites the Giry monad only in its header essay at `:56`, `:59`, `:65`; `rg -i 'measurable|probability measure|Meas\b'` finds no category of measurable spaces, no `Prob` functor and no monad. `Construction/Cospan/BlackBox.v` and `Structure/Monoidal/CopyDiscard.v` likewise mention Markov kernels only in prose. So the abstract theory has no concrete model, which is exactly what docs/INHABITATION.md tracks.

## Work to be done
- Build `Meas`: a measurable space as a carrier setoid together with a σ-algebra (a family of subsets closed under complement and countable union, presented as data so no classical principle is smuggled in), and measurable functions as morphisms; prove the category laws.
- Build `Prob : Meas ⟶ Meas`: probability measures on a measurable space, with the σ-algebra generated by the evaluation maps `ev_X`; prove functoriality (pushforward of measures).
- Equip `Prob` with the monad structure: unit the Dirac measure, multiplication by integration; discharge the unit and associativity laws. State honestly in the file header how much measure theory (integration of a measurable function against a measure) has to be developed in-tree, and scope the integral to what the monad laws need.
- Prove that `Kleisli Prob` is the category of measurable spaces and Markov kernels, and record the finite-discrete case as the Markov-chain example.
- Optionally close the loop with the abstract theory: exhibit `Kleisli Prob` as an instance of `Structure/Monoidal/Markov.v`'s `Markov` class, which would give that development its first concrete model.
- Suggested modules: `Instance/Meas.v`, `Monad/Instance/Giry.v`, `Instance/Meas/Markov.v`. Donors: `Instance/Sets.v`, `Theory/Monad.v`, `Monad/Kleisli.v`, `Structure/Monoidal/Markov.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Example 5.1.5(iv) and §5.2 Example 5.2.11(iv); setoid `≈` on morphisms, never `=`.
- [ ] `Meas` is a category in-tree; `Prob` is a functor; the Giry monad laws are proved.
- [ ] `Kleisli Prob` identified with measurable spaces and Markov kernels.
- [ ] The measure-theoretic scope (which integration facts are assumed as data versus proved) is disclosed in the file header, and any classical/choice principle used is enumerated in docs/AXIOMS.md.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond those disclosed above.
- [ ] `Print Assumptions` reported for `Meas`, `Prob`, the monad, and the Kleisli identification.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] docs/INHABITATION.md updated — this would be the first concrete model of the in-tree Markov-category axiomatics.

## Verification
- `coqc -R . Category Instance/Meas.v`, `coqc -R . Category Monad/Instance/Giry.v`, `coqc -R . Category Instance/Meas/Markov.v` compile after their dependencies.
- `Print Assumptions` on the Giry monad and the Kleisli identification, reconciled against docs/AXIOMS.md.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the unit/multiplication against Riehl §5.1 Example 5.1.5(iv) and the header's disclosure of measure-theoretic scope.

## Dependencies
None as filed issues (self-contained over `Instance/Sets.v`, `Theory/Monad.v` and `Monad/Kleisli.v`).

<!-- catalog: {"ids":["riehl:5.1:example5"],"deps":[]} -->

---8<---
title: "Riehl 5.1: Characterizations of an idempotent monad — μ invertible, μ monic, and ηT = Tη"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:5.1:exiii]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.1 Exercise 5.1.iii (printed p. 187, PDF p. 207). Item: `riehl:5.1:exiii`.

## Background
An [idempotent monad](https://ncatlab.org/nlab/show/idempotent+monad) admits three equivalent descriptions: the multiplication is invertible, the multiplication is monic, or the two whiskerings `ηT` and `Tη` of the unit agree. The exercise also asks for the standard source of examples, the monad induced by a [reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory).

## Current state in the library
The trailing clause is fully proved and the library goes beyond it; the characterisation theorem is not proved at all. `Construction/Reflective/Idempotent.v:81` takes the *first* description as the definition — `Class IdempotentMonad (M : C ⟶ C) `{@Monad C M} := { idem_join_iso {x} : IsIsomorphism (@join C M _ x) }` — so no equivalence with the other two is available. `:139` `join_iso_fmap_ret` proves only the forward implication (i) ⇒ (iii) (`fmap[M] ret ≈ ret (M x)` from invertibility of `join`), and the one genuine biconditional in the file, `:132` `join_iso_iff_ret_M_iso`, characterises (i) by invertibility of `ret` at `M x` — a condition Riehl does not list. The exercise's fourth clause is `:194` `Reflective_Monad := Adjunction_Induced_Monad (reflective_adj R)` with `:198` `Reflective_IdempotentMonad`, and the file additionally proves the converse `:345` `Idempotent_Reflective` and the Eilenberg–Moore equivalence `:464` `Idempotent_EM_Equivalence`.

Description (ii) is absent in both directions. The Phase-D verifier corrected one detail of the Phase-C record here and it matters for the implementer: lowercase "monic" *does* occur in `Construction/Reflective/Idempotent.v`, at lines 102 and 137, but only inside comments observing that an invertible `join` is monic — there is no lemma anywhere stating that a monic `join` is invertible, so the substantive gap stands.

## Work to be done
- State the three conditions over a monad `(T, η, μ)` on `C`: (i) `join` is invertible at every object; (ii) `join` is monic at every object; (iii) `fmap[T] ret ≈ ret (T x)` at every object (the two whiskerings agree). Prove the cycle (i) ⇒ (ii) ⇒ (iii) ⇒ (i); the last step is the substantive one, and it is where a two-sided inverse for `join` has to be produced from `ret`.
- Package the result as a single `idempotent_monad_iff` statement so downstream code can move between the presentations, and re-express `Construction/Reflective/Idempotent.v:81`'s class in terms of it (keeping the existing field as the definition, with the other two as derived characterisations, so no existing proof breaks).
- Note in the header that the in-tree conditions are stated objectwise (`IsIsomorphism` at each object) rather than as invertibility of the natural transformation `μ`; these agree in this setting and the header should say so.
- Suggested module: extend `Construction/Reflective/Idempotent.v`, or add `Monad/Idempotent/Characterization.v` if the file is already large. Donors: `Construction/Reflective/Idempotent.v`, `Theory/Monad.v`, `Theory/Morphisms.v` (`Monic`).

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Exercise 5.1.iii (all three conditions, proved equivalent); setoid `≈` on morphisms, never `=`.
- [ ] The (ii) ⇒ (i) direction is genuinely proved, not assumed; the derivation from monicity is the content of the exercise.
- [ ] The equivalence is packaged as one statement, and `IdempotentMonad`'s existing users continue to compile unchanged.
- [ ] The objectwise-vs-natural-transformation reading is disclosed in the header.
- [ ] The comments at `Construction/Reflective/Idempotent.v:102` and `:137` are updated to point at the new lemma instead of gesturing at it.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the three-way equivalence.
- [ ] Changed/new file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification
- `coqc -R . Category Construction/Reflective/Idempotent.v` (or the new module) compiles, and every existing consumer of `IdempotentMonad` still compiles.
- `Print Assumptions` on the three-way equivalence.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the three conditions against Riehl §5.1 Exercise 5.1.iii.

## Dependencies
None (self-contained over `Construction/Reflective/Idempotent.v` and `Theory/Monad.v`).

<!-- catalog: {"ids":["riehl:5.1:exiii"],"deps":[]} -->

---8<---

title: "Riehl 5.1: The ultrafilter monad on Sets, as a submonad of the double power set monad"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:5.1:exii]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.1 Exercise 5.1.ii (printed p. 186, PDF p. 206). Item: `riehl:5.1:exii`.

This issue also formalizes clause (v) of §5.1 Example 5.1.4 (printed p. 184, PDF p. 204) — the monad `β` obtained from the composite adjunction `Set ⇄ Top ⇄ cHaus` — whose catalogue row is carried by §5.1's self-adjoint-exponential issue.

## Background
The set of [ultrafilters](https://ncatlab.org/nlab/show/ultrafilter) on a set is the object part of the [ultrafilter monad](https://ncatlab.org/nlab/show/ultrafilter+monad) `β`, whose unit is the principal-ultrafilter map and which sits inside the double power set monad as a submonad; Riehl also obtains `β` as the monad of the composite adjunction `Set ⇄ Top ⇄ cHaus`, its left adjoint being the Stone–Čech compactification of a discrete space.

## Current state in the library
Nothing is constructed. `rg 'ultrafilter'` returns exactly three hits tree-wide, all header-essay prose: `Theory/Monad.v:65` (the Manes remark that the algebras of the ultrafilter monad are the compact Hausdorff spaces), `Theory/Kan/Extension.v:39` (the Leinster citation) and `:86` (the codensity remark). `rg 'Ultrafilter'` returns zero. There is no filter or ultrafilter datatype, no Boolean-algebra category, no power set functor on `Sets` (the only "power" hit is the internal power *object* `Pow a := Ω ^ a` at `Structure/Topos.v:129`), and hence neither the double power set monad the exercise's hint uses nor the codensity route the essays mention. The ultrafilter functor and its unit are the deliverables of #700; the multiplication, the monad laws and the submonad statement are not in anyone's scope yet.

## Work to be done
- On top of the covariant ultrafilter endofunctor and unit of #700, define the multiplication `μ : β² ⇒ β`, `μ_A(𝔘) = { S ⊆ A | { V ∈ βA | S ∈ V } ∈ 𝔘 }`, prove each `μ_A(𝔘)` is an ultrafilter, and prove naturality.
- Discharge the monad unit and associativity laws, giving `@Monad Sets β`.
- Prove the exercise's hint as a theorem rather than a remark: the inclusion `β ⇒ P²` (an ultrafilter is in particular a set of subsets) is a morphism of monads into the double power set monad of the continuation-monad issue for §5.1, i.e. `β` is a submonad — the unit and multiplication squares commute and the components are monic.
- Record in the header that Riehl's presentation of `β` as the monad of `Set ⇄ Top ⇄ cHaus` is the content of #489 and is not re-derived here; this issue supplies the monad that #489 consumes.
- Suggested module: `Monad/Instance/Ultrafilter.v` (or an extension of #700's `Instance/BoolAlg/Ultrafilter.v`). Donors: #700's ultrafilter functor, `Theory/Monad.v`, `Theory/Natural/Transformation.v`, `Instance/Sets.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.1 Exercise 5.1.ii and Example 5.1.4(v); setoid `≈` on morphisms, never `=`.
- [ ] `μ : β² ⇒ β` defined, proved to land in ultrafilters, and proved natural.
- [ ] The monad unit and associativity laws proved, giving an in-tree `@Monad Sets β`.
- [ ] The submonad statement `β ↪ P²` proved as a morphism of monads with monic components.
- [ ] Any choice principle (the ultrafilter lemma / Boolean prime ideal theorem) that the *examples* need — as opposed to the monad structure itself, which needs none — is isolated, disclosed in the header and enumerated in docs/AXIOMS.md.
- [ ] No `Admitted`, `admit`, or `Axiom` beyond those explicitly disclosed.
- [ ] `Print Assumptions` reported for `β`, `μ` and the monad laws.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated, and `Theory/Monad.v:65`'s essay repointed at the in-tree monad.

## Verification
- `coqc -R . Category Monad/Instance/Ultrafilter.v` compiles after its dependencies.
- `Print Assumptions` on the monad and on the submonad morphism, reconciled against docs/AXIOMS.md.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the multiplication formula and the submonad claim against Riehl §5.1 Exercise 5.1.ii.

## Dependencies
Depends on: #700 (the ultrafilter functor `Ult : BA^op ⟶ Sets` and the covariant ultrafilter endofunctor with its unit)
Depends on: #704 (the contravariant powerset functor and the double-powerset unit)

<!-- catalog: {"ids":["riehl:5.1:exii"],"deps":["#700","#704"]} -->

---8<---

title: "Riehl 5.2: Affine spaces — translation actions, affine combinations, and algebras for the affine-combination monad"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.2:def1, riehl:5.2:def2, riehl:5.2:def3]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.2 Definitions 5.2.1, 5.2.2 and 5.2.3 (printed pp. 187–188, PDF pp. 207–208). Items: `riehl:5.2:def1`, `riehl:5.2:def2`, `riehl:5.2:def3`.

## Background
An [affine space](https://ncatlab.org/nlab/show/affine+space) can be presented three ways: as a set with a simply transitive translation action of a vector space, as a set in which affine linear combinations (coefficients summing to one) can be evaluated, or — the presentation Riehl adopts — as an algebra for the monad of formal affine combinations. See also Wikipedia, [Affine space](https://en.wikipedia.org/wiki/Affine_space).

## Current state in the library
Entirely absent, and so is the vocabulary. `rg -i 'affine'` returns ten hits, every one either the unrelated "semicartesian (affine) monoidal" sense (`Structure/Monoidal/Semicartesian.v`, `Semicocartesian.v`, `Markov.v`) or prose about affine schemes (`Structure/Pullback.v:112`, `Structure/Group.v:97`); `rg -i 'torsor|simply transitive|principal homogeneous'` returns nothing, and the only group actions in-tree are the symmetric-group actions on multicategory arities (`Theory/Multicategory.v:393`, `Theory/Multicategory/Operad.v:207`). `rg -i 'convex|barycentric|linear combination'` returns zero hits across the whole tree. There are no scalars, no field, no vector space and no action of an algebraic structure on an object (`Structure/Group.v:109` defines only the internal `GroupObject`). The generic vehicle for the third presentation does exist — `Monad/Algebra.v:24` `TAlgebra` — but the item's own content, the monad `Aff_k` of formal affine combinations, has no counterpart.

## Work to be done
- Over a field (or commutative ring) `k` and a `k`-module `V` supplied by #258, define an affine space in Riehl's first sense: a setoid `A` with `+ : V × A → A` satisfying `0 + a ≈ a`, `(v + w) + a ≈ v + (w + a)`, and simple transitivity (each `(−) + a : V → A` is an isomorphism in `Sets`). Define affine maps and assemble the category.
- Define the affine-combination monad `Aff_k : Sets ⟶ Sets`: formal `k`-linear combinations whose coefficients sum to `1`, quotiented by permutation of summands, deletion of zero-coefficient summands and addition of coefficients on repeats (`Construction/Quotient.v` is the in-tree quotient idiom). Prove functoriality, and the monad laws with unit the singleton combination and multiplication by distribution.
- Prove that `Aff_k`-algebras are exactly affine spaces in the second sense, and prove the comparison with the first: given a base point, an affine space in the algebra sense acquires a simply transitive `V`-action, independently of the chosen base point. Riehl's footnote 8 deliberately drops the traditional non-emptiness requirement — follow that and say so in the header, since it is what makes the algebra presentation match on the nose.
- Suggested modules: `Instance/Affine.v` (the category), `Monad/Instance/Affine.v` (the monad and the algebra characterisation). Donors: #258's module category, `Instance/Sets.v`, `Construction/Quotient.v`, `Monad/Algebra.v`, `Monad/Eilenberg/Moore.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.2 Definitions 5.2.1–5.2.3; setoid `≈` on morphisms, never `=`.
- [ ] All three presentations formalized, with the two comparison theorems (translation-action ⟺ affine combinations, affine combinations ⟺ `Aff_k`-algebras) proved.
- [ ] The independence of the affine-combination structure from the chosen origin is proved, not assumed.
- [ ] The dropped non-emptiness condition (Riehl's footnote 8) is disclosed in the header.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond stdlib axioms already enumerated in docs/AXIOMS.md for the `Instance/` layer.
- [ ] `Print Assumptions` reported for the monad, the algebra characterisation and both comparisons.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Affine.v` and `coqc -R . Category Monad/Instance/Affine.v` compile after their dependencies.
- `Print Assumptions` on the `Aff_k` monad and on both comparison theorems.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks all three definitions against Riehl §5.2, including the footnote-8 deviation.

## Dependencies
Depends on: #258 (module categories `R-Mod` and friends — the scalars and the acting module)

<!-- catalog: {"ids":["riehl:5.2:def1","riehl:5.2:def2","riehl:5.2:def3"],"deps":["#258"]} -->

---8<---

title: "Riehl 5.2: Eilenberg–Moore algebras as presheaves on the Kleisli category"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:5.2:exvi]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.2 Exercise 5.2.vi (printed pp. 194–195, PDF pp. 214–215). Item: `riehl:5.2:exvi`.

## Background
Restricting the Yoneda embedding along the full and faithful comparison `K : C_T → C^T` sends an algebra to the presheaf `C^T(K−, (A,a))` on the [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category); the [Eilenberg–Moore category](https://ncatlab.org/nlab/show/Eilenberg-Moore+category) is isomorphic to the full subcategory of presheaves on `C_T` whose restriction along the free functor is representable.

## Current state in the library
Doubly blocked. The comparison `K : C_T ⟶ C^T` that the construction restricts along does not exist — `rg 'Kleisli.*EilenbergMoore|EilenbergMoore.*Kleisli|⟶ EilenbergMoore'` returns only `EM_Free` (`Monad/Eilenberg/Moore/Adjunction.v:79`) and `idem_G` (`Construction/Reflective/Idempotent.v:411`), and the free-algebra embedding is asserted only in comments (`Monad/Kleisli.v:29`, `Monad/Eilenberg/Moore.v:33-35`). And no functor out of an Eilenberg–Moore category into a presheaf category exists anywhere: `rg -i 'restricted yoneda'` → 0 hits, `rg -i 'nerve'` finds only prose in `Theory/Kan/Extension.v` and `Construction/Grothendieck.v`, and `Presheaf`/`Presheaves` (`Theory/Sheaf.v:124`, `:127`) are generic and never applied to a Kleisli category. Nothing in the tree states representability of a restriction along a free functor.

## Work to be done
- Over the comparison functor delivered by #475 (instantiated at the Eilenberg–Moore resolution), define the restricted-Yoneda functor `N : C^T ⟶ [C_T^op, Sets]`, `N(A,a) := C^T(K −, (A,a))`, and prove functoriality.
- Prove that for every algebra the restriction of `N(A,a)` along `Kleisli_Free : C ⟶ C_T` is representable in `[C^op, Sets]` — represented by `A` itself — using the free/forgetful transposition `EM_adj_iso` (`Monad/Eilenberg/Moore/Adjunction.v:157`).
- Prove that `N` is an isomorphism onto the full subcategory of presheaves on `C_T` whose restriction along `Kleisli_Free` is representable: full and faithful from the fullness/faithfulness of `K` plus Yoneda, and essentially surjective (indeed bijective on objects) by reconstructing the algebra structure from a representing object.
- Suggested module: `Monad/Kleisli/Presheaf.v`. Donors: #475's comparison, `Functor/Hom/Yoneda.v`, `Theory/Sheaf.v` (`Presheaf`, `Presheaves`), `Monad/Eilenberg/Moore/Adjunction.v`, `Construction/Subcategory.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.2 Exercise 5.2.vi (all three clauses); setoid `≈` on morphisms, never `=`.
- [ ] The restricted-Yoneda functor is defined and its functoriality proved.
- [ ] The representability of the restriction along the free functor is proved for every algebra.
- [ ] The isomorphism onto the full subcategory of restriction-representable presheaves is proved; if the setoid setting forces an equivalence rather than an isomorphism at any step, that is stated and justified in the header rather than glossed.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the functor and the isomorphism.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification
- `coqc -R . Category Monad/Kleisli/Presheaf.v` compiles after its dependencies.
- `Print Assumptions` on the restricted-Yoneda functor and on the isomorphism.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the three clauses against Riehl §5.2 Exercise 5.2.vi.

## Dependencies
Depends on: #475 (the Kleisli comparison functor and the free-object subcategory)

<!-- catalog: {"ids":["riehl:5.2:exvi"],"deps":["#475"]} -->

---8<---

title: "Riehl 5.3: Algebras for an idempotent monad form a reflective subcategory, and reflective inclusions are monadic"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.3:prop3, riehl:5.3:exi]
deps_item_ids: [riehl:5.1:exiii]
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.3 Proposition 5.3.3 (printed pp. 196–197, PDF pp. 216–217) and Exercise 5.3.i (printed p. 197, PDF p. 217). Items: `riehl:5.3:prop3`, `riehl:5.3:exi`.

## Background
For an [idempotent monad](https://ncatlab.org/nlab/show/idempotent+monad), carrying an algebra structure is a *property*: an object admits one exactly when its unit component is invertible, and then the structure map is forced to be that inverse. So the forgetful functor exhibits the algebras as a [reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory), and conversely every reflective inclusion is [monadic](https://ncatlab.org/nlab/show/monadic+functor). Since every algebra is then free, the Kleisli and Eilenberg–Moore categories agree.

## Current state in the library
Clause (i) holds in substance but is routed through a different subcategory, and clause (ii) is missing outright. `Construction/Reflective/Idempotent.v` proves both halves of the iff pointwise — `:354` `local_algebra : IsIsomorphism (ret b) → TAlgebra M b` with `t_alg := ret⁻¹`, and `:373` `algebra_ret_iso : TAlgebra M a → IsIsomorphism (ret a)` with the structure map as the two-sided inverse — but the reflectivity conclusion is stated of the bespoke `MLocal_Subcategory` (`:345` `Idempotent_Reflective`), not of `U^T : C^T ⟶ C` itself, and the comparison `:411` `idem_G` with `:464` `Idempotent_EM_Equivalence` is built by hand rather than as `EM_Comparison` of the reflection adjunction. Uniqueness of the algebra structure map is only implicit: it follows from `comp_inverse_unique` (used by the file at `:110`, `:126`, `:361`) but no lemma states `t_alg[alg] ≈ ret⁻¹`.

Clause (ii) has no in-tree statement at all: `Monadic (Incl C S)` appears nowhere, and although `:198` `Reflective_IdempotentMonad` shows a reflective subcategory induces an idempotent monad and `:464` equates that monad's algebras with its local objects, nothing joins the two — no result identifies a given `Sub C S` (for `S` reflective) with the `MLocal_Subcategory` of its induced monad.

Exercise 5.3.i is entirely absent: `rg -i 'Kleisli.*idempotent|idempotent.*Kleisli'` → 0 hits, and since no functor `C_T ⟶ C^T` exists at all the exercise's input (Riehl's Lemma 5.2.14, #475) is missing too.

## Work to be done
- State clause (i) in Riehl's own form: for an idempotent monad, `U^T : C^T ⟶ C` is a fully faithful right adjoint, i.e. exhibits `C^T` as a reflective subcategory of `C`; and add the missing uniqueness lemma `t_alg[alg] ≈ ret⁻¹`, so "being an algebra is a property" is an in-tree theorem rather than a reading of two separate lemmas.
- Prove clause (ii): for a reflective subcategory `S ⊆ C`, `Monadic (Incl C S)` — i.e. `EM_Comparison (reflective_adj R)` is an equivalence. The honest route is to identify `Sub C S` with the `MLocal_Subcategory` of `Reflective_Monad` (using #985's essential-image characterisation of the objects of a reflective subcategory) and then transport `Idempotent_EM_Equivalence` along that identification, checking that the transported functor really is `EM_Comparison` and not merely equivalent data.
- Prove Exercise 5.3.i: for an idempotent monad every algebra is free, so the comparison `C_T ⟶ C^T` of #475 is an equivalence; conclude that the Kleisli adjunction of an idempotent monad is monadic.
- Suggested module: `Construction/Reflective/Monadic.v` (with the uniqueness lemma added to `Construction/Reflective/Idempotent.v`). Donors: `Construction/Reflective/Idempotent.v`, `Construction/Reflective.v`, `Monad/Comparison.v`, `Monad/Eilenberg/Moore.v`, #475's Kleisli comparison, #985.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.3 Proposition 5.3.3 (both clauses) and Exercise 5.3.i; setoid `≈` on morphisms, never `=`.
- [ ] The uniqueness of the algebra structure map for an idempotent monad is a named lemma.
- [ ] Clause (i) is stated of `U^T : C^T ⟶ C`, not only of the M-local subcategory.
- [ ] `Monadic (Incl C S)` is proved for an arbitrary reflective subcategory, with the comparison shown to be `EM_Comparison` of the reflection adjunction.
- [ ] Kleisli ≃ Eilenberg–Moore for an idempotent monad, and monadicity of its Kleisli adjunction, are proved.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the uniqueness lemma, the reflectivity statement, the monadicity of the inclusion, and the Kleisli equivalence.
- [ ] New/changed files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the reflective/idempotent entry gains the monadicity statement.

## Verification
- `coqc -R . Category Construction/Reflective/Monadic.v` compiles after its dependencies.
- `Print Assumptions` on `Monadic (Incl C S)` and on the Kleisli equivalence.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks both clauses against Riehl §5.3 Proposition 5.3.3, in particular that clause (ii)'s equivalence is the canonical comparison functor.

## Dependencies
Depends on: #475 (the Kleisli comparison functor and the free-object subcategory)
Depends on: #985 (the essential image of a reflective subcategory, and its local objects)
Depends on: riehl:5.1:exiii (the characterizations of an idempotent monad)

<!-- catalog: {"ids":["riehl:5.3:prop3","riehl:5.3:exi"],"deps":["#475","#985","riehl:5.1:exiii"]} -->

---8<---

title: "Riehl 5.3/5.6: Monadic functors are conservative, and bijective homomorphisms of algebras are isomorphisms"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.6:lem1, riehl:5.3:exiii, riehl:5.6:cor4]
deps_item_ids: [riehl:5.5:def5]
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20). §5.3 Exercise 5.3.iii (printed p. 197, PDF p. 217); §5.6 Lemma 5.6.1 and Corollary 5.6.4 (printed pp. 209–210, PDF pp. 229–230). Items: `riehl:5.6:lem1`, `riehl:5.3:exiii`, `riehl:5.6:cor4`.

## Background
A [monadic functor](https://ncatlab.org/nlab/show/monadic+functor) is [conservative](https://ncatlab.org/nlab/show/conservative+functor): if the underlying morphism of an algebra homomorphism is invertible then so is the homomorphism, because the inverse automatically satisfies the algebra square. The standard corollary is that a bijective homomorphism of algebraic structures — a bijective group homomorphism, say — is an isomorphism.

## Current state in the library
Every ingredient of the one-line proof is present and the composite is never formed. `Monad/Monadicity/BeckObjects.v:177` gives `#[export] Instance em_forget_reflects_isos : ReflectsIsos (EM_Forget T)` for every monad on every base, proved by exactly Riehl's argument (`:143` `em_iso_inverse_commutes` conjugates the algebra square with the inverse on both sides); `Theory/Equivalence/Limit.v:456` gives `equivalence_reflects_isos`; and `Monad/Comparison.v:198` gives `EM_Comparison_Forget : EM_Forget ◯ EM_Comparison ≈ U`. But there is no theorem `Monadic U → ReflectsIsos U`, and the two structural lemmas needed to chain the three ingredients are both missing: `ReflectsIsos` is nowhere shown stable under functor composition, and nowhere shown transportable along `≈` of functors. The whole tree has 14 `ReflectsIsos` occurrences (the class at `Structure/Limit/Preservation.v:243`; `ff_reflects_isos` and `equivalence_reflects_isos` at `Theory/Equivalence/Limit.v:335`, `:456`; `em_forget_reflects_isos`; `creates_split_reflects_isos` and `beck_reflects` at `Monad/Monadicity/Beck.v:264`, `:304`; the rest `Context` hypotheses at `Monad/Lifting.v:497`, `Theory/Lawvere/Monad.v:89`), and none has `Monadic` as a hypothesis. The nearest implication, `creates_split_reflects_isos`, derives conservativity from Beck's *creation* hypothesis, not from monadicity, and `Monad/Monadicity/Beck.v:104-110` records that transporting the converse along the comparison equivalence is "deliberately left to a later development".

For Corollary 5.6.4 there is a same-name-but-weaker trap the implementer must not fall into: `ReflectsIsos (ev1 T)` *does* appear, at `Theory/Lawvere/Monad.v:89` — but as a `Context` hypothesis feeding `Lawvere_crude_monadicity` (`:91`), never discharged, in contrast with `ev1_Faithful` (`Theory/Lawvere/Sets.v:105`), which is a real theorem. The bijective-implies-iso bridge exists only in `Sets` (`Instance/Sets.v:400` `bijective_is_iso`, `Defined` so it computes), and `Instance/CMon.v` proves nothing about reflection of isomorphisms.

## Work to be done
- Add the two structural lemmas to `Structure/Limit/Preservation.v` (or a new `Structure/Limit/Reflection.v` if #481 creates one): `ReflectsIsos` of a composite `G ◯ F` from `ReflectsIsos G` and `ReflectsIsos F`; and transport of `ReflectsIsos` along a natural isomorphism of functors, so a `≈`-equation between functors can move the property across. Both are missing today, which is why the three existing ingredients cannot simply be chained by `apply`.
- Prove `monadic_reflects_isos : Monadic U → ReflectsIsos U` by Riehl's argument: destructure `Monadic U` into `F ⊣ U` with `EM_Comparison` an equivalence, use `equivalence_reflects_isos` on the comparison and `em_forget_reflects_isos` on `EM_Forget`, and transport along `EM_Comparison_Forget`.
- Derive Corollary 5.6.4 in the library's own vocabulary: discharge `ReflectsIsos (ev1 T)` for `ev1 : Models T Sets ⟶ Sets` (`Theory/Lawvere/Sets.v:83`) and remove it from the `Context` at `Theory/Lawvere/Monad.v:89`, so `Lawvere_crude_monadicity` stops assuming its own corollary; state the elementary consequence over `Sets` by composing with `bijective_is_iso`.
- Record the surrounding contrapositive (`Top` and `Poset` are not monadic over `Set`) as scoped out or as a follow-on, since it needs `Top` (#259); do not leave it as an unstated claim in the header.
- Suggested module: `Monad/Conservative.v`. Donors: `Monad/Monadicity/BeckObjects.v`, `Monad/Comparison.v`, `Theory/Equivalence/Limit.v`, `Structure/Limit/Preservation.v`, `Theory/Lawvere/Sets.v`, `Theory/Lawvere/Monad.v`, `Instance/Sets.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.6 Lemma 5.6.1, Corollary 5.6.4 and §5.3 Exercise 5.3.iii; setoid `≈` on morphisms, never `=`.
- [ ] `Monadic U → ReflectsIsos U` proved for an arbitrary `U`.
- [ ] The transport-along-`≈` lemma for `ReflectsIsos` is stated and proved as reusable infrastructure, not inlined.
- [ ] `ReflectsIsos (ev1 T)` discharged, and the corresponding `Context` hypothesis removed from `Theory/Lawvere/Monad.v:89` (with `Lawvere_crude_monadicity` still compiling).
- [ ] The bijective-homomorphism corollary stated in the library's model-category vocabulary.
- [ ] The `Top`/`Poset` contrapositive is either proved or explicitly scoped out in the header with its dependency named.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for `monadic_reflects_isos` and the corollary.
- [ ] New/changed files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the monadicity entry gains conservativity from monadicity, complementing `creates_split_reflects_isos`.

## Verification
- `coqc -R . Category Monad/Conservative.v` compiles, and `Theory/Lawvere/Monad.v` still compiles with one fewer `Context` hypothesis.
- `Print Assumptions monadic_reflects_isos.` closed.
- `rg -n 'ReflectsIsos' Theory/Lawvere/Monad.v` shows the hypothesis gone.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the proof shape against Riehl §5.6 Lemma 5.6.1 (transport along the comparison equivalence).

## Dependencies
Depends on: #481 (reflection of coequalizers — the reflection vocabulary this issue extends)
Depends on: #259 (`Top`, needed only for the scoped-out contrapositive)
Depends on: riehl:5.5:def5 (the notion "category of models for an algebraic theory", in which Corollary 5.6.4 is stated)

<!-- catalog: {"ids":["riehl:5.6:lem1","riehl:5.3:exiii","riehl:5.6:cor4"],"deps":["#481","#259","riehl:5.5:def5"]} -->

---8<---

title: "Riehl 5.5: Lattices and semilattices as categories over Set"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:def-lattice]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5, the footnote definition supporting Corollary 5.5.3 clause (iii) (printed p. 203, PDF p. 223). Item: `riehl:5.5:def-lattice`.

## Background
A [lattice](https://ncatlab.org/nlab/show/lattice) is a poset with all finite meets and all finite joins — finite limits and finite colimits in its thin category — and a lattice morphism is an order-preserving map preserving both; dropping one half gives a meet or join [semilattice](https://ncatlab.org/nlab/show/semilattice). See also Wikipedia, [Lattice (order)](https://en.wikipedia.org/wiki/Lattice_%28order%29).

## Current state in the library
No such structure exists. `rg -i '\blattice\b|semilattice'` finds only background-essay prose — `Instance/Poset.v:60`, `:90`, `:93`, `:95` (Birkhoff and Galois connections), `Construction/FAlg.v:43` (Knaster–Tarski), `Construction/Opposite.v:39`, `Theory/Adjunction.v:81`, `Structure/Limit.v:108`, `:110`, `Structure/Complete.v:71`, `Theory/Lawvere.v:87`, `Instance/ZX.v:161` (lattice surgery) — with no `Definition`, `Class` or `Record`. `Instance/Poset.v` declares exactly three things (`eq_equiv` at `:111`, `Poset` at `:116`, `LessThanEqualTo_Category` at `:120`) and `Instance/Proset.v` two (`Proset` at `:33`, `LessThanEqualTo_Category` at `:47`); neither carries finite-meet or finite-join structure, and there is no lattice-morphism notion. There is no neighbouring order structure to stand in either: `rg -i 'heyting|boolean algebra|frame\b|locale'` finds no Heyting algebra, Boolean algebra, frame or locale.

## Work to be done
- Define `MeetSemilattice`, `JoinSemilattice` and `Lattice` over the in-tree poset/preorder substrate, taking the finite meets and joins as *data* (a nullary and a binary operation with their universal properties) rather than as existence claims, so no choice principle enters — this is the same discipline `Structure/Limit/Product.v` uses.
- Prove the dictionary the definition is really making: a meet semilattice is exactly a poset whose thin category is `Cartesian` with a `Terminal` object, and dually for joins with `Cocartesian`/`Initial`, so that "finite limits and finite colimits" is a theorem about the categorical structure and not a second definition.
- Define the corresponding homomorphisms (order-preserving, preserving the chosen meets and/or joins) and assemble the three categories, each with its forgetful functor to `Sets`.
- Suggested module: `Instance/Lattice.v`. Donors: `Instance/Poset.v`, `Instance/Proset.v`, `Structure/Cartesian.v`, `Structure/Cocartesian.v`, `Structure/Terminal.v`, `Structure/Initial.v`, `Instance/CMon.v` (the template for an algebraic category over setoids).

## Definition of Done
- [ ] Statement fidelity to Riehl §5.5's footnote definition; setoid `≈` on morphisms, never `=`.
- [ ] All three structures defined with their finite (co)limits as data, plus the categorical dictionary proved in both directions.
- [ ] The three categories and their forgetful functors to `Sets` are in-tree.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for each category and each forgetful functor.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (a new concrete instance family).

## Verification
- `coqc -R . Category Instance/Lattice.v` compiles after its dependencies.
- `Print Assumptions` on the three categories and the forgetful functors.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the definition against Riehl §5.5 (poset with all finite meets and joins; morphisms preserve both).

## Dependencies
None (self-contained over `Instance/Poset.v` and the finite (co)limit classes).

<!-- catalog: {"ids":["riehl:5.5:def-lattice"],"deps":[]} -->

---8<---

title: "Riehl 5.5: Finitary functors and monads, and categories of models for an algebraic theory"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:def4, riehl:5.5:def5]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5 Definitions 5.5.4 and 5.5.5 with the surrounding prose (printed p. 204, PDF p. 224). Items: `riehl:5.5:def4`, `riehl:5.5:def5`.

## Background
A functor is *finitary* when it preserves filtered colimits; a [finitary monad](https://ncatlab.org/nlab/show/finitary+monad) is one whose endofunctor is. A category is a category of models for an algebraic theory — an [algebraic category](https://ncatlab.org/nlab/show/algebraic+category) — when it admits a finitary monadic functor to `Set`; every such category is locally finitely presentable, and compact Hausdorff spaces are the standard example of a category monadic over `Set` that is *not* of this form.

## Current state in the library
"Finitary" cannot even be stated. `rg -i 'finitary'` returns 16 hits, every one inside a background essay (`Theory/Lawvere.v:52`, `:86`, `:90`, `:93`; `Theory/Monad.v:62`, `:64`; `Theory/Lawvere/Monad.v:25`, `:59-60`; `Instance/FinSet.v:61`; `Instance/Comp.v:16`; `Instance/Poset.v:66`; `Theory/Coq.v:76`; `Theory/Coq/Traversable.v:48`; `Functor/Traversable.v:61`; and `Structure/Distributive.v:13`, where the word means *finite products*); `rg -i 'filtered'` returns exactly one hit, `Comonad/CoKleisli.v:81`, about a filtered stream. There is no `Filtered` class, no filtered-colimit predicate, and no finitary-functor or finitary-monad predicate. The preservation vocabulary that would host the definition does exist (`Structure/Limit/Preservation.v:196` `PreservesColimit`, `:232` `PreservesAllColimits`) but is never instantiated at a filtered shape. `rg -i 'locally finitely presentable'` returns zero hits.

The algebraic-theory side is realized in a different idiom. `Theory/Lawvere/Model.v:50` `Record Model` (a cartesian- and terminal-preserving functor out of the theory) and `:77` `Models := Sub (Fun (law_cat T) C) Models_sub`, with `ev1 : Models T Sets ⟶ Sets` at `Theory/Lawvere/Sets.v:83`, give models of a Lawvere theory; and `Theory/Lawvere/Monad.v:91` `Lawvere_crude_monadicity` yields an equivalence — but only with the free-model left adjoint `L ⊣ ev1 T` and all three crude-monadicity hypotheses supplied as `Context` data (`Theory/Lawvere/Monad.v:31-38` says constructing that left adjoint is out of scope for that file). So the book's *defining criterion* — existence of a finitary monadic functor into `Set` — is not expressible, the monadicity of `ev1` is assumed rather than proved, and the theory ⟷ finitary-monad equivalence that would license the two presentations as interchangeable is explicitly deferred (`Theory/Lawvere/Monad.v:59-62`, "ledger 2").

## Work to be done
- On top of the filtered machinery of #559, define `Finitary F := PreservesColimit F` restricted to filtered shapes (state it over the cone-level preservation the library prefers, and say in the header which of `PreservesColimit`/`PreservesImageColimit` is meant and why).
- Specialize to monads: `FinitaryMonad T` for `T : C ⟶ C` a monad; and prove Riehl's transfer remark — if a right adjoint is finitary then so is its induced monad, because the left adjoint preserves all colimits (`Adjunction/Continuity.v:223` `left_adjoint_preserves_colimits`).
- Define the predicate `AlgebraicCategory A := { U : A ⟶ Sets & Monadic U * FinitaryMonad (induced monad of U) }`, i.e. Riehl's Definition 5.5.5, and prove that `Models T Sets` satisfies it once its free-model left adjoint is available (keeping that adjoint an explicit input, as `Theory/Lawvere/Monad.v` already does, rather than silently assuming it).
- Record the two trailing prose claims honestly: local finite presentability of such a category is the subject of #986 and should be cross-referenced, not restated; the compact-Hausdorff non-example needs `cHaus` (#489) and should be flagged as pending rather than asserted.
- Suggested modules: `Structure/Finitary.v` (the predicates), `Theory/Lawvere/Algebraic.v` (the algebraic-category predicate and the `Models` instance). Donors: #559's filtered machinery, `Structure/Limit/Preservation.v`, `Adjunction/Continuity.v`, `Theory/Lawvere/Model.v`, `Theory/Lawvere/Sets.v`, `Theory/Lawvere/Monad.v`, `Monad/Comparison.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.5 Definitions 5.5.4 and 5.5.5; setoid `≈` on morphisms, never `=`.
- [ ] `Finitary` and `FinitaryMonad` defined over the filtered vocabulary of #559.
- [ ] The right-adjoint transfer lemma (finitary right adjoint ⇒ finitary induced monad) proved.
- [ ] `AlgebraicCategory` defined exactly as "∃ a finitary monadic functor to `Sets`", and shown to hold of `Models T Sets` under the explicitly named left-adjoint hypothesis.
- [ ] The local-finite-presentability claim cross-referenced to #986 and the `cHaus` non-example flagged as pending, both in the file header, so nothing is asserted that is not proved.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the predicates and the transfer lemma.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Lawvere-theory entry gains the finitary vocabulary.

## Verification
- `coqc -R . Category Structure/Finitary.v` and `coqc -R . Category Theory/Lawvere/Algebraic.v` compile after their dependencies.
- `Print Assumptions` on `Finitary`, `FinitaryMonad`, the transfer lemma and `AlgebraicCategory`.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the definitions against Riehl §5.5 Definitions 5.5.4/5.5.5 and confirms the header claims match what is proved.

## Dependencies
Depends on: #559 (filtered categories and filtered colimits)
Depends on: #986 (locally presentable categories and accessible functors — for the cross-referenced LFP claim)

<!-- catalog: {"ids":["riehl:5.5:def4","riehl:5.5:def5"],"deps":["#559","#986"]} -->

---8<---

title: "Riehl 5.5: Paré's theorem — the contravariant power set functor is monadic"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:thm9, riehl:5.5:lem10]
deps_item_ids: [riehl:5.1:example4]
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5 Theorem 5.5.9 and Lemma 5.5.10 (printed pp. 206–207, PDF pp. 226–228). Items: `riehl:5.5:thm9`, `riehl:5.5:lem10`.

## Background
Paré's theorem: the contravariant [power set](https://ncatlab.org/nlab/show/power+set) functor `P : Set^op ⟶ Set` is [monadic](https://ncatlab.org/nlab/show/monadic+functor). The proof applies the reflexive tripleability theorem — `P` is self-adjoint on the right, `Set^op` has coequalizers of reflexive pairs because `Set` has equalizers of coreflexive pairs, those are pullbacks of monomorphisms so the [Beck–Chevalley condition](https://ncatlab.org/nlab/show/Beck-Chevalley+condition) makes the induced diagram of power sets a split coequalizer, and `P` is faithful hence conservative.

## Current state in the library
Neither the theorem nor its inputs exist. The only in-tree power construct is the internal power *object* `Pow {C} {H : ElementaryTopos C} (a : C) : C := Ω ^ a` (`Structure/Topos.v:129`), never made into a functor `C^op ⟶ C`, never given a monad structure, and involved in no adjunction. `rg -i 'self-adjoint|mutually right adjoint'` returns two hits, both about the identity functor (`Adjunction/Compose.v:29`, `Instance/Adjoints.v:17`), so the source of the left adjoint in Paré's proof is missing; `rg -i 'double power'` returns nothing, so the induced monad is missing too. The closest relatives are `Sub : C^op ⟶ Sets` (`Theory/Subobject/Functor.v:180`, with `sub_reindex` at `:35` and `sub_reindex_comp` at `:152` — the inverse-image half, proved by exactly the pullback pasting the book's proof invokes) and `classifier_classifies` (`Structure/SubobjectClassifier.v:187`); neither carries a left adjoint, faithfulness or monadicity, and `Sub` needs `HasPullbacks`, whose only tree-wide instance is `FinSet_Pullbacks` (`Instance/FinSet/Classifier.v:264`), so `Sub` is not even available at `Sets`.

Lemma 5.5.10 is likewise absent: `rg -i 'beck.?chevalley'` returns two header-prose hits (`Comonad/Coalgebra.v:94`, `Theory/Bicategory.v:104`) and no statement, and there is no direct-image or inverse-image operator on subsets anywhere (`preimage` occurs only as the chosen `fmap`-preimage of a full functor, `Theory/Functor.v:332`). The Phase-D verifier added one correction the implementer should have: the base-change functors themselves *do* exist one file over from where Phase C looked — `Construction/Slice/Pullback.v:50` `Bang_Functor` (`Σ_f`) and `:67` `Star_Functor` (`f*`) — what is missing there is the adjunction (only a commented `Base_Functor_Adjunction` stub at `:121`, whose orientation error that file's header flags at `:38-40`).

What *is* in place is the criterion: Riehl's Proposition 5.5.8, the reflexive tripleability theorem, is present in-tree as the crude-monadicity development (`Monad/Monadicity/Crude.v:601` `crude_monadicity`, over `HasReflexiveCoequalizers`, `PreservesReflexiveCoequalizers` and `ReflectsIsos`), so the proof has a landing pad.

## Work to be done
- Build the contravariant power set functor on setoids, `P : Sets^op ⟶ Sets` (subsets as `≈`-respecting predicates up to pointwise `iff`; `Instance/Sets/Classifier.v`'s `PropSetoid` under `iffT` is the in-tree precedent for the truth-value setoid, including its universe discipline), with `fmap` the inverse image. Prove the self-adjunction `P^op ⊣ P` from the cartesian closed structure (`Instance/Sets/Cartesian/Closed.v`), i.e. `Sets(a, P b) ≅ Sets(a × b, Ω) ≅ Sets(b, P a)`, natural in both variables.
- Define the direct image `∃_f : P a → P b` and prove Lemma 5.5.10: for a pullback square of monomorphisms, direct image along one leg followed by inverse image along the opposite edge equals inverse image followed by direct image, as maps `P b' → P a`. Prove it the book's way, by the pullback pasting criterion (`Theory/Morphisms/Stability.v` has the pasting toolkit), and note in the header that this is the `Sets` instance of the general Beck–Chevalley condition of #980. Record the immediate corollary that `f*` after `∃_f` is the identity for a monomorphism `f`.
- Prove the three hypotheses of the reflexive tripleability theorem for `P` and feed `crude_monadicity`: (a) `Set^op` has coequalizers of reflexive pairs, from equalizers of coreflexive pairs in `Sets` (#407 supplies the equalizers); (b) `P` preserves them, via Lemma 5.5.10 making the induced diagram a split coequalizer; (c) `P` is faithful — a parallel pair is separated by the subsets of `a × b` classified through the transposes of the singleton map — hence conservative in `Sets`.
- Conclude `Monadic P`, and record in the header that the argument goes through verbatim over any elementary topos (`Structure/Topos.v:112`), which the library already has, without claiming that generalization as proved unless it is.
- **Module coordination:** `Instance/Sets/Powerset.v` is already proposed by #466 (the *covariant* power set monad and its sup-lattice algebras) and by #704 (the contravariant functor and the double-powerset unit); land the contravariant functor and Lemma 5.5.10 in that same module beside the covariant half rather than opening a second powerset file, and put only Paré's theorem in a new module.
- Suggested modules: `Instance/Sets/Powerset.v` (the functor, the self-adjunction, direct image and Lemma 5.5.10 — shared with #466/#704), `Instance/Sets/Powerset/Monadic.v` (Paré's theorem). Donors: `Instance/Sets.v`, `Instance/Sets/Classifier.v`, `Instance/Sets/Cartesian/Closed.v`, `Theory/Morphisms/Stability.v`, `Monad/Monadicity/Crude.v`, `Structure/Coequalizer/Reflexive.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.5 Theorem 5.5.9 and Lemma 5.5.10; setoid `≈` on morphisms, never `=`.
- [ ] `P : Sets^op ⟶ Sets` defined with the self-adjunction `P^op ⊣ P` proved natural in both variables.
- [ ] Lemma 5.5.10 proved by the pullback-pasting argument, with the mono-cancellation corollary.
- [ ] `Monadic P` proved by feeding the in-tree reflexive/crude tripleability theorem, with all three hypotheses discharged rather than assumed.
- [ ] The universe discipline of the subset setoid is disclosed in the header (the truth-value setoid lives one level up, as `Instance/Sets/Classifier.v` already documents), and any resulting size restriction is stated.
- [ ] No `Admitted`, `admit`, or `Axiom` beyond stdlib axioms already enumerated in docs/AXIOMS.md for the `Instance/` layer.
- [ ] `Print Assumptions` reported for `P`, the self-adjunction, Lemma 5.5.10 and the monadicity witness.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index and docs/INHABITATION.md updated — a genuinely non-algebraic monadicity witness.

## Verification
- `coqc -R . Category Instance/Sets/Powerset.v` and `coqc -R . Category Instance/Sets/Powerset/Monadic.v` compile after their dependencies.
- `Print Assumptions` on the self-adjunction, Lemma 5.5.10 and `Monadic P`, reconciled against docs/AXIOMS.md.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks Lemma 5.5.10's statement and the three tripleability hypotheses against Riehl §5.5.

## Dependencies
Depends on: #407 (completeness of `Sets` — in particular equalizers)
Depends on: #704 (the contravariant powerset functor on `Sets` and the double-powerset unit — same module, coordinate the layout)
Depends on: #466 (the covariant power set monad — same module, coordinate the layout)
Depends on: #980 (the Beck–Chevalley transformations and their invertibility over a pullback square)
Depends on: riehl:5.1:example4 (clauses (vii)–(viii): the self-adjoint exponential and its continuation monad, of which the double power set monad is the `S = 2` case)

<!-- catalog: {"ids":["riehl:5.5:thm9","riehl:5.5:lem10"],"deps":["#407","#704","#466","#980","riehl:5.1:example4"]} -->

---8<---

title: "Riehl 5.5: Restriction along a functor of small categories — the left Kan extension by copowers, and monadicity"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:exv, riehl:5.5:exvi]
deps_item_ids: []
deps_pending: [riehl:6.2:thm1]

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5 Exercises 5.5.v and 5.5.vi (printed p. 208, PDF p. 228). Items: `riehl:5.5:exv`, `riehl:5.5:exvi`.

This issue also formalizes clause (iii) of §5.5 Example 5.5.7 (printed p. 205, PDF pp. 225–226) — for `C` with coproducts and `J` small, the restriction `ev : C^J ⟶ C^{ob J}` is monadic — whose catalogue row is carried by §5.1/§5.5's quiver issue.

## Background
For a small category `J` and a cocomplete `C`, restriction along the inclusion of the objects of `J` has a left adjoint given by the [left Kan extension](https://ncatlab.org/nlab/show/left+Kan+extension) formula — a coproduct of copowers `∐_x J(x,j) · F x` — and the resulting adjunction is [monadic](https://ncatlab.org/nlab/show/monadic+functor); more generally, restriction along suitable functors `K : I → J` strictly creates coequalizers of split pairs.

## Current state in the library
The generic restriction functor is available and the rest is not. The Phase-D verifier corrected the Phase-C record on exactly this point, and the correction changes how the work should start: `Theory/Kan/Extension.v:127` defines `Induced : [B, C] ⟶ [A, C]`, `G ↦ G ○ F`, the general precomposition functor, and `Instance/Discrete.v:52` `DiscreteCat_Functor {A : Type} {C : Category} (f : A → C) : DiscreteCat A ⟶ C` supplies the inclusion `DiscreteCat (obj J) ⟶ J` — so Riehl's `ev : C^J ⟶ C^{ob J}` is one instantiation away, not missing. (Both files are registered, `_CoqProject:445` and `:182`.) What is genuinely absent: the composite is never assembled; the left adjoint is never built — `Theory/Kan/Extension.v:222` `Class LeftKan := { Lan : [A,C] ⟶ [B,C]; lan_adjoint : Lan ⊣ Induced }` carries the adjoint purely as *data*, and no instance of `LeftKan`/`LocalLeftKan`/`RightKan` is ever constructed anywhere in the tree (the only consumer is `Structure/Limit/Kan/Extension.v:46` `Kan_Limit`, which takes a `RightKan` hypothesis); `rg -i 'copower'` returns 0 hits, so the formula cannot even be written; and no restriction functor is claimed monadic. `rg -i 'strictly creates|StrictlyCreates|strict creation'` returns 0 hits: the only creation predicate is `Monad/Monadicity/Beck.v:164` `CreatesUSplitCoequalizers`, stated up to a comparison isomorphism for an arbitrary `U` and never instantiated at a restriction functor.

## Work to be done
- Assemble `ev : [J, C] ⟶ [DiscreteCat (obj J), C]` by instantiating `Induced` at `DiscreteCat_Functor (fun x => x)`, and record the identification `[DiscreteCat (obj J), C] ≃ (ob J)-indexed families in C`.
- Define the copower `S · c` of an object by a set (donor: #366) and, using indexed coproducts (#320), build `Lan F j := ∐_{x ∈ ob J} J(x,j) · F x` on objects; define its action on morphisms of `J` (Exercise 5.5.v(i)) and on morphisms of the restricted functor category (clause (ii)).
- Prove `Lan ⊣ ev` by the Yoneda lemma (clause (iii)), producing an instance of `Theory/Kan/Extension.v:222`'s `LeftKan` — the library's first — and note in the header that this discharges the "no `LeftKan` instance exists" gap that `Structure/Limit/Kan/Extension.v` currently works around.
- Prove the adjunction monadic (clause (iv)) by the completed Beck theorem (#484), and hence Example 5.5.7(iii).
- Exercise 5.5.vi: identify a class of functors `K : I ⟶ J` for which `res_K : [J,C] ⟶ [I,C]` strictly creates coequalizers of `res_K`-split pairs (bijective-on-objects functors are the natural candidate; state precisely what is proved), and conclude that all such restrictions are monadic. Riehl's challenge clause — the explicit left adjoint via the general Kan extension formula — is Chapter 6 material; scope it here or defer it explicitly.
- Suggested modules: `Structure/Limit/Copower.v` (if #366 has not landed it), `Theory/Kan/Extension/Discrete.v` (the `LeftKan` instance), `Theory/Kan/Extension/Monadic.v` (the monadicity). Donors: `Theory/Kan/Extension.v`, `Instance/Discrete.v`, `Instance/Fun.v`, `Structure/Limit/Product.v` (the `iprod` template to dualize), `Monad/Monadicity/Beck.v`, `Functor/Hom/Yoneda.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.5 Exercises 5.5.v (all four clauses) and 5.5.vi, and Example 5.5.7(iii); setoid `≈` on morphisms, never `=`.
- [ ] `ev` assembled from the existing `Induced` and `DiscreteCat_Functor` rather than rebuilt.
- [ ] Indexed coproducts and copowers are *consumed* from #320/#366, not re-specified here — no second `IsIndexedCoproduct`/`icoprod` definition is introduced.
- [ ] `Lan ⊣ ev` proved and packaged as an in-tree `LeftKan` instance.
- [ ] Monadicity of `ev` proved through `beck_monadicity`.
- [ ] Exercise 5.5.vi's class of functors is defined, the strict-creation property proved for it, and monadicity concluded; the challenge clause is either delivered or explicitly deferred in the header.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for `Lan`, the adjunction, and each monadicity witness.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Kan-extension entry gains its first constructed instance.

## Verification
- `coqc -R . Category Theory/Kan/Extension/Discrete.v` and `coqc -R . Category Theory/Kan/Extension/Monadic.v` compile after their dependencies.
- `rg -n 'IsIndexedCoproduct|icoprod' --glob '*.v'` shows only the definitions introduced by #320, with the new files consuming them.
- `Print Assumptions` on the `LeftKan` instance and the monadicity witnesses.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the four clauses of Exercise 5.5.v against the book.

## Dependencies
Depends on: #320 (indexed coproducts)
Depends on: #366 (copowers and powers as an adjunction with a parameter)
Depends on: #484 (the completed Beck monadicity theorem)

<!-- catalog: {"ids":["riehl:5.5:exv","riehl:5.5:exvi"],"deps":["#320","#366","#484"]} -->

---8<---

title: "Riehl 5.5: The Lawvere theory of a monad on Set, built from its Kleisli category"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.5:exvii, riehl:5.5:def-lawvere-theory]
deps_item_ids: [riehl:5.5:def4, riehl:5.2:exvi]
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5 Exercise 5.5.vii and the prose definition interleaved between its two clauses (printed pp. 208–209, PDF pp. 228–229). Items: `riehl:5.5:exvii`, `riehl:5.5:def-lawvere-theory`.

## Background
For a monad `T` on `Set`, the full subcategory of its [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category) spanned by the finite ordinals, opposed, is the [Lawvere theory](https://ncatlab.org/nlab/show/Lawvere+theory) associated to `T` when `T` is finitary: an identity-on-objects functor `N^op → L` preserving strict finite products, whose hom-sets `L(n,1)` are the n-ary operations. Models are finite-product-preserving functors into `Set`, and the category of `T`-algebras is recovered from them.

## Current state in the library
Only the `N^op` leg exists, and the two developments are entirely unconnected. `Instance/FinSet/Lawvere.v:39` `FinSetOp_Lawvere : LawvereTheory` is exactly the exercise's `N^op` — skeletal finite sets, opposed, packaged as a theory whose object-level strictness holds by `eq_refl` even at open arguments (`law_zero_terminal := eq_refl`, `law_plus_product := fun m n => eq_refl`). But strict *associativity* of the product is not among the fields of `Class LawvereTheory` (`Theory/Lawvere.v:116`) and is not proved for `FinSet^op` — and the Phase-D verifier confirmed why this is real work rather than bookkeeping: associativity of natural-number addition is not `eq_refl` at open arguments, it needs induction on the first summand. The models half is present and in fact more general than the book's (`Theory/Lawvere/Model.v:50` `Model` as a cartesian- and terminal-preserving functor, `:77` `Models`, `:110` `Models_Full` making every natural transformation a morphism of models, over an arbitrary cartesian target, with `ev1 : Models T Sets ⟶ Sets` at `Theory/Lawvere/Sets.v:83`), and `Theory/Lawvere.v:156` `law_pow_one : law_pow n = law_of_nat n` records that every named object is an iterated power of the generic object.

Everything on the Kleisli side is missing. `rg 'Kleisli'` inside `Theory/Lawvere.v` and `Theory/Lawvere/` returns 0 hits and `rg 'Lawvere'` inside `Monad/` returns 0 hits: nothing forms the full subcategory of a Kleisli category on the finite ordinals, nothing takes its opposite, there is no identity-on-objects `I : N^op ⟶ L`, and no functor runs from `T`-algebras to models — the only bridge, `Theory/Lawvere/Monad.v:78` `Lawvere_EM_Comparison : Models T Sets ⟶ EilenbergMoore …`, runs the other way and is scoped to a hypothesized `L ⊣ ev1` supplied as data. `Theory/Lawvere/Monad.v:59-62` records that the full finitary-monad ⟷ Lawvere-theory equivalence is deferred ("ledger 2"). Note also the honest weakness of the in-tree class: `law_of_nat` is a naming function with propositional strictness equalities and bijectivity is deliberately *not* required, so consumers must add reachability by hand (`Theory/Lawvere/Sets.v:105` `ev1_Faithful` takes it as a hypothesis, witnessed on the base at `:176` `FinSetOp_reach`).

## Work to be done
- Build `L`: the full subcategory of `Kleisli T` (`Monad/Kleisli.v:38`) spanned by the objects `0, 1, 2, …` of the in-tree skeleton `Instance/FinSet.v`, and take its opposite (`Construction/Subcategory.v`, `Construction/Opposite.v`).
- Prove clause (i): `N^op` and `L` have finite products, strictly associative on objects, preserved by the identity-on-objects functor `I : N^op ⟶ L`. This includes discharging the associativity obligation the in-tree `LawvereTheory` class does not carry — prove it for `FinSet^op` by induction on the first summand, and either add it as a field or state it as a companion lemma with the header explaining the choice.
- Package the result as `LawvereTheory` and, when `T` is finitary (the `Finitary` predicate of the §5.5 finitary issue), name it the theory associated to `T`; state precisely which of Riehl's claims about `L` — that its objects are exactly the iterated powers of `1`, so the data is the family `L(n,1)` — is proved and which needs the reachability hypothesis the class omits.
- Prove clause (ii): a functor from `T`-algebras to `Models (associated theory) Sets`, using the presheaf-on-the-Kleisli-category description of algebras from the §5.2 Exercise 5.2.vi issue, as Riehl's hint directs. Relate it to the existing `Lawvere_EM_Comparison`, which runs in the opposite direction, and say in the header whether the two compose to an equivalence or whether that remains the deferred "ledger 2" item.
- Suggested module: `Theory/Lawvere/OfMonad.v`. Donors: `Monad/Kleisli.v`, `Instance/FinSet.v`, `Instance/FinSet/Lawvere.v`, `Construction/Subcategory.v`, `Theory/Lawvere.v`, `Theory/Lawvere/Model.v`, `Theory/Lawvere/Sets.v`, `Theory/Lawvere/Monad.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.5 Exercise 5.5.vii (both clauses) and the associated-theory definition; setoid `≈` on morphisms, never `=`.
- [ ] `L` constructed from the Kleisli category and shown to be a `LawvereTheory`.
- [ ] Strict associativity of the finite products is *proved* (by induction on the first summand), not assumed by `eq_refl`, and its status relative to the `LawvereTheory` class fields is documented.
- [ ] `I : N^op ⟶ L` identity-on-objects and finite-product-preserving.
- [ ] The functor from `T`-algebras to models constructed, with its relation to `Lawvere_EM_Comparison` stated.
- [ ] The reachability caveat of the in-tree `LawvereTheory` class is disclosed wherever it is load-bearing.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for `L`, `I`, the strictness lemmas and the algebras-to-models functor.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Lawvere entry gains the monad-to-theory direction, and `Theory/Lawvere/Monad.v:59-62`'s deferral note is updated to say what is now covered.

## Verification
- `coqc -R . Category Theory/Lawvere/OfMonad.v` compiles after its dependencies.
- `Print Assumptions` on the associated theory, the strict-associativity lemma and the algebras-to-models functor.
- `rg -n 'Kleisli' Theory/Lawvere/` now returns the new construction (previously 0 hits).
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks both clauses against Riehl §5.5 Exercise 5.5.vii and confirms the associativity claim is proved rather than asserted.

## Dependencies
Depends on: #475 (the Kleisli comparison functor and the free-object subcategory)
Depends on: riehl:5.5:def4 (the `Finitary` predicate, without which "the theory associated to a finitary monad" cannot be stated)
Depends on: riehl:5.2:exvi (algebras as presheaves on the Kleisli category — the hint clause (ii) rests on)

<!-- catalog: {"ids":["riehl:5.5:exvii","riehl:5.5:def-lawvere-theory"],"deps":["#475","riehl:5.5:def4","riehl:5.2:exvi"]} -->

---8<---

title: "Riehl 5.6: Monadic functors create limits, and the colimits preserved by T and T²"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.6:thm5, riehl:5.6:exii, riehl:5.6:cor7]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.6 Theorem 5.6.5, Corollary 5.6.7 and Exercise 5.6.ii (printed pp. 210–211 and 217, PDF pp. 230–231 and 237). Items: `riehl:5.6:thm5`, `riehl:5.6:exii`, `riehl:5.6:cor7`.

## Background
A [monadic functor](https://ncatlab.org/nlab/show/monadic+functor) [creates](https://ncatlab.org/nlab/show/created+limit) every limit its codomain has — the structure map on the apex is induced by the limiting cone — and every colimit its codomain has that both the induced monad and its square preserve. In particular a category monadic over `Set` is complete, with limits computed on underlying sets.

## Current state in the library
Neither clause is stated, at any level of generality. `rg -i 'creates'` finds exactly two creation developments tree-wide: `CreatesUSplitCoequalizers` (`Monad/Monadicity/Beck.v:164`, discharged at `:911` as `monadic_creates` for `EM_Forget`), which creates only coequalizers of `U`-split pairs, and `equivalence_creates_limits` / `equivalence_creates_colimits` (`Theory/Equivalence/Limit.v:486`, `:582`), which is Riehl's Lemma 3.4.6 — the *tool* this theorem's proof reduces along, not the theorem. There is no limit or colimit content anywhere in the monad tree: `rg -i 'limit' Monad/ Comonad/` returns only `Require` lines and header prose, and `Monad/Eilenberg/Moore.v` has exactly one top-level definition, `EilenbergMoore` at `:44`, with no limit structure. `EM_Forget` is a right adjoint (`EM_Adjunction`) so RAPL gives preservation, but preservation is strictly weaker than the required creation.

Corollary 5.6.7 has an additional missing input: no category in the tree is proved complete. `rg 'Complete\b' Instance/` returns exactly one hit, `Instance/ZX.v:141`, and it is a paper title; tree-wide, `Structure/Complete.v`'s `Complete` occurs only as a hypothesis (`Adjunction/GAFT.v:242`, `Adjunction/SAFT.v:145`, `:184`, `:241`, `:253`, `:275`, `Construction/Comma/Limit.v`). The near miss `Instance/Sets/Karoubi.v:101` `Sets_IdempotentsSplit` is Cauchy completeness, a different notion.

One header claim to be careful with: `Structure/Complete.v:57-59` says, citing the nLab, that "monadic functors create limits, so algebras for a monad on a complete category are again complete". The Phase-D verifier read the passage and confirmed it is a background-essay statement about mathematics in general, not an assertion that the library contains the result — it is therefore not a library defect, but it *should* be repointed at the theorem once this issue lands.

## Work to be done
- State creation of limits for `EM_Forget` first (#467's deliverable), then prove Riehl's Theorem 5.6.5(i) for an arbitrary monadic `U` by transporting along the comparison equivalence with `equivalence_creates_limits`; the transport needs the same "creation along an equivalence" plumbing that `Monad/Monadicity/Beck.v:104-110` defers for the coequalizer case, so build it once, reusably.
- Prove clause (ii) — Exercise 5.6.ii: `U` creates any colimit that `C` has and that both `T` and `T²` preserve. The argument mirrors clause (i): the structure map on the nadir is induced by the universal property of the colimit under `T U^T D`, and preservation by `T²` is what makes the associativity law check.
- Derive Corollary 5.6.7: a category monadic over `Sets` is complete, with its limits created by the forgetful functor — consuming `Complete Sets` from #407 rather than reproving it.
- Suggested module: `Monad/Eilenberg/Moore/Limits.v` (extending #467's file) plus `Monad/Creation.v` for the transport-along-an-equivalence lemmas. Donors: `Monad/Eilenberg/Moore/Adjunction.v`, `Monad/Comparison.v`, `Theory/Equivalence/Limit.v`, `Structure/Limit.v`, `Structure/Limit/Preservation.v`, `Structure/Complete.v`.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.6 Theorem 5.6.5 (both clauses), Exercise 5.6.ii and Corollary 5.6.7; setoid `≈` on morphisms, never `=`.
- [ ] Clause (i) proved for an arbitrary monadic functor, not only for `EM_Forget`.
- [ ] Clause (ii) proved with the `T`- and `T²`-preservation hypotheses stated exactly as Riehl states them.
- [ ] The creation-transports-along-an-equivalence lemma is a named, reusable result (it is the same plumbing `Monad/Monadicity/Beck.v:104-110` defers).
- [ ] Corollary 5.6.7 proved, consuming `Complete Sets` from #407.
- [ ] `Structure/Complete.v:57-59`'s essay repointed at the in-tree theorem.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for both clauses and the corollary.
- [ ] New/changed files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (creation of limits by monadic functors is flagship-level).

## Verification
- `coqc -R . Category Monad/Creation.v` and `coqc -R . Category Monad/Eilenberg/Moore/Limits.v` compile after their dependencies.
- `Print Assumptions` on both clauses of Theorem 5.6.5 and on Corollary 5.6.7.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the hypotheses of clause (ii) against Riehl §5.6 Theorem 5.6.5.

## Dependencies
Depends on: #467 (the Eilenberg–Moore forgetful functor creates limits)
Depends on: #481 (reflection of coequalizers — the creation/reflection vocabulary)
Depends on: #407 (completeness of `Sets`, for Corollary 5.6.7)

<!-- catalog: {"ids":["riehl:5.6:thm5","riehl:5.6:exii","riehl:5.6:cor7"],"deps":["#467","#481","#407"]} -->

---8<---

title: "Riehl 5.6: Cocompleteness of a monadic category reduces to coequalizers — coproducts of algebras as coequalizers of free algebras"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.6:prop11, riehl:5.6:exiii, riehl:5.6:construction-free-product]
deps_item_ids: []
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.6: the unnumbered free-product construction (printed pp. 212–213, PDF pp. 232–233), Proposition 5.6.11 (printed p. 213, PDF p. 233) and Exercise 5.6.iii (printed p. 217, PDF p. 237). Items: `riehl:5.6:prop11`, `riehl:5.6:exiii`, `riehl:5.6:construction-free-product` (the general clause; the concrete free product of groups is recorded on #450).

## Background
When `U : A → C` is monadic over a [cocomplete](https://ncatlab.org/nlab/show/cocomplete+category) `C`, the category `A` is cocomplete as soon as it has coequalizers: coproducts of algebras are built as coequalizers of a canonical pair between free algebras on the coproducts downstairs, and coproducts plus coequalizers give all colimits. This is the same construction that presents the free product of groups.

## Current state in the library
No theorem in the tree concludes cocompleteness of anything. `rg 'Cocomplete'` returns six hits: the definition and its header (`Structure/Complete.v`) and two hypothesis uses (`Theory/Adamek/Corollaries.v:51`, `:61`); no category carries an inhabitant. The (co)products-plus-(co)equalizers reduction that clause (ii) ⇒ (i) needs exists only as header prose (`Structure/Complete.v:51-54`, `Structure/Equalizer.v:80`, `Structure/Limit.v:71`, `Structure/Topos.v:23`), and the one real assertion runs the other way (`Adjunction/GAFT.v:193` `Complete_HasEqualizers` extracts equalizers *from* completeness). `HasCoequalizers` (`Structure/Coequalizer.v:68`) and `HasReflexiveCoequalizers` (`Structure/Coequalizer/Reflexive.v:54`) exist but appear only as monadicity inputs (`Monad/Monadicity/Crude.v`, `Theory/Lawvere/Monad.v:87`), never as conclusions.

The Eilenberg–Moore category has no colimits of any shape: `rg 'Colimit|Cocartesian|coproduct' Monad/ Comonad/` returns a single comment (`Monad/Monadicity/Crude.v:44`), and `EilenbergMoore T` (`Monad/Eilenberg/Moore.v:44`) carries no `Cocartesian` instance, no initial object and no coequalizers — so the object whose universal property Exercise 5.6.iii asks about cannot currently be formed. `rg -i 'free product'` returns eight hits, all prose (`Construction/Funny.v:34`, `:64`, `:113`, `Construction/Funny/Associator.v:30`, `Construction/Funny/Hom.v:8`, `Construction/Groupoid.v:62`, `Structure/Cocartesian.v:44`, `:68`). The Phase-D verifier added one near-miss Phase C had missed and it is worth knowing: `Instance/Comp.v` does contain a free-algebra construction with its universal property (`:92` `Free`, `:108` `induced_hom`, `:116` `from_free_unique`) and a group signature (`:382` `Group := Algebra GroupOp GroupEq`) — but `Algs` (`:151`) is the category of algebras for a signature with *no* equations, there is no adjunction (`rg 'Adjunction' Instance/Comp.v` → 0 hits), and `Algs_Cocartesian` at `:224` sits inside a comment block opening at `:223` and closing at `:232`, so it is not in force.

## Work to be done
- Construct the coproduct of a family of `T`-algebras `(A_i, a_i)` as the coequalizer, in `C^T`, of the canonical pair between the free algebras on `∐_i A_i` and on `∐_i T A_i`: one leg the free-algebra map induced by the family of structure maps, the other built from the comparison `∐_i T A_i → T (∐_i A_i)` followed by the multiplication. Prove Exercise 5.6.iii — that this coequalizer really does have the coproduct universal property.
- Prove Proposition 5.6.11: for `C` cocomplete and `U : A ⟶ C` monadic, `A` is cocomplete iff `A` has coequalizers. The forward direction is trivial; for the converse, replace `A` by `C^T` along the comparison equivalence, supply coproducts by the previous step and conclude by the coproducts-plus-coequalizers reduction — which must itself be proved, since it is currently only prose in the library (state it as `HasCoequalizers C → HasIndexedCoproducts C → Cocomplete C`, the dual of the classical limit reduction).
- Record the general form of Riehl's free-product construction: for any monadic `U : A ⟶ C` over cocomplete `C`, a binary coproduct in `A` is the coequalizer of `F(U ε ⊔ U ε)` and `ε ∘ F(k)` on `F(U a ⊔ U b)`, whenever that coequalizer exists — and cross-reference #450 for the concrete free product of groups.
- Suggested modules: `Structure/Colimit/Reduction.v` (the coproducts-plus-coequalizers theorem), `Monad/Eilenberg/Moore/Colimits.v` (the coproduct of algebras and Proposition 5.6.11). Donors: `Structure/Coequalizer.v`, `Structure/Complete.v`, `Monad/Eilenberg/Moore/Adjunction.v`, `Monad/Comparison.v`, `Structure/Limit/Product.v` (the `iprod` template to dualize), #320's indexed coproducts.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.6 Proposition 5.6.11, Exercise 5.6.iii and the general clause of the free-product construction; setoid `≈` on morphisms, never `=`.
- [ ] The coproduct of algebras is constructed as the stated coequalizer and its universal property is *proved*, not asserted.
- [ ] The coproducts-plus-coequalizers ⇒ cocomplete reduction is proved in-tree (it is currently prose only) and cited by, rather than inlined into, the proposition.
- [ ] Proposition 5.6.11 proved in both directions for an arbitrary monadic functor.
- [ ] Indexed coproducts are consumed from #320, not re-specified.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the coproduct construction, the reduction theorem and the proposition.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated — the Eilenberg–Moore entry gains colimits.

## Verification
- `coqc -R . Category Structure/Colimit/Reduction.v` and `coqc -R . Category Monad/Eilenberg/Moore/Colimits.v` compile after their dependencies.
- `Print Assumptions` on the coproduct universal property and on Proposition 5.6.11.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the parallel pair against Riehl §5.6 Proposition 5.6.11 and confirms Exercise 5.6.iii is discharged.

## Dependencies
Depends on: #320 (indexed coproducts)
Depends on: #329 (chain unions as colimits and the cocompleteness of `Sets`)
Depends on: #483 (the canonical presentation of an algebra as a coequalizer of free algebras)

<!-- catalog: {"ids":["riehl:5.6:prop11","riehl:5.6:exiii","riehl:5.6:construction-free-product"],"deps":["#320","#329","#483"]} -->

---8<---

title: "Riehl 5.6: Algebras for a finitary monad are complete and cocomplete, and categories of models are cocomplete"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:5.6:thm12, riehl:5.6:cor14]
deps_item_ids: [riehl:5.5:def4, riehl:5.6:prop11, riehl:5.6:thm5]
deps_pending: []

## Source
Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.6 Theorem 5.6.12 (printed pp. 213–217, PDF pp. 233–237) and Corollary 5.6.14 (printed p. 217, PDF p. 237). Items: `riehl:5.6:thm12`, `riehl:5.6:cor14`.

## Background
For a [finitary monad](https://ncatlab.org/nlab/show/finitary+monad) on a complete, cocomplete, locally small category, the category of algebras is again complete and cocomplete: completeness is creation of limits, and cocompleteness reduces to coequalizers, which the general adjoint functor theorem supplies once a solution set is produced by an ω-indexed approximating construction that the finitary monad's preservation of filtered colimits makes converge. Hence every [algebraic category](https://ncatlab.org/nlab/show/algebraic+category) is cocomplete.

## Current state in the library
Nothing of the theorem, and one of its two hypotheses is unstatable. `rg -i 'finitary'` returns 16 hits, all header prose, with no `Finitary` class or predicate anywhere; `rg -i 'filtered'` returns one unrelated hit (`Comonad/CoKleisli.v:81`), so "T preserves filtered colimits" cannot be written. `rg 'Complete|Cocomplete' Monad/` returns 0 hits: `EilenbergMoore T` (`Monad/Eilenberg/Moore.v:44`) is never shown to have limits or colimits of any shape. On the models side, `Theory/Lawvere/Model.v` proves nothing about (co)limits of `Models T C`, and the only relevant occurrence in `Theory/Lawvere/` is the *hypothesis* `Context (RC : HasReflexiveCoequalizers (Models T Sets))` at `Theory/Lawvere/Monad.v:87`; the in-tree varieties file `Instance/Comp.v` proves only `Algs_Terminal` (`:160`), `Algs_Cartesian` (`:169`), `Algs_Initial` (`:209`) and an indexed `Product` (`:434`), with `Algs_Cocartesian` (`:224`) commented out.

The engine the book's proof uses *is* in place and should be consumed rather than rebuilt: `Adjunction/GAFT.v:241` `Theorem GAFT (U : C ⟶ D) (comp : @Complete C) (cont : @PreservesImageLimit C D U) (sols : ∀ d, SolutionSet U d) : { F : D ⟶ C & F ⊣ U }`, with `Record SolutionSet` at `:159`; it has never been applied to a category of algebras. Also in place: `Instance/Omega.v:72` `Omega` and `Construction/Chain.v` for the ω-indexed construction.

## Work to be done
- Completeness: immediate from the monadic-creation theorem of the §5.6 Theorem 5.6.5 issue, given `Complete C`.
- Cocompleteness: by the §5.6 Proposition 5.6.11 issue it suffices to produce coequalizers in `C^T`. Follow Riehl and get them as a left adjoint to the constant-diagram functor into the category of parallel pairs of algebras, via `GAFT`: the constant-diagram functor preserves limits because limits in functor categories are pointwise, so only the solution-set condition is at issue.
- The solution set is the technical core and should be built exactly as the book does: for a parallel pair of algebra maps, take coequalizers `q₀` and `p₀` downstairs, set `P_{n+1} := T Q_n` with `Q_{n+1}` the coequalizer of the pair built from the multiplication and the previous maps, pass to the sequential colimit over `Omega` (which `T` preserves because it is finitary and ω is filtered), verify the unit and associativity laws on the colimit, and show every fork under the given pair factors through it by the inductively constructed family satisfying the book's displayed condition.
- Corollary 5.6.14: any category of models for an algebraic theory (the predicate of the §5.5 finitary issue) is cocomplete, since `Sets` is complete (#407) and cocomplete (#329). Record the closing remark about compact Hausdorff spaces — cocomplete despite a non-finitary monad, by reflectivity in `Top` — as a cross-reference to #489 and #434 rather than as an in-file claim.
- Suggested module: `Monad/Eilenberg/Moore/Bicomplete.v`. Donors: `Adjunction/GAFT.v`, `Instance/Omega.v`, `Construction/Chain.v`, `Structure/Coequalizer.v`, `Monad/Eilenberg/Moore.v`, `Structure/Limit/Preservation.v`, and the §5.5 finitary and §5.6 Prop 5.6.11 / Thm 5.6.5 issues.

## Definition of Done
- [ ] Statement fidelity to Riehl §5.6 Theorem 5.6.12 and Corollary 5.6.14; setoid `≈` on morphisms, never `=`.
- [ ] Completeness of `C^T` derived from the monadic-creation theorem, not reproved.
- [ ] The solution-set construction carried out over `Omega`, with the finitary hypothesis used exactly where the book uses it (preservation of the sequential colimit), and the factorization condition proved.
- [ ] `GAFT` applied, not re-derived; `docs/INHABITATION.md` updated, since this would be the first application of the in-tree adjoint functor theorem to a category of algebras.
- [ ] Corollary 5.6.14 proved for the algebraic-category predicate.
- [ ] The `cHaus` remark recorded as a cross-reference, not as an unproved assertion.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` closed for the bicompleteness theorem and the corollary.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` adds no new hits.
- [ ] CLAUDE.md Key Files index updated (bicompleteness of algebra categories is flagship-level).

## Verification
- `coqc -R . Category Monad/Eilenberg/Moore/Bicomplete.v` compiles after its dependencies.
- `Print Assumptions` on the bicompleteness theorem and on Corollary 5.6.14.
- `rg -n 'GAFT' Monad/` shows the theorem consuming the in-tree adjoint functor theorem.
- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.
- Reviewer checks the ω-indexed solution-set construction against Riehl §5.6 Theorem 5.6.12.

## Dependencies
Depends on: #407 (completeness of `Sets`)
Depends on: #329 (cocompleteness of `Sets`)
Depends on: riehl:5.5:def4 (the `Finitary` predicate and the algebraic-category notion)
Depends on: riehl:5.6:prop11 (cocompleteness of a monadic category reduces to coequalizers)
Depends on: riehl:5.6:thm5 (monadic functors create limits)

<!-- catalog: {"ids":["riehl:5.6:thm12","riehl:5.6:cor14"],"deps":["#407","#329","riehl:5.5:def4","riehl:5.6:prop11","riehl:5.6:thm5"]} -->

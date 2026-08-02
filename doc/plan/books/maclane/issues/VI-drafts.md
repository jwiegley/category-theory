title: "MacLane VI.1: Monads on a preorder are closure operators, and their algebras are the closed elements"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.1:remark2, maclane:VI.2:remark1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VI.1 (book p. 139, PDF p. 148) and §VI.2 (book p. 141, PDF p. 150). Items: `maclane:VI.1:remark2`, `maclane:VI.2:remark1`.

## Background
A monad on a poset, viewed as a thin category, is exactly a **closure operator**: a monotone map `t` with `x ≤ t x` (extensivity, the unit) and `t (t x) = t x` (idempotency, the multiplication); its algebras are precisely the closed (fixed) elements. See nLab [closure operator](https://ncatlab.org/nlab/show/closure+operator) and [idempotent monad](https://ncatlab.org/nlab/show/idempotent+monad).

## Current state in the library
Posets are formalized as thin categories (`Instance/Poset.v:116`, via `Proset`), the general `Monad` class lives in `Theory/Monad.v:92`, and the categorified idempotent-monad theory is fully present — `Construction/Reflective/Idempotent.v:81` `IdempotentMonad`, with `Idempotent_EM_Equivalence` (`Construction/Reflective/Idempotent.v:464`) proving the Eilenberg–Moore category of an idempotent monad is equivalent to its subcategory of local/fixed-point objects. What is missing is the *elementary* poset statement: `Instance/Poset.v:48-49` and the `Theory/Monad.v` header assert "a monad is a closure operator" only in prose. There is no `ClosureOperator` datatype, no lemma exhibiting a `Monad` on a poset as `(monotone t, x ≤ t x, t (t x) = t x)`, and no instance showing its `TAlgebra`s are the closed elements (`grep` for `ClosureOperator|closure_operator` returns 0 hits).

## Work to be done
- Define a `ClosureOperator` on a poset/preorder `P`: an endo on `P` (monotone map) with extensivity `x ≤ t x` and idempotency `t (t x) ≈ t x` (in a partial order this is equality; over a preorder use `≈`/`iso`).
- Prove the correspondence `Monad` on `Proset P` `↔` `ClosureOperator P` (all monad diagrams hold automatically by thinness; the content is the two inequalities).
- Prove that a `TAlgebra` for such a monad is exactly a closed element (`t x ≤ x`, hence `x ≈ t x`), instantiating the general fixed-point result of `Construction/Reflective/Idempotent.v` on the poset case.
- Suggested module: `Instance/Poset/Closure.v` (donors: `Instance/Poset.v`, `Theory/Monad.v`, `Monad/Algebra.v`, `Construction/Reflective/Idempotent.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.1/§VI.2 (paraphrased above); morphism/order equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (core theory stays axiom-free per docs/AXIOMS.md).
- [ ] `Print Assumptions` clean for `ClosureOperator`, the `Monad ↔ ClosureOperator` correspondence, and the algebras-are-closed-elements lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result is deemed flagship-level.

## Verification
- `coqc -R . Category Instance/Poset/Closure.v` compiles after its dependencies.
- `Print Assumptions` on the correspondence and the algebra lemma shows no axioms.
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` pass.
- Reviewer confirms the in-tree statement is Mac Lane's "monad on a poset = closure operator; algebras = closed elements".

## Dependencies
None (builds on in-tree `Instance/Poset.v`, `Theory/Monad.v`, `Monad/Algebra.v`, `Construction/Reflective/Idempotent.v`).

<!-- catalog: {"ids":["maclane:VI.1:remark2","maclane:VI.2:remark1"],"deps":[]} -->

---8<---

title: "MacLane VI.2: The group-action monad G×(−) and its algebras are G-sets"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.2:remark2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.2 (book p. 141, PDF p. 150). Item: `maclane:VI.2:remark2`.

## Background
For a fixed group `G`, the endofunctor `T X = G × X` on `Set` carries a monad structure (unit `x ↦ (e, x)`, multiplication `(g₁,(g₂,x)) ↦ (g₁ g₂, x)`); its Eilenberg–Moore algebras are exactly left `G`-actions (`G`-sets). See Wikipedia [Group action](https://en.wikipedia.org/wiki/Group_action) and nLab [algebra over a monad](https://ncatlab.org/nlab/show/algebra+over+a+monad).

## Current state in the library
There is no `G × (−)` monad and no category of `G`-sets. A blind search (`grep -i 'G.?set|group.?action|writer'`) turns up only the symmetric-group actions of the multicategory/operad development, groupoids, and the delooping of a monoid as a one-object bicategory (`Theory/Bicategory/OneObject.v`) — none is the `G × (−)` monad or its algebras. `Instance/Coq/Monad.v` builds no product/writer monad. The in-tree `GroupObject` (`Structure/Group.v:109`) supplies a group object in `(Sets, ×)`, which is the only reusable donor.

## Work to be done
- Fix a group object `G` in `(Sets, ×)` (donor: `Structure/Group.v`, `Instance/Sets.v`). Build the endofunctor `G × (−) : Sets ⟶ Sets` and equip it with `ret`/`join` as above; discharge the `Monad` laws (`Theory/Monad.v`).
- Define the category of `G`-sets (a set with an action `h : G × X → X`, `h(g₁ g₂, x) ≈ h(g₁, h(g₂, x))`, `h(e, x) ≈ x`; equivariant maps as morphisms).
- Prove an isomorphism (or equivalence) `EilenbergMoore (G × (−)) ≅ G-Set`, matching the `TAlgebra` structure map to the action.
- Suggested module: `Instance/Sets/Action.v` (donors: `Structure/Group.v`, `Instance/Sets.v`, `Theory/Monad.v`, `Monad/Algebra.v`, `Monad/Eilenberg/Moore.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.2 (paraphrased above); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the monad `G × (−)` and the `G-Set ≅ EM` comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Sets/Action.v` compiles after its dependencies.
- `Print Assumptions` on the monad and the comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the in-tree statement against Mac Lane §VI.2 (algebras of `G × (−)` = `G`-sets).

## Dependencies
None required as filed issues (builds on the in-tree `GroupObject`, `Sets`, and Eilenberg–Moore machinery).

<!-- catalog: {"ids":["maclane:VI.2:remark2"],"deps":[]} -->

---8<---

title: "MacLane VI.2: The monad R⊗(−) on Ab and its algebras are left R-modules"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.2:remark3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.2 (book p. 142, PDF p. 151). Item: `maclane:VI.2:remark3`.

## Background
For a ring `R`, the endofunctor `T A = R ⊗ A` on the category of abelian groups carries a monad structure (unit `a ↦ 1 ⊗ a`, multiplication `r₁ ⊗ (r₂ ⊗ a) ↦ r₁ r₂ ⊗ a`) whose Eilenberg–Moore algebras are exactly the left `R`-modules. See nLab [module](https://ncatlab.org/nlab/show/module) and [algebra over a monad](https://ncatlab.org/nlab/show/algebra+over+a+monad).

## Current state in the library
There is no category `Ab` of abelian groups and no `R ⊗ (−)` monad; a blind search returns only prose (`Structure/Abelian.v:68` names `Ab` as a motivating example; Morita/Lawvere prose mention modules). The nearest concrete additive witness is `Instance/CMon.v` (commutative monoids), not `Ab` or `R`-modules. The category `Ab` and the category of `R`-modules are the subjects of the already-filed issues #256 and #258; this item adds the monad-theoretic content on top of them.

## Work to be done
- On top of a category of abelian groups (issue #256) and a ring `R`, build the endofunctor `R ⊗ (−) : Ab ⟶ Ab` and its `Monad` structure (`ret`, `join`, laws).
- Prove `EilenbergMoore (R ⊗ (−)) ≅ R-Mod` (issue #258), identifying the `TAlgebra` structure map with the scalar action.
- Suggested module: `Instance/RMod/TensorMonad.v` (donors: the `Ab` and `R-Mod` instances from #256/#258, `Theory/Monad.v`, `Monad/Eilenberg/Moore.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.2 (paraphrased above); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the `R ⊗ (−)` monad and the `R-Mod ≅ EM` comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/RMod/TensorMonad.v` compiles after its dependencies.
- `Print Assumptions` on the monad and comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.2 (algebras of `R ⊗ (−)` on `Ab` = left `R`-modules).

## Dependencies
Depends on: #256 (the category `Ab` of abelian groups)
Depends on: #258 (module categories `R-Mod`)

<!-- catalog: {"ids":["maclane:VI.2:remark3"],"deps":["#256","#258"]} -->

---8<---

title: "MacLane VI.2: The power-set monad and complete semilattices (Manes)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.2:ex1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.2, Exercise 1 (book p. 142, PDF p. 151). Item: `maclane:VI.2:ex1`.

## Background
The covariant power-set functor `𝒫` on `Set`, with unit `x ↦ {x}` and multiplication = union of a set of subsets, is a monad whose Eilenberg–Moore algebras are exactly the (small) complete join-semilattices, with sup-preserving maps as morphisms (Manes). See nLab [power set](https://ncatlab.org/nlab/show/power+set) and [suplattice](https://ncatlab.org/nlab/show/suplattice) (which states `SupLat` is monadic over `Set` via the covariant power-set monad).

## Current state in the library
There is no covariant power-set monad and no category of complete semilattices. A blind search finds "Manes" only as a prose citation (`Theory/Monad.v`); `Pow a := Ω^a` (`Structure/Topos.v`) is the power *object*, and `pow X n` (`Theory/Multicategory/Algebra.v`) is a finite arity `Xⁿ` — neither is the covariant power-set functor. `Structure/Complete.v` is "complete category" (all small limits), not the algebraic complete lattice.

## Work to be done
- Build the covariant power-set endofunctor on `Sets` (donor: `Instance/Sets.v`; over setoids, use the setoid of subsets/predicates up to `iff`) with `ret` = singleton and `join` = union; discharge the `Monad` laws.
- Define the category of complete (join-)semilattices / sup-lattices and sup-preserving maps.
- Prove the two directions: every `𝒫`-algebra `(X,h)` is a complete semilattice under `x ≤ y ↔ h {x,y} ≈ y` with `sup S = h S`; conversely every small complete semilattice is a `𝒫`-algebra; assemble the isomorphism/equivalence `EilenbergMoore 𝒫 ≅ SupLat`.
- Suggested module: `Instance/Sets/Powerset.v` (plus `Instance/SupLat.v`); donors: `Instance/Sets.v`, `Theory/Monad.v`, `Monad/Eilenberg/Moore.v`.

## Definition of Done
- [ ] Statement matches Mac Lane §VI.2 Ex. 1 (paraphrased above); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the power-set monad and the `SupLat ≅ EM` comparison.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Sets/Powerset.v` compiles after its dependencies.
- `Print Assumptions` on the monad and comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks all four parts of the exercise against Mac Lane §VI.2 Ex. 1.

## Dependencies
None (self-contained over `Instance/Sets.v` and the Eilenberg–Moore machinery).

<!-- catalog: {"ids":["maclane:VI.2:ex1"],"deps":[]} -->

---8<---

title: "MacLane VI.2: The Eilenberg–Moore forgetful functor creates limits"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.2:ex2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.2, Exercise 2 (book p. 142, PDF p. 151). Item: `maclane:VI.2:ex2`.

## Background
The forgetful functor `Gᵀ : Xᵀ → X` of the Eilenberg–Moore category **creates limits**: a limit of the underlying diagram lifts uniquely to a limit of algebras, whose structure map is induced by the monad on the limit. See nLab [monadic functor](https://ncatlab.org/nlab/show/monadic+functor) and [created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
The Eilenberg–Moore category and its forgetful functor exist (`Monad/Eilenberg/Moore.v:44`, `EM_Forget`), but there is no theorem that it creates (or even preserves) limits. The only in-tree `EM_Forget` creation result is `em_forget_creates_split`/`monadic_creates` (`Monad/Monadicity/BeckObjects.v:396`, `Monad/Monadicity/Beck.v:911`): creation of `U`-*split coequalizers* — a colimit-side property for Beck's theorem, not creation of limits. General "creates limits" vocabulary exists only for equivalences (`Theory/Equivalence/Limit.v`) and comma projections (`Construction/Comma/Limit.v`), the latter over the honest cone-level `PreservesImageLimit` (`Construction/Comma/Limit.v:110`, filed as #406's neighbourhood). `EM_Forget` is a right adjoint (`EM_Adjunction`) so it preserves limits (RAPL), but preservation is strictly weaker than the required creation.

## Work to be done
- State and prove `EM_Forget` **creates limits** for the general Eilenberg–Moore category `Monad/Eilenberg/Moore.v`, using the creation-of-limits vocabulary underpinning issue #406 (`Structure/Limit`/`Construction/Comma/Limit.v`).
- Concretely: given a diagram in `Xᵀ` whose underlying diagram in `X` has a limit, transport the monad action along the limiting cone to a unique algebra structure on the apex, and show the lifted cone is limiting in `Xᵀ`.
- Suggested module: `Monad/Eilenberg/Moore/Limits.v` (donors: `Monad/Eilenberg/Moore/Adjunction.v`, `Structure/Limit.v`, the creation-of-limits definition of #406).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.2 Ex. 2 (`Gᵀ` creates limits); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the creation-of-limits theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Eilenberg/Moore/Limits.v` compiles after its dependencies.
- `Print Assumptions` on the theorem shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.2 Ex. 2 and against the creation-of-limits definition used by #406.

## Dependencies
Depends on: #406 (creation of limits by a functor — the vocabulary this theorem instantiates)

<!-- catalog: {"ids":["maclane:VI.2:ex2"],"deps":["#406"]} -->

---8<---

title: "MacLane VI.2: Morphisms of monads, the category of monads, and the induced functor between algebra categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.2:ex3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.2, Exercise 3 (book p. 142, PDF p. 151). Item: `maclane:VI.2:ex3`.

## Background
A **morphism of monads** `θ : T ⇒ T'` on a fixed category is a natural transformation compatible with the units and multiplications; monads and their morphisms form a category, and each `θ` induces a functor `θ* : X^{T'} → X^{T}` between Eilenberg–Moore categories commuting with the forgetful functors. See nLab [monad](https://ncatlab.org/nlab/show/monad) (2-category of monads, morphisms of monads).

## Current state in the library
Only a restricted shape is present: `Monad/Transformer.v:46` `MonadTransformer` packages the monad-morphism laws as `lift : M ⟹ T M` (`lift_return`, `lift_bind`), i.e. compatibility with unit and Kleisli-bind, but only for the special source/target `M ⟹ T M`. There is **no** general `MonadHom` class between two arbitrary monads `T, T'`, no category of monads on a fixed `X`, and — the exercise's substantive content — no induced `θ* : X^{T'} → X^{T}` with `Gᵀ ∘ θ* = G^{T'}` nor the accompanying `F^{T'} ⇒ θ* ∘ Fᵀ`. (`crude_theta` in `Monad/Monadicity/Crude.v` is an unrelated mediator, not this `θ*`.)

## Work to be done
- Define `MonadHom T T'` (a natural transformation `θ : T ⇒ T'` with `θ ∘ ret ≈ ret'` and `θ ∘ join ≈ join' ∘ θ θ`), generalizing the `MonadTransformer` laws.
- Assemble the category `Monads X` (objects = monads on `X`, arrows = `MonadHom`).
- Construct the induced functor `θ* : EilenbergMoore T' → EilenbergMoore T` (reindex an algebra `(x, h')` to `(x, h' ∘ θ_x)`), prove `EM_Forget T ∘ θ* ≈ EM_Forget T'`, and build the natural transformation `Fᵀ' ⇒ θ* ∘ Fᵀ`.
- Suggested module: `Monad/Morphism.v` (donors: `Theory/Monad.v`, `Monad/Algebra.v`, `Monad/Eilenberg/Moore.v`, `Monad/Transformer.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.2 Ex. 3 (parts a and b); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `MonadHom`, `Monads X`, and `θ*` with `Gᵀ ∘ θ* ≈ G^{T'}`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Morphism.v` compiles after its dependencies.
- `Print Assumptions` on `θ*` and the forgetful-commuting law shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.2 Ex. 3.

## Dependencies
None (builds on in-tree `Theory/Monad.v`, `Monad/Algebra.v`, `Monad/Eilenberg/Moore.v`).

<!-- catalog: {"ids":["maclane:VI.2:ex3"],"deps":[]} -->

---8<---

title: "MacLane VI.3: The discrete-space adjunction induces the identity monad — a non-monadic example"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.3:remark1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.3 (book p. 144, PDF p. 153). Item: `maclane:VI.3:remark1`.

## Background
The forgetful functor `Top → Set` has the discrete-topology functor as left adjoint with identity unit, so the induced monad on `Set` is the identity monad, whose algebras are just sets; the comparison functor `Top → Top^I = Set` is the forgetful functor itself, which is neither an isomorphism nor an equivalence — an explicit non-monadic adjunction. See nLab [monadic functor](https://ncatlab.org/nlab/show/monadic+functor).

## Current state in the library
There is no category `Top` and no discrete-topology functor in the tree (`Instance/Discrete.v` is the discrete *category* on a type, unrelated). The identity monad appears only via the identity adjunction `Id ⊣ Id` (`Monad/Monadicity/Examples.v`), which is proved **monadic** (`identity_monadic`) — the opposite of this remark's point. `Top` and its adjoint triple are the subjects of the already-filed issues #259 and #456; this item adds the monad-theoretic consequence (identity monad + failure of monadicity).

## Work to be done
- Using the category `Top` (#259) and its discrete ⊣ underlying adjunction (#456), show the induced monad on `Set` is the identity monad (`Adjunction_Induced_Monad` `≅` the identity monad).
- Exhibit the comparison functor into the Eilenberg–Moore category of the identity monad and show it coincides (up to the identity-monad algebra iso) with the forgetful `Top → Set`, hence is not an equivalence — a concrete inhabitant witnessing "adjunction inducing the identity monad, not monadic".
- Suggested module: `Instance/Top/Monadicity.v` (donors: the `Top` instance and its adjunction from #259/#456, `Monad/Comparison.v`, `Monad/Monadicity/Examples.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.3 (paraphrased above); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the induced-identity-monad claim and the non-equivalence of the comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Top/Monadicity.v` compiles after its dependencies.
- `Print Assumptions` shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.3.

## Dependencies
Depends on: #259 (the category `Top` of topological spaces)
Depends on: #456 (the underlying-set functor of `Top` and its adjoint triple — the discrete adjunction)

<!-- catalog: {"ids":["maclane:VI.3:remark1"],"deps":["#259","#456"]} -->

---8<---

title: "MacLane VI.4: The word monad, the free-semigroup adjunction, and monadicity of semigroups over Set"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.4:construction1, maclane:VI.4:prop1, maclane:VI.4:prop2, maclane:VI.4:cor1, maclane:VI.4:remark1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.4 (book pp. 144–146, PDF pp. 153–155). Items: `maclane:VI.4:construction1`, `maclane:VI.4:prop1`, `maclane:VI.4:prop2`, `maclane:VI.4:cor1`, `maclane:VI.4:remark1`.

## Background
The free semigroup on a set is the set `⨆_{n≥1} Xⁿ` of nonempty words under juxtaposition; the forgetful functor `Smgrp → Set` has it as left adjoint, and the induced **word monad** `W` has singleton unit and bracket-erasing (concatenation) multiplication. Its algebras are sets with a compatible family of n-ary operations, equivalently semigroups, so the comparison functor `Smgrp → Set^W` is an isomorphism — `Smgrp` is monadic over `Set`. See nLab [free monoid](https://ncatlab.org/nlab/show/free+monoid) and [monadic functor](https://ncatlab.org/nlab/show/monadic+functor).

## Current state in the library
None of this is present. There is no category `Smgrp` of semigroups (`Theory/Category/Semi.v` is a semigroup*oid*/semicategory; `Theory/Coq/Semigroup.v` is an ops-only typeclass) and no free-semigroup functor. The in-tree `list_Monad` (`Theory/Coq/List.v:113`, `flatten` at `:84`) is the free-*monoid* monad `⨆_{n≥0} Xⁿ` (with the empty word) presented only as ops on Coq's `list` — the categorical monad laws are unproven and no `@Monad Coq list` exists (the `IsMonad` bridge covers only Identity/arrow/Compose). So neither §VI.4's free-*semigroup* object nor the assertion that `W` is a monad nor the algebra characterization is formalized.

## Work to be done
- Build the category `Smgrp` of semigroups and homomorphisms (over `Sets`), the free-semigroup functor `F X = (⨆_{n≥1} Xⁿ, juxtaposition)`, and the adjunction `Set ⇀ Smgrp` (universal arrow `x ↦ ⟨x⟩`, counit erasing brackets).
- Define the word monad `W` as the induced monad (`Adjunction_Induced_Monad`) and discharge its `Monad` laws (`join` = concatenation).
- Prove the algebra characterization: a `W`-algebra is a set with an n-ary operation `vₙ` per `n≥1` satisfying `v₁ = id` and the concatenation-compatibility law; and the corollary that this is equivalent to a single associative binary operation with its iterated powers (`v_{n+1} = vₙ ∘ (v₂ × 1)`).
- Prove the comparison functor `K : Smgrp → EilenbergMoore W` is an isomorphism (or, minimally, an equivalence) — semigroups are monadic over `Set`.
- Suggested modules: `Instance/Semigroup.v`, `Monad/Instance/Word.v` (donors: `Instance/Sets.v`, `Theory/Monad.v`, `Monad/Adjunction.v`, `Monad/Comparison.v`, `Monad/Algebra.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.4 (construction, Prop. 1, Prop. 2, corollary, monadicity remark); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the word monad, the algebra characterization, and the comparison functor.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/Word.v` compiles after its dependencies.
- `Print Assumptions` on `W`, the algebra characterization, and `K` shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks each of the four numbered results against Mac Lane §VI.4.

## Dependencies
None as filed issues (a self-contained §VI.4 development; may optionally reuse the in-tree `EM_Comparison` for the monadicity leg).

<!-- catalog: {"ids":["maclane:VI.4:construction1","maclane:VI.4:prop1","maclane:VI.4:prop2","maclane:VI.4:cor1","maclane:VI.4:remark1"],"deps":[]} -->

---8<---

title: "MacLane VI.4: The monoid monad W₀ and monoids as its algebras"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.4:ex1]
deps_item_ids: [maclane:VI.4:prop2]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.4, Exercise 1 (book p. 146, PDF p. 155). Item: `maclane:VI.4:ex1`.

## Background
The forgetful functor `Mon → Set` induces the free-**monoid** monad `W₀` (`W₀ X = ⨆_{n≥0} Xⁿ`, i.e. all finite words including the empty one); a `W₀`-algebra is a set with a nullary operation `v₀` (the unit) and n-ary operations `vₙ` (the n-fold product), i.e. exactly a monoid. See nLab [free monoid](https://ncatlab.org/nlab/show/free+monoid).

## Current state in the library
The underlying object matches the in-tree `list_Monad` (`Theory/Coq/List.v:113`) — the free monoid `list X = ⨆_{n≥0} Xⁿ` with singleton `ret` and `flatten` join — and `list` is a certified endofunctor on Coq (`list_Functor : IsFunctor`, `Theory/Coq/List/Proofs.v:1047`). But `list_Monad` is the ops-only Haskell-style class (laws in prose, not fields): the categorical monad laws are unproven, no `@Monad Coq list` (or `@Monad Sets`) is built, and the exercise's deliverable — `W₀`-algebras are monoids via the `v₀, v₁, …` presentation — is entirely absent (no ordinary category `Mon`, no algebra characterization).

## Work to be done
- Build the free-monoid monad `W₀` as a genuine `@Monad` on `Sets` (donor: the list construction; discharge unit/associativity laws), or on `Coq` with an `IsMonad` witness.
- Define the category `Mon` of monoids (donor: `MonoidObject` in `(Sets, ×)`, `Structure/Monoid.v`).
- Prove the `W₀`-algebra characterization (`v₀` nullary, `v₁ = id`, `vₙ` the n-fold product) and the isomorphism/equivalence `EilenbergMoore W₀ ≅ Mon`, reusing the n-ary-operation algebra framework of the §VI.4 word-monad development.
- Suggested module: `Monad/Instance/List.v` (donors: `Theory/Coq/List.v`, `Structure/Monoid.v`, `Monad/Algebra.v`, `Monad/Eilenberg/Moore.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.4 Ex. 1; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the lawful `W₀` monad and the `Mon ≅ EM` comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/List.v` compiles after its dependencies.
- `Print Assumptions` on `W₀` and the comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.4 Ex. 1.

## Dependencies
Depends on: maclane:VI.4:prop2 (the n-ary-operation algebra framework of the word monad, reused for the monoid case)

<!-- catalog: {"ids":["maclane:VI.4:ex1"],"deps":["maclane:VI.4:prop2"]} -->

---8<---

title: "MacLane VI.4: The free R-module monad on Set and R-modules as its algebras"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.4:ex2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.4, Exercise 2 (book p. 146, PDF p. 155). Item: `maclane:VI.4:ex2`.

## Background
For a ring `R` with unit, the forgetful functor `R-Mod → Set` has a left adjoint, giving a monad `T_R` on `Set` with `T_R X` = the finitely-supported functions `X → R` (free `R`-module on `X`); its Eilenberg–Moore algebras are exactly the `R`-modules, presented through the linear-combination operations. See nLab [free module](https://ncatlab.org/nlab/show/free+module).

## Current state in the library
There is no `R-Mod` category, no ring category, and no free-`R`-module monad (no finitely-supported-function functor `T_R`). `Instance/CMon.v` and the abstract `Structure/Abelian.v` supply neither `R`-modules nor a free-module adjunction. Module categories and the `R-Mod → Ab` adjoints are the subjects of the already-filed issues #258 and #360; this item builds the monad and its algebra characterization on top of them.

## Work to be done
- On top of `R-Mod` (#258) and its free/forgetful adjunction to `Set` (cf. #360), define `T_R X` = finitely-supported `X → R`, with the transition/unit/multiplication maps described in the exercise, and discharge the `Monad` laws.
- Prove `EilenbergMoore T_R ≅ R-Mod`, matching the structure map to formation of linear combinations.
- Suggested module: `Monad/Instance/FreeModule.v` (donors: the `R-Mod` instance of #258, `Theory/Monad.v`, `Monad/Eilenberg/Moore.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.4 Ex. 2 (parts a–c); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `T_R` and the `R-Mod ≅ EM` comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/FreeModule.v` compiles after its dependencies.
- `Print Assumptions` on `T_R` and comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.4 Ex. 2.

## Dependencies
Depends on: #258 (module categories `R-Mod`)
Depends on: #360 (the forgetful `R-Mod → Ab`/`Set` and its adjoints)

<!-- catalog: {"ids":["maclane:VI.4:ex2"],"deps":["#258","#360"]} -->

---8<---

title: "MacLane VI.4: The polynomial-ring monad from CRng"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.4:ex3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.4, Exercise 3 (book p. 146, PDF p. 155). Item: `maclane:VI.4:ex3`.

## Background
The forgetful functor `CRng → Set` from commutative rings has a left adjoint sending a set `X` to the polynomial ring `ℤ[x : x ∈ X]` (the free commutative ring on `X`); the exercise asks for a complete description of this adjunction and its induced monad. See nLab [polynomial ring](https://ncatlab.org/nlab/show/polynomial+ring) ("the free commutative R-algebra generated by X").

## Current state in the library
There is no category `CRng` (or `Ring`) of commutative rings, no forgetful `CRng → Set`, and no polynomial-ring monad. The "polynomial" hits in-tree are polynomial *functors* (initial-algebra theory), unrelated to `ℤ[X]`. Polynomial rings as universal arrows are the subject of the already-filed issue #309; this item adds the full adjunction and the induced monad on top of that (and the ring category of #257).

## Work to be done
- Build the category of commutative rings (`CRng`) and the forgetful functor to `Set` with its free-commutative-ring left adjoint (reusing the polynomial-ring universal arrow of #309, and the ring category of #257).
- Define the induced monad `T X = ℤ[X]` (`Adjunction_Induced_Monad`) and describe `ret`, `join` explicitly; discharge the `Monad` laws.
- Suggested module: `Monad/Instance/Polynomial.v` (donors: the ring category of #257, #309's construction, `Theory/Monad.v`, `Monad/Adjunction.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.4 Ex. 3; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the adjunction and the polynomial-ring monad.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/Polynomial.v` compiles after its dependencies.
- `Print Assumptions` on the monad shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.4 Ex. 3.

## Dependencies
Depends on: #257 (the category `Rng`/`CRng` of rings)
Depends on: #309 (polynomial rings as universal arrows — the free commutative ring)

<!-- catalog: {"ids":["maclane:VI.4:ex3"],"deps":["#257","#309"]} -->

---8<---

title: "MacLane VI.4: The tensor-algebra monad on Ab and rings as its algebras"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.4:ex4]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.4, Exercise 4 (book p. 146, PDF p. 155). Item: `maclane:VI.4:ex4`.

## Background
The forgetful functor `Rng → Ab` (forgetting ring multiplication) has a left adjoint whose induced monad `T` on abelian groups is the tensor-algebra monad — the analogue of the word monad `W` with `Xⁿ` replaced by the n-fold tensor power and `⨆` by the direct sum; its algebras are exactly the rings, and the comparison functor is an isomorphism. See nLab [tensor algebra](https://ncatlab.org/nlab/show/tensor+algebra) ("the free monoid object" from the tensor powers).

## Current state in the library
There is no concrete category `Ab` of abelian groups (the abstract `Structure/Abelian.v` is a class, not the category), no `Rng`, no tensor-algebra endofunctor `⨁ₙ A^{⊗n}`, and no `Rng → T-Alg` comparison. Tensor algebras as universal arrows are the subject of the already-filed issue #310; this item adds the monad on `Ab` and the ring-algebra characterization, over the categories `Ab` (#256) and `Rng` (#257).

## Work to be done
- On top of `Ab` (#256) and `Rng` (#257), build the tensor-algebra endofunctor `T A = ⨁_{n} A^{⊗n}` on `Ab`, its unit and multiplication (the analogue of the word monad), and discharge the `Monad` laws (reusing #310's tensor-algebra universal arrow).
- Prove the algebra characterization and the isomorphism/equivalence `EilenbergMoore T ≅ Rng`.
- Suggested module: `Monad/Instance/TensorAlgebra.v` (donors: the `Ab`/`Rng` instances of #256/#257, #310's construction, `Theory/Monad.v`, `Monad/Comparison.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.4 Ex. 4 (parts a and b); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the tensor-algebra monad and the `Rng ≅ EM` comparison.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Instance/TensorAlgebra.v` compiles after its dependencies.
- `Print Assumptions` on the monad and comparison shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.4 Ex. 4.

## Dependencies
Depends on: #256 (the category `Ab` of abelian groups)
Depends on: #257 (the category `Rng` of rings)
Depends on: #310 (tensor algebras as universal arrows)

<!-- catalog: {"ids":["maclane:VI.4:ex4"],"deps":["#256","#257","#310"]} -->

---8<---

title: "MacLane VI.5: The Kleisli comparison functor and the free-object subcategory"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.5:construction1, maclane:VI.5:thm2, maclane:VI.5:ex1, maclane:VI.5:ex2, maclane:VI.5:ex3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.5 (book pp. 147–148, PDF pp. 156–157). Items: `maclane:VI.5:construction1`, `maclane:VI.5:thm2`, `maclane:VI.5:ex1`, `maclane:VI.5:ex2`, `maclane:VI.5:ex3`.

## Background
For any adjunction `⟨F,G,ε⟩ : X ⇀ A` defining a monad `T`, there is a unique comparison functor `L : X_T → A` from the Kleisli category with `G ∘ L = G_T` and `L ∘ F_T = F`; its image is the full subcategory of `A` on the free objects `Fx`, so `L` restricts to an equivalence `X_T ≃ FX`, which need not be an isomorphism. Restricting an adjunction to any full subcategory containing all `Fx` yields an adjunction defining the same monad. See nLab [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category) (the Kleisli category as the free-algebra subcategory of Eilenberg–Moore).

## Current state in the library
The Kleisli category and its free/forgetful adjunction are fully present (`Monad/Kleisli.v:38`, `Monad/Kleisli/Adjunction.v`, `Kleisli_Monad_agrees`), but the comparison functor `L` is absent: the only functors out of `Kleisli` are `Kleisli_Forget` (to `X`), and the tree's sole comparison functor is `EM_Comparison : A → X^T` (`Monad/Comparison.v:186`) — the *opposite* direction. There is no functor `Kleisli → A` for an arbitrary resolution, no image-is-`FX` characterization, no `X_T ≃ FX` equivalence, and no restriction-of-an-adjunction-to-a-full-subcategory construction (`Construction/Subcategory.v` has the raw full-subcategory infrastructure but no such lemma). "`X_T` is the full subcategory of free algebras" occurs only as header prose in `Monad/Kleisli.v`.

## Work to be done
- Construct the restricted-adjunction lemma: given `F ⊣ U : X ⇀ A` and a full subcategory `B ⊆ A` with every `F x ∈ B`, produce `F_B ⊣ G_B : X ⇀ B` via the same hom-bijection, and show it defines the same monad (donor: `Construction/Subcategory.v`).
- Construct the Kleisli comparison `L : Kleisli → A` for an arbitrary resolution, with `U ∘ L ≈ Kleisli_Forget`-style laws and `L ∘ Kleisli_Free ≈ F`; prove uniqueness.
- Show the (essential) image of `L` is the full subcategory `FX` on the free objects, and that `L` restricts to an equivalence `X_T ≃ FX`; give the one-point-set (constant) monad counterexample showing this equivalence need not be an isomorphism (a monad whose left adjoint is not injective on objects).
- Suggested module: `Monad/Kleisli/Comparison.v` (donors: `Monad/Kleisli.v`, `Monad/Kleisli/Adjunction.v`, `Construction/Subcategory.v`, `Theory/Equivalence.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.5 (Thm. 2, Exs. 1–3, the restriction construction); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `L`, its uniqueness, the image characterization, and the `X_T ≃ FX` equivalence.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Kleisli/Comparison.v` compiles after its dependencies.
- `Print Assumptions` on `L` and the equivalence shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Thm. 2 and Exs. 1–3 against Mac Lane §VI.5.

## Dependencies
None as filed issues (self-contained over the in-tree Kleisli development and `Construction/Subcategory.v`).

<!-- catalog: {"ids":["maclane:VI.5:construction1","maclane:VI.5:thm2","maclane:VI.5:ex1","maclane:VI.5:ex2","maclane:VI.5:ex3"],"deps":[]} -->

---8<---

title: "MacLane VI.5: The category of resolutions of a monad — Kleisli initial, Eilenberg–Moore terminal"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.5:thm3, maclane:VI.5:ex4, maclane:VI.5:ex5]
deps_item_ids: [maclane:VI.5:thm2, maclane:VI.7:def1]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.5 (book p. 148, PDF p. 157). Items: `maclane:VI.5:thm3`, `maclane:VI.5:ex4`, `maclane:VI.5:ex5`.

## Background
For a fixed monad `T` on `X`, the adjunctions defining `T`, with maps of adjunctions that are the identity on `X`, form a category in which the Kleisli construction is **initial** and the Eilenberg–Moore construction is **terminal**, linked by the comparison functors `X_T →ᴸ A →ᴷ X^T`. See nLab [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category) and [Eilenberg-Moore category](https://ncatlab.org/nlab/show/Eilenberg-Moore+category).

## Current state in the library
The two extreme resolutions exist (`Kleisli_Monad_agrees`, `EM_Monad_agrees`) and the Eilenberg–Moore comparison `EM_Comparison` (`Monad/Comparison.v:186`) is present, but there is **no** category whose objects are the adjunctions defining a fixed monad: no arrow notion (a map of adjunctions identity on `X`), and no initiality/terminality theorem. The "Kleisli initial / Eilenberg–Moore terminal" claim appears only as prose in `Theory/Monad.v` and `Comonad/Duality.v`. `Instance/Adjoints.v` builds a different category (adjunctions-as-arrows-between-categories). No lemma relates the monad induced by a composite adjunction to its factors (Ex. 5).

## Work to be done
- Assemble the category `Res T` of resolutions of `T`: objects = adjunctions defining `T`; morphisms = comparisons of resolutions (the comparison-of-adjunctions definition from §VI.7, a separate issue in this chapter).
- Prove the Kleisli resolution is initial and the Eilenberg–Moore resolution is terminal in `Res T`, using the Kleisli comparison `L` (§VI.5, a separate issue in this chapter) and `EM_Comparison`.
- Discuss the size/foundational status of `Res T` (Ex. 4) in the library's universe-polymorphic setting, and prove Ex. 5: composing a resolution `X ⇀ B` with a second adjunction `B ⇀ A` that defines the identity monad on `B` yields a composite `X ⇀ A` defining the same `T` (donor: `Adjunction/Compose.v`).
- Suggested module: `Monad/Resolution.v` (donors: `Monad/Kleisli/Adjunction.v`, `Monad/Eilenberg/Moore/Adjunction.v`, `Monad/Comparison.v`, `Adjunction/Compose.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.5 (Thm. 3, Exs. 4–5); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `Res T`, the initiality of Kleisli, and the terminality of Eilenberg–Moore.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Resolution.v` compiles after its dependencies.
- `Print Assumptions` on the initial/terminal objects shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Thm. 3 and Exs. 4–5 against Mac Lane §VI.5.

## Dependencies
Depends on: maclane:VI.5:thm2 (the Kleisli comparison functor `L`)
Depends on: maclane:VI.7:def1 (comparison of adjunctions — the morphism notion for the resolution category)

<!-- catalog: {"ids":["maclane:VI.5:thm3","maclane:VI.5:ex4","maclane:VI.5:ex5"],"deps":["maclane:VI.5:thm2","maclane:VI.7:def1"]} -->

---8<---

title: "MacLane VI.6: The absolute-coequalizer (absolute-colimit) predicate"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.6:def2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.6 (book p. 149, PDF p. 158). Item: `maclane:VI.6:def2`.

## Background
An arrow `e` is an **absolute coequalizer** of a parallel pair when every functor `T` sends the coequalizer fork to a coequalizer; absolute colimits (Paré) are defined analogously, and split coequalizers are the archetypal example. See nLab [absolute colimit](https://ncatlab.org/nlab/show/absolute+colimit) and [split coequalizer](https://ncatlab.org/nlab/show/split+coequalizer).

## Current state in the library
The defining `∀`-functor-preservation content is *proven* but only for split coequalizers: `functor_preserves_split` and `split_coequalizer_preserved` (`Structure/Coequalizer/Split.v:104`, `:132`) show, for an arbitrary functor `F`, that the image of a split fork is again a (split) coequalizer. But there is no first-class predicate `AbsoluteCoequalizer e` (nor `AbsoluteColimit`): `grep` for `Definition/Record/Class Absolute*` returns 0 hits, and "absolute (co)limit" appears only in header essays (`Structure/Coequalizer/Split.v`, `Construction/Karoubi.v:67`). One cannot state "`e` is an absolute coequalizer" anywhere in the tree, so Beck's condition (ii) cannot be phrased.

## Work to be done
- Define `AbsoluteCoequalizer f g q e := ∀ (D : Category)(T : C ⟶ D), IsCoequalizer (fmap T f)(fmap T g)(T q)(fmap T e)` (and optionally a general `AbsoluteColimit`).
- Prove `AbsoluteCoequalizer ⇒ IsCoequalizer` (take `T = Id`), and that every `SplitCoequalizer` yields an `AbsoluteCoequalizer` (re-expressing `split_coequalizer_preserved`).
- Suggested module: `Structure/Coequalizer/Absolute.v` (donors: `Structure/Coequalizer.v`, `Structure/Coequalizer/Split.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.6 (paraphrased above); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `AbsoluteCoequalizer`, `AbsoluteCoequalizer ⇒ IsCoequalizer`, and `SplitCoequalizer ⇒ AbsoluteCoequalizer`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Structure/Coequalizer/Absolute.v` compiles after its dependencies.
- `Print Assumptions` on the predicate and its two lemmas shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the definition against Mac Lane §VI.6.

## Dependencies
None (extends the in-tree split-coequalizer development).

<!-- catalog: {"ids":["maclane:VI.6:def2"],"deps":[]} -->

---8<---

title: "MacLane VI.6: The dom/cod fork in Cat and its splitting by a terminal object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.6:remark1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.6 (book p. 150, PDF p. 159). Item: `maclane:VI.6:remark1`.

## Background
In `Cat`, for any category `C` the diagram `C² ⇒ C → 1` (the arrow category, the domain and codomain functors, and the unique functor to the terminal category) is a fork; when `C` has a terminal object the fork is split. See nLab [split coequalizer](https://ncatlab.org/nlab/show/split+coequalizer).

## Current state in the library
No `SplitCoequalizer` is instantiated in `Cat`. The ingredients exist — the arrow category `Arrow {C} := (Id[C] ↓ Id[C])` (`Construction/Arrow.v:110`) with its `dom`/`cod` comma projections, and `Cat_Terminal` with `one[C] : C ⟶ 1` (`Instance/One.v:54`) — but no construction assembles `(dom, cod : C⃗ ⇉ C)`, the fork to `1`, or the split-when-`C`-has-a-terminal-object claim. (The `fork` hits in `Instance/Cat/Cartesian.v` are the product pairing `⟨F,G⟩`, a different notion.)

## Work to be done
- Assemble the parallel pair `dom, cod : Arrow C ⇉ C` and the fork `Arrow C ⇉ C → 1` in `Cat`.
- Given a terminal object `a₀` of `C`, build the sections `s` (sending `1`'s object to `a₀`) and `t` (sending each object `c` to the unique arrow `c → a₀`) and verify the four split-fork laws, yielding a `SplitCoequalizer`.
- Suggested module: `Instance/Cat/SplitFork.v` (donors: `Construction/Arrow.v`, `Instance/One.v`, `Instance/Cat.v`, `Structure/Coequalizer/Split.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.6 (paraphrased above); all equations/functor identities use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the fork and its splitting.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Cat/SplitFork.v` compiles after its dependencies.
- `Print Assumptions` on the split fork shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the construction against Mac Lane §VI.6.

## Dependencies
None (self-contained over `Construction/Arrow.v`, `Instance/One.v`, and the split-coequalizer development).

<!-- catalog: {"ids":["maclane:VI.6:remark1"],"deps":[]} -->

---8<---

title: "MacLane VI.6: Algebraic quotients as coequalizers split under the forgetful functor (groups and rings)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.6:remark2, maclane:VI.6:ex1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.6 (book p. 150, PDF p. 159): the worked example `maclane:VI.6:remark2` and Exercise 1 `maclane:VI.6:ex1`.

## Background
For a normal subgroup `N ◁ G`, the projection `G → G/N` is the coequalizer in `Grp` of a parallel pair `G ⋉ N ⇉ G` built from the semidirect product; the fork is generally not split in `Grp` but becomes split after applying the forgetful functor to `Set` (via a coset-representative section). The same pattern exhibits a quotient ring `R/A` (by an ideal `A`) as a coequalizer in `Rng` split under `Rng → Set`. See Wikipedia [Quotient group](https://en.wikipedia.org/wiki/Quotient_group) and [Quotient ring](https://en.wikipedia.org/wiki/Quotient_ring).

## Current state in the library
There is no category `Grp` of groups-and-homomorphisms and no category `Rng` of rings (`Structure/Group.v` is about group *objects*; the only algebraic-structure category among `Instance/` is `CMon`). No normal-subgroup / semidirect-product / ideal / quotient machinery exists, and no proof that an algebraic quotient projection is a coequalizer that becomes split under the forgetful functor to `Set`. These categories are the subjects of the already-filed issues #255 (`Grp`) and #257 (`Rng`); quotient groups by universality are the subject of #313. The split-coequalizer API this needs is in-tree (`Structure/Coequalizer/Split.v`).

## Work to be done
- On top of `Grp` (#255) and quotient groups (#313): build the parallel pair `G ⋉ N ⇉ G` (`d₀(x,n) = x`, `d₁(x,n) = x n`), show the projection `p : G → G/N` is its coequalizer in `Grp`, and exhibit a `SplitCoequalizer` for the image pair under `U : Grp → Set` via a coset-representative section.
- Repeat for rings (#257): exhibit `R/A` as the coequalizer of the analogous pair in `Rng`, split under `Rng → Set` (Ex. 1).
- Suggested modules: `Instance/Grp/Coequalizer.v`, `Instance/Rng/Coequalizer.v` (donors: the `Grp`/`Rng` instances of #255/#257, `Structure/Coequalizer.v`, `Structure/Coequalizer/Split.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.6 (the group example and Ex. 1 for rings); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the coequalizer claims and the split-under-forgetful witnesses.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/Grp/Coequalizer.v` and `Instance/Rng/Coequalizer.v` compile after their dependencies.
- `Print Assumptions` on the coequalizer/split-fork results shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks both examples against Mac Lane §VI.6.

## Dependencies
Depends on: #255 (the category `Grp` of groups)
Depends on: #257 (the category `Rng` of rings)
Depends on: #313 (quotient groups and the isomorphism theorems by universality)

<!-- catalog: {"ids":["maclane:VI.6:remark2","maclane:VI.6:ex1"],"deps":["#255","#257","#313"]} -->

---8<---

title: "MacLane VI.6: Contractible (Beck) parallel pairs"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.6:ex2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.6, Exercise 2 (book p. 150, PDF p. 159). Item: `maclane:VI.6:ex2`.

## Background
A parallel pair `∂₀, ∂₁ : a ⇉ b` is **contractible** (Beck) when there is an arrow `t : b → a` with `∂₀ ∘ t = 1_b` and `∂₁ ∘ t ∘ ∂₀ = ∂₁ ∘ t ∘ ∂₁` — an equational condition on the pair alone, not presupposing any coequalizer or splitting. The exercise asks to prove (a) the pair `∂₀, ∂₁` of any split fork is contractible, and (b) if a contractible pair has a coequalizer, that coequalizer is split. See nLab [split coequalizer](https://ncatlab.org/nlab/show/split+coequalizer) (contractible/split pairs).

## Current state in the library
There is no standalone contractible-pair definition. "Contractible" occurs in-tree only for terminal-hom/`poly_unit` contractibility, never for a parallel pair. The contraction data of a split fork lives inside `SplitCoequalizer` (`Structure/Coequalizer/Split.v`: `scoeq_t`, `scoeq_law3`, `scoeq_law4`) but is never extracted as "the underlying pair is contractible"; the `U`-split-pair device in `Monad/Monadicity/Beck.v` is a different (`U`-image) notion, and `ReflexivePair` (`Structure/Coequalizer/Reflexive.v`) is a genuinely different concept (a common section splitting both legs). Part (b) has no in-tree counterpart.

## Work to be done
- Define a `ContractiblePair f g` over a parallel pair `f, g : a ⇉ b` with contraction `t : b → a` and the two Beck equations `f ∘ t ≈ id[b]` and `g ∘ t ∘ f ≈ g ∘ t ∘ g` (recovered from the source page: `∂₀t = 1`, `∂₁t∂₀ = ∂₁t∂₁`; the earlier scan misread `d₁∘t = d₀∘d₁` is non-composable and should be ignored).
- Prove (a): the underlying pair of any `SplitCoequalizer` is a `ContractiblePair` (extract `scoeq_t` and the relevant laws).
- Prove (b): a `ContractiblePair` that admits an `IsCoequalizer` admits a `SplitCoequalizer` on the same coequalizing arrow.
- Suggested module: `Structure/Coequalizer/Contractible.v` (donors: `Structure/Coequalizer.v`, `Structure/Coequalizer/Split.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.6 Ex. 2 (contraction equations `∂₀t = 1`, `∂₁t∂₀ = ∂₁t∂₁`); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `ContractiblePair` and parts (a), (b).
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Structure/Coequalizer/Contractible.v` compiles after its dependencies.
- `Print Assumptions` on the definition and both parts shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the definition and parts (a)/(b) against Mac Lane §VI.6 Ex. 2 (contraction equations `∂₀t = 1`, `∂₁t∂₀ = ∂₁t∂₁`).

## Dependencies
None (extends the in-tree split-coequalizer development).

<!-- catalog: {"ids":["maclane:VI.6:ex2"],"deps":[]} -->

---8<---

title: "MacLane VI.7: Reflection of coequalizers — definition, and from creation or from preservation+conservativity"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.7:def2, maclane:VI.7:ex1, maclane:VI.7:ex3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7 (book p. 154, PDF p. 163) and Exercises 1, 3 (book pp. 154–155, PDF pp. 163–164). Items: `maclane:VI.7:def2`, `maclane:VI.7:ex1`, `maclane:VI.7:ex3`.

## Background
A functor **reflects colimits** of a diagram when a cone whose image is colimiting is already colimiting; specializations are "reflects coequalizers" and "reflects isomorphisms" (conservative). Two entailments: creation of coequalizers implies their reflection (Ex. 1), and — when the domain has coequalizers, the functor preserves them, and it is conservative — the functor reflects coequalizers (Ex. 3). See nLab [conservative functor](https://ncatlab.org/nlab/show/conservative+functor) and [created limit](https://ncatlab.org/nlab/show/created+limit).

## Current state in the library
Only the isomorphism specialization is first-class: `ReflectsIsos` (`Structure/Limit/Preservation.v:243`). "Reflects colimits/coequalizers" exists only as the unfolded conclusion of theorems about full+faithful (`ff_reflects_limit`, `Theory/Equivalence/Limit.v:401`) or equivalence (`equivalence_reflects_colimits`, `:568`) functors — there is no standalone predicate over an arbitrary functor and no "reflects coequalizers" specialization at all. Correspondingly, creation-of-coequalizers-implies-reflection is not a general theorem (the tree only has `creates_split_reflects_isos`, reflection of *isos* from `U`-split creation, and a reflection clause baked into `CreatesUSplitCoequalizers`), and the Ex. 3 lemma (preserves + conservative ⇒ reflects coequalizers) is absent.

## Work to be done
- Define general predicates `ReflectsColimits F` / `ReflectsCoequalizers F` over an arbitrary functor (donor pattern: `ReflectsIsos`, `Structure/Limit/Preservation.v`).
- Prove Ex. 1: a functor that creates coequalizers reflects them (relate to the general "creates coequalizers" notion; where the tree has only `CreatesUSplitCoequalizers`, state the general creation and derive reflection).
- Prove Ex. 3: if the domain has coequalizers, `F` preserves them, and `F` is conservative (`ReflectsIsos`), then `F` reflects coequalizers.
- Suggested module: `Structure/Limit/Reflection.v` (donors: `Structure/Limit/Preservation.v`, `Structure/Coequalizer.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 Def. (reflects colimits) and Exs. 1, 3; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the reflection predicates and both entailment lemmas.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Structure/Limit/Reflection.v` compiles after its dependencies.
- `Print Assumptions` on the predicates and lemmas shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the definition and Exs. 1, 3 against Mac Lane §VI.7.

## Dependencies
None (extends the in-tree preservation/reflection vocabulary).

<!-- catalog: {"ids":["maclane:VI.7:def2","maclane:VI.7:ex1","maclane:VI.7:ex3"],"deps":[]} -->

---8<---

title: "MacLane VI.7: Comparison of adjunctions defining the same monad (definition and uniqueness)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.7:def1, maclane:VI.7:lem1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7 (book pp. 153–154, PDF pp. 162–163). Items: `maclane:VI.7:def1`, `maclane:VI.7:lem1`.

## Background
Given two adjunctions `⟨F,G,η,ε⟩ : X ⇀ A` and `⟨F',G',η',ε'⟩ : X ⇀ A'` inducing the same monad, a **comparison** of `F'` to `F` is a functor `M : A' → A` with `M ∘ F' = F` and `G ∘ M = G'`; such an `M` is a map of adjunctions and satisfies `M ∘ ε' = ε ∘ M`. When `G` creates coequalizers of pairs with a split coequalizer under `G`, the comparison into that resolution exists and is unique. See nLab [monadic adjunction](https://ncatlab.org/nlab/show/monadic+adjunction).

## Current state in the library
There is no general "comparison of two adjunctions defining the same monad": searches for morphism/map/comparison of adjunctions and "resolution" turn up only concrete resolutions and the specific Eilenberg–Moore comparison `EM_Comparison` (`Monad/Comparison.v:186`), which does carry the two structural laws (`EM_Comparison_Free` = `M ∘ F' = F`, `EM_Comparison_Forget` = `G ∘ M = G'`) but only for `A' = X^T`, and not the compatibility `M ∘ ε' = ε ∘ M`. The uniqueness content is realized only via `Beck_Inverse` (`Monad/Monadicity/Beck.v:443`) as a full *quasi-inverse* of `K` built under `CreatesUSplitCoequalizers`, not as "the unique comparison `M`" over an arbitrary resolution with a uniqueness clause.

## Work to be done
- Define `Comparison` of two resolutions of a monad: a functor `M : A' → A` with `M ∘ F' ≈ F`, `G ∘ M ≈ G'`; prove the derived `M ∘ ε' ≈ ε ∘ M` (reusing the general maps-of-adjunctions machinery of #393, of which this comparison is the identity-on-`X` specialization).
- Prove the existence-and-uniqueness lemma: when `G` creates `U`-split coequalizers (Beck hypothesis (iii), in-tree `CreatesUSplitCoequalizers`), for any other resolution there is a unique comparison `M`; specialize to the Eilenberg–Moore resolution to recover the §VI.3 comparison (`EM_Comparison`).
- Suggested module: `Monad/Comparison/Resolution.v` (donors: `Monad/Comparison.v`, `Monad/Monadicity/Beck.v`, `Monad/Adjunction.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 (Def. of comparison, the comparison lemma); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `Comparison`, the compatibility law, and the existence/uniqueness lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Comparison/Resolution.v` compiles after its dependencies.
- `Print Assumptions` on the definition and lemma shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the definition and lemma against Mac Lane §VI.7.

## Dependencies
Depends on: #393 (maps of adjunctions — the general notion of which a comparison of resolutions is the identity-on-`X` specialization, supplying the derived `M ∘ ε' ≈ ε ∘ M`). Otherwise uses the in-tree Beck engine (`CreatesUSplitCoequalizers`/`Beck_Inverse`) and `EM_Comparison`.

<!-- catalog: {"ids":["maclane:VI.7:def1","maclane:VI.7:lem1"],"deps":["#393"]} -->

---8<---

title: "MacLane VI.7: The graded weak and precise tripleability construction (left adjoint to K, unit/counit isos, algebra presentation)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.7:ex2, maclane:VI.7:ex4, maclane:VI.7:ex5]
deps_item_ids: [maclane:VI.7:def2]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7, Exercises 2, 4, 5 (book pp. 154–155, PDF pp. 163–164). Items: `maclane:VI.7:ex4`, `maclane:VI.7:ex2`, `maclane:VI.7:ex5`.

## Background
The Weak (Ex. 2) and Precise (Ex. 5) Tripleability constructions build the left adjoint `L` to the comparison functor `K` incrementally: (a) `K` has a left adjoint when `A` has the relevant coequalizers; (b) the unit `I ≅ K L` is an iso when `G` preserves them; (c) the counit `L K ≅ I` is an iso when `G` reflects them — over all coequalizers (WTT) or over pairs split under `G` (PTT). The tool is the canonical presentation of a `T`-algebra as a coequalizer of free algebras (Ex. 4). See nLab [monadicity theorem](https://ncatlab.org/nlab/show/monadicity+theorem).

## Current state in the library
The full equivalence exists (`beck_monadicity`, `Monad/Monadicity/Beck.v:739`, built over exactly Ex. 5's set of `U`-split pairs, with `beck_U_coeq` the preserved coequalizer and `beck_equivalence_unit`/`_counit` the (co)unit isos), but it **bundles** existence+preservation+reflection into the single `CreatesUSplitCoequalizers` hypothesis rather than isolating (a) "`K` has a left adjoint from coequalizers alone", (b) "unit iso from preservation", (c) "counit iso from reflection" under incrementally-added hypotheses. For Ex. 4, part (b) is present verbatim (`beck_is_coeq`/`crude_is_coeq`: `M(x,h)` **is** the coequalizer `FGFx ⇉ Fx → M(x,h)`), while part (a) — the `X^T`-level coequalizer of free algebras `⟨T²x,μ⟩ ⇉ ⟨Tx,μ⟩ → ⟨x,h⟩` — is present only downstairs as the split fork `canonical_split` (`Monad/Monadicity/BeckObjects.v:75`). The WTT over *all* coequalizers is not developed.

## Work to be done
- Ex. 4: state and prove the canonical presentation of a `T`-algebra at the `X^T` level (every algebra is the coequalizer of the free-algebra pair `⟨T²x,μ_{Tx}⟩ ⇉ ⟨Tx,μ_x⟩ → ⟨x,h⟩`), applying the in-tree `created_is_coequalizer` machinery.
- Ex. 2 (WTT): construct `K`'s left adjoint `L` from the assumption that `A` has all coequalizers; show the unit is iso when `G` preserves all coequalizers; show the counit is iso when `G` reflects all coequalizers (using the reflects-coequalizers predicate from §VI.7, a separate issue in this chapter).
- Ex. 5 (PTT): the same three graded steps over the set of pairs whose `U`-image has a split coequalizer, re-factoring `beck_monadicity` so each step is a named intermediate.
- Suggested modules: `Monad/Monadicity/Weak.v`, `Monad/Monadicity/Precise.v` (donors: `Monad/Monadicity/Beck.v`, `Monad/Monadicity/BeckObjects.v`, `Monad/Comparison.v`, the §VI.7 reflects-coequalizers predicate).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 Exs. 2, 4, 5 (the graded (a)/(b)/(c) construction and the algebra presentation); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for `K`'s left adjoint, the graded unit/counit isos, and the `X^T`-level algebra presentation.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Monadicity/Weak.v` and `Monad/Monadicity/Precise.v` compile after their dependencies.
- `Print Assumptions` on the graded results shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Exs. 2, 4, 5 against Mac Lane §VI.7.

## Dependencies
Depends on: maclane:VI.7:def2 (the reflects-coequalizers predicate, used for the counit-iso step)

<!-- catalog: {"ids":["maclane:VI.7:ex2","maclane:VI.7:ex4","maclane:VI.7:ex5"],"deps":["maclane:VI.7:def2"]} -->

---8<---

title: "MacLane VI.7: Complete Beck's monadicity theorem (isomorphism conclusion, absolute-coequalizer condition, general converse)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.7:thm1, maclane:VI.7:ex6]
deps_item_ids: [maclane:VI.6:def2, maclane:VI.7:ex5]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7, Theorem 1 (book pp. 151–154, PDF pp. 160–163) and Exercise 6 (book p. 155, PDF p. 164). Items: `maclane:VI.7:thm1`, `maclane:VI.7:ex6`.

## Background
Beck's theorem: for an adjunction inducing a monad `T`, the comparison `K : A → X^T` is an isomorphism (Thm. 1) iff `G` creates coequalizers of exactly the pairs whose image has an **absolute** coequalizer, iff the same with **split** coequalizers; the equivalence-conclusion variant (Ex. 6) replaces "isomorphism" with "equivalence". See nLab [monadicity theorem](https://ncatlab.org/nlab/show/monadicity+theorem) and Wikipedia [Beck's monadicity theorem](https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem).

## Current state in the library
The deep forward direction is fully in-tree as `beck_monadicity` (`Monad/Monadicity/Beck.v:739`): `CreatesUSplitCoequalizers U ⇒ EquivalenceOfCategories (EM_Comparison A)` — which is precisely Ex. 6's equivalence conclusion (`Monadic` is defined this way, `Monad/Comparison.v:273`). Three gaps remain versus the full biconditional (Beck.v header discloses them): (a) the conclusion is `EquivalenceOfCategories`, not Mac Lane Thm. 1's on-the-nose isomorphism of categories; (b) the necessity direction is proved only for the Eilenberg–Moore forgetful `U^T` (`monadic_creates`, `:911`), not transported to a general monadic `U`; (c) the **absolute**-coequalizer condition (ii) is not stated or shown equivalent to the split-coequalizer condition (iii) — only `SplitCoequalizer` exists (with split ⇒ absolute via `split_coequalizer_preserved`), while the absolute-coequalizer predicate itself is being added by the §VI.6 absolute-coequalizer issue.

## Work to be done
- Add condition (ii): using the §VI.6 absolute-coequalizer predicate, state the Beck hypothesis over pairs whose `U`-image has an *absolute* coequalizer and prove (ii) ⟺ (iii) (split ⇒ absolute is present; absolute ⇒ the required creation/preservation over that class).
- Transport the necessity direction from `U^T` to a general monadic `U`: monadic `U` ⇒ `U` creates `U`-split coequalizers (closing the biconditional `Monadic U ⟺ CreatesUSplitCoequalizers U`), using the graded precise-tripleability construction of §VI.7 Ex. 5.
- Optionally strengthen the conclusion to a strict isomorphism of categories where the setoid discipline allows, or explicitly document why the equivalence conclusion is the faithful (non-evil) rendering of Thm. 1.
- Suggested modules: extend `Monad/Monadicity/Beck.v`; new `Monad/Monadicity/Absolute.v` (donors: `Structure/Coequalizer/Absolute.v` from the §VI.6 absolute-coequalizer issue, `Monad/Monadicity/BeckObjects.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 Thm. 1 and Ex. 6 (all three equivalent conditions; iso vs equivalence documented); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the (ii)⟺(iii) equivalence and the general converse `Monadic U ⟺ CreatesUSplitCoequalizers U`.
- [ ] New/extended file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (Beck's theorem is flagship-level).

## Verification
- `coqc -R . Category Monad/Monadicity/Beck.v` (and `Monad/Monadicity/Absolute.v`) compile after their dependencies.
- `Print Assumptions` on the closed biconditional and the (ii)⟺(iii) equivalence shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the completed statement against Mac Lane §VI.7 Thm. 1 and Ex. 6.

## Dependencies
Depends on: maclane:VI.6:def2 (the absolute-coequalizer predicate — needed for condition (ii))
Depends on: maclane:VI.7:ex5 (the graded precise-tripleability construction — used to transport the converse to a general monadic U)

<!-- catalog: {"ids":["maclane:VI.7:thm1","maclane:VI.7:ex6"],"deps":["maclane:VI.6:def2","maclane:VI.7:ex5"]} -->

---8<---

title: "MacLane VI.7: The CTT/VTT/PTT tripleability predicates and their monadicity theorems"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.7:def3, maclane:VI.7:ex7, maclane:VI.7:ex8]
deps_item_ids: [maclane:VI.7:def2, maclane:VI.7:thm1]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7 (book p. 155, PDF p. 164): the tripleability-property definitions (`maclane:VI.7:def3`) and Exercises 7, 8 (`maclane:VI.7:ex7`, `maclane:VI.7:ex8`).

## Background
For `G : A → X`, let `C_G` (resp. `S_G`) be the parallel pairs whose image has a coequalizer (resp. split coequalizer). `G` is **CTT** (crude tripleable), **VTT** (vulgar), or **PTT** (precise) according to which preservation/reflection/existence conditions it satisfies over `C_G` or `S_G`; both CTT and VTT imply PTT, and each implies the comparison `K` is an equivalence (Exs. 7, 8). See nLab [monadic functor](https://ncatlab.org/nlab/show/monadic+functor).

## Current state in the library
None of the three predicates is defined, and the index sets `C_G`/`S_G` are not introduced; "vulgar"/`VTT`/`CTT`/`PTT` have **0 hits** in the tree. What exists is the *content* of two sufficient-condition monadicity theorems under different hypothesis packagings: `beck_monadicity` (`Monad/Monadicity/Beck.v:739`, essentially PTT via `CreatesUSplitCoequalizers`) and `crude_monadicity` (`Monad/Monadicity/Crude.v:601`, an equivalence from reflexive coequalizers + `PreservesReflexiveCoequalizers` + `ReflectsIsos` — the Barr–Wells crude form, not Mac Lane's `C_G`-quantified CTT). VTT (reflect — but not necessarily preserve — coequalizers of split-under-`G` pairs, with `A` having those split coequalizers) has no counterpart at all.

## Work to be done
- Define the index sets `C_G`, `S_G` and the three predicates `CTT`, `VTT`, `PTT G` per Mac Lane Def. VI.7.3 (has-left-adjoint + the stated preserve/reflect/existence conditions over `C_G`/`S_G`), using the §VI.7 reflects-coequalizers predicate.
- Prove `CTT ⇒ PTT`, `VTT ⇒ PTT`.
- Prove Ex. 7 (CTT ⇒ `K` an equivalence) and Ex. 8 (VTT ⇒ `K` an equivalence), routing through the completed Beck theorem (the §VI.7 Theorem 1 issue) / `beck_monadicity`; reconcile the crude form (`crude_monadicity`) with the `C_G`-quantified CTT.
- Suggested module: `Monad/Monadicity/Tripleability.v` (donors: `Monad/Monadicity/Beck.v`, `Monad/Monadicity/Crude.v`, `Structure/Coequalizer/Split.v`, the §VI.7 reflects-coequalizers predicate).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 Def. VI.7.3 and Exs. 7, 8; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the three predicates and the CTT/VTT ⇒ equivalence theorems.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Monadicity/Tripleability.v` compiles after its dependencies.
- `Print Assumptions` on the predicates and theorems shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the predicates and Exs. 7, 8 against Mac Lane §VI.7.

## Dependencies
Depends on: maclane:VI.7:def2 (the reflects-coequalizers predicate, in the predicate definitions)
Depends on: maclane:VI.7:thm1 (the completed Beck theorem, routing the CTT/VTT ⇒ equivalence proofs)

<!-- catalog: {"ids":["maclane:VI.7:def3","maclane:VI.7:ex7","maclane:VI.7:ex8"],"deps":["maclane:VI.7:def2","maclane:VI.7:thm1"]} -->

---8<---

title: "MacLane VI.7: Tripleability is closed under composition (CTT/VTT/PTT composites)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.7:ex9, maclane:VI.7:ex10, maclane:VI.7:ex11]
deps_item_ids: [maclane:VI.7:def3]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.7, Exercises 9, 10, 11 (book p. 155, PDF p. 164). Items: `maclane:VI.7:ex9`, `maclane:VI.7:ex10`, `maclane:VI.7:ex11`.

## Background
The tripleability properties are stable under composition: the composite of a CTT, a PTT, and a VTT functor is PTT (Ex. 9); the composite of two VTT functors is VTT (Ex. 10); the composite of two CTT functors is CTT (Ex. 11). See nLab [monadic functor](https://ncatlab.org/nlab/show/monadic+functor).

## Current state in the library
There is no composite-tripleability theorem: the CTT/VTT/PTT vocabulary is undefined (0 hits), and `grep` for composition + monadic/tripleable returns nothing. `Adjunction/Compose.v` composes adjunctions (`Adjunction_Compose : (F' ◯ F) ⊣ (U ◯ U')`) but proves nothing about the composite being monadic or tripleable. The crude/precise theorems (`crude_monadicity`, `beck_monadicity`) are not shown closed under composition.

## Work to be done
- On top of the CTT/VTT/PTT predicates (the §VI.7 tripleability-predicates issue), prove: `CTT G₁`, `PTT G₂`, `VTT G₃` ⇒ `PTT (G₃ ∘ G₂ ∘ G₁)` (Ex. 9); `VTT`∘`VTT` is `VTT` (Ex. 10); `CTT`∘`CTT` is `CTT` (Ex. 11).
- Use `Adjunction_Compose` for the composite left adjoint, and reason about the images of the pair-index sets `C_G`/`S_G` under composition.
- Suggested module: `Monad/Monadicity/Composite.v` (donors: `Adjunction/Compose.v`, the §VI.7 CTT/VTT/PTT predicates).

## Definition of Done
- [ ] Statements match Mac Lane §VI.7 Exs. 9, 10, 11; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the three composition-closure theorems.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Monad/Monadicity/Composite.v` compiles after its dependencies.
- `Print Assumptions` on the three theorems shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Exs. 9, 10, 11 against Mac Lane §VI.7.

## Dependencies
Depends on: maclane:VI.7:def3 (the CTT/VTT/PTT tripleability predicates)

<!-- catalog: {"ids":["maclane:VI.7:ex9","maclane:VI.7:ex10","maclane:VI.7:ex11"],"deps":["maclane:VI.7:def3"]} -->

---8<---

title: "MacLane VI.8: Algebras of a variety are T-algebras (equational categories are monadic over Set)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.8:thm1, maclane:VI.8:ex1]
deps_item_ids: [maclane:VI.7:thm1, maclane:VI.6:def2]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.8, Theorem 1 (book p. 156, PDF p. 165) and Exercise 1 (book p. 157, PDF p. 166). Items: `maclane:VI.8:thm1`, `maclane:VI.8:ex1`.

## Background
For a set `Ω` of operators and a set `E` of identities, the forgetful functor `⟨Ω,E⟩-Alg → Set` is monadic: the comparison functor `K : ⟨Ω,E⟩-Alg → Set^T` is an isomorphism of categories, proved via Beck's theorem (`G` creates coequalizers of pairs whose underlying maps have an absolute coequalizer `e`, transporting each n-ary operation along `eⁿ`); Exercise 1 reproves it through split coequalizers with the explicit coset-product operation transport. See nLab [variety of algebras](https://ncatlab.org/nlab/show/variety+of+algebras) (algebras monadic over Set) and [monadicity theorem](https://ncatlab.org/nlab/show/monadicity+theorem).

## Current state in the library
No in-tree theorem states that a variety's forgetful functor to `Set` is monadic. The closest is `Lawvere_crude_monadicity` (`Theory/Lawvere/Monad.v:91`), which (a) yields only an *equivalence*, not an isomorphism; (b) is hypothesis-scoped — the free-model left adjoint `L ⊣ ev1 T` and the crude hypotheses are all assumed as data; (c) works with Lawvere-theory models over setoids, not `⟨Ω,E⟩` signature presentations. The syntactic variety category `Algs` (`Instance/Comp.v:268`, over `Type`) exists but is entirely disconnected from any monad, `Set^T`, or comparison functor (its free-object universal property is a comment, not a formalized adjunction). Beck's theorem is being completed by the §VI.7 Theorem 1 issue in this chapter, and the variety category / free-algebra adjunction are the already-filed issues #440, #441.

## Work to be done
- Connect the variety category `Algs` (`Instance/Comp.v`, #440) and its free-algebra adjunction (#441) to the induced monad `T` on `Set`, and construct the comparison functor into `Set^T`.
- Prove `⟨Ω,E⟩-Alg → Set` is monadic by the completed Beck theorem (§VI.7, a separate issue in this chapter), using the §VI.6 absolute-coequalizer condition: `G` creates coequalizers of absolute-under-`G` pairs, with each operation transported along `eⁿ`.
- Prove Exercise 1: the same result through split coequalizers, defining each operation on the quotient from a splitting `⟨s,t⟩` by `ω_X(x₁,…,xₙ) = e · ω_B(s x₁,…,s xₙ)`.
- Suggested module: `Instance/Comp/Monadicity.v` (donors: `Instance/Comp.v`, #440/#441, `Monad/Monadicity/Beck.v`, `Structure/Coequalizer/Absolute.v`, `Structure/Coequalizer/Split.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.8 Thm. 1 and Ex. 1 (comparison an isomorphism; both proof routes); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the variety-monadicity theorem and the comparison isomorphism.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (variety monadicity is flagship-level).

## Verification
- `coqc -R . Category Instance/Comp/Monadicity.v` compiles after its dependencies.
- `Print Assumptions` on the monadicity theorem shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Thm. 1 and Ex. 1 against Mac Lane §VI.8.

## Dependencies
Depends on: maclane:VI.7:thm1 (the completed Beck monadicity theorem)
Depends on: maclane:VI.6:def2 (the absolute-coequalizer predicate — for the Theorem 1 proof route)
Depends on: #440 (the category of algebras of a variety)
Depends on: #441 (the free-algebra adjunction for a variety)

<!-- catalog: {"ids":["maclane:VI.8:thm1","maclane:VI.8:ex1"],"deps":["maclane:VI.7:thm1","maclane:VI.6:def2","#440","#441"]} -->

---8<---

title: "MacLane VI.8: Beck's theorem for K-Alg over K-Mod"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VI.8:ex2]
deps_item_ids: [maclane:VI.7:thm1]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.8, Exercise 2 (book p. 157, PDF p. 166). Item: `maclane:VI.8:ex2`.

## Background
For a commutative ring `K`, the forgetful functor from associative `K`-algebras to `K`-modules is monadic — Beck's theorem applies to `K-Alg → K-Mod` (the tensor-algebra monad on `K-Mod`). See nLab [associative algebra](https://ncatlab.org/nlab/show/associative+algebra) and [monadicity theorem](https://ncatlab.org/nlab/show/monadicity+theorem).

## Current state in the library
The categories the exercise is about — `K-Mod` and `K-Alg` for a commutative ring `K`, and the forgetful functor between them — are not defined anywhere (`Instance/` has only `CMon` among algebraic-structure categories). Beck's theorem exists in general form (`beck_monadicity`, `crude_monadicity`), and is being completed by the §VI.7 Theorem 1 issue in this chapter, but the specific `K-Alg → K-Mod` instance and its objects have no in-tree counterpart. Module categories are the already-filed issue #258.

## Work to be done
- Build (or reuse, on top of #258) the category `K-Mod` of modules over a commutative ring `K` and the category `K-Alg` of associative `K`-algebras, with the forgetful functor `K-Alg → K-Mod` and its free (tensor-algebra) left adjoint.
- Verify Beck's theorem applies (via the completed §VI.7 Beck theorem, a separate issue in this chapter): the forgetful functor creates the relevant coequalizers, so `K-Alg` is monadic over `K-Mod`.
- Suggested module: `Instance/KAlg/Monadicity.v` (donors: the module categories of #258, `Monad/Monadicity/Beck.v`).

## Definition of Done
- [ ] Statement matches Mac Lane §VI.8 Ex. 2; all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the `K-Alg → K-Mod` monadicity result.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if flagship-level.

## Verification
- `coqc -R . Category Instance/KAlg/Monadicity.v` compiles after its dependencies.
- `Print Assumptions` on the monadicity result shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks the statement against Mac Lane §VI.8 Ex. 2.

## Dependencies
Depends on: maclane:VI.7:thm1 (the completed Beck monadicity theorem)
Depends on: #258 (module categories, generalized to `K-Mod`)

<!-- catalog: {"ids":["maclane:VI.8:ex2"],"deps":["maclane:VI.7:thm1","#258"]} -->

---8<---

title: "MacLane VI.9: Compact Hausdorff spaces are monadic over Set (the ultrafilter monad)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VI.9:thm1, maclane:VI.9:def1, maclane:VI.9:lem1, maclane:VI.9:ex1]
deps_item_ids: [maclane:VI.7:thm1, maclane:VI.6:def2]
deps_pending: []

## Source
Mac Lane, *CWM*, 2nd ed., §VI.9, Theorem 1 with its supporting closure-space setup and lemma, and Exercise 1 (book pp. 157–159, PDF pp. 166–168). Items: `maclane:VI.9:thm1`, `maclane:VI.9:def1`, `maclane:VI.9:lem1`, `maclane:VI.9:ex1`.

## Background
The forgetful functor from compact Hausdorff spaces to `Set` is monadic (Manes): its left adjoint is the Stone–Čech compactification of a discrete set, and by Beck's theorem `G` creates coequalizers of pairs whose underlying maps have an absolute coequalizer; the proof regards a space as a Kuratowski closure space, uses that a continuous map from a compact to a Hausdorff space is closed, and shows the constructed coequalizer carries the quotient topology (Ex. 1). See nLab [ultrafilter monad](https://ncatlab.org/nlab/show/ultrafilter+monad) (its Eilenberg–Moore category is compact Hausdorff spaces), [compact Hausdorff space](https://ncatlab.org/nlab/show/compact+Hausdorff+space), and [Stone-Čech compactification](https://ncatlab.org/nlab/show/Stone-Cech+compactification).

## Current state in the library
Entirely absent: there is no category `Top`, no compact Hausdorff spaces, no Kuratowski closure space, no continuous/closed-map notion on subsets of a fixed set, and no Stone–Čech compactification. Every compact/Hausdorff/ultrafilter/Stone–Čech hit in the tree is background-essay prose (`Theory/Monad.v:65-66`, `Theory/Kan/Extension.v`, etc.); "continuous" in code always means the limit-preserving-functor sense. The topological substrate is the subject of the already-filed issues #259 (`Top`), #413 (compact Hausdorff and creation of limits), and #455 (Stone–Čech via the adjoint functor theorems). Beck's theorem is being completed by the §VI.7 Theorem 1 issue in this chapter and the absolute-coequalizer predicate by the §VI.6 issue.

## Work to be done
- On the topological substrate (#259/#413), define the closure-space (Kuratowski) presentation of a space, continuous and closed maps, and prove that a continuous map from a compact space to a Hausdorff space is closed.
- Using the Stone–Čech left adjoint (#455) to `CompHaus → Set`, prove monadicity by the completed Beck theorem (§VI.7, a separate issue in this chapter) with the §VI.6 absolute-coequalizer condition: `G` creates coequalizers of absolute-under-`G` pairs, transporting the closure operation along the coequalizer.
- Prove Exercise 1: the topology on the coequalizer object `W` is the quotient (final) topology along `e : Y → W`.
- Suggested module: `Instance/CompHaus/Monadicity.v` (donors: the `Top`/`CompHaus` and Stone–Čech instances of #259/#413/#455, `Monad/Monadicity/Beck.v`, `Structure/Coequalizer/Absolute.v`).

## Definition of Done
- [ ] Statements match Mac Lane §VI.9 (Thm. 1, the closure-space setup, the lemma, Ex. 1); all equations use setoid `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`.
- [ ] `Print Assumptions` clean for the monadicity theorem, the closed-map lemma, and the quotient-topology result.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 (nix targets).
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (compact-Hausdorff monadicity is flagship-level).

## Verification
- `coqc -R . Category Instance/CompHaus/Monadicity.v` compiles after its dependencies.
- `Print Assumptions` on the monadicity theorem and lemma shows no axioms.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` pass.
- Reviewer checks Thm. 1, the lemma, and Ex. 1 against Mac Lane §VI.9.

## Dependencies
Depends on: maclane:VI.7:thm1 (the completed Beck monadicity theorem)
Depends on: maclane:VI.6:def2 (the absolute-coequalizer predicate)
Depends on: #259 (the category `Top` of topological spaces)
Depends on: #413 (compact Hausdorff spaces and the creation of limits)
Depends on: #455 (the Stone–Čech compactification via the adjoint functor theorems)

<!-- catalog: {"ids":["maclane:VI.9:thm1","maclane:VI.9:def1","maclane:VI.9:lem1","maclane:VI.9:ex1"],"deps":["maclane:VI.7:thm1","maclane:VI.6:def2","#259","#413","#455"]} -->

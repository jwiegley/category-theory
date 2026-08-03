---
title: "MacLane XI.1: The braiding as a natural isomorphism, unit compatibility, and the inverse braiding"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.1:def2, maclane:XI.1:remark1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.1 (book pp. 252–253, PDF pp. 259–260). Items `maclane:XI.1:def2` (the braiding for a monoidal category) and `maclane:XI.1:remark1` (the pointwise-inverse family is again a braiding).

## Background

A braiding on a monoidal category is a natural *isomorphism* `γ_{a,b} : a ⊗ b ≅ b ⊗ a` satisfying the two hexagon identities and the unit-compatibility law `λ ∘ γ_{a,e} = ρ`; it is not required to square to the identity (that is the symmetric case). Mac Lane's accompanying remark observes that the pointwise inverse `γ⁻¹` is again a braiding, the first hexagon for `γ` being equivalent to the second for `γ⁻¹`. See the nLab, [braided monoidal category](https://ncatlab.org/nlab/show/braided+monoidal+category).

## Current state in the library

Partial. `Structure/Monoidal/Braided.v:128` defines `Class BraidedMonoidal`, but its `braid` field at `Structure/Monoidal/Braided.v:132` is typed `x ⨂ y ~> y ⨂ x` — a bare morphism, **not** an isomorphism `≅` — and the class carries `braid_natural` and both hexagons but no invertibility field and no unit-compatibility field. Invertibility is genuinely extra: the candidate inverse `braid_{y,x}` is a two-sided inverse only under the symmetry law, so it is not derivable from the two hexagons alone. The unit-compatibility equation `λ ∘ γ_{a,e} = ρ` is derived in-tree only as `braid_unit_left` at `Structure/Monoidal/Braided/Proofs.v:529`, which sits inside `Section BraidedUnitors` under a `SymmetricMonoidal` hypothesis (`Context` at `Structure/Monoidal/Braided/Proofs.v:506`), so it is unavailable for a general (non-symmetric) braided category. The reverse/inverse-braiding remark has no in-tree counterpart: the only cousin, `Braided_op` at `Construction/Opposite/Monoidal.v:148`, builds a braiding on the *opposite* category `C^op` out of `braid_{y,x}` (not the inverse family `γ⁻¹`) with the two hexagons exchanging roles — a different construction on a different category.

## Work to be done

- Upgrade the braiding of `BraidedMonoidal` (§XI.1) to a genuine natural isomorphism: either re-type the `braid` field as `x ⨂ y ≅ y ⨂ x`, or keep the bare morphism and add a field/derived lemma exhibiting a two-sided inverse, so that consumers may invert `γ`.
- Add the unit-compatibility law `λ ∘ γ_{a,e} ≈ ρ` as a field of, or a theorem for, a general braided monoidal category (Joyal–Street Prop. 2.1), lifting the current symmetric-only `braid_unit_left` to the braided setting.
- Prove Mac Lane's remark: the pointwise-inverse family `γ⁻¹` is again a braiding on the same category (the first hexagon for `γ` is equivalent to the second hexagon for `γ⁻¹`, and dually), yielding a `BraidedMonoidal` instance built from `γ⁻¹`.
- Suggested modules: edit `Structure/Monoidal/Braided.v` (the class and the invertibility/unit fields) and `Structure/Monoidal/Braided/Proofs.v` (the general unit-compatibility lemma and the inverse-braiding instance). In-tree donors: the existing hexagons and `braid_natural` in `Structure/Monoidal/Braided.v`, the symmetric-only `braid_unit_left` in `Structure/Monoidal/Braided/Proofs.v` as the template to generalize, and `Construction/Opposite/Monoidal.v:148` (`Braided_op`) as a structural reference for hexagon bookkeeping.

## Definition of Done

- [ ] The braiding of `BraidedMonoidal` is available as a natural isomorphism (field or derived two-sided inverse), and downstream users can form `γ⁻¹`.
- [ ] Unit compatibility `λ ∘ γ_{a,e} ≈ ρ` holds for a general braided (not merely symmetric) monoidal category.
- [ ] The inverse-braiding result: `γ⁻¹` is a braiding on the same category (a `BraidedMonoidal` instance from the inverse family).
- [ ] The misleading source comment on the `braid` field at `Structure/Monoidal/Braided.v:132` (which labels it `≅` though its type is a bare morphism) is corrected to match whatever the field ends up being.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the invertibility, unit-compatibility, and inverse-braiding results.
- [ ] Edited/new files remain registered in `_CoqProject`; downstream files that consume `BraidedMonoidal` still build.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Structure/Monoidal/Braided/Proofs.v` (and the whole tree, since the class changes) compiles cleanly.
- `Print Assumptions braid_unit_left.` (now general) and `Print Assumptions` on the inverse-braiding instance show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the braiding is a natural isomorphism, `λ ∘ γ_{a,e} ≈ ρ` holds without a symmetry hypothesis, and `γ⁻¹` is a braiding; statements match Mac Lane §XI.1 (braiding definition and the inverse-braiding remark).

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XI.1:def2","maclane:XI.1:remark1"],"deps":[]} -->

---8<---

---
title: "MacLane XI.2: Monoidal natural transformations compose, and the category of monoidal functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.2:remark2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.2 (book p. 256, PDF p. 263). Item `maclane:XI.2:remark2` (the evident composite of two monoidal natural transformations is again monoidal; closure under vertical composition, hence a category of monoidal functors).

## Background

Monoidal natural transformations between monoidal functors are closed under vertical composition, and with the identity transformation this makes monoidal functors `M ⟶ M'` into a category. See the nLab, [monoidal natural transformation](https://ncatlab.org/nlab/show/monoidal+natural+transformation).

## Current state in the library

Absent. `Natural/Transformation/Monoidal.v:31` defines `Class LaxMonoidal_Transform` (the two coherence squares over an underlying `N : F ⟹ G`), but the file provides no identity instance, no vertical-composition instance, and no category of monoidal functors built from it; a whole-tree search finds `LaxMonoidal_Transform` used only at its definition and in three places inside `Natural/Transformation/Applicative.v`. By contrast, closure under composition for monoidal *functors* is fully proved (`Functor/Structure/Monoidal/Compose.v:59` for the strong case and `Functor/Structure/Monoidal/Compose.v:291` for the lax case), so the analogous closure for monoidal *natural transformations* is the missing companion.

## Work to be done

- Prove that the identity natural transformation is a monoidal natural transformation, and that the vertical composite of two monoidal natural transformations is again one (both coherence squares compose).
- Assemble the category whose objects are (lax, and separately strong) monoidal functors `M ⟶ M'` and whose morphisms are monoidal natural transformations, with vertical composition and identities.
- Suggested modules: `Natural/Transformation/Monoidal.v` (identity and vertical-composition instances for `LaxMonoidal_Transform`) and a new `Functor/Structure/Monoidal/Category.v` (the category of monoidal functors). In-tree donors: `Natural/Transformation/Monoidal.v:31` (`LaxMonoidal_Transform`), `Functor/Structure/Monoidal/Compose.v` (the functor-level composition already proved), `Instance/Fun.v` (the ordinary functor category as the structural template).

## Definition of Done

- [ ] Identity and vertical-composition instances for `LaxMonoidal_Transform` proved (both the unit and tensor coherence squares).
- [ ] A category of monoidal functors `M ⟶ M'` (lax and strong variants) assembled with monoidal natural transformations as morphisms.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the composition instances and the category.
- [ ] New/edited files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Functor/Structure/Monoidal/Category.v` compiles cleanly.
- `Print Assumptions` on the vertical-composition instance and the category of monoidal functors shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: composition of monoidal natural transformations preserves both coherence squares, and the assembled category has the expected identities/associativity; statement matches Mac Lane §XI.2.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XI.2:remark2"],"deps":[]} -->

---8<---

---
title: "MacLane XI.2: The word-indexed comparison transformation F_v of a monoidal functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.2:construction1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.2 (book pp. 256–257, PDF pp. 263–264). Item `maclane:XI.2:construction1` (the natural transformation `F_v` attached to a monoidal functor and a tensor word `v`).

## Background

For a monoidal functor `F` and each `⊗`-word `v` in `n` letters there is a comparison natural transformation `F_v : v(F a₁,…,F aₙ) → F(v(a₁,…,aₙ))`, defined by induction on `v` with `F_□ = F₂`, `F_e = F₀`, and `F_{v ⊗ v'} = F₂ ∘ (F_v ⊗ F_{v'})`; it makes all the resulting coherence diagrams commute and generalizes the binary/nullary monoidal-functor axioms. See the nLab, [monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor).

## Current state in the library

Absent. The monoidal functor at `Functor/Structure/Monoidal.v:110` (`LaxMonoidalFunctor`) exposes only the binary comparison `lax_ap` (`F₂`), the nullary `lax_pure` (`F₀`), and a few fixed low-arity derived isos (`pure_left`/`pure_right`/`ap_assoc`); there is no inductive family `F_v` indexed by `⊗`-words with `F_□ = F₂`, `F_e = F₀`, `F_{v ⊗ v'} = F₂ ∘ (F_v ⊗ F_{v'})`, and none of the two generalized coherence squares (against a word-comparison `η : v ⇒ w` built from `α, λ, ρ`, and against a monoidal natural transformation `θ`). The object-level `⊗`-word fold machinery `tensor_list`/`tfold` (`Theory/Multicategory/Representable.v:55,67`) is never lifted to a monoidal-functor comparison.

## Work to be done

- Reusing the inductive type of `⊗`-words from the free-monoidal-category development (issue #496), define the family `F_v` for a monoidal functor `F` by induction on words, with `F_□ = F₂`, `F_e = F₀`, `F_{v ⊗ v'} = F₂ ∘ (F_v ⊗ F_{v'})`.
- Prove the two coherence squares: (i) for a word-comparison `η : v ⇒ w` assembled from the associator/unitors, the square relating `F_v`, `F_w`, `η` commutes; (ii) for a monoidal natural transformation `θ : F ⇒ G`, the square relating `F_v`, `G_v`, `θ` commutes — recovering the binary monoidal-functor and monoidal-transformation axioms as the length-2 / length-1 cases.
- Suggested module: `Functor/Structure/Monoidal/Word.v`. In-tree donors: `Functor/Structure/Monoidal.v` (`LaxMonoidalFunctor`, `lax_ap`, `lax_pure`), the `⊗`-word datatype from #496 (`Construction/FreeMonoidal.v`), `Natural/Transformation/Monoidal.v` (`LaxMonoidal_Transform` for square (ii)).

## Definition of Done

- [ ] The inductive family `F_v` defined for a (lax) monoidal functor and every `⊗`-word, with the three base/step equations.
- [ ] Coherence square (i) against a word-comparison `η` built from `α, λ, ρ`.
- [ ] Coherence square (ii) against a monoidal natural transformation `θ`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `F_v` and both coherence squares.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Functor/Structure/Monoidal/Word.v` compiles cleanly.
- `Print Assumptions F_word.` (or the chosen name) and the two coherence lemmas show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `F_v` is the inductive word-indexed comparison with `F_□ = F₂`, `F_e = F₀`, `F_{v ⊗ v'} = F₂ ∘ (F_v ⊗ F_{v'})`, and both coherence squares hold; statement matches Mac Lane §XI.2.

## Dependencies

Depends on: #496

<!-- catalog: {"ids":["maclane:XI.2:construction1"],"deps":["#496"]} -->

---8<---

---
title: "MacLane XI.3: Strictification — every monoidal category is monoidally equivalent to a strict one"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.3:thm1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.3 Theorem 1 (book pp. 257–259, PDF pp. 264–266). Item `maclane:XI.3:thm1`.

## Background

Every monoidal category `M` is monoidally equivalent to a strict monoidal category `S` via strong monoidal functors both ways; in Mac Lane's proof `S` is the free monoid on the objects of `M` (finite strings under concatenation, empty string the unit, structure isos identities), `F : S ⟶ M` sends a string to the front-associated tensor of its entries and `G : M ⟶ S` sends an object to its singleton string, with `F ∘ G = id` and `G ∘ F ≅ id`. See the nLab, [coherence theorem for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent. A whole-tree search for `strictif` / "equivalent to a strict" / "free monoid on ... objects" turns up only header essays (`Structure/Monoidal.v:71` states the fact in prose) and unrelated hits (the pseudo-double-category and skeleton strictifications, and the strict-2-category `StrictCat`). The strict-monoidal class `Structure/Monoidal/Strict.v:52` (`StrictMonoidal`) exists but is instantiated only for PROP-family carriers, never obtained from an arbitrary monoidal category; there is no `S` built as the free monoid on the objects of `M`, and no strong monoidal `F : S ⟶ M`, `G : M ⟶ S` exhibiting an equivalence. (Note: the §VII.1 no-go issue #495 formalizes only that naive strictification-by-identifying-isomorphic-objects fails; the positive strictification theorem is a different, complementary result.)

## Work to be done

- Construct `S` as the free monoid (finite strings) on the objects of `M`, with concatenation tensor, empty-string unit, and identity structure isomorphisms — a `StrictMonoidal` instance.
- Define `F : S ⟶ M` sending a string to the front-associated (left-parenthesized) tensor of its entries, and `G : M ⟶ S` sending an object to its singleton string; equip both with strong monoidal structure.
- Prove `F ∘ G = id_M` and `G ∘ F ≅ id_S`, and conclude a monoidal equivalence `M ≃ S`.
- Suggested module: `Structure/Monoidal/Strictify.v` (kept distinct from the §VII.1 no-go module of #495). In-tree donors: `Structure/Monoidal/Strict.v` (`StrictMonoidal`), `Functor/Structure/Monoidal.v` (`MonoidalFunctor`, strong comparisons), `Theory/Multicategory/Representable.v:55,67` (`tensor_list`/`tfold`, the front-associated fold of a list of objects), `Theory/Equivalence.v` and `Theory/Equivalence/Monoidal.v` (monoidal equivalence infrastructure).

## Definition of Done

- [ ] `S` built as the free monoid on the objects of `M` and shown `StrictMonoidal`.
- [ ] Strong monoidal `F : S ⟶ M` and `G : M ⟶ S` defined, with `F ∘ G = id` and `G ∘ F ≅ id`.
- [ ] The monoidal equivalence `M ≃ S` concluded (via the library's monoidal-equivalence vocabulary).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the strictification equivalence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Structure/Monoidal/Strictify.v` compiles cleanly.
- `Print Assumptions monoidal_strictification.` (the equivalence) shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `S` is strict, `F`/`G` are strong monoidal with `F ∘ G = id` and `G ∘ F ≅ id`, giving a monoidal equivalence; statement matches Mac Lane §XI.3 Theorem 1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XI.3:thm1"],"deps":[]} -->

---8<---

---
title: "MacLane XI.3: The endofunctor category [C,C] as a strict monoidal category (Exercise 1)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:XI.3:ex1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.3 Exercise 1 (book p. 260, PDF p. 267). Item `maclane:XI.3:ex1`.

## Background

For any category `C`, the endofunctor category `[C,C]` with composition of endofunctors as tensor and the identity functor as unit is a *strict* monoidal category. See the nLab, [strict monoidal category](https://ncatlab.org/nlab/show/strict+monoidal+category).

## Current state in the library

Partial. `Structure/Monoidal/Compose.v:42` provides `Compose_Monoidal : @Monoidal ([C, C])` with functor composition as tensor and the identity functor as unit, and it is genuinely used (e.g. `Monad/Monoid.v:41`, `Monoid_Monad`, characterizing monads as monoids in `[C,C]`). But it is registered only as a general `@Monoidal`, not as `@StrictMonoidal`: the file header (`Structure/Monoidal/Compose.v:35–40`) explicitly notes the structure "is strict in the literature" yet is "presented as a general (non-strict) Monoidal instance". No `StrictMonoidal` instance for `[C,C]` exists (that class is instantiated only for PROP carriers), so the exercise's actual content — strictness — is not formalized.

## Work to be done

- Establish the `StrictMonoidal` instance for `[C,C]` over `Compose_Monoidal`: the object-level (Leibniz) equalities `(F ◯ G) ◯ H = F ◯ (G ◯ H)`, `Id ◯ F = F`, `F ◯ Id = F` on the *functor* objects of `[C,C]`, together with the structural isos equal to the transported identities.
- Note the central obstacle: strictness here is object-level equality of composite *functors* (records), which in this setoid library is the same subtlety already navigated by `StrictMonoidalFunctor` (`Functor/Structure/Monoidal/Strict.v:54`); the composite functors agree definitionally on objects (`F(G(H x))`), so discharge the record-level equalities either definitionally or with the tree's existing axiom-free technique for object-level functor equality, without introducing `funext`/UIP axioms.
- Suggested module: `Structure/Monoidal/Compose.v` (add the `StrictMonoidal` instance beside `Compose_Monoidal`). In-tree donors: `Structure/Monoidal/Strict.v` (`StrictMonoidal`, the target class), `Functor/Structure/Monoidal/Strict.v:54` (`StrictMonoidalFunctor`, the object-equality pattern), `Theory/Functor.v` (functor composition and its unit/associativity).

## Definition of Done

- [ ] `StrictMonoidal ([C,C])` instance over `Compose_Monoidal`, with the three object-level equalities and the transported-identity structural-iso fields.
- [ ] The object-level functor equalities are discharged without new axioms (no `funext`/UIP beyond what docs/AXIOMS.md already scopes), or the honest obstruction is documented if a base equality is genuinely unavailable.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for the strict instance.
- [ ] Edited file remains registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Structure/Monoidal/Compose.v` compiles cleanly.
- `Print Assumptions` on the `StrictMonoidal ([C,C])` instance shows closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: the instance is `StrictMonoidal` (not merely `Monoidal`), with composition tensor and identity-functor unit; statement matches Mac Lane §XI.3 Exercise 1.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:XI.3:ex1"],"deps":[]} -->

---8<---

---
title: "MacLane XI.3: The tensoring functor T : M ⟶ [M,M] and an independent strictification proof (Exercises 2–3)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:XI.3:ex2, maclane:XI.3:ex3]
deps_item_ids: [maclane:XI.3:ex1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.3 Exercises 2 and 3 (book p. 260, PDF p. 267). Items `maclane:XI.3:ex2` (the strong monoidal functor `T : M ⟶ M^M`) and `maclane:XI.3:ex3` (an independent proof of strictification via `T`).

## Background

The self-action / regular representation of a monoidal category `M` sends `a` to the endofunctor `a ⊗ −`; with tensor comparison given by the associator and unit comparison by the inverse left unitor, this is a strong monoidal functor `T : M ⟶ [M,M]` into the strict monoidal endofunctor category. Its image can be used to prove strictification independently of the coherence theorem, which then yields coherence back via strictification. See the nLab, [actegory](https://ncatlab.org/nlab/show/actegory) and [coherence theorem for monoidal categories](https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories).

## Current state in the library

Absent. There is no functor `M ⟶ [M,M]` built from the tensor: a search for a tensoring/left-regular functor `a ↦ a ⊗ −` yields nothing, and the only `C ⟶ [D,E]` functors in-tree (`Functor/Diagonal.v`, `Functor/Hom.v`) are unrelated. `Construction/Cayley.v` is the *Hom*-based Yoneda/Cayley embedding `C ⟶ [C,Sets]`, not the tensor-based `T` with `T₂ = α`, `T₀ = λ⁻¹`, and it carries no monoidal-functor structure. In-tree "strong" (`Functor/Strong.v`, tensorial strength) is a different notion, not a strong (pseudo) monoidal functor. Consequently the Exercise-3 route — an independent strictification via the closure of `T`'s image — is absent as well (no strictification exists by any route; see the §XI.3 strictification issue).

## Work to be done

- Define `T : M ⟶ [M,M]` with `T(a) = a ⊗ −`, tensor comparison `T₂(a,b)` the associator `α_{a,b,−}` (componentwise), and unit comparison `(T₀)_a = λ⁻¹`; prove it is a strong monoidal functor, checking that its monoidal-functor axioms reduce to the monoidal-category axioms of `M` (as Mac Lane indicates).
- Using the strict monoidal structure on `[M,M]` (§XI.3 Exercise 1) and the functor `T`, give a proof that `M` is monoidally equivalent to a strict monoidal category that does not invoke the coherence theorem — realizing `M` inside the strict `[M,M]` via `T` and closing up its image.
- Suggested modules: `Functor/Structure/Monoidal/Tensoring.v` (the functor `T`) and `Structure/Monoidal/Strictify/ViaEndofunctors.v` (the independent strictification). In-tree donors: the strict `[M,M]` from §XI.3 Exercise 1 (`Structure/Monoidal/Compose.v`), `Functor/Structure/Monoidal.v` (`MonoidalFunctor`), `Structure/Monoidal.v` (the associator/unitor equations `T` must reduce to), `Construction/Cayley.v` (the Hom-based embedding as a structural reference). This provides an alternative route to the main strictification result of §XI.3.

## Definition of Done

- [ ] `T : M ⟶ [M,M]` defined with `T(a) = a ⊗ −`, `T₂ = α`, `T₀ = λ⁻¹`, and proved a strong monoidal functor.
- [ ] The reduction of `T`'s monoidal-functor axioms to the monoidal-category axioms of `M` is exhibited.
- [ ] An independent (coherence-free) proof that `M` is monoidally equivalent to a strict monoidal category, using the strict `[M,M]` and `T`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context for `T` and the independent strictification.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Functor/Structure/Monoidal/Tensoring.v Structure/Monoidal/Strictify/ViaEndofunctors.v` compiles cleanly.
- `Print Assumptions T_tensoring.` and `Print Assumptions strictification_via_endofunctors.` show closed under the global context.
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `T` is strong monoidal with `T₂ = α`, `T₀ = λ⁻¹`; the strictification proof uses `T` and the strictness of `[M,M]` and does not depend on the coherence theorem; statements match Mac Lane §XI.3 Exercises 2–3.

## Dependencies

Depends on: maclane:XI.3:ex1

<!-- catalog: {"ids":["maclane:XI.3:ex2","maclane:XI.3:ex3"],"deps":["maclane:XI.3:ex1"]} -->

---8<---

---
title: "MacLane XI.4: The Artin braid group B_n"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.4:def1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.4 (book pp. 260–261, PDF pp. 267–268). Item `maclane:XI.4:def1` (the braid group `B_n`).

## Background

The Artin braid group `B_n` is presented by generators `σ₁,…,σ_{n-1}` with the braid relations `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}` and `σ_i σ_j = σ_j σ_i` for `|i−j| ≠ 1`; equivalently it is the fundamental group of the configuration space of `n` distinct points in the plane, with `B_1` trivial and `B_2 ≅ ℤ`. See the nLab, [braid group](https://ncatlab.org/nlab/show/braid+group), and Wikipedia, [Braid group](https://en.wikipedia.org/wiki/Braid_group).

## Current state in the library

Absent. A braid-group sweep (`artin` / `braid group` / `B_n` / `σ_i` / configuration space / fundamental group) finds only prose citations inside the `Structure/Monoidal/Braided.v` background essay; there is no group named `B_n` and no braid-on-`n`-strings type. Crucially there is no group-by-generators-and-relations machinery anywhere: `Structure/Group.v:109` defines the internal `GroupObject` in a cartesian monoidal category (Eckmann–Hilton), not a concrete discrete group presented by generators and relations, and no free group / presented group is built. The only "braid" in-tree is the categorical braiding morphism of a `BraidedMonoidal` category (`Structure/Monoidal/Braided.v:132`), a structure, not the discrete group.

## Work to be done

- Building on the free-group construction of issue #298, present `B_n` as the free group on generators `σ₁,…,σ_{n-1}` modulo the normal closure of the braid relations, using the tree's congruence-quotient machinery.
- Provide the group structure (multiplication, unit, inverses) and the defining relations as lemmas; record the special cases `B_1` trivial and `B_2 ≅ ℤ`.
- Suggested module: `Construction/BraidGroup.v` (axiom-free, following the free-monoid / free-PROP precedent) or `Instance/BraidGroup.v` if stdlib support is needed. In-tree donors: the free groups of #298, `Construction/Quotient.v` (hom-congruence / relation quotients), `Construction/PROP/Presentation.v` (generators-and-relations presentation as a design reference), `Construction/Free/Quiver.v` (free-structure pattern). The presentation machinery built here is reused by the `B_n ⟶ S_n` surjection and the braid category of §XI.4.

## Definition of Done

- [ ] `B_n` constructed as a group presented by `σ₁,…,σ_{n-1}` and the braid relations.
- [ ] Group laws proved; the braid relations hold; `B_1` trivial and `B_2 ≅ ℤ` recorded.
- [ ] All equations use setoid `≈` where the carrier is a setoid; never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (or, for an `Instance/`-layer placement, only the stdlib axioms enumerated in docs/AXIOMS.md).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level foundational construction).

## Verification

- `coqc -R . Category Construction/BraidGroup.v` compiles cleanly.
- `Print Assumptions BraidGroup.` shows closed under the global context (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `B_n` is the group presented by `σ_i` with the two braid relations, with `B_1`/`B_2` special cases; statement matches Mac Lane §XI.4.

## Dependencies

Depends on: #298

<!-- catalog: {"ids":["maclane:XI.4:def1"],"deps":["#298"]} -->

---8<---

---
title: "MacLane XI.4: The surjection B_n ⟶ S_n and the symmetric group by transpositions"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.4:construction1]
deps_item_ids: [maclane:XI.4:def1]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.4 (book pp. 261–262, PDF pp. 268–269). Item `maclane:XI.4:construction1` (the surjective homomorphism `B_n ⟶ S_n` and the presentation of `S_n` by transpositions).

## Background

Sending each braid to the permutation it induces on its endpoints is a surjective group homomorphism `B_n ⟶ S_n` (`σ_i ↦ (i, i+1)`); it is exactly the quotient adjoining `σ_i² = 1`, and `S_n` is presented by transpositions `τ_i` with `τ_i² = 1`, the braid relation, and commutativity for non-adjacent indices. See Wikipedia, [Symmetric group](https://en.wikipedia.org/wiki/Symmetric_group), and the nLab, [symmetric group](https://ncatlab.org/nlab/show/symmetric+group).

## Current state in the library

Absent. There is no symmetric group `S_n` as a group: the only permutation machinery is the `Type`-valued `tperm` witness in `Theory/Multicategory.v:242`, whose header explicitly disallows descent to the symmetric group (there is deliberately no `S_n` quotient), and stdlib `Sorting.Permutation` is imported only to bridge witnesses, not as a group. Consequently there is no homomorphism `B_n ⟶ S_n` and no presentation of `S_n` by transpositions. The braid group `B_n` itself is the subject of the §XI.4 braid-group issue.

## Work to be done

- Reusing the presentation machinery established for the braid group (§XI.4), build `S_n` as the group presented by transpositions `τ₁,…,τ_{n-1}` with relations `τ_i² = 1`, the braid relation, and commutativity for `|i−j| ≠ 1`.
- Define the group homomorphism `B_n ⟶ S_n` by `σ_i ↦ τ_i`, prove it is well-defined (the braid relations map to relations that hold in `S_n`) and surjective, and identify it as the quotient adjoining `σ_i² = 1`.
- Suggested modules: `Construction/SymmetricGroup.v` (or `Instance/SymmetricGroup.v`) and the homomorphism beside the braid group in `Construction/BraidGroup.v`. In-tree donors: the braid-group presentation of §XI.4 (same generators-and-relations technique), `Construction/Quotient.v`, `Construction/PROP/Presentation.v` (presentation reference).

## Definition of Done

- [ ] `S_n` constructed as the group presented by transpositions with the stated relations.
- [ ] The surjective homomorphism `B_n ⟶ S_n` (`σ_i ↦ τ_i`) defined, proved well-defined and surjective, and identified as the `σ_i² = 1` quotient.
- [ ] All equations use setoid `≈` where the carrier is a setoid; never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (or, for an `Instance/`-layer placement, only the stdlib axioms enumerated in docs/AXIOMS.md).
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated if the result rises to flagship level.

## Verification

- `coqc -R . Category Construction/SymmetricGroup.v` compiles cleanly.
- `Print Assumptions Bn_to_Sn.` shows closed under the global context (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `S_n` is presented by transpositions, and `B_n ⟶ S_n` is the surjective `σ_i ↦ τ_i` quotient adjoining `σ_i² = 1`; statement matches Mac Lane §XI.4.

## Dependencies

Depends on: maclane:XI.4:def1

<!-- catalog: {"ids":["maclane:XI.4:construction1"],"deps":["maclane:XI.4:def1"]} -->

---8<---

---
title: "MacLane XI.4: The braid category B as a braided (non-symmetric) monoidal category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.4:construction2, maclane:XI.4:construction3]
deps_item_ids: [maclane:XI.4:def1, maclane:XI.1:def2]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.4 (book pp. 262–263, PDF pp. 269–270). Items `maclane:XI.4:construction2` (the braid category `B`) and `maclane:XI.4:construction3` (the braiding `γ_{m,n}` making `B` braided but not symmetric).

## Background

The braid groups assemble into a strict monoidal category `B`: objects are the natural numbers, `hom(n,n) = B_n`, no arrows between distinct objects, tensor `+` on objects with side-by-side juxtaposition of braids. The block-crossing family `γ_{m,n} : m + n ⟶ n + m` is a braiding satisfying both hexagons, but it is **not** a symmetry — `γ² = 1` fails — so `B` is a concrete braided monoidal category that is not symmetric. See the nLab, [braided monoidal category](https://ncatlab.org/nlab/show/braided+monoidal+category).

## Current state in the library

Absent. There is no braid category: no category with objects `ℕ` and `hom(n,n) = B_n` exists. The closest in-tree object is the free PROP `FreeCat S` (`Construction/PROP/*`), which has objects `ℕ` under `+` and a strict monoidal structure but is **symmetric** — `Construction/PROP/Symmetric.v` proves `free_braid_invol` (`σ ∘ σ = id`), so its `hom(n,n)` are permutations (`S_n`), not braids (`B_n`); `Construction/PROP/Braided.v:76` (`FreeBraided`) equips it with a braiding that is nonetheless a symmetry. The abstract class `BraidedMonoidal` (`Structure/Monoidal/Braided.v:128`) has no `braid_invol` field, so braided need not be symmetric, but there is **no concrete braided-not-symmetric instance** realizing the braid-category braiding (`Structure/Monoidal/Drinfeld.v` builds `Drinfeld_Braided` from any monoidal category — a general centre construction, not `B`).

## Work to be done

- Construct the braid category `B`: objects `ℕ`, `hom(n,n) = B_n` (with no arrows between distinct objects), identities and composition from the braid groups of §XI.4; give it the strict monoidal structure with tensor `+` on objects and juxtaposition of braids, unit the object `0`.
- Define the braiding `γ_{m,n} : m + n ⟶ n + m` (the block of `m` strings crossing over the block of `n`), prove it is natural in `m, n` and satisfies both hexagon identities, and instantiate `BraidedMonoidal B` (using the braiding-as-isomorphism upgrade of §XI.1).
- Prove `γ² ≠ 1` (`B` is not symmetric), giving the first in-tree concrete braided monoidal category that is genuinely not symmetric.
- Suggested module: `Instance/BraidCategory.v`. In-tree donors: the braid group `B_n` of §XI.4, `Structure/Monoidal/Braided.v` (`BraidedMonoidal`), `Structure/Monoidal/Strict.v` (`StrictMonoidal`), `Construction/PROP/*` (the symmetric analogue as a structural reference). This braided category is the carrier for the §XI.5 freeness and coherence theorems.

## Definition of Done

- [ ] `B : Category` with objects `ℕ`, `hom(n,n) = B_n`, no cross-object arrows; strict monoidal under `+` and braid juxtaposition.
- [ ] The braiding `γ_{m,n}` defined, natural, satisfying both hexagons; `BraidedMonoidal B` instantiated.
- [ ] `γ² ≠ 1` proved (`B` is braided but not symmetric).
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (or, for an `Instance/`-layer placement, only the stdlib axioms enumerated in docs/AXIOMS.md).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level: first concrete braided-not-symmetric category).

## Verification

- `coqc -R . Category Instance/BraidCategory.v` compiles cleanly.
- `Print Assumptions BraidCategory.` and `Print Assumptions BraidCategory_Braided.` show closed under the global context (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: `B` has objects `ℕ` and `hom(n,n) = B_n`, is strict monoidal under `+`, `γ_{m,n}` is a braiding, and `γ² ≠ 1`; statement matches Mac Lane §XI.4.

## Dependencies

Depends on: maclane:XI.4:def1
Depends on: maclane:XI.1:def2

<!-- catalog: {"ids":["maclane:XI.4:construction2","maclane:XI.4:construction3"],"deps":["maclane:XI.4:def1","maclane:XI.1:def2"]} -->

---8<---

---
title: "MacLane XI.5: The braid category is the free braided monoidal category on one object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.5:thm1]
deps_item_ids: [maclane:XI.4:construction2, maclane:XI.3:thm1, maclane:XI.1:def2, maclane:XI.2:remark2]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.5 Theorem 1 (book pp. 263–265, PDF pp. 270–272). Item `maclane:XI.5:thm1`.

## Background

The braid category `B` is the free braided monoidal category on one generating object (Joyal–Street): for any braided monoidal category `M` with underlying ordinary category `M₀`, evaluation at the object `1 ∈ B` is an equivalence between the category of strong braided monoidal functors `B ⟶ M` (with monoidal natural transformations) and `M₀`. See the nLab, [braided monoidal category](https://ncatlab.org/nlab/show/braided+monoidal+category).

## Current state in the library

Absent. There is no free-braided-monoidal-category-on-one-object result and no evaluation-at-1 equivalence. The `FreeBraided` PROP sections (`Construction/PROP/Braided.v:76`) equip the free PROP with a braiding, but it is a *symmetry* (`braid_invol` holds), so that is the free strict *symmetric* monoidal category, not the Joyal–Street braided freeness. `BraidedMonoidalFunctor` exists (`Functor/Structure/Monoidal/Braided.v:67`), but there is no category of such functors into an arbitrary braided `M` and no evaluation equivalence. The carrier braid category `B` is itself the subject of the §XI.4 braid-category issue.

## Work to be done

- Form the category of strong braided monoidal functors `B ⟶ M` and their monoidal natural transformations (reusing the category-of-monoidal-functors construction of §XI.2), and the evaluation functor "value at `1`" to `M₀`.
- Prove evaluation at `1` is full, faithful, and essentially surjective (hence an equivalence): after strictifying `M` (§XI.3), for each object `a` build the strict braided monoidal functor `F_a` with `F_a(1) = a`, `F_a(n) = a^{⊗ n}`, `F_a(σ_i) = 1^{⊗(i-1)} ⊗ γ_{a,a} ⊗ 1^{⊗(n-i-1)}`, verify the braid relations from the two hexagons, and show every strong braided monoidal functor is determined up to iso by its value at `1`.
- Suggested module: `Instance/BraidCategory/Universal.v`. In-tree donors: the braid category of §XI.4, the strictification of §XI.3, the braiding-as-isomorphism of §XI.1, the category of monoidal functors of §XI.2, `Functor/Structure/Monoidal/Braided.v:67` (`BraidedMonoidalFunctor`), `Theory/Equivalence/FullFaithful.v` (the full+faithful+eso characterization of equivalences).

## Definition of Done

- [ ] The category of strong braided monoidal functors `B ⟶ M` with monoidal natural transformations, and the evaluation-at-`1` functor to `M₀`.
- [ ] The functors `F_a` constructed (on objects and generators) with the braid relations verified from the hexagons.
- [ ] Evaluation at `1` proved full, faithful, and essentially surjective, hence an equivalence `hom_BMC(B, M) ≃ M₀`.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (or, for an `Instance/`-layer placement, only the stdlib axioms enumerated in docs/AXIOMS.md).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Instance/BraidCategory/Universal.v` compiles cleanly.
- `Print Assumptions braid_category_free.` shows closed under the global context (or documented Instance-layer axioms).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: evaluation at `1` is an equivalence between strong braided monoidal functors `B ⟶ M` and `M₀`, with the `F_a` witnesses; statement matches Mac Lane §XI.5 Theorem 1 (Joyal–Street).

## Dependencies

Depends on: maclane:XI.4:construction2
Depends on: maclane:XI.3:thm1
Depends on: maclane:XI.1:def2
Depends on: maclane:XI.2:remark2

<!-- catalog: {"ids":["maclane:XI.5:thm1"],"deps":["maclane:XI.4:construction2","maclane:XI.3:thm1","maclane:XI.1:def2","maclane:XI.2:remark2"]} -->

---8<---

---
title: "MacLane XI.5: Braided coherence via the underlying braid, and the B_2 action on a tensor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:XI.5:thm2, maclane:XI.5:remark1]
deps_item_ids: [maclane:XI.4:def1, maclane:XI.5:thm1, maclane:XI.4:construction2]
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §XI.5 (book pp. 263 and 266, PDF pp. 270 and 273). Items `maclane:XI.5:thm2` (braided coherence: two composites are equal iff they determine the same element of `B_n`) and `maclane:XI.5:remark1` (the canonical automorphisms `1, γ², γ⁻², γ⁴, …` of a tensor and the resulting `B_2` action).

## Background

Braided coherence (Joyal–Street) is a classification, not "all diagrams commute": every composite of canonical maps (built from `α, λ, ρ, γ`) on an `n`-fold tensor has a well-defined underlying element of the braid group `B_n`, and two such composites are equal in every braided monoidal category iff they determine the same braid. The subtlety is real already at `n = 2`: the maps `1, γ², γ⁻², γ⁴, …` on `a ⊗ b` are in general distinct, so a subgroup of `B_2` acts and not every `γ`-diagram commutes. See the nLab, [braided monoidal category](https://ncatlab.org/nlab/show/braided+monoidal+category).

## Current state in the library

Absent. There is no braided-coherence classification: the "underlying braid" invariant and the biconditional cannot even be stated without the braid group `B_n` (the subject of the §XI.4 braid-group issue). Only one soundness-direction consequence is proved — `Yang_Baxter_equation` (`Structure/Monoidal/Braided.v:155`), the braid relation on a triple tensor — which holds in every `BraidedMonoidal` and is not a fragment of the classification (there is no completeness/`iff` side and no free-braided-category comparison). For the remark, the enabling structural fact (`braid ∘ braid` need not be the identity) is present only implicitly: `BraidedMonoidal` (`Structure/Monoidal/Braided.v:128`) lacks a `braid_invol` field and the non-collapse is stated only in the header essay (`Structure/Monoidal/Braided.v:70–72`); no lemma exhibits a nontrivial `γ²` or the canonical-automorphism family.

## Work to be done

- Define, for a canonical composite on an `n`-fold tensor in a braided monoidal category, its underlying element of `B_n` (via evaluation into the braid category / the freeness of §XI.5).
- Prove braided coherence: two canonical composites are equal in every braided monoidal category iff they have the same underlying braid — the soundness direction (equal braids ⇒ equal composites) and the completeness direction (distinct braids ⇒ some braided category separates them, from the freeness of the braid category).
- Prove the remark: in a general braided category the canonical automorphisms `1, γ², γ⁻², γ⁴, …` of `a ⊗ b` realize an action of a subgroup of `B_2`, and exhibit a witness (e.g. the braid category of §XI.4) where `γ²` has infinite order, so the powers are genuinely distinct.
- Suggested module: `Structure/Monoidal/Braided/Coherence.v`. In-tree donors: the braid group `B_n` and braid category of §XI.4, the freeness theorem of §XI.5, `Structure/Monoidal/Braided.v:155` (`Yang_Baxter_equation`, the soundness seed), `Structure/Monoidal/Symmetric.v` (the symmetric coherence collapse as a contrast).

## Definition of Done

- [ ] The underlying-braid map from canonical composites on an `n`-fold tensor to `B_n` defined.
- [ ] Braided coherence proved as a biconditional: equal composites iff equal underlying braid (both directions).
- [ ] The `B_2` action on `a ⊗ b` and the genuine distinctness of `γ^{2k}` established, with an explicit witnessing braided category.
- [ ] All morphism equations use setoid `≈`, never `=` on hom-sets.
- [ ] No `Admitted`, `admit`, or `Axiom`; `Print Assumptions` closed under the global context (or, for any `Instance/`-layer witness, only the stdlib axioms enumerated in docs/AXIOMS.md).
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; `nix build` targets for Coq 8.19 / 8.20 pass.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md Key Files index updated (flagship-level result).

## Verification

- `coqc -R . Category Structure/Monoidal/Braided/Coherence.v` compiles cleanly.
- `Print Assumptions braided_coherence.` shows closed under the global context (or documented Instance-layer axioms for the witness).
- `nix build .#category-theory_9_1` and the `_8_20` / `_8_19` targets succeed.
- Review: coherence is the `iff` classification by underlying braid (not merely Yang–Baxter), and the `B_2`-action remark is realized with a witness; statements match Mac Lane §XI.5 (Joyal–Street braided coherence and the canonical-automorphisms remark).

## Dependencies

Depends on: maclane:XI.4:def1
Depends on: maclane:XI.5:thm1
Depends on: maclane:XI.4:construction2

<!-- catalog: {"ids":["maclane:XI.5:thm2","maclane:XI.5:remark1"],"deps":["maclane:XI.4:def1","maclane:XI.5:thm1","maclane:XI.4:construction2"]} -->

---
title: "MacLane VIII.1: Equalizers as kernels of differences in an Ab-category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.1:remark2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §VIII.1 (Kernels and Cokernels), book p. 192, PDF p. 200. Item: `maclane:VIII.1:remark2`.

## Background

In a category enriched in abelian groups, a morphism `h` equalizes a parallel pair `f, g` exactly when `(f − g) ∘ h = 0`, so the equalizer of `f` and `g` coincides with the kernel of the single arrow `f − g`; this is why one works with kernels rather than general equalizers in `R`-Mod, `Ab`, and the like. See [nLab: kernel](https://ncatlab.org/nlab/show/kernel) and [Wikipedia: Kernel (category theory)](https://en.wikipedia.org/wiki/Kernel_(category_theory)).

## Current state in the library

The library only performs the reverse specialization: a kernel is *defined* as an equalizer against the zero morphism, `IsKernel f i := IsEqualizer f zero_mor k i` (`Structure/Kernel.v:53`). The forward identity — that a general equalizer is the kernel of a difference — appears only as background prose in the essay of `Structure/Equalizer.v:56`–`58` ("the equalizer of f and g is the kernel of f − g"), with no lemma. Additive subtraction is available as `psub`/`pneg` with `padd_pneg` (`Structure/Additive.v:34`), but nothing relates equalizers to kernels of differences. Gap: there is no lemma stating `Eq(f,g) = Ker(f − g)` in an additive/Ab-category.

## Work to be done

- In a preadditive category carrying additive inverses (i.e. over `Additive`, or a `Preadditive` extended with `pneg`), prove that for parallel `f g : x ~> y` and `i : k ~> x`, `IsEqualizer f g k i` holds **iff** `IsKernel (psub f g) i` holds (both directions), phrased with the setoid `≈`.
- Derive the corollary that an additive category with all kernels has the equalizer of every parallel pair (feeds the finite-completeness assembly of §VIII.3).
- Suggested module: extend `Structure/Kernel.v`, or a new `Structure/Equalizer/Difference.v`.
- Donors: `Structure/Kernel.v` (`IsKernel`, `kernel_desc`), `Structure/Additive.v` (`psub`, `padd_pneg`, bilinearity `compose_padd_left/right`), `Structure/Equalizer/Fork.v` (`IsEqualizer`, `equalizer_desc`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.1 (setoid `≈` throughout; never `=` on morphisms).
- [ ] No `Admitted`, `admit`, or `Axiom` in the new definitions/proofs (core-theory zero-axiom scope, `docs/AXIOMS.md`).
- [ ] `Print Assumptions` closed under the global context for the principal artifact (`equalizer_iff_kernel_sub` or the chosen name).
- [ ] New/changed file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category <path>` compiles standalone after its dependencies.
- `Print Assumptions equalizer_iff_kernel_sub.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` and `.#category-theory_8_20` succeed.
- Reviewer confirms the biconditional matches Mac Lane §VIII.1 (equalizer of `f,g` = kernel of `f − g`).

## Dependencies

None (uses only in-tree `Additive`/`Kernel`/`Equalizer` donors, all present). This lemma is a reusable prerequisite of the finite-(co)completeness assembly in §VIII.3.

<!-- catalog: {"ids":["maclane:VIII.1:remark2"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.1: The kernel–cokernel Galois connection"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.1:construction1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.1, book p. 192, PDF pp. 200–201. Item: `maclane:VIII.1:construction1`.

## Background

Fixing an object `c` in a category with a zero object, kernels and cokernels, the arrows into `c` (preordered by factorization) and the arrows out of `c` (dually preordered) are related by an antitone Galois connection: choosing a kernel of each arrow out and a cokernel of each arrow in gives order maps with `f ≤ ker u ⟺ u∘f = 0 ⟺ coker f ≥ u`, whose triangular identities express that an arrow is a kernel iff it equals `ker(coker −)`. See [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection) and [Wikipedia: Galois connection](https://en.wikipedia.org/wiki/Galois_connection).

## Current state in the library

The categorical *core* lemmas exist: the triangular identities `kernel_of_any_cokernel` (`Structure/Kernel.v:177`) and its dual, and `normal_mono_kernel_of_cokernel` (`Structure/Kernel.v:226`) giving "a normal mono is the kernel of its cokernel". The subobject factorization preorder `sub_le` is the monos-only fragment of the "arrows into `c`" preorder (`Theory/Subobject.v:55`). The general fact that a Galois connection is an adjunction of posets is documented (`Instance/Poset.v:47`) but not instantiated here. Gap: the two full preorders `P_c` (all arrows into `c`) and `Q^c` (all arrows out of `c`) are not built, `ker`/`coker` are not exhibited as monotone maps between them, and the antitone Galois connection `f ≤ ker u ⟺ u∘f = 0 ⟺ coker f ≥ u` is never assembled.

## Work to be done

- Build the two preorders `P_c` and `Q^c` (arrows into / out of `c`, preordered by factorization, as thin categories or `Instance/Poset.v` posets), quotienting to the factorization preorder.
- Define `ker : Q^c → P_c` and `coker : P_c → Q^c` on chosen (co)kernels and prove monotone.
- Prove the antitone Galois connection and its two triangular identities, and the fixed-point characterization "`g` is a kernel iff `g ≈ ker(coker g)`".
- Suggested module: `Structure/Kernel/Galois.v`.
- Donors: `Structure/Kernel.v` (`kernel_of_any_cokernel`, `cokernel_of_any_kernel`, `normal_mono_kernel_of_cokernel`, `kernel_desc`, `cokernel_desc`), `Theory/Subobject.v` (`sub_le`), `Instance/Poset.v`, and the poset-adjunction/Galois framework filed as #380.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.1 (setoid `≈`; never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope, `docs/AXIOMS.md`).
- [ ] `Print Assumptions` closed for the principal artifacts (the Galois connection and the `ker(coker −)` fixed-point lemma).
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Kernel/Galois.v` compiles standalone after dependencies.
- `Print Assumptions ker_coker_galois.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the connection and triangular identities match Mac Lane §VIII.1.

## Dependencies

Depends on: #380 (Galois connections as adjunctions between preorders — the poset-adjunction framework).

<!-- catalog: {"ids":["maclane:VIII.1:construction1"],"deps":["#380"]} -->

---8<---

---
title: "MacLane VIII.1: The canonical factorization f = ker(coker f) ∘ q and its diagonal fill-in"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.1:remark3, maclane:VIII.1:lem1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.1, book p. 193, PDF pp. 201–202. Items: `maclane:VIII.1:remark3` (canonical factorization), `maclane:VIII.1:lem1` (diagonal fill-in; `q` epi).

## Background

In any category with a zero object, kernels and cokernels, every arrow `f` factors canonically as `f = m ∘ q` with `m = ker(coker f)`; given any second factorization `f = m' ∘ q'` in which `m'` is a kernel there is a unique diagonal `t` with `m ≈ m' ∘ t` and `q' ≈ t ∘ q`, and when equalizers exist and every mono is a kernel the mediator `q` is epi (so `f = m ∘ q` is an epi–mono factorization). See [nLab: image](https://ncatlab.org/nlab/show/image) and [Wikipedia: Image (category theory)](https://en.wikipedia.org/wiki/Image_(category_theory)).

## Current state in the library

All the content exists, but only under the *full* `Abelian C` structure: `abelian_image f = ker(coker f)` is monic (`Structure/Abelian.v:261`, `:272`) and `abelian_image_med_comm` gives `f ≈ ker(coker f) ∘ q` (`Structure/Abelian.v:286`); the mediator is epi via `image_mediator_epic` (`Structure/Abelian.v:353`); the unique diagonal is delivered by the orthogonality `abelian_epi_mono_ortho` (`Structure/Abelian.v:431`) together with `factorization_lift_unique`/`factorization_unique` (`Structure/Factorization.v:185`, `:216`). Gap: Mac Lane states the factorization for *any* category with a zero object, kernels and cokernels (the diagonal fill-in needs no epi hypothesis), and the `q`-epi conclusion under only "equalizers exist and every mono is a kernel"; the in-tree results all require the additive + biproduct + normality package, and no standalone lemma is exposed at Mac Lane's weaker generality even though the underlying construction uses only `ZeroObject`/`HasKernels`/`HasCokernels`.

## Work to be done

- State and prove the canonical factorization `f ≈ ker(coker f) ∘ q` over `ZeroObject + HasKernels + HasCokernels` (no additive/normality hypotheses), extracting the mediator `q` via `kernel_desc` from `coker f ∘ f ≈ 0`.
- Prove the diagonal fill-in against an arbitrary kernel-factorization `f = m' ∘ q'` (`m'` a kernel, `q'` unconstrained): unique `t` with `m ≈ m' ∘ t`, `q' ≈ t ∘ q`.
- Prove the mediator `q` is epi under the added hypotheses "has equalizers and every mono is a kernel".
- Suggested module: `Structure/Kernel/Factorization.v` (generalizing the abelian-only facts of `Structure/Abelian.v`).
- Donors: `Structure/Kernel.v` (`kernel_desc`, `cokernel_desc`, `kernel_monic`, `normal_mono_kernel_of_cokernel`), `Structure/Abelian.v` (the abelian-level proofs to be re-based), `Structure/Factorization.v` (`factorization_unique`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.1 at the stated weaker generality (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the factorization lemma, the diagonal-fill-in lemma, and the `q`-epi lemma.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Kernel/Factorization.v` compiles standalone.
- `Print Assumptions canonical_factorization.` and `Print Assumptions factorization_diagonal.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms `m = ker(coker f)`, the unique `t`, and the `q`-epi hypotheses match Mac Lane §VIII.1 Lemma 1.

## Dependencies

None filed (uses only `Kernel`/`Cokernel`/`Factorization` donors, all present). Provides the general-position factorization that the full abelian image factorization (already in-tree over `Abelian C`) specializes.

<!-- catalog: {"ids":["maclane:VIII.1:remark3","maclane:VIII.1:lem1"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: Characterization of the zero object in an Ab-category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:prop1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2 (Additive Categories), Proposition 1, book p. 194, PDF p. 202. Item: `maclane:VIII.2:prop1`.

## Background

In a category enriched in abelian groups, for an object `z` the four conditions — `z` initial, `z` terminal, `1_z = 0`, and the endomorphism group `A(z,z)` trivial — are equivalent; in particular any initial or terminal object of such a category is automatically a zero object. See [nLab: zero object](https://ncatlab.org/nlab/show/zero+object) and [nLab: additive category](https://ncatlab.org/nlab/show/additive+category).

## Current state in the library

`ZeroObject` packages an initial structure, a terminal structure, and their coincidence as *data* (`Structure/ZeroObject.v:35`); `pzero_zero_mor` (`Structure/Preadditive.v:87`) proves the enrichment unit coincides with the tunnelled zero morphism. Gap (ABSENT): nothing derives the automatic equivalence "`z` initial ⟺ `z` terminal ⟺ `1_z ≈ pzero` ⟺ `A(z,z)` is the zero group" that holds in a preadditive/Ab-category; the coincidence of initial and terminal is assumed as data rather than obtained from the additive hom-structure.

## Work to be done

- Over a `Preadditive` category, prove the equivalence of: `z` is initial; `z` is terminal; `1_z ≈ pzero`; every endomorphism of `z` is `pzero` (equivalently `A(z,z)` is the trivial group). Use that in a preadditive category an object is initial iff its identity is the additive zero.
- Derive: an initial or a terminal object of a preadditive category is a `ZeroObject` (constructing the coincidence rather than assuming it).
- Suggested module: extend `Structure/Preadditive.v` or a new `Structure/Preadditive/ZeroObject.v`.
- Donors: `Structure/Preadditive.v` (`pzero`, `compose_pzero_left/right`, `pzero_zero_mor`), `Structure/ZeroObject.v`, `Theory/Morphisms.v` (initial/terminal notions).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Prop 1 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the characterization lemma.
- [ ] New/changed file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category <path>` compiles standalone.
- `Print Assumptions preadditive_zero_object_iff.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the four-way equivalence matches Mac Lane §VIII.2 Proposition 1.

## Dependencies

None (uses `Preadditive` + `ZeroObject`, both present).

<!-- catalog: {"ids":["maclane:VIII.2:prop1"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: Product, biproduct, and coproduct coincide in an Ab-category"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:thm2, maclane:VIII.2:ex1]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Theorem 2 (book p. 194, PDF pp. 202–203) and Exercise 1 (book p. 197, PDF p. 205). Items: `maclane:VIII.2:thm2`, `maclane:VIII.2:ex1`.

## Background

In a category enriched in abelian groups two objects have a product iff they have a biproduct iff they have a coproduct: a biproduct diagram is simultaneously a product (via its projections) and a coproduct (via its injections), and conversely a product extends uniquely to a biproduct; equivalently, the canonical comparison `a ⊔ b → a × b` is an isomorphism. See [nLab: biproduct](https://ncatlab.org/nlab/show/biproduct) and [Wikipedia: Biproduct](https://en.wikipedia.org/wiki/Biproduct).

## Current state in the library

`cartesian_biproduct` shows that in a `Preadditive` category with a `ZeroObject` every binary product is a biproduct (`Structure/Semiadditive.v:227`), and the `Biproduct` record makes a biproduct simultaneously a product and coproduct through the definitional fields `bi_is_product`/`bi_is_coproduct` (`Structure/Biproduct.v:59`); `cartesian_has_biproducts` promotes all products to all biproducts (`Structure/Semiadditive.v:243`). So "product ⟺ biproduct" and "biproduct ⟹ coproduct" are covered on hypotheses even weaker than Mac Lane's. Gaps: (1) the dual leg "has a coproduct ⟹ has a biproduct" is not instantiated (no `cocartesian_biproduct`); (2) the canonical comparison `can_comparison : x + y → x × y` is *defined* (`Structure/Semiadditive.v:288`) but its invertibility is only ever *assumed* (Context hypothesis at `Structure/Semiadditive.v:324`), never derived; (3) the `n`-ary comparison `⊔ᵢ aᵢ → ×ᵢ aᵢ` of Exercise 1 is absent.

## Work to be done

- Construct `cocartesian_biproduct`/`cocartesian_has_biproducts` (the dual of the existing product-side construction over `C^op`), closing the three-way equivalence product ⟺ biproduct ⟺ coproduct.
- Prove `IsIsomorphism (can_comparison x y)` as a *theorem* in a preadditive category with the biproduct (Exercise 1, binary case), rather than an assumed context.
- Add the `n`-ary canonical comparison `⊔ᵢ aᵢ → ×ᵢ aᵢ` and prove it an isomorphism (connecting to the finite-biproduct work of §VIII.2).
- Suggested module: extend `Structure/Semiadditive.v` (dual construction + `can_comparison_iso`).
- Donors: `Structure/Semiadditive.v` (`cartesian_biproduct`, `can_comparison`, `can_inv`), `Structure/Biproduct.v`, `Construction/Opposite.v` (for the dualization).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Thm 2 / Ex 1 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `cocartesian_biproduct` and `can_comparison_iso`.
- [ ] New/changed file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Semiadditive.v` compiles standalone.
- `Print Assumptions can_comparison_iso.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the three-way equivalence and the κ-iso match Mac Lane §VIII.2 Theorem 2 and Exercise 1.

## Dependencies

None (dualizes the in-tree product-side construction; uses `Semiadditive`/`Biproduct`, both present). The `n`-ary comparison connects to the finite-biproduct issue (`maclane:VIII.2:construction2`).

<!-- catalog: {"ids":["maclane:VIII.2:thm2","maclane:VIII.2:ex1"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: The biproduct bifunctor and its associativity and commutativity"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:construction1, maclane:VIII.2:ex3]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, construction of `⊕ : A × A → A` (book pp. 195–196, PDF pp. 203–204) and Exercise 3 (book p. 198, PDF p. 206). Items: `maclane:VIII.2:construction1`, `maclane:VIII.2:ex3`.

## Background

When all binary biproducts exist, a chosen `a ⊕ b` makes `⊕` a bifunctor `A × A → A`; the arrow `f ⊕ g` is characterized equivalently by the product rule and the coproduct rule, the identification of the product bifunctor with the coproduct bifunctor is a natural isomorphism, and `⊕` is associative and commutative up to natural isomorphism. See [nLab: biproduct](https://ncatlab.org/nlab/show/biproduct) and [nLab: matrix calculus](https://ncatlab.org/nlab/show/matrix+calculus).

## Current state in the library

The morphism action `bimap` exists on biproducts, defined through the product side, with the product-rule commutations `bimap_exl`/`bimap_exr` (`Structure/Biproduct.v:197`, `:203`–`213`) and `bimap_bi_pair` (`Structure/Semiadditive.v:113`). A genuine product bifunctor `InternalProductFunctor : C ∏ C ⟶ C` exists but only for the cartesian presentation (`Functor/Product/Internal.v:34`). Associativity/commutativity are available for the categorical product/coproduct — `prod_comm`/`prod_assoc` (`Structure/Cartesian.v:479`), `coprod_comm`/`coprod_assoc` (`Structure/Cocartesian.v:393`), and the cartesian symmetric-monoidal assembly — but not at the biproduct level. Gaps: (1) `bimap` is not packaged as a `Functor (C ∏ C) C` over `HasBiproducts` (no `bimap_id`/`bimap_comp`); (2) the coproduct-side law `(f ⊕ g) ∘ inl ≈ inl' ∘ f` is not stated; (3) the product-vs-coproduct natural isomorphism is not proved; (4) there is no biproduct-native `bi_assoc`/`bi_comm` natural iso.

## Work to be done

- Prove `bimap_id` and `bimap_comp` and bundle `bimap` into a `Functor (C ∏ C) C` over a `HasBiproducts` category.
- Prove the coproduct-side characterization of `f ⊕ g` and the natural isomorphism identifying the product and coproduct bifunctor structures.
- Prove `bi_comm : x ⊕ y ≅ y ⊕ x` and `bi_assoc : (x ⊕ y) ⊕ z ≅ x ⊕ (y ⊕ z)` as biproducts, with naturality (Exercise 3).
- Suggested module: `Structure/Biproduct/Functor.v`.
- Donors: `Structure/Biproduct.v` (`bimap`, `bi_pair`, `bi_copair`, interaction laws), `Structure/Semiadditive.v` (`bimap_bi_pair`), `Functor/Bifunctor.v`, `Structure/Cartesian.v`/`Cocartesian.v` (assoc/comm templates).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the biproduct bifunctor and `bi_assoc`/`bi_comm`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Biproduct/Functor.v` compiles standalone.
- `Print Assumptions BiproductFunctor.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms both characterizations of `f ⊕ g` and the associativity/commutativity natural isos match Mac Lane §VIII.2 and Exercise 3.

## Dependencies

None (uses `Biproduct`/`Semiadditive`, both present). The bifunctor is a reusable donor for the matrix calculus (`maclane:VIII.2:construction2`) and the addition-from-biproduct formula.

<!-- catalog: {"ids":["maclane:VIII.2:construction1","maclane:VIII.2:ex3"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: Finite biproducts and the matrix calculus of arrows"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:construction2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, book p. 196, PDF p. 204. Item: `maclane:VIII.2:construction2`.

## Background

Iterating the binary biproduct yields finite biproducts `⊕ⱼ aⱼ` characterized by the completeness relation `Σⱼ iⱼ ∘ pⱼ = 1` and the Kronecker relations `pₖ ∘ iⱼ = δₖⱼ`; then `A(⊕ₖ cₖ, ⊕ⱼ aⱼ) ≅ Σⱼₖ A(cₖ, aⱼ)`, every arrow is determined by its matrix of components `fₖⱼ = pₖ ∘ f ∘ iⱼ`, and composition of arrows is matrix multiplication. See [nLab: matrix calculus](https://ncatlab.org/nlab/show/matrix+calculus) and [Wikipedia: Biproduct](https://en.wikipedia.org/wiki/Biproduct).

## Current state in the library

Only the binary (`n = 2`) fragments exist: the completeness relation `i₁ p₁ + i₂ p₂ ≈ 1` (`biproduct_id_decomp`, `Structure/Semiadditive.v:61`), the four Kronecker laws (`Structure/Biproduct.v:51`), and the `1×2 · 2×1` matrix product `bi_copair_pair` (`Structure/Semiadditive.v:101`). The `Structure/Abelian.v` header describes the matrix calculus in prose but does not formalize it. Gap: no iterated `n`-fold biproduct object `⊕ⱼ aⱼ`, no hom-set isomorphism `A(⊕ c, ⊕ a) ≅ Σ A(c, a)`, no general `n × m` matrix representation of an arrow, and no "composition = matrix multiplication" theorem.

## Work to be done

- Define the finite (`n`-ary) biproduct object over a `HasBiproducts` category with a zero object (as an indexed fold), with its projections/injections and the completeness + Kronecker relations at general `n`.
- Prove the hom-set isomorphism `A(⊕ₖ cₖ, ⊕ⱼ aⱼ) ≅ Σⱼₖ A(cₖ, aⱼ)` (a setoid iso), the matrix representation `fₖⱼ = pₖ ∘ f ∘ iⱼ`, and that composition is matrix multiplication.
- Suggested module: `Structure/Biproduct/Finite.v`.
- Donors: `Structure/Biproduct.v` (binary biproduct, Kronecker laws), `Structure/Semiadditive.v` (`biproduct_id_decomp`, `bi_copair_pair`), the biproduct bifunctor (`maclane:VIII.2:construction1`), `Structure/Preadditive.v` (hom-monoid sums).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the finite biproduct object, the hom-matrix isomorphism, and the composition-as-matrix-multiplication theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Biproduct/Finite.v` compiles standalone.
- `Print Assumptions hom_matrix_iso.` and `Print Assumptions matrix_compose.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the finite biproduct, the hom-matrix iso, and matrix multiplication match Mac Lane §VIII.2.

## Dependencies

None filed. Uses the binary biproduct (present); benefits from the biproduct bifunctor issue `maclane:VIII.2:construction1`.

<!-- catalog: {"ids":["maclane:VIII.2:construction2"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: Additive functors are exactly the biproduct-preserving functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:prop4]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Proposition 4, book p. 197, PDF p. 205. Item: `maclane:VIII.2:prop4`.

## Background

If `A` has all binary biproducts, a functor `T : A → B` between Ab-categories is additive (`T(f + f') = Tf + Tf'`) iff it carries every binary biproduct diagram to a biproduct, equivalently iff it carries binary products to products, equivalently iff it carries binary coproducts to coproducts. See [nLab: additive functor](https://ncatlab.org/nlab/show/additive+functor) and [Wikipedia: Additive category](https://en.wikipedia.org/wiki/Additive_category).

## Current state in the library

ABSENT. The base notion "additive functor" (`T(f + f') ≈ Tf + Tf'`) is itself not yet in-tree (it is filed for §I.8 as #264). The generic product-preservation vocabulary that exists — `CartesianFunctor`, `InternalProductFunctor` (`Functor/Product/Internal.v:34`) — is never connected to an additive-functor notion, and no theorem states "`T` additive ⟺ `T` carries binary biproducts/products/coproducts to one of the same kind".

## Work to be done

- On top of the additive-functor notion (#264), prove Proposition 4: for `A` with all binary biproducts, `T` additive iff `T` preserves binary biproducts, iff `T` preserves binary products, iff `T` preserves binary coproducts.
- Include the corollary `T` additive ⟹ `T 0 ≈ 0` on objects (carries the zero object to a zero object) as needed.
- Suggested module: `Functor/Structure/Additive.v` (the biproduct-preservation characterization), building on the additive-functor class introduced by #264.
- Donors: the additive-functor class (#264), `Structure/Biproduct.v` (`Biproduct`, `bi_is_product`, `bi_is_coproduct`), `Structure/Semiadditive.v` (`biproduct_addition`, `cartesian_biproduct`), `Functor/Structure/Cartesian.v` (product-preservation templates).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Prop 4 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the additive-iff-preserves-biproducts characterization.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Functor/Structure/Additive.v` compiles standalone.
- `Print Assumptions additive_iff_preserves_biproduct.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the four-way characterization matches Mac Lane §VIII.2 Proposition 4.

## Dependencies

Depends on: #264 (Ab-categories and additive functors — supplies the additive-functor class this proposition characterizes).

<!-- catalog: {"ids":["maclane:VIII.2:prop4"],"deps":["#264"]} -->

---8<---

---
title: "MacLane VIII.2: The infinite canonical coproduct-to-product map need not be an isomorphism"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:ex2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Exercise 2, book p. 197, PDF p. 205. Item: `maclane:VIII.2:ex2`.

## Background

While the *finite* canonical comparison from a coproduct to the corresponding product is an isomorphism in any additive category, the *infinite* canonical map `⊔_I aᵢ → ×_I aᵢ` need not be — the classic witness being a countable family of abelian groups, where the direct sum (eventually-zero families) is a proper subobject of the direct product. See [nLab: additive category](https://ncatlab.org/nlab/show/additive+category) and [Wikipedia: Category of abelian groups](https://en.wikipedia.org/wiki/Category_of_abelian_groups).

## Current state in the library

ABSENT. Only the binary `can_comparison` is defined (`Structure/Semiadditive.v:288`); there is no infinite-biproduct / infinite-direct-sum machinery and no additive category instance exhibiting the infinite comparison as a non-isomorphism. Indexed products (`Structure/Limit/Product.v`, `iprod`) exist but carry no matching indexed coproduct with a canonical comparison, and there is no counterexample construction.

## Work to be done

- Define the infinite canonical comparison `⊔_I aᵢ → ×_I aᵢ` in a category with `I`-indexed products and coproducts and a zero object (matrix with identity diagonal, zero off-diagonal).
- Exhibit a concrete additive category (the category of abelian groups, #256, is the natural home) with a countable family for which this comparison is monic but not epic, hence not an isomorphism — the eventually-zero-vs-arbitrary sequences example.
- Suggested module: `Instance/AbGroup/InfiniteBiproduct.v` (or alongside the concrete `Ab` construction).
- Donors: `Structure/Semiadditive.v` (`can_comparison`), `Structure/Limit/Product.v` (`iprod`), and the concrete category of abelian groups (#256, with its infinite products/coproducts).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Ex 2 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (concrete-instance layer may use the stdlib axioms enumerated in `docs/AXIOMS.md`, but no new axioms).
- [ ] `Print Assumptions` reported for the counterexample witness (documenting any stdlib axioms per `docs/AXIOMS.md`).
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category <path>` compiles standalone.
- `Print Assumptions infinite_can_not_iso.` reviewed against `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the infinite comparison and the non-iso witness match Mac Lane §VIII.2 Exercise 2.

## Dependencies

Depends on: #256 (the category of abelian groups — the concrete additive category with infinite products/coproducts in which the counterexample lives).

<!-- catalog: {"ids":["maclane:VIII.2:ex2"],"deps":["#256"]} -->

---8<---

---
title: "MacLane VIII.2: Group completion of the semiadditive enrichment (Ex 4b)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:ex4]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Exercise 4, book p. 198, PDF p. 206. Item: `maclane:VIII.2:ex4`.

## Background

For a category with a null object, finite products and finite coproducts in which the canonical map `a₁ ⊔ a₂ → a₁ × a₂` is always an isomorphism, `f + f' := ∇ ∘ (f × f') ∘ Δ` makes each hom-set a commutative monoid over which composition distributes; if additionally each object `a` carries `vₐ : a → a` with `vₐ + 1ₐ = 0`, each hom-set is an abelian group, giving `A` the structure of an additive category (Mac Lane 1950). See [nLab: additive category](https://ncatlab.org/nlab/show/additive+category) and [Wikipedia: Additive category](https://en.wikipedia.org/wiki/Additive_category).

## Current state in the library

Part (a) is exactly `bicartesian_preadditive` (`Structure/Semiadditive.v:573`): a bicartesian category with a zero object and invertible canonical comparison is `Preadditive`, with convolution `conv f g = (f ▽ g) ∘ can_inv ∘ (id △ id)` (`Structure/Semiadditive.v:369`) as addition, commutative/associative/unital, composition distributing on both sides (`conv_compose_left`/`conv_compose_right`, `Structure/Semiadditive.v:547`, `:557`). Gap: part (b) is not formalized — there is no theorem upgrading this commutative-monoid enrichment to an abelian group (hence to an `Additive` structure) from a family of object-wise witnesses `vₐ` with `vₐ + 1ₐ ≈ 0`; the `Additive` class instead takes `pneg` as primitive data (`Structure/Additive.v:34`).

## Work to be done

- Prove that given `bicartesian_preadditive` and, for each object `a`, an arrow `vₐ : a → a` with `padd vₐ id ≈ pzero`, each hom-set is an abelian group; i.e. derive a `pneg` with `padd f (pneg f) ≈ pzero` (define `pneg f := f ∘ vₐ` or `vᵦ ∘ f` and verify), and assemble an `Additive C` structure.
- Suggested module: `Structure/Additive/FromSemiadditive.v`.
- Donors: `Structure/Semiadditive.v` (`bicartesian_preadditive`, `conv`, `conv_compose_left/right`), `Structure/Additive.v` (target class), `Structure/Preadditive.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Ex 4(b) (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the group-upgrade and the derived `Additive` structure.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Additive/FromSemiadditive.v` compiles standalone.
- `Print Assumptions additive_from_negation_witnesses.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the group-upgrade matches Mac Lane §VIII.2 Exercise 4(b).

## Dependencies

None (extends the in-tree `bicartesian_preadditive`; part (a) is already present).

<!-- catalog: {"ids":["maclane:VIII.2:ex4"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: The free Ab-category on a category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:ex5]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Exercise 5, book p. 198, PDF p. 206. Item: `maclane:VIII.2:ex5`.

## Background

Every category `C` has a universal map to an Ab-category: take the same objects as `C` and hom-groups `A(b,c) = ℤ(C(b,c))`, the free abelian group on the hom-set, with composition extended bilinearly; the inclusion `C → A` is universal from `C` to an Ab-category. See [nLab: additive category](https://ncatlab.org/nlab/show/additive+category) and [nLab: Ab](https://ncatlab.org/nlab/show/Ab).

## Current state in the library

ABSENT. Only free *monoid* constructions exist (`Theory/Coq/List.v`, `Construction/Free.v`, `Construction/PROP.v`); there is no free abelian group on a set and no Ab-category with hom-groups `ℤ(C(b,c))` plus a universal functor `C → A`. `Instance/CMon.v` is commutative monoids, with no free-commutative-monoid / free-abelian-group functor feeding a free Ab-category.

## Work to be done

- Construct the free abelian group `ℤ(S)` on a setoid `S` (formal finite ℤ-linear combinations, quotiented), with its universal property into abelian groups.
- Build the Ab-category `A` on the objects of `C` with `A(b,c) = ℤ(C(b,c))` and bilinearly-extended composition; provide the functor `C → A` and prove it universal from `C` to an Ab-category (i.e. left adjoint to the forgetful functor from Ab-categories, or the universal-arrow form).
- Suggested module: `Construction/FreeAb.v` (with the free abelian group in `Theory/Algebra/` or reusing `Instance/Comp.v` `Group`).
- Donors: the additive-functor / Ab-category class (#264) as the target-structure vocabulary, `Instance/Comp.v` (`Group`), `Instance/CMon.v`, `Construction/Free/Quiver.v` (free-construction pattern), `Theory/Universal/Arrow.v` (universal-arrow packaging).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Ex 5 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` beyond the enumerated instance-layer stdlib axioms (`docs/AXIOMS.md`).
- [ ] `Print Assumptions` reported for the free Ab-category and its universal property.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Construction/FreeAb.v` compiles standalone.
- `Print Assumptions FreeAb_universal.` reviewed against `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms `A(b,c) = ℤ(C(b,c))` and the universal property match Mac Lane §VIII.2 Exercise 5.

## Dependencies

None filed as a hard prerequisite; relates to the category of abelian groups (#256) as the enrichment target and to the additive-functor vocabulary (#264).

<!-- catalog: {"ids":["maclane:VIII.2:ex5"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.2: The free additive category Add(A) and Add(K) = Matr_K"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.2:ex6]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.2, Exercise 6, book p. 198, PDF p. 206. Item: `maclane:VIII.2:ex6`.

## Background

Every Ab-category `A` has a universal map to an additive category `Add(A)` (the additive completion): objects are finite tuples of `A`-objects and arrows are matrices of `A`-arrows; for the commutative ring `K` viewed as a one-object Ab-category, `Add(K)` is the matrix category `Matr_K`. See [nLab: additive category](https://ncatlab.org/nlab/show/additive+category) and [nLab: matrix calculus](https://ncatlab.org/nlab/show/matrix+calculus).

## Current state in the library

ABSENT. There is no additive-completion functor (objects = tuples of `A`-objects, arrows = matrices of `A`-arrows) and no identification `Add(K) ≅ Matr_K`; `Instance/` contains no `Matr`/`R`-Mod/`Vect` instance and no `Add(−)` construction (only prose "matrix" mentions in unrelated headers).

## Work to be done

- Construct `Add(A)` for an Ab-category `A`: objects are finite lists of `A`-objects, `Add(A)(⟨cₖ⟩, ⟨aⱼ⟩)` are matrices `(fₖⱼ)` of `A`-arrows, composition is matrix multiplication; provide the additive-category instance (zero object = empty tuple, biproducts = concatenation) and the universal functor `A → Add(A)`, proving it universal from `A` to an additive category.
- Prove `Add(K) ≅ Matr_K` for the one-object Ab-category on a commutative ring `K`, matching the matrix category filed as #221.
- Suggested module: `Construction/Additive/Completion.v`.
- Donors: the Ab-category class (#264), the matrix category `Matr_K` (#221), the finite-biproduct matrix calculus (`maclane:VIII.2:construction2`), `Construction/Free/Quiver.v` (universal-construction pattern).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.2 Ex 6 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` beyond enumerated instance-layer stdlib axioms (`docs/AXIOMS.md`).
- [ ] `Print Assumptions` reported for `Add`, its universal property, and the `Add(K) ≅ Matr_K` identification.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Construction/Additive/Completion.v` compiles standalone.
- `Print Assumptions Add_universal.` and `Print Assumptions Add_K_Matr.` reviewed against `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the matrix construction, universal property, and `Add(K) = Matr_K` match Mac Lane §VIII.2 Exercise 6.

## Dependencies

Depends on: #221 (the matrix category `Matr_K`, for the `Add(K) = Matr_K` identification) and #264 (the Ab-category class `Add` takes as input). Benefits from the finite-biproduct matrix calculus (`maclane:VIII.2:construction2`).

<!-- catalog: {"ids":["maclane:VIII.2:ex6"],"deps":["#221","#264"]} -->

---8<---

---
title: "MacLane VIII.3: Abelian categories are finitely (co)complete and balanced"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:remark1, maclane:VIII.3:remark2]
deps_item_ids: [maclane:VIII.1:remark2]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3 (Abelian Categories), book pp. 198–199, PDF pp. 206–207. Items: `maclane:VIII.3:remark1` (all finite limits and colimits), `maclane:VIII.3:remark2` (mono + epi ⟹ iso, i.e. balanced).

## Background

Given a null object and biproducts, the kernels of an abelian category supply all finite limits (the equalizer of `f,g` is `ker(f − g)`, biproducts give finite products) and dually cokernels give all finite colimits; moreover an abelian category is balanced — every arrow that is both monic and epic is an isomorphism. See [nLab: abelian category](https://ncatlab.org/nlab/show/abelian+category), [nLab: balanced category](https://ncatlab.org/nlab/show/balanced+category), and [Wikipedia: Abelian category](https://en.wikipedia.org/wiki/Abelian_category).

## Current state in the library

The additive substrate is present: `ZeroObject` bundles terminal + initial (`Structure/ZeroObject.v:35`) and every `Biproduct` is a binary product and coproduct via `bi_is_product`/`bi_is_coproduct` (`Structure/Biproduct.v:59`). For balancedness, both ingredients exist — `abelian_epic_strong : Epic f → StrongEpi f` (`Structure/Abelian.v:422`) and `strong_epi_mono_is_iso` (`Structure/Factorization/StrongEpi.v:154`) — and compose to the result, but the corollary is never exposed (`Theory/Isomorphism.v:259` has only the converse). Gaps: (1) the reduction "equalizer of `f,g` = `ker(f − g)`" is only prose in `Structure/Equalizer.v:56`–`59`, so there is no in-tree proof that an abelian (or additive) category has all finite limits/colimits (no `abelian ⟹ Complete/FinitelyComplete` instance); (2) the balanced corollary `Monic f ∧ Epic f → IsIsomorphism f` is not stated.

## Work to be done

- Using the equalizer-as-kernel-of-difference lemma (`maclane:VIII.1:remark2`), prove that an additive/abelian category has all binary equalizers, hence (with biproducts + a terminal object) all finite limits; dually all finite colimits. Package as the appropriate finite-(co)completeness statements/instances.
- Expose the balanced corollary `abelian_balanced : Monic f → Epic f → IsIsomorphism f` by composing `abelian_epic_strong` with `strong_epi_mono_is_iso`.
- Suggested module: `Structure/Abelian/Limits.v` (finite (co)completeness) plus the balanced lemma in `Structure/Abelian.v`.
- Donors: `maclane:VIII.1:remark2` (equalizer = kernel of difference), `Structure/Biproduct.v`, `Structure/ZeroObject.v`, `Structure/Abelian.v` (`abelian_epic_strong`), `Structure/Factorization/StrongEpi.v` (`strong_epi_mono_is_iso`), `Structure/Limit.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the finite-(co)completeness result and `abelian_balanced`.
- [ ] New/changed files registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Limits.v` compiles standalone.
- `Print Assumptions abelian_finitely_complete.` and `Print Assumptions abelian_balanced.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms finite (co)completeness and balancedness match Mac Lane §VIII.3 remarks.

## Dependencies

Depends on: `maclane:VIII.1:remark2` (equalizers as kernels of differences — §VIII.1). The pullbacks obtained here feed the pullback-of-epi proposition (`maclane:VIII.4:prop2`).

<!-- catalog: {"ids":["maclane:VIII.3:remark1","maclane:VIII.3:remark2"],"deps":["maclane:VIII.1:remark2"]} -->

---8<---

---
title: "MacLane VIII.3: Functor and product categories inherit abelian structure"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:remark3, maclane:VIII.3:ex2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, remark on functor categories (book p. 199, PDF p. 207) and Exercise 2 (book p. 202, PDF p. 210). Items: `maclane:VIII.3:remark3`, `maclane:VIII.3:ex2`.

## Background

If `A` is abelian then so is every functor category `A^J`, with natural transformations forming abelian groups under termwise addition, the constant-null functor as null object, termwise biproducts, and termwise kernels/cokernels; likewise the product `A × B` of two abelian categories is abelian, componentwise. See [nLab: abelian category](https://ncatlab.org/nlab/show/abelian+category) and [Wikipedia: Abelian category](https://en.wikipedia.org/wiki/Abelian_category).

## Current state in the library

ABSENT for both closures. `Instance/Fun.v` carries no `Preadditive`/`Additive`/`Biproduct`/`HasKernels`/`Abelian` instance (only a Freyd citation in its essay, `Instance/Fun.v:50`); `Construction/Product.v` supplies the product category but no abelian/additive instance on it. The only `Preadditive` instances tree-wide are `Instance/CMon.v` (+ `Instance/CMon/Biproduct.v`), which are semiadditive commutative monoids, not abelian. Gaps: no pointwise abelian structure on `[J, A]`, no componentwise abelian structure on `A × B`, and no proof that `Nat(S,T)` is an abelian group under termwise addition. (The concrete `R`-Mod/`Ab` abelian-ness folded into the same remark is tracked separately by the concrete-category issues `maclane:VIII.3:ex3`/`ex4` and the module-category issue #258.)

## Work to be done

- Build the pointwise `Abelian` instance on the functor category `[J, A]` for abelian `A`: termwise hom abelian groups (`(α + β)_j = α_j + β_j`), constant-null functor, termwise biproducts, termwise kernels/cokernels, and termwise normality of monos/epis.
- Build the componentwise `Abelian` instance on `A × B`.
- Suggested modules: `Instance/Fun/Abelian.v` and `Construction/Product/Abelian.v`.
- Donors: `Structure/Abelian.v` (the `Abelian` class + facts), `Instance/Fun.v`, `Construction/Product.v`, `Structure/Preadditive.v`, `Structure/Biproduct.v`, `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the functor-category and product-category `Abelian` instances.
- [ ] New files registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Instance/Fun/Abelian.v` and `Construction/Product/Abelian.v` compile standalone.
- `Print Assumptions Fun_Abelian.` and `Print Assumptions Product_Abelian.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the termwise/componentwise abelian structure matches Mac Lane §VIII.3.

## Dependencies

None (uses the abstract `Abelian` class and the existing functor/product categories, all present).

<!-- catalog: {"ids":["maclane:VIII.3:remark3","maclane:VIII.3:ex2"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.3: Coimage and the canonical coimage-to-image isomorphism"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:def2]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, book p. 200, PDF p. 208. Item: `maclane:VIII.3:def2`.

## Background

For the monic–epi factorization `f = m ∘ e`, the image `im f := m = ker(coker f)` is a subobject of the codomain and the coimage `coim f := e = coker(ker f)` is a quotient object of the domain; more generally any factorization `f = m₁ ∘ t ∘ e₁` with `m₁` monic, `t` iso, `e₁` epi identifies `m₁ ≡ im f`, `e₁ ≡ coim f`, with `t` the canonical coimage-to-image isomorphism. See [nLab: coimage](https://ncatlab.org/nlab/show/coimage) and [Wikipedia: Coimage](https://en.wikipedia.org/wiki/Coimage).

## Current state in the library

The image is present exactly: `abelian_image_obj`/`abelian_image = ker(coker f)`, a monic subobject of the codomain (`Structure/Abelian.v:261`, `:272`), and the epi mediator `abelian_image_med` exists (`Structure/Abelian.v:282`), with `factorization_unique` giving up-to-iso uniqueness. Gap: the *coimage* as a distinct named quotient object `coker(ker f)` of the domain is not defined, the `coim`/`im` terminology is absent, and the canonical coimage-to-image isomorphism is not stated as such — "coimage" occurs only in the `Structure/Abelian.v:90` essay prose; the epi mediator is present but unnamed and not identified with `coker(ker f)`.

## Work to be done

- Define `abelian_coimage_obj`/`abelian_coimage := coker(ker f)` (a quotient object of the domain) with its epi structure, dual to the existing image.
- Prove the epi mediator `abelian_image_med` coincides (up to the canonical iso) with `coim f`, and construct the canonical coimage-to-image isomorphism `coim f → im f` with `f = m ∘ t ∘ e`.
- Prove the general recognition: any `f = m₁ ∘ t ∘ e₁` (`m₁` monic, `t` iso, `e₁` epi) has `m₁ ≡ im f`, `e₁ ≡ coim f`.
- Suggested module: extend `Structure/Abelian.v` (a `Structure/Abelian/Image.v` section).
- Donors: `Structure/Abelian.v` (`abelian_image`, `abelian_image_med`, `abelian_coker`, `abelian_kernel`), `Structure/Factorization.v` (`factorization_unique`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 def of image/coimage (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `abelian_coimage` and the canonical coimage-to-image iso.
- [ ] New/changed file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category <path>` compiles standalone.
- `Print Assumptions abelian_coimage_image_iso.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the coimage definition and the canonical iso match Mac Lane §VIII.3.

## Dependencies

None (extends the in-tree abelian image). Provides the coimage used by exact sequences (`maclane:VIII.3:def4`) and subquotients (`maclane:VIII.3:ex6`).

<!-- catalog: {"ids":["maclane:VIII.3:def2"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.3: Exact sequences and short exact sequences"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:def3, maclane:VIII.3:def4, maclane:VIII.3:def-short-right-left-exact]
deps_item_ids: [maclane:VIII.3:def2]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, book pp. 200–201, PDF pp. 208–209. Items: `maclane:VIII.3:def3` (exact at an object), `maclane:VIII.3:def4` (short exact sequence), `maclane:VIII.3:def-short-right-left-exact` (short right/left exact).

## Background

A composable pair `a → b → c` is exact at `b` when `im f = ker g` as subobjects of `b` (equivalently `coker f = coim g`), which classically means `g ∘ f = 0` and everything killed by `g` lies in the image of `f`; the diagram `0 → a → b → c → 0` is short exact when exact at all three objects (`f` monic, `g` epi, `f = ker g`, `g = coker f`), with the one-sided variants named short right/left exact. See [nLab: exact sequence](https://ncatlab.org/nlab/show/exact+sequence), [nLab: short exact sequence](https://ncatlab.org/nlab/show/short+exact+sequence), and [Wikipedia: Exact sequence](https://en.wikipedia.org/wiki/Exact_sequence).

## Current state in the library

ABSENT. The ingredients `abelian_image` (`Structure/Abelian.v:261`) and `IsKernel` (`Structure/Kernel.v:53`) exist, and the subobject comparison `sub_le` is available (`Theory/Subobject.v:55`), but there is no "exact at `b`" predicate (`im f = ker g` as subobjects), no short-exact-sequence record/predicate `0 → a → b → c → 0`, and no short right/left exact terminology. Every mathematical occurrence of "exact" in the tree is either the Coq tactic or an essay/citation.

## Work to be done

- Define `ExactAt f g` in an abelian category as the equality of subobjects `im f ≈ ker g` (with the equivalent `coker f ≈ coim g` proven), plus the classical characterization `g ∘ f ≈ 0 ∧ (∀ k, g ∘ k ≈ 0 → k factors through im f)`.
- Define `ShortExact f g` as exactness at all three positions of `0 → a → b → c → 0`, and prove the equivalent bundling "`f` monic, `g` epi, `f ≈ ker g`, `g ≈ coker f`".
- Define short right exact / short left exact and relate to `coker`/`ker`.
- Suggested module: `Structure/Abelian/Exact.v`.
- Donors: coimage (`maclane:VIII.3:def2`), `Structure/Abelian.v` (`abelian_image`), `Structure/Kernel.v` (`IsKernel`, `IsCokernel`), `Theory/Subobject.v` (`sub_le`, `sub_equiv_iff_mutual`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 defs of exactness (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `ExactAt`, `ShortExact`, and the characterization lemmas.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (exact sequences are flagship homological-algebra vocabulary).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Exact.v` compiles standalone.
- `Print Assumptions ShortExact.` and `Print Assumptions exact_at_char.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms exactness, short/short-left/short-right exactness match Mac Lane §VIII.3.

## Dependencies

Depends on: `maclane:VIII.3:def2` (coimage — for the `coker f = coim g` form of exactness). This is the reusable exact-sequence vocabulary that the diagram lemmas, exact functors, `Ses A`, and homology all build on.

<!-- catalog: {"ids":["maclane:VIII.3:def3","maclane:VIII.3:def4","maclane:VIII.3:def-short-right-left-exact"],"deps":["maclane:VIII.3:def2"]} -->

---8<---

---
title: "MacLane VIII.3: Exact and left-exact functors"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:def-exact-functor, maclane:VIII.3:def-left-exact-functor, maclane:VIII.3:ex1]
deps_item_ids: [maclane:VIII.3:def4, maclane:VIII.3:remark1]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, book pp. 201–202, PDF pp. 209–210. Items: `maclane:VIII.3:def-exact-functor`, `maclane:VIII.3:def-left-exact-functor`, `maclane:VIII.3:ex1`.

## Background

A functor between abelian categories is exact when it preserves all finite limits and colimits — equivalently, when it is additive and preserves kernels and cokernels — and it then carries exact sequences to exact sequences; it is left exact when it preserves finite limits (additive + preserves kernels), and an additive functor is exact iff it preserves short exact sequences. See [nLab: exact functor](https://ncatlab.org/nlab/show/exact+functor) and [Wikipedia: Exact functor](https://en.wikipedia.org/wiki/Exact_functor).

## Current state in the library

ABSENT for the specific notions. The nearest vocabulary — per-diagram `PreservesLimit`/`PreservesColimit` and global `Continuous`/`Cocontinuous` (`Structure/Limit/Preservation.v`) — is genuinely more general (all limits, not finite; not additive; never tied to abelian categories). There is no "exact functor", no "left exact functor", and no "exact ⟺ preserves short exact sequences" characterization. The base "additive functor" notion is filed for §I.8 as #264.

## Work to be done

- Define `ExactFunctor`/`LeftExactFunctor` between abelian categories as additive functors preserving kernels and cokernels (resp. kernels), and prove equivalence with preservation of finite limits/colimits (resp. finite limits).
- Prove exact functors carry exact sequences to exact sequences, and the biconditional "additive `T` is exact ⟺ `T` preserves short exact sequences" (Exercise 1).
- Suggested module: `Functor/Structure/Exact.v`.
- Donors: the additive-functor class (#264), exact sequences (`maclane:VIII.3:def4`), finite (co)completeness (`maclane:VIII.3:remark1`), `Structure/Limit/Preservation.v`, `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `ExactFunctor`, `LeftExactFunctor`, and the SES-preservation characterization.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Functor/Structure/Exact.v` compiles standalone.
- `Print Assumptions exact_iff_preserves_SES.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the exact/left-exact definitions and the SES characterization match Mac Lane §VIII.3.

## Dependencies

Depends on: #264 (additive functors — the base notion); `maclane:VIII.3:def4` (exact/short exact sequences); `maclane:VIII.3:remark1` (finite (co)completeness, so "preserves finite limits" is meaningful).

<!-- catalog: {"ids":["maclane:VIII.3:def-exact-functor","maclane:VIII.3:def-left-exact-functor","maclane:VIII.3:ex1"],"deps":["#264","maclane:VIII.3:def4","maclane:VIII.3:remark1"]} -->

---8<---

---
title: "MacLane VIII.3: The economical (Freyd–Schubert) axiomatization of abelian categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:remark-economical-axioms]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, book p. 201, PDF p. 209. Item: `maclane:VIII.3:remark-economical-axioms`.

## Background

Mac Lane records (attributing Freyd 1964 / Schubert 1970, proof omitted) that the abelian-group hom-enrichment need not be assumed: a category with a null object, kernels and cokernels for every arrow, every mono a kernel and every epi a cokernel, and merely binary products *and* coproducts, automatically admits an addition on each hom-set making it abelian — the additive enrichment is derivable from finite (co)products. See [nLab: abelian category](https://ncatlab.org/nlab/show/abelian+category) and [nLab: biproduct](https://ncatlab.org/nlab/show/semiadditive+category).

## Current state in the library

The *semiadditive* half is present: `bicartesian_preadditive` (`Structure/Semiadditive.v:573`) derives a commutative-monoid enrichment (convolution addition, Eckmann–Hilton commutativity/associativity) from a bicartesian category with a zero object and an *invertible* canonical comparison, and `biproduct_addition` (`Structure/Semiadditive.v:130`) realizes Mac Lane's formula (2.6). Gaps: (a) only a commutative *monoid* enrichment is derived, not an abelian *group* — negatives/subtraction are not derived (the `Additive` class takes `pneg` as primitive, `Structure/Additive.v:34`); (b) invertibility of the coproduct-to-product comparison is *assumed* here, whereas Freyd derives it from kernels/cokernels + normality; (c) there is no theorem "(null object, binary products+coproducts, all kernels/cokernels, every mono a kernel & every epi a cokernel) ⟹ Abelian".

## Work to be done

- Derive invertibility of the canonical comparison `a ⊔ b → a × b` from the abelian axioms (kernels/cokernels + normality), feeding `bicartesian_preadditive` without assuming it.
- Derive negatives (abelian-group enrichment) from the axioms, upgrading the semiadditive enrichment to `Additive`.
- Assemble the theorem: a category with a null object, binary products and coproducts, all kernels and cokernels, every mono a kernel and every epi a cokernel, is `Abelian` (enrichment derived, not assumed).
- Suggested module: `Structure/Abelian/Economical.v`.
- Donors: `Structure/Semiadditive.v` (`bicartesian_preadditive`, `conv`, `biproduct_addition`), `Structure/Abelian.v` (target), `Structure/Kernel.v` (normality), the group-upgrade issue `maclane:VIII.2:ex4`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 (Freyd–Schubert) (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the economical-axiomatization theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Economical.v` compiles standalone.
- `Print Assumptions abelian_from_economical_axioms.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the derivation of enrichment and comparison-invertibility matches Mac Lane §VIII.3's economical axiomatization.

## Dependencies

None filed. Builds on the in-tree semiadditivity machinery; complements the group-upgrade route `maclane:VIII.2:ex4`.

<!-- catalog: {"ids":["maclane:VIII.3:remark-economical-axioms"],"deps":[]} -->

---8<---

---
title: "MacLane VIII.3: (Finite) abelian groups are abelian; free abelian groups are not"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:ex3, maclane:VIII.3:ex4]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, Exercises 3 and 4, book p. 202, PDF p. 210. Items: `maclane:VIII.3:ex3` (free abelian groups not abelian), `maclane:VIII.3:ex4` (finite abelian groups form an abelian category).

## Background

The category of all abelian groups is the motivating abelian category; its full subcategory of finite abelian groups is again abelian, whereas the full subcategory of free abelian groups is not (it lacks the cokernels needed — e.g. multiplication by 2 on ℤ has no cokernel among free groups). See [nLab: Ab](https://ncatlab.org/nlab/show/Ab) and [Wikipedia: Category of abelian groups](https://en.wikipedia.org/wiki/Category_of_abelian_groups).

## Current state in the library

ABSENT. No concrete category of abelian groups exists in-tree (`Instance/CMon.v` is commutative *monoids*, which lack inverses; `Structure/Group.v` is *internal* group objects, not the concrete category `Ab`), so neither the abelian-ness of finite abelian groups nor the failure of abelian-ness for free abelian groups can be stated. The `Abelian` class is never instantiated on any concrete category.

## Work to be done

- Over the category of abelian groups (#256), form the full subcategory of finite abelian groups and prove it is `Abelian` (kernels, cokernels, biproducts, normality all inherited within finite groups).
- Form the full subcategory of free abelian groups and show it fails an abelian axiom (exhibit an arrow with no cokernel in the subcategory, or a mono that is not a kernel), i.e. it is not `Abelian`.
- Suggested module: `Instance/AbGroup/Abelian.v` (finite case) and a non-example lemma alongside.
- Donors: the category of abelian groups (#256), `Structure/Abelian.v` (the `Abelian` class), `Instance/Comp.v` (`Group`), `Instance/CMon.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 Ex 3/4 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` beyond enumerated instance-layer stdlib axioms (`docs/AXIOMS.md`).
- [ ] `Print Assumptions` reported for `FinAb_Abelian` and the free-abelian non-example.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Instance/AbGroup/Abelian.v` compiles standalone.
- `Print Assumptions FinAb_Abelian.` reviewed against `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the finite-abelian instance and the free-abelian non-example match Mac Lane §VIII.3 Exercises 3 and 4.

## Dependencies

Depends on: #256 (the category of abelian groups `Ab`, the ambient category for both subcategories).

<!-- catalog: {"ids":["maclane:VIII.3:ex3","maclane:VIII.3:ex4"],"deps":["#256"]} -->

---8<---

---
title: "MacLane VIII.3: Finitely generated modules over a left noetherian ring form an abelian category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:ex5]
deps_item_ids: []
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, Exercise 5, book p. 202, PDF p. 210. Item: `maclane:VIII.3:ex5`.

## Background

For a left noetherian ring `R`, the category of finitely generated left `R`-modules is abelian: finite generation is preserved by submodules (using the noetherian hypothesis), quotients, and finite biproducts, so kernels and cokernels of module maps stay finitely generated. See [nLab: Ab](https://ncatlab.org/nlab/show/Ab) and [Wikipedia: Noetherian ring](https://en.wikipedia.org/wiki/Noetherian_ring).

## Current state in the library

ABSENT. No rings, modules, or noetherian conditions are formalized in-tree; there is no `R`-Mod category (filed for §I.7 as #258) and thus no finitely-generated-module subcategory and no abelian instance on it.

## Work to be done

- Over the category of left `R`-modules (#258), formalize "finitely generated" and, assuming `R` left noetherian, the full subcategory of finitely generated modules.
- Prove this subcategory is `Abelian`: kernels/cokernels/biproducts of maps of finitely generated modules are again finitely generated (kernels via the noetherian hypothesis), with normality inherited.
- Suggested module: `Instance/Module/Noetherian.v`.
- Donors: the module category `R`-Mod (#258), `Structure/Abelian.v` (the `Abelian` class).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 Ex 5 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` beyond enumerated instance-layer stdlib axioms (`docs/AXIOMS.md`).
- [ ] `Print Assumptions` reported for the abelian instance on finitely generated modules.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Instance/Module/Noetherian.v` compiles standalone.
- `Print Assumptions fg_module_Abelian.` reviewed against `docs/AXIOMS.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the finitely-generated-module abelian instance matches Mac Lane §VIII.3 Exercise 5.

## Dependencies

Depends on: #258 (the module categories `R`-Mod — the ambient category for finitely generated modules).

<!-- catalog: {"ids":["maclane:VIII.3:ex5"],"deps":["#258"]} -->

---8<---

---
title: "MacLane VIII.3: Subquotients and the ker/im ≅ coim/coker isomorphism"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.3:ex6]
deps_item_ids: [maclane:VIII.3:def2]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.3, Exercise 6, book p. 202, PDF p. 210. Item: `maclane:VIII.3:ex6`.

## Background

For subobjects `u ≤ v` of an object `a` in an abelian category there is a quotient object `v/u` (agreeing with the usual notion in `Ab`); and for `g ∘ f = 0`, the subquotient `ker g / im f` is isomorphic to the dual object `coim g / coker f`. See [nLab: subquotient](https://ncatlab.org/nlab/show/subquotient) and [Wikipedia: Subquotient](https://en.wikipedia.org/wiki/Subquotient).

## Current state in the library

ABSENT. `Theory/Subobject.v` supplies the subobject preorder the exercise references — `sub_le u v` and `sub_equiv_iff_mutual` (`Theory/Subobject.v:55`, `:93`) — so the `u ≤ v` premise exists; but there is no quotient-object `v/u` construction and no `ker g / im f ≅ coim g / coker f` isomorphism. `Structure/Abelian.v` has `abelian_image` and cokernels but assembles no subquotient.

## Work to be done

- Define the quotient object `v/u` for subobjects `u ≤ v` of `a` (as the cokernel of the inclusion of `u` into `v`, or the image of the induced map), and verify it agrees with the module-level notion.
- Prove the isomorphism `ker g / im f ≅ coim g / coker f` for `g ∘ f = 0`.
- Suggested module: `Structure/Abelian/Subquotient.v`.
- Donors: coimage (`maclane:VIII.3:def2`), `Theory/Subobject.v` (`sub_le`), `Structure/Abelian.v` (`abelian_image`, `abelian_coker`, `abelian_kernel`), `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.3 Ex 6 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the subquotient and the `ker/im ≅ coim/coker` isomorphism.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Subquotient.v` compiles standalone.
- `Print Assumptions subquotient_iso.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the subquotient and the duality isomorphism match Mac Lane §VIII.3 Exercise 6.

## Dependencies

Depends on: `maclane:VIII.3:def2` (coimage — for the `coim g / coker f` side). Provides the subquotient used by homology (`maclane:VIII.4:def-homology-object`).

<!-- catalog: {"ids":["maclane:VIII.3:ex6"],"deps":["maclane:VIII.3:def2"]} -->

---8<---

---
title: "MacLane VIII.4: Members (pseudo-elements) and the diagram-chasing rules"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:def-member, maclane:VIII.4:thm3]
deps_item_ids: [maclane:VIII.4:prop2, maclane:VIII.3:def4]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4 (Diagram Lemmas), book pp. 204–205, PDF pp. 212–213. Items: `maclane:VIII.4:def-member` (member of an object; the `≡` relation), `maclane:VIII.4:thm3` (Theorem 3, the elementary rules).

## Background

A member of an object `a` is any arrow with codomain `a`; two members are equivalent (`x ≡ y`) when they agree after precomposition with suitable epimorphisms, giving each object a zero member and each member a negative. Theorem 3 lists the elementary rules that let one chase diagrams in any abelian category as if with elements: monic ⟺ reflects the zero member, monic ⟺ injective on members, epic ⟺ surjective on members, the zero-arrow test, the member characterization of exactness, and the subtraction rule. See [nLab: diagram chasing](https://ncatlab.org/nlab/show/diagram+chasing) and [nLab: abelian category](https://ncatlab.org/nlab/show/abelian+category).

## Current state in the library

The member apparatus is ABSENT; only categorical shadows of two of the six rules exist. `Monic f` is defined as left cancellation (`Theory/Morphisms.v:116`) — rule (ii) read with strict `≈`; the abelian vanishing test `monic_iff_kernel_pzero` (`Structure/Abelian.v:170`) is rule (i) read with `≈` for `≡`; `epic_iff_cokernel_pzero` (`Structure/Abelian.v:200`) is a *co*-vanishing test, a different statement from rule (iii) (epic = surjective on members). Gap: no notion of member (`x ∈ₘ a`), no `≡` equivalence, no member-classes, zero member, or negatives — no member file anywhere; hence Theorem 3 cannot be stated in its member form, and rules (iii), (iv), (v) (which also needs the "exact at" predicate), and (vi) are absent.

## Work to be done

- Define members of an object (arrows into `a`), the equivalence `x ≡ y :⟺ ∃ epis u,v, x ∘ u ≈ y ∘ v` (transitivity via pullbacks of epis, `maclane:VIII.4:prop2`), member-classes, the zero member, and negatives; and the action of an arrow on members respecting `≡`.
- Prove Theorem 3's six rules over the member calculus: (i) monic ⟺ `f x ≡ 0 ⟹ x ≡ 0`; (ii) monic ⟺ injective on members; (iii) epic ⟺ surjective on members; (iv) zero-arrow test; (v) exactness at `b` via members (uses the exact-at predicate); (vi) subtraction.
- Suggested module: `Structure/Abelian/Member.v`.
- Donors: pullbacks of epis (`maclane:VIII.4:prop2`), exact sequences (`maclane:VIII.3:def4`), `Structure/Abelian.v` (`monic_iff_kernel_pzero`, `epic_iff_cokernel_pzero`), `Theory/Morphisms.v` (`Monic`, `Epic`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 def of member + Theorem 3 (setoid `≈`/`≡`; never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the `≡` relation and all six Theorem-3 rules.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (the member calculus is the flagship diagram-chasing tool).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Member.v` compiles standalone.
- `Print Assumptions member_equiv.` and `Print Assumptions member_rules.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the member relation and the six rules match Mac Lane §VIII.4 Theorem 3.

## Dependencies

Depends on: `maclane:VIII.4:prop2` (pullbacks of epis — for transitivity of `≡`); `maclane:VIII.3:def4` (exactness — for rule (v)). This member calculus is the reusable engine for the five lemma and the snake lemma.

<!-- catalog: {"ids":["maclane:VIII.4:def-member","maclane:VIII.4:thm3"],"deps":["maclane:VIII.4:prop2","maclane:VIII.3:def4"]} -->

---8<---

---
title: "MacLane VIII.4: Pullbacks of epimorphisms and of short exact sequences"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:prop2, maclane:VIII.4:remark-ext-bifunctor]
deps_item_ids: [maclane:VIII.3:remark1, maclane:VIII.3:def4]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, Proposition 2 (book pp. 203–204, PDF pp. 211–212) and the following remark (book p. 203, PDF p. 211). Items: `maclane:VIII.4:prop2`, `maclane:VIII.4:remark-ext-bifunctor`.

## Background

In an abelian category the pullback of an epimorphism along any arrow is again an epimorphism, and the kernel of the original epi factors through the kernel of the pulled-back epi; consequently pulling a short exact sequence back along an arrow into its right-hand end yields a short exact sequence (the operation whose classes, with the dual pushout, organize `Ext(c,a)` into a bifunctor — a topic Mac Lane defers). See [nLab: regular epimorphism](https://ncatlab.org/nlab/show/regular+epimorphism), [nLab: Ext](https://ncatlab.org/nlab/show/Ext), and [Wikipedia: Pullback (category theory)](https://en.wikipedia.org/wiki/Pullback_(category_theory)).

## Current state in the library

ABSENT. Regular-epi pullback stability exists only as a *field* (assumed axiom) of the `Regular` class (`Structure/Regular.v:25`, `:81`), never derived for abelian categories (there is no `Abelian ⟹ Regular` instance and `Abelian` carries no `HasPullbacks`); `monic_pullback_stable` (`Theory/Morphisms/Stability.v:226`) is the companion mono statement (Lemma V.7), not the epi claim. Abelian epis are regular via `cokernel_regular_epi`/`abelian_epic_normal` (`Structure/Abelian.v:427`), but with no pullbacks provided by `Abelian` the proposition is neither stated nor derivable. Mac Lane himself defers `Ext` ("not developed here").

## Work to be done

- Using the finite (co)completeness of abelian categories (`maclane:VIII.3:remark1`, which supplies pullbacks/pushouts), prove that the pullback of an epi is an epi, and the kernel factorization `k = g' ∘ k'`.
- Derive the corollary: the pullback of a short exact sequence along an arrow into its right end is short exact (and dually for pushouts).
- Record the `Ext(c,a)` bifunctor as an explicitly deferred extension (Mac Lane defers it); the required concrete deliverable is the pullback/pushout transport of short exact sequences, not the full `Ext` development.
- Suggested module: `Structure/Abelian/Pullback.v`.
- Donors: finite (co)completeness (`maclane:VIII.3:remark1`), short exact sequences (`maclane:VIII.3:def4`), `Structure/Regular.v` (`RegularEpi`), `Structure/Abelian.v` (`cokernel_regular_epi`), `Theory/Morphisms/Stability.v` (`monic_pullback_stable`), `Structure/Pullback.v`, `Structure/Pushout.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 Prop 2 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the pullback-of-epi theorem and the pullback-of-SES corollary.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Pullback.v` compiles standalone.
- `Print Assumptions abelian_pullback_epi.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the pullback-of-epi and pullback-of-SES results match Mac Lane §VIII.4 Proposition 2.

## Dependencies

Depends on: `maclane:VIII.3:remark1` (finite (co)completeness — supplies pullbacks/pushouts in an abelian category); `maclane:VIII.3:def4` (short exact sequences — for the pullback-of-SES corollary). Required by the member calculus (`maclane:VIII.4:def-member`) and the snake lemma.

<!-- catalog: {"ids":["maclane:VIII.4:prop2","maclane:VIII.4:remark-ext-bifunctor"],"deps":["maclane:VIII.3:remark1","maclane:VIII.3:def4"]} -->

---8<---

---
title: "MacLane VIII.4: The additive category Ses A of short exact sequences"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:def-morphism-ses, maclane:VIII.4:construction-ses, maclane:VIII.4:ex7]
deps_item_ids: [maclane:VIII.3:def4]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, book p. 202 (PDF p. 210) and Exercise 7 (book p. 208, PDF p. 216). Items: `maclane:VIII.4:def-morphism-ses` (morphism of short exact sequences), `maclane:VIII.4:construction-ses` (the category `Ses A`), `maclane:VIII.4:ex7` (`Ses A` is not in general abelian).

## Background

A morphism of short exact sequences is a triple `⟨f,g,h⟩` making the two-row ladder commute; the short exact sequences of an abelian category `A` and these morphisms form a category `Ses A`, which is additive but in general not abelian. See [nLab: short exact sequence](https://ncatlab.org/nlab/show/short+exact+sequence) and [Wikipedia: Exact sequence](https://en.wikipedia.org/wiki/Exact_sequence).

## Current state in the library

ABSENT. With no short-exact-sequence notion in-tree there is no morphism-of-SES type, no category `Ses A`, and no additivity/non-abelianness statement (`Construction/Arrow.v` carries no such content).

## Work to be done

- Define a morphism `⟨f,g,h⟩` between short exact sequences (the commuting ladder) and assemble the category `Ses A` (objects = short exact sequences of `A`, arrows = triples), with its `Category` and `Additive` instances (componentwise addition, componentwise zero object and biproducts).
- Prove `Ses A` is additive, and exhibit a witness showing it is not abelian in general (Exercise 7).
- Suggested module: `Construction/Ses.v`.
- Donors: short exact sequences (`maclane:VIII.3:def4`), `Structure/Additive.v`, `Construction/Arrow.v` / `Construction/Comma.v` (ladder-category patterns), `Structure/Abelian.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `Ses`, its `Additive` instance, and the non-abelian witness.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Construction/Ses.v` compiles standalone.
- `Print Assumptions Ses_Additive.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms `Ses A`, its additivity, and its non-abelianness match Mac Lane §VIII.4 and Exercise 7.

## Dependencies

Depends on: `maclane:VIII.3:def4` (short exact sequences — the objects of `Ses A`). The morphism-of-SES notion is reused by the short five lemma and the snake lemma.

<!-- catalog: {"ids":["maclane:VIII.4:def-morphism-ses","maclane:VIII.4:construction-ses","maclane:VIII.4:ex7"],"deps":["maclane:VIII.3:def4"]} -->

---8<---

---
title: "MacLane VIII.4: The short five lemma and the five lemma"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:lem1, maclane:VIII.4:lem4, maclane:VIII.4:ex1, maclane:VIII.4:ex2]
deps_item_ids: [maclane:VIII.4:def-member, maclane:VIII.3:def4, maclane:VIII.4:def-morphism-ses]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, Lemma 1 (short five lemma, book pp. 202–203, PDF pp. 210–211), Lemma 4 (five lemma, book pp. 205–206, PDF pp. 213–214), Exercises 1 and 2 (book p. 208, PDF p. 216). Items: `maclane:VIII.4:lem1`, `maclane:VIII.4:lem4`, `maclane:VIII.4:ex1`, `maclane:VIII.4:ex2`.

## Background

The short five lemma: in a morphism `⟨f,g,h⟩` of short exact sequences, if `f` and `h` are monic (resp. epi) then `g` is monic (resp. epi). The five lemma: in a ladder of two five-term rows with exact rows, if the four outer verticals are isomorphisms then the middle one is; the exercises sharpen the hypotheses (monic half from `f₂,f₄` monic and `f₁` epi) and give the epi half by a member chase. See [nLab: five lemma](https://ncatlab.org/nlab/show/five+lemma) and [Wikipedia: Five lemma](https://en.wikipedia.org/wiki/Five_lemma).

## Current state in the library

ABSENT. There is no five lemma or short five lemma in-tree, and no exact rows over which to state them (every "snake"/"five" token in the tree is the compact-closed zigzag identity or the Coq tactic).

## Work to be done

- Prove the short five lemma over a morphism of short exact sequences (`maclane:VIII.4:def-morphism-ses`), both the monic and the epi conclusion.
- Prove the five lemma over five-term ladders with exact rows, via the member calculus; and the two exercise refinements (minimal hypotheses for `f₃` monic; `f₃` epi by a member chase using the subtraction rule).
- Suggested module: `Structure/Abelian/FiveLemma.v`.
- Donors: the member calculus (`maclane:VIII.4:def-member`, Theorem 3 rules), exact sequences (`maclane:VIII.3:def4`), the morphism-of-SES notion (`maclane:VIII.4:def-morphism-ses`), `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 Lemmas 1 and 4 and Exercises 1–2 (setoid `≈`/`≡`; never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `short_five_lemma` and `five_lemma`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (the five lemma is a flagship diagram lemma).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/FiveLemma.v` compiles standalone.
- `Print Assumptions five_lemma.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the (short) five lemma and its refinements match Mac Lane §VIII.4.

## Dependencies

Depends on: `maclane:VIII.4:def-member` (the member calculus / Theorem 3); `maclane:VIII.3:def4` (exact/short exact sequences); `maclane:VIII.4:def-morphism-ses` (morphism of short exact sequences, for the short five lemma).

<!-- catalog: {"ids":["maclane:VIII.4:lem1","maclane:VIII.4:lem4","maclane:VIII.4:ex1","maclane:VIII.4:ex2"],"deps":["maclane:VIII.4:def-member","maclane:VIII.3:def4","maclane:VIII.4:def-morphism-ses"]} -->

---8<---

---
title: "MacLane VIII.4: The snake lemma (the ker–coker exact sequence)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:construction-ker-coker-rows, maclane:VIII.4:lem5, maclane:VIII.4:ex3, maclane:VIII.4:ex4]
deps_item_ids: [maclane:VIII.4:def-member, maclane:VIII.4:prop2, maclane:VIII.3:def4, maclane:VIII.4:def-morphism-ses]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, the induced kernel/cokernel rows (book p. 206, PDF p. 214), Lemma 5 (book pp. 206–208, PDF pp. 214–216), Exercises 3 and 4 (book p. 208, PDF p. 216). Items: `maclane:VIII.4:construction-ker-coker-rows`, `maclane:VIII.4:lem5`, `maclane:VIII.4:ex3`, `maclane:VIII.4:ex4`.

## Background

From a morphism `⟨f,g,h⟩` of short exact sequences, adjoining kernels and cokernels yields exact kernel and cokernel rows; the snake lemma supplies a connecting arrow `δ : Keh → Cof` making the six-term ker–coker sequence `0 → Kef → Keg → Keh → Cof → Cog → Coh → 0` exact, with `δ` built from a pullback and a pushout and natural in the morphism of short exact sequences. See [nLab: snake lemma](https://ncatlab.org/nlab/show/snake+lemma) and [Wikipedia: Snake lemma](https://en.wikipedia.org/wiki/Snake_lemma).

## Current state in the library

ABSENT. There is no ker–coker row construction, no connecting/boundary morphism `δ`, and no six-term sequence; `Structure/Pullback.v`/`Structure/Pushout.v` exist but `δ` is not built from them, and no exactness predicate is available.

## Work to be done

- Construct the induced kernel row `Kef → Keg → Keh` and cokernel row `Cof → Cog → Coh` from a morphism of short exact sequences, and prove their partial exactness (member chase).
- Construct the connecting arrow `δ : Keh → Cof` via the pullback of `e` and `ker h` and the pushout of `coker f` and `m'` (using pullbacks of epis, `maclane:VIII.4:prop2`), and prove the full six-term ker–coker sequence exact (Exercise 3 completes the exactness).
- Prove `δ` is natural (Exercise 4): a natural transformation on the category of morphisms of short exact sequences.
- Suggested module: `Structure/Abelian/Snake.v`.
- Donors: the member calculus (`maclane:VIII.4:def-member`), pullbacks of epis (`maclane:VIII.4:prop2`), exact sequences (`maclane:VIII.3:def4`), the morphism-of-SES notion (`maclane:VIII.4:def-morphism-ses`), `Structure/Pullback.v`, `Structure/Pushout.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 Lemma 5 (setoid `≈`/`≡`; never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `snake_connecting` and `snake_lemma` (six-term exactness) and the naturality of `δ`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (the snake lemma is a flagship result).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Snake.v` compiles standalone.
- `Print Assumptions snake_lemma.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the connecting map, the six-term exact sequence, and its naturality match Mac Lane §VIII.4 Lemma 5 and Exercises 3–4.

## Dependencies

Depends on: `maclane:VIII.4:def-member` (member calculus); `maclane:VIII.4:prop2` (pullbacks of epis — for building `δ`); `maclane:VIII.3:def4` (exact/short exact sequences); `maclane:VIII.4:def-morphism-ses` (morphism of short exact sequences).

<!-- catalog: {"ids":["maclane:VIII.4:construction-ker-coker-rows","maclane:VIII.4:lem5","maclane:VIII.4:ex3","maclane:VIII.4:ex4"],"deps":["maclane:VIII.4:def-member","maclane:VIII.4:prop2","maclane:VIII.3:def4","maclane:VIII.4:def-morphism-ses"]} -->

---8<---

---
title: "MacLane VIII.4: The 3×3 lemma and the exact sequence of a composite"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:ex5, maclane:VIII.4:ex6]
deps_item_ids: [maclane:VIII.4:lem5]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, Exercises 5 and 6, book p. 208, PDF p. 216. Items: `maclane:VIII.4:ex5` (3×3 lemma and middle 3×3 lemma), `maclane:VIII.4:ex6` (six-term sequence of a composite).

## Background

Two standard consequences of the ker–coker machinery: the 3×3 lemma (in a bordered-by-zeros commutative 3×3 diagram, if all columns and two of the rows are short exact then so is the third row; likewise the middle 3×3 lemma), and, for a composite `gf`, the six-term exact sequence `0 → Kef → Ke(gf) → Keg → Cof → Co(gf) → Cog → 0`. See [nLab: 3x3 lemma](https://ncatlab.org/nlab/show/nine+lemma) and [Wikipedia: Nine lemma](https://en.wikipedia.org/wiki/Nine_lemma).

## Current state in the library

ABSENT. There is no 3×3/nine lemma and no six-term composite sequence; kernels and cokernels of `f`, `g`, `gf` exist only as the `Structure/Kernel.v` API, with no exactness predicate and no assembled sequences.

## Work to be done

- Prove the 3×3 lemma and the middle 3×3 lemma, both directly and (for Exercise 5(b)) as a consequence of the snake/ker–coker sequence.
- Prove the six-term exact sequence of a composite `gf`.
- Suggested module: `Structure/Abelian/NineLemma.v` (or extend `Structure/Abelian/Snake.v`).
- Donors: the snake lemma / ker–coker sequence (`maclane:VIII.4:lem5`), exact sequences, the member calculus, `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 Ex 5/6 (setoid `≈`/`≡`; never `=` on morphisms).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for the 3×3 lemma and the composite six-term sequence.
- [ ] New/changed file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/NineLemma.v` compiles standalone.
- `Print Assumptions nine_lemma.` and `Print Assumptions composite_ker_coker_sequence.` print "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the 3×3 lemma and the composite exact sequence match Mac Lane §VIII.4 Exercises 5 and 6.

## Dependencies

Depends on: `maclane:VIII.4:lem5` (the snake / ker–coker exact sequence, from which both consequences follow).

<!-- catalog: {"ids":["maclane:VIII.4:ex5","maclane:VIII.4:ex6"],"deps":["maclane:VIII.4:lem5"]} -->

---8<---

---
title: "MacLane VIII.4: Chain complexes and homology objects"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:def-chain-complex, maclane:VIII.4:def-homology-object]
deps_item_ids: [maclane:VIII.3:ex6]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, book p. 202, PDF p. 210. Items: `maclane:VIII.4:def-chain-complex`, `maclane:VIII.4:def-homology-object`.

## Background

In an abelian category a chain complex is a sequence of composable arrows with successive composites zero (`∂ₙ ∘ ∂ₙ₊₁ = 0`), and its `n`-th homology object `Hₙ = Ker(∂ₙ) / Im(∂ₙ₊₁)` measures the deviation from exactness at `cₙ`, using the subquotient construction. See [nLab: chain complex](https://ncatlab.org/nlab/show/chain+complex) and [Wikipedia: Chain complex](https://en.wikipedia.org/wiki/Chain_complex).

## Current state in the library

ABSENT. `Construction/Chain.v` is the initial-algebra ω-chain of an endofunctor (`0 → F0 → F²0 → …`), not a chain complex — it has no `∂ ∘ ∂ = 0` condition. There is no homology object; every "homology"/"chain complex" occurrence in the tree is background-essay prose.

## Work to be done

- Define a chain complex in an abelian category (an `ℤ`- or `ℕ`-indexed family of objects and boundary maps with `∂ₙ ∘ ∂ₙ₊₁ ≈ 0`, using `zero_mor`), and the dual cochain complex.
- Define the `n`-th homology object `Hₙ c := Ker(∂ₙ) / Im(∂ₙ₊₁)` via the subquotient (`maclane:VIII.3:ex6`), and prove it well defined up to iso.
- Suggested module: `Structure/Abelian/Homology.v`.
- Donors: subquotients (`maclane:VIII.3:ex6`), `Structure/Abelian.v` (`abelian_image`, kernels), `Structure/Kernel.v`.

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 def of chain complex / homology (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` (core-theory zero-axiom scope).
- [ ] `Print Assumptions` closed for `ChainComplex` and `homology_obj`.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (homology is flagship homological algebra).
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Homology.v` compiles standalone.
- `Print Assumptions homology_obj.` prints "Closed under the global context".
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the chain-complex and homology definitions match Mac Lane §VIII.4.

## Dependencies

Depends on: `maclane:VIII.3:ex6` (subquotients — `Hₙ` is the subquotient `Ker(∂ₙ)/Im(∂ₙ₊₁)`).

<!-- catalog: {"ids":["maclane:VIII.4:def-chain-complex","maclane:VIII.4:def-homology-object"],"deps":["maclane:VIII.3:ex6"]} -->

---8<---

---
title: "MacLane VIII.4: The Freyd–Mitchell embedding theorem"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:VIII.4:remark-embedding]
deps_item_ids: [maclane:VIII.3:def-exact-functor]
deps_pending: []
---

## Source

Mac Lane, *CWM*, 2nd ed., §VIII.4, chapter-end Notes, book p. 209, PDF p. 217. Item: `maclane:VIII.4:remark-embedding`.

## Background

The Lubkin–Heron–Freyd–Mitchell embedding theorem: every small abelian category admits a faithful exact functor into `Ab`, and a full and faithful exact functor into `R`-Mod for a suitable ring `R`; consequently the abelian-category diagram lemmas can be reduced to the case of modules. See [nLab: Freyd–Mitchell embedding theorem](https://ncatlab.org/nlab/show/Freyd-Mitchell+embedding+theorem) and [Wikipedia: Mitchell's embedding theorem](https://en.wikipedia.org/wiki/Mitchell%27s_embedding_theorem).

## Current state in the library

ABSENT. Freyd–Mitchell appears only in the `Structure/Abelian.v` background-essay comments (`Structure/Abelian.v:40`, `:51`, `:109`–`111`, `:345`) as the classical warrant for diagram chasing, never as a formalized theorem; no "exact functor" definition and no `Ab`/`R`-Mod target category exist in-tree. The result is meaningfully formalizable (the library is universe-polymorphic), so this is ABSENT rather than out of scope.

## Work to be done

- State the theorem: for a small abelian category `A`, a faithful exact functor `A → Ab` and a full and faithful exact functor `A → R`-Mod for a suitable ring `R`.
- A full formalization is a substantial flagship undertaking; at minimum, state the theorem precisely over the exact-functor vocabulary (`maclane:VIII.3:def-exact-functor`) and the module category (#258), and record it (with the in-tree diagram lemmas proven directly) as a parametric/conditional target per `docs/INHABITATION.md` conventions if a full constructive proof is deferred.
- Suggested module: `Structure/Abelian/Embedding.v`.
- Donors: exact functors (`maclane:VIII.3:def-exact-functor`), the module category `R`-Mod (#258), `Structure/Abelian.v`, full/faithful functor vocabulary (`Theory/Functor.v`).

## Definition of Done

- [ ] Statement faithful to Mac Lane §VIII.4 Notes (setoid `≈`; never `=`).
- [ ] No `Admitted`/`admit`/`Axiom` in any completed proof (core-theory zero-axiom scope); if stated conditionally, record the hypothesis honestly per `docs/INHABITATION.md`.
- [ ] `Print Assumptions` reported for the embedding statement / any proven fragment.
- [ ] New file registered in `_CoqProject`.
- [ ] `make` green on Rocq 9.1; builds on Coq 8.19/8.20.
- [ ] CLAUDE.md Key Files index updated (Freyd–Mitchell is a flagship theorem); `docs/INHABITATION.md` updated if stated conditionally.
- [ ] `make todo` adds no new hits.

## Verification

- `coqc -R . Category Structure/Abelian/Embedding.v` compiles standalone.
- `Print Assumptions freyd_mitchell_embedding.` reviewed against `docs/AXIOMS.md`/`docs/INHABITATION.md`.
- `nix build .#category-theory_9_1` / `.#category-theory_8_20` succeed.
- Reviewer confirms the embedding statement matches Mac Lane §VIII.4 Notes (small abelian → `Ab` faithful exact, → `R`-Mod full faithful exact).

## Dependencies

Depends on: `maclane:VIII.3:def-exact-functor` (exact functors — the embedding is by exact functors); #258 (the module categories `R`-Mod — the embedding target).

<!-- catalog: {"ids":["maclane:VIII.4:remark-embedding"],"deps":["maclane:VIII.3:def-exact-functor","#258"]} -->





```yaml
title: "Awodey 9.1/9.9 Ex 3: Binary products and coproducts from an adjoint to the diagonal functor"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.1:example2, awodey:9:ex3]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, Chapter 9 "Adjoints".

- §9.1, Example 9.2 — printed pp. 216–217, PDF pp. 225–226 (`awodey:9.1:example2`).
- §9.9, Exercise 3 — printed p. 262, PDF p. 271 (`awodey:9:ex3`).

## Background

The diagonal functor Δ : C ⟶ C × C sends an object to the pair (c, c) and an
arrow to (f, f); the book's point is that Δ *has a right adjoint exactly when*
C has binary products, and dually a left adjoint exactly when C has binary
coproducts — so the product and coproduct universal properties are not merely
*witnessed by* adjunctions, they are *equivalent to* them. See
[nLab: diagonal functor](https://ncatlab.org/nlab/show/diagonal+functor) and
[nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor).

## Current state in the library

Only the "if" direction exists, and only for products.

- `Adjunction/Diagonal/Product.v:36` —
  `Program Instance Diagonal_Product_Adjunction (C : Category) \`{@Cartesian C} : Diagonal_Product C ⊣ ×(C)`.
  The hypothesis `{@Cartesian C}` is taken up front, so this is products ⇒ adjunction.
- `Adjunction/GAFT/Examples.v:65` `diagonal_unique` and `:121`
  `diagonal_product_via_gaft_is_diagonal` reconstruct the same adjunction through
  GAFT; that section also opens with `Context \`{@Cartesian C}`, so it likewise
  assumes products.
- `Structure/Limit/Cartesian.v:39` —
  `Theorem Cartesian_Limit (C : Category) : (∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C`
  is a genuine biconditional, but it is stated over limits of two-object discrete
  diagrams, **not** over the existence of a right adjoint to the diagonal. The
  bridge from one to the other is itself unformalized.
- `Functor/Diagonal.v:78` `Diagonal_Product_Two` relates `Diagonal_Product C` to
  `Diagonal Two_Discrete` — this is the book's "C² for a two-element index"
  identification and is the natural hinge for the converse.

Precise gaps:

1. There is no statement of the form
   `(∃ R : C ∏ C ⟶ C, Diagonal_Product C ⊣ R) → @Cartesian C`.
2. Nothing states the coproduct half at all, in either direction:
   `Adjunction/Diagonal/` contains only `Product.v`, and
   `Functor/Coproduct.v:61` `CoproductFunctor : C ∐ C ⟶ C` is the codiagonal
   *out of the coproduct category*, whose own header (lines 24–30) disclaims
   being the cocartesian codiagonal. There is no internal binary-coproduct
   bifunctor `C ∏ C ⟶ C` anywhere.
3. `Structure/Limit.v:80–83` asserts the adjoint reading of limits and colimits
   as background prose without disclosing that it is unformalized in-tree.

## Work to be done

Suggested module paths: extend `Adjunction/Diagonal/Product.v`; add
`Functor/Coproduct/Internal.v` (mirroring `Functor/Product/Internal.v`) and
`Adjunction/Diagonal/Coproduct.v`.

- Define the internal binary-coproduct bifunctor `+(C) : C ∏ C ⟶ C` for
  `{@Cocartesian C}`, mirroring `InternalProductFunctor`.
- Prove `Coproduct_Diagonal_Adjunction : +(C) ⊣ Diagonal_Product C`. In-tree
  donors make this cheap: `Structure/Cocartesian.v:115` defines
  `Cocartesian C := @Cartesian (C^op)`, so instantiating
  `Diagonal_Product_Adjunction` at `C^op` and transporting along
  `Adjunction/Opposite.v:34` `Opposite_Adjunction` gives the statement, modulo
  the identification of `(C^op ∏ C^op)^op` with `C ∏ C` (which should be proved
  as a named `Isomorphism` in `Cat`, since it will be reused).
- Prove the two converses:
  `Cartesian_of_diagonal_right_adjoint : ∀ R, Diagonal_Product C ⊣ R → @Cartesian C`
  and its dual. The product data is read off the counit: the two components of
  `ε_(x,y) : Δ (R (x,y)) ~> (x, y)` are the projections, and the transpose
  `⌈−⌉` supplies `fork`, with `ump_products` from `adj_univ_impl`
  (`Theory/Adjunction.v:248`).
- Record the resulting biconditionals as named theorems and relate them to the
  limit-form biconditional `Cartesian_Limit` through `Diagonal_Product_Two`.
- Fix the background prose at `Structure/Limit.v:80–83` so it discloses which
  half of the adjoint reading is actually formalized.

Exercise 3's last clause (both adjoints of Δ : Sets ⟶ Sets^J for a general small
J) is the general-index sandwich and belongs to the already-filed issue named
under Dependencies; it is out of scope here.

## Definition of Done

- [ ] The two biconditionals are stated and proved for products and coproducts,
      matching Awodey §9.1 Example 9.2 (setoid `≈` discipline throughout; never
      `=` on morphisms)
- [ ] `+(C) : C ∏ C ⟶ C` exists as a bona fide bifunctor with `Proper` instances
- [ ] The dualization lemma `(C^op ∏ C^op)^op ≅ C ∏ C` is named and reusable
- [ ] `Structure/Limit.v:80–83` header prose corrected to disclose what is (and
      is not) formalized about the adjoint reading of (co)limits
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` reports "Closed under the global context" for each
      principal artifact (`Coproduct_Diagonal_Adjunction`,
      `Cartesian_of_diagonal_right_adjoint`, and its dual)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated if the coproduct adjunction is
      indexed alongside `Adjunction/Diagonal/Product.v`

## Verification

```bash
coqc -R . Category Functor/Coproduct/Internal.v
coqc -R . Category Adjunction/Diagonal/Coproduct.v
coqc -R . Category Adjunction/Diagonal/Product.v

coqtop -R . Category -l Adjunction/Diagonal/Coproduct.v <<< \
  'Print Assumptions Coproduct_Diagonal_Adjunction.'
coqtop -R . Category -l Adjunction/Diagonal/Product.v <<< \
  'Print Assumptions Cartesian_of_diagonal_right_adjoint.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: the statement matches Awodey §9.1 Example 9.2 as a
biconditional (not merely the "if" half); the coproduct half is genuinely dual
and not a re-proof; no morphism equation is stated with `=`.

## Dependencies

Depends on: #351
Depends on: #353

<!-- catalog: {"ids":["awodey:9.1:example2","awodey:9:ex3"],"deps":["#351","#353"]} -->

---8<---

```yaml
title: "Awodey 9.1: The lower-set completion is left adjoint to the forgetful functor from cocomplete posets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.1:example3]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.1, Example 9.3 — printed pp. 217–218, PDF
pp. 226–227 (`awodey:9.1:example3`).

## Background

For a poset P, the poset Low(P) of downward-closed subsets ordered by inclusion
is cocomplete (joins are unions), and the principal-down-set map
P ⟶ Low(P) exhibits Low(P) as the *free* cocomplete poset on P: every monotone
map from P into a cocomplete poset extends uniquely along it by a join-preserving
map. Equivalently, Low is left adjoint to the forgetful functor from cocomplete
posets and join-preserving maps to posets and monotone maps. See
[nLab: lower set](https://ncatlab.org/nlab/show/lower+set) and
[nLab: free cocompletion](https://ncatlab.org/nlab/show/free+cocompletion).

## Current state in the library

Nothing of this example exists.

- There is no category whose *objects* are posets: `Instance/Poset.v:116`
  defines `Poset` as the thin category built **from one** poset (a bare alias
  for `Instance/Proset.v:33`'s `Proset`), and its header at line 21 mentions
  "`Pos`, the category of posets" only as an aspiration.
- There is no notion of a cocomplete poset, join-semilattice or sup-lattice:
  `Structure/Complete.v:115,119` define `Complete`/`Cocomplete` only as
  `∀ D F, Limit F` / `Colimit F` for categories, and no category anywhere in the
  tree is exhibited as complete or cocomplete.
- Lower sets, down-sets and downward-closed subsets appear only as header prose
  (`Theory/Sheaf.v:117`, `Instance/Fun.v:63`, `Construction/Slice.v:81`,
  `Construction/Day.v:111`); there is no definition, lemma or instance.
- "Cocompletion" occurs three times in the tree, all in comment prose; no
  theorem asserts any construction is a free cocompletion.

## Work to be done

Suggested module paths: `Instance/Pos/LowerSets.v` (or, if the reflector is
developed over the general thin-category machinery, `Construction/LowerSets.v`),
building on whatever `Pos` and `Low(P)` land as under the dependencies below.

- Define the category `CPos` of cocomplete posets and join-preserving monotone
  maps, and its forgetful functor `CPos_Forget : CPos ⟶ Pos`.
- Show `Low(P)` is cocomplete: arbitrary joins are unions of down-sets.
- Construct the left adjoint `Low : Pos ⟶ CPos` with unit the
  principal-down-set embedding `p ↦ ↓p`, and prove the adjunction
  `Low ⊣ CPos_Forget`.
- Preferred route, since it keeps the library's existing shape: build the
  pointwise universal arrow with `Theory/Universal/Arrow.v:158`
  `universal_arrow_from_UMP` (a monotone map P ⟶ U(Q) extends to a unique
  join-preserving `Low(P) ⟶ Q` by `S ↦ ⋁_{p ∈ S} f p`), then assemble with
  `Theory/Universal/Arrow.v:214` `AdjunctionFromUniversalArrows`. This mirrors
  exactly how `Construction/Free/Quiver.v:518,550` builds the free-category
  adjunction and reuses that file as a template.
- Record the thin-category degeneracy explicitly: because `Instance/Proset.v`'s
  hom-setoid is `equiv _ _ := True`, the adjunction's hom-setoid isomorphism is
  definitionally the two-way rule `Low(P) ≤ Q ⟺ P ≤ U Q`.

## Definition of Done

- [ ] `CPos`, `CPos_Forget`, `Low` and `Low ⊣ CPos_Forget` are defined and
      proved, matching Awodey §9.1 Example 9.3 (setoid `≈` discipline; never `=`
      on morphisms)
- [ ] Cocompleteness of `Low(P)` is proved, not assumed
- [ ] The unit is shown to be the principal-down-set embedding
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed under the global context for `Low`,
      `CPos_Forget` and the adjunction
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated (this is the library's first
      free-cocompletion theorem and its first non-trivial order-theoretic
      adjunction)

## Verification

```bash
coqc -R . Category Instance/Pos/LowerSets.v

coqtop -R . Category -l Instance/Pos/LowerSets.v <<< \
  'Print Assumptions Low_Forgetful_Adjunction.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: the statement matches Awodey §9.1 Example 9.3; the adjunction
is between *categories of posets*, not between the thin categories of two fixed
posets; joins in `Low(P)` are proved to be unions rather than postulated.

## Dependencies

Depends on: #641
Depends on: #714
Depends on: #684

<!-- catalog: {"ids":["awodey:9.1:example3"],"deps":["#641","#714","#684"]} -->

---8<---

```yaml
title: "Awodey 9.2/9.8: Recovering universal arrows from an adjunction — each unit component is initial in the comma category"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.2:prop4, awodey:9.8:construction-comma-x-u]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, Chapter 9 "Adjoints".

- §9.2, Proposition 9.4 — printed pp. 218–221, PDF pp. 227–230
  (`awodey:9.2:prop4`).
- §9.8, the comma construction (X ↓ U) and its initial-object criterion —
  printed p. 253, PDF p. 262 (`awodey:9.8:construction-comma-x-u`).

## Background

The two standard presentations of an adjunction — a unit whose components are
universal arrows, and a hom-set bijection natural in both arguments — are
equivalent, and the equivalence is carried by the formulas φ(g) = U(g) ∘ η and
η = φ(1). Read comma-categorically: U has a left adjoint exactly when each
comma category (X ↓ U) has an initial object, that initial object being
(F X, η_X). See
[nLab: universal arrow](https://ncatlab.org/nlab/show/universal+arrow) and
[nLab: comma category](https://ncatlab.org/nlab/show/comma+category).

## Current state in the library

Everything except the direction *from* an adjunction *back to* universal arrows.

- `Theory/Adjunction.v:130` `Class Adjunction` is the hom-set presentation
  taken as primitive (a hom-setoid isomorphism `adj` with the four naturality
  fields), with `unit := ⌊id⌋` at `:214` and the relating formula
  `to_adj_unit {x y} (f : F x ~> y) : ⌊f⌋ ≈ fmap[U] f ∘ η` at `:264`.
- `Theory/Universal/Arrow.v:127` `Class UniversalArrow (c : C) (F : D ⟶ C)`
  *is* an initial object of the comma `=(c) ↓ F`, with `arrow_obj`/`arrow` its
  projections; `:139` `ump_universal_arrows` is the unit's universal property;
  `:158` `universal_arrow_from_UMP` builds one from the `∃!` factorization;
  `:214` `AdjunctionFromUniversalArrows` assembles a family into an adjunction.
- `Adjunction/GAFT.v:180`
  `Theorem GAFT_from_initials (U : C ⟶ D) (H : forall d, @Initial (=(d) ↓ U)) : { F : D ⟶ C & F ⊣ U }`
  is the "if" half of the comma criterion.
- `Construction/Comma.v:127` `Comma` instantiated at `=(X)` and `U` is exactly
  Awodey's (X ↓ U); `Construction/Comma.v:87–89` states the correspondence in
  prose only.

Precise gap: **nothing in the tree takes an `F ⊣ U` and produces a
`UniversalArrow d U`, an `@Initial (=(d) ↓ U)`, or even the bare
`∃! g, f ≈ fmap[U] g ∘ η`.** Every consumer of `UniversalArrow`
(`Construction/Free/Quiver.v:518`, `Adjunction/GAFT.v`, `Monad/Lifting.v:445`)
*produces* an adjunction rather than consuming one. Consequently neither
Proposition 9.4's biconditional nor the comma criterion's "only if" half can be
cited; the only biconditionals available relate two forms of the hom-set
presentation to each other (`Adjunction/Hom.v:223,259`,
`Theory/Profunctor/Adjunction.v:70`) or to the unit-and-counit-with-triangles
form (`Adjunction/Natural/Transformation/Universal.v:42,84`), which is a richer
datum than the book's unit-with-universal-property condition.

## Work to be done

Suggested module path: extend `Theory/Universal/Arrow.v` (or add
`Adjunction/Universal.v` if the section context is awkward there).

- Prove `adjunction_unit_universal {c} : F ⊣ U → UniversalArrow c U`, whose
  content is one rewrite: `Theory/Adjunction.v:195` `adj_univ`
  (`f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g`) plus `to_adj_unit` (`:264`) give exactly the `∃!`
  hypothesis of `universal_arrow_from_UMP` (`Theory/Universal/Arrow.v:158`).
- Derive `adjunction_comma_initial {c} : F ⊣ U → @Initial (=(c) ↓ U)` by
  projecting `arrow_initial`.
- Package the biconditional the book states: a named theorem
  `adjunction_iff_universal_arrows : (∀ c, UniversalArrow c U) ↔ { F & F ⊣ U }`
  (with the honest caveat, already visible at
  `Theory/Adjunction.v` and `Theory/Universal/Arrow.v:214`, that the forward
  direction *reconstructs* the left adjoint, so for a pre-existing F the
  round trip closes only up to `left_adjoint_iso`, `Theory/Adjunction.v:404`).
- Add the comma-criterion corollary
  `left_adjoint_iff_comma_initial : (∀ d, @Initial (=(d) ↓ U)) ↔ { F & F ⊣ U }`,
  pairing the new direction with the existing `GAFT_from_initials`.

## Definition of Done

- [ ] `adjunction_unit_universal` and `adjunction_comma_initial` proved
- [ ] Both biconditionals stated as named theorems, matching Awodey §9.2
      Proposition 9.4 and the §9.8 comma criterion (setoid `≈`; never `=` on
      morphisms)
- [ ] The "reconstructed vs. given left adjoint" caveat is stated in the file
      header, not silently elided
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for `adjunction_unit_universal`,
      `adjunction_iff_universal_arrows` and `left_adjoint_iff_comma_initial`
- [ ] Any new file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated (the adjunction entry should
      record that the three presentations now round-trip in both directions)

## Verification

```bash
coqc -R . Category Theory/Universal/Arrow.v
coqc -R . Category Adjunction/GAFT.v

coqtop -R . Category -l Theory/Universal/Arrow.v <<< \
  'Print Assumptions adjunction_iff_universal_arrows.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.2 Proposition 9.4 in both
directions; the comma criterion is stated over `=(d) ↓ U` (the library's own
spelling of (X ↓ U)); the round-trip caveat is honestly disclosed.

## Dependencies

Depends on: #347

<!-- catalog: {"ids":["awodey:9.2:prop4","awodey:9.8:construction-comma-x-u"],"deps":["#347"]} -->

---8<---

```yaml
title: "Awodey 9.4: The interior operator as a right adjoint to the inclusion of open sets"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.4:example11]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.4, Example 9.11 — printed p. 228, PDF p. 237
(`awodey:9.4:example11`).

## Background

For a topological space X the poset O(X) of open sets sits inside the powerset
poset P(X), and this inclusion has a right adjoint: the interior operation,
int(S) being the largest open set contained in S. The two-way rule
U ⊆ S ⟺ U ⊆ int(S) (for U open) is exactly the adjunction, and the induced
comonad on P(X) is the interior operator. See
[nLab: interior](https://ncatlab.org/nlab/show/interior) (which gives the
largest-open-subset characterization) and
[Wikipedia: Interior (topology)](https://en.wikipedia.org/wiki/Interior_(topology)).

## Current state in the library

Absent in every ingredient.

- No topological spaces: there is no `Top`, no `TopologicalSpace`, and no
  `Instance/Top*` file (`ls Instance/` gives Cat, CMon, Cones, Coq, FinSet, Fun,
  Lambda, One, Sets, StrictCat, Two). Every occurrence of "topolog" in the tree
  is bibliographic prose.
- No poset of opens and no powerset poset: the only in-tree `Pow` is
  `Structure/Topos.v:129` `Pow a := Ω ^ a`, an internal power *object* with no
  adjoints; there is no P(X) presented as a preorder category.
- No interior or closure operator: "interior" occurs twice in the tree, both
  unrelated prose (`Test/ProbeFunnyPoly.v:19`, `Theory/Lawvere.v:90`);
  `Instance/Poset.v:65` mentions "a monad is a closure operator" only in its
  header essay.
- No frames or locales (`Instance/Lambda/Full.v`'s `Frame` is an evaluation
  context, unrelated).

## Work to be done

Suggested module paths: `Instance/Top/Opens.v` for the poset of opens and the
adjunction, over whatever `Top` and the powerset preorder land as under the
dependencies below.

- Present the powerset of a set as a preorder category (subsets under
  inclusion) — this is the same object the powerset direct-image/inverse-image
  work needs, so reuse rather than duplicate it.
- Define the inclusion functor `O(X) ⟶ P(X)` (monotone, since opens are
  subsets).
- Define `interior : P(X) ⟶ O(X)` as the union of all open subsets, prove it
  monotone, and prove the two-way rule as an `Adjunction` instance in the sense
  of `Theory/Adjunction.v:130`. Because both hom-setoids are subsingletons
  (`Instance/Proset.v:33` sets `equiv _ _ := True`), the four naturality fields
  are trivially inhabited and the adjunction *is* the bi-implication — record
  this explicitly so the proof does not do unnecessary work.
- Derive the standard consequences the example points at: `int` is idempotent
  and deflationary (i.e. the counit of a coreflection), and O(X) is
  coreflective in P(X). Where the library already names a coreflective
  subcategory (`Construction/Reflective.v`), instantiate that vocabulary rather
  than inventing new terms.
- State the dual (closure as a left adjoint to the inclusion of closed sets) if
  it costs only a dualization.

## Definition of Done

- [ ] The adjunction `inclusion ⊣ interior` between O(X) and P(X) is stated and
      proved, matching Awodey §9.4 Example 9.11 (setoid `≈` discipline; never
      `=` on morphisms)
- [ ] `interior` is *constructed*, not axiomatized, and shown monotone
- [ ] The coreflection reading (idempotent deflationary comonad) is recorded
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for the adjunction and for `interior`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated if `Top` gains an index entry
      as part of this work

## Verification

```bash
coqc -R . Category Instance/Top/Opens.v

coqtop -R . Category -l Instance/Top/Opens.v <<< \
  'Print Assumptions Opens_Interior_Adjunction.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.4 Example 9.11; the powerset
preorder is the shared one, not a private copy; the subsingleton degeneracy of
the hom-setoids is exploited rather than re-proved pointwise.

## Dependencies

Depends on: #259
Depends on: #268
Depends on: #382
Depends on: #380
Depends on: #685 (Awodey 6.3: Powersets and open-set lattices as complete Heyting algebras — creates `Instance/Top/Opens.v`, the module this issue extends)

<!-- catalog: {"ids":["awodey:9.4:example11"],"deps":["#259","#268","#382","#380","#685"]} -->

---8<---

```yaml
title: "Awodey 9.5: Quantifiers as adjoints to weakening — a syntactic hyperdoctrine and its geometric reading"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.5:construction-quantifiers-adjoints, awodey:9.5:construction-geometric-quantifiers]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.5 "Quantifiers as adjoints".

- The adjoint triple ∃ ⊣ weakening ⊣ ∀ over preorders of formulas-in-context —
  printed pp. 230–231, PDF pp. 239–240
  (`awodey:9.5:construction-quantifiers-adjoints`).
- The geometric reading: in a model, ∃ is image along a projection, weakening is
  pullback, ∀ is dual image — printed pp. 232–234, PDF pp. 241–243
  (`awodey:9.5:construction-geometric-quantifiers`).

## Background

Lawvere's observation: fix a first-order language and order the formulas in a
given context by provable entailment. Adding a dummy variable is a monotone map
between these preorders, and existential and universal quantification over that
variable are its left and right adjoints — the introduction and elimination
rules being literally the two halves of the transposition bijection. Under
Tarski semantics the same triple becomes image ⊣ inverse image ⊣ dual image
along a product projection. See
[nLab: hyperdoctrine](https://ncatlab.org/nlab/show/hyperdoctrine) and
[nLab: existential quantifier](https://ncatlab.org/nlab/show/existential+quantifier).

## Current state in the library

Both constructions are entirely absent, and so is the syntax they run on.

- Quantifiers and hyperdoctrines appear only as header prose:
  `Theory/Adjunction.v:75–77` ("the quantifiers form the adjoint triple ∃ ⊣
  substitution ⊣ ∀ over the fibres of a hyperdoctrine"), `Instance/Poset.v:70`,
  `Structure/Topos.v:38,85`. There is no `Definition`, `Class` or `Lemma`.
- There is no first-order syntax layer at all: no language, no formulas, no
  context, no entailment preorder. `Lib/MapDecide.v`'s `formula` is a reflective
  decision procedure for finite maps; `Instance/Lambda/Ren.v`'s "weakening" is
  de Bruijn renaming of terms, with no entailment order and no adjoint.
- There is no model theory: no satisfaction relation, no L-structure, no
  extension of a formula.
- The nearest semantic relative is `Construction/Slice/Pullback.v`, which
  defines the post-composition functor at `:50` and the pullback (base change)
  functor at `:67`; but the adjunction between them is a commented-out stub at
  `:121–127` (stated in the wrong direction), the dependent product does not
  exist even as a stub, and — decisively for this item — there is no logic in
  the tree for those operations to be *identified with*.

## Work to be done

Suggested module paths: `Instance/FirstOrder/Syntax.v` (language, terms,
formulas-in-context, entailment), `Instance/FirstOrder/Hyperdoctrine.v` (the
preorder fibres, weakening, and the two adjunctions), and
`Instance/FirstOrder/Semantics.v` (the geometric reading).

- Define a first-order signature and the raw formulas over a context of
  variables, with a substitution/renaming action (the de Bruijn machinery in
  `Instance/Lambda/Ren.v` is the obvious in-tree template to copy, not reuse).
- Define provable entailment between formulas in a fixed context and present the
  resulting preorder as a category via `Instance/Proset.v:33` `Proset` — as at
  `Instance/Props.v`, the trivial hom-setoid makes the resulting adjunctions
  *definitionally* two-way rules.
- Define the weakening (dummy-variable) functor between the preorders of two
  contexts differing by one variable.
- Prove the two adjunctions `∃x ⊣ weakening` and `weakening ⊣ ∀x` as
  `Theory/Adjunction.v:130` `Adjunction` instances, and record that the
  introduction and elimination rules of the calculus are exactly the transposes
  `⌊−⌋`/`⌈−⌉`.
- For the geometric reading: define interpretation of formulas as subsets of a
  power of the carrier, and prove that under this interpretation weakening is
  inverse image along a product projection, ∃ is direct image, and ∀ is dual
  image — reusing the powerset triple named under Dependencies rather than
  re-deriving it. Prove the interpretation is a morphism of the two adjoint
  triples (i.e. soundness of the quantifier rules).

## Definition of Done

- [ ] The syntactic triple ∃ ⊣ weakening ⊣ ∀ is stated and proved, matching
      Awodey §9.5 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The two adjunctions are `Adjunction` instances, not merely bi-implications
      stated by hand
- [ ] The geometric reading is proved as a compatibility between the syntactic
      triple and the powerset triple along the interpretation
- [ ] `Theory/Adjunction.v:75–77`, `Instance/Poset.v:70` and
      `Structure/Topos.v:38,85` are updated to point at the new development
      instead of describing it as unformalized folklore
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for both quantifier adjunctions and for the
      soundness statement
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated — this is the library's first
      first-order logic layer and its first hyperdoctrine

## Verification

```bash
coqc -R . Category Instance/FirstOrder/Syntax.v
coqc -R . Category Instance/FirstOrder/Hyperdoctrine.v
coqc -R . Category Instance/FirstOrder/Semantics.v

coqtop -R . Category -l Instance/FirstOrder/Hyperdoctrine.v <<< \
  'Print Assumptions Exists_Weakening_Adjunction. Print Assumptions Weakening_Forall_Adjunction.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.5 (the adjunctions are between
preorders of *formulas in context*, not powersets); the geometric reading is a
theorem relating the two triples, not a second definition of the same thing.

## Dependencies

Depends on: #384
Depends on: #382
Depends on: #380

<!-- catalog: {"ids":["awodey:9.5:construction-quantifiers-adjoints","awodey:9.5:construction-geometric-quantifiers"],"deps":["#384","#382","#380"]} -->

---8<---

```yaml
title: "Awodey 9.7: Change of base for indexed families of sets — the adjoint triple with its fibrewise formulas"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:construction-change-of-base, awodey:9.7:construction-sum-delta-product]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7 "Locally cartesian closed categories".

- Change of base along a function of index sets — printed p. 241, PDF
  pp. 250–252 (`awodey:9.7:construction-change-of-base`).
- The special case over the one-element index: sum ⊣ constant-family ⊣ product —
  printed p. 242, PDF p. 251 (`awodey:9.7:construction-sum-delta-product`).

## Background

An I-indexed family of sets is a functor from the discrete category on I to
Sets. Reindexing along α : J ⟶ I is precomposition, and it has both adjoints,
computed fibrewise: the left adjoint takes the disjoint sum over each fibre
α⁻¹(i), the right adjoint the cartesian product over that fibre. Taking I to be
a singleton recovers the familiar sum ⊣ constant ⊣ product transposition rules.
See [nLab: base change](https://ncatlab.org/nlab/show/base+change),
[nLab: dependent sum](https://ncatlab.org/nlab/show/dependent+sum) and
[nLab: dependent product](https://ncatlab.org/nlab/show/dependent+product).

## Current state in the library

The middle functor exists in full generality; both adjoints exist only as
hypotheses, and no fibrewise computation exists anywhere.

- `Theory/Kan/Extension.v:127` `Induced : [B, C] ⟶ [A, C] := G ↦ G ◯ F` is
  precisely the reindexing (precomposition) functor for arbitrary F and target.
- `Theory/Kan/Extension.v:222` `Class LeftKan := { Lan; lan_adjoint : Lan ⊣ Induced }`
  and `:140` `Class RightKan := { Ran; ran_adjoint : Induced ⊣ Ran }` state the
  adjoint-triple *shape* — but these classes have **no instance anywhere in the
  tree**; their sole consumer, `Structure/Limit/Kan/Extension.v:46` `Kan_Limit`,
  also takes `RightKan` as a hypothesis.
- `Structure/Limit/Product.v:105` `iprod_ump` gives the product transposition
  rule as a universal property relative to an assumed
  `Limit (DiscreteCat_Functor f)`, and `Functor/Diagonal.v:33` `Diagonal J`
  is the constant-family functor; but `HasIndexedProducts`
  (`Structure/Limit/Product.v:128`) is a declaration with **zero instances**, and
  there is no elementary indexed *coproduct* at all (`Colimit F` is only
  `Limit (F^op)`, `Structure/Limit.v:158`).
- Sets is never shown to have limits or colimits: `Structure/Complete.v:115,119`
  define `Complete`/`Cocomplete` and every use in the tree is as a hypothesis.
- Nothing specializes any of this to discrete categories, and nothing computes a
  fibre.

## Work to be done

Suggested module paths: `Structure/Limit/Coproduct.v` (the dual of
`Structure/Limit/Product.v`), `Instance/Sets/IndexedFamilies.v`, and
`Instance/Sets/ChangeOfBase.v`.

- Dualize `Structure/Limit/Product.v` to obtain `icoprod`, `icoprod_inj` and
  `icoprod_ump` over `Instance/Discrete.v`'s `DiscreteCat`, plus
  `HasIndexedCoproducts`. This is the reusable half of the work and should land
  first.
- Construct the indexed product and coproduct of a family of setoids in `Sets`,
  i.e. give `Sets` its `HasIndexedProducts` and `HasIndexedCoproducts`
  instances. Keep the construction funext-free, in the style of
  `Instance/Sets/Coend.v` and `Instance/FinSet/Closed.v`.
- Define the fibre of α over i and the two fibrewise operations, and prove
  `Sigma_alpha ⊣ alpha_star` and `alpha_star ⊣ Pi_alpha` as `Adjunction`
  instances, where `alpha_star := Induced (DiscreteCat_Functor α)` with target
  `Sets`.
- Instantiate `LeftKan`/`RightKan` at this data — this would be the tree's
  **first** instance of either class, and should be flagged as such.
- Derive the singleton-index case as a corollary, recovering the sum ⊣ constant
  ⊣ product rules, and connect the constant-family functor to
  `Functor/Diagonal.v:33` `Diagonal`.

## Definition of Done

- [ ] `icoprod`/`icoprod_ump` and `HasIndexedCoproducts` defined, dual to the
      existing indexed-product API
- [ ] `Sets` carries indexed products and indexed coproducts, constructed
      (not assumed), funext-free
- [ ] Both adjunctions proved as `Adjunction` instances with the fibrewise
      formulas, matching Awodey §9.7 (setoid `≈` discipline; never `=` on
      morphisms)
- [ ] `LeftKan`/`RightKan` instantiated for the discrete-index Sets case, with a
      header note that these are the tree's first instances
- [ ] The singleton-index corollary is stated
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for both adjunctions and for the Sets indexed
      (co)product instances
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated (first Kan-extension instances;
      first indexed (co)products in Sets)

## Verification

```bash
coqc -R . Category Structure/Limit/Coproduct.v
coqc -R . Category Instance/Sets/IndexedFamilies.v
coqc -R . Category Instance/Sets/ChangeOfBase.v

coqtop -R . Category -l Instance/Sets/ChangeOfBase.v <<< \
  'Print Assumptions Sigma_Star_Adjunction. Print Assumptions Star_Pi_Adjunction.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7; the two adjoints are
*constructed* fibrewise rather than assumed via `LeftKan`/`RightKan`
hypotheses; the singleton case really is derived, not re-proved.

## Dependencies

Depends on: #590
Depends on: #353

<!-- catalog: {"ids":["awodey:9.7:construction-change-of-base","awodey:9.7:construction-sum-delta-product"],"deps":["#590","#353"]} -->

---8<---

```yaml
title: "Awodey 9.7: The dependent product — the right adjoint to base change on slices"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:prop18, awodey:9.7:construction-slice-adjoints-explicit, awodey:9.7:construction-product-exponential-factorization]
deps_item_ids: [awodey:9.7:remark21]
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7 "Locally cartesian closed categories".

- Proposition 9.18 (pullback along a function of sets has both adjoints) —
  printed p. 243, PDF pp. 252–253 (`awodey:9.7:prop18`).
- The explicit description of the two adjoints, the right one by partial
  sections over a fibre — printed p. 244, PDF pp. 253–254
  (`awodey:9.7:construction-slice-adjoints-explicit`).
- The product–exponential adjunction factored through a slice — printed p. 245,
  PDF p. 254 (`awodey:9.7:construction-product-exponential-factorization`).

## Background

Base change along f — pullback between slice categories — has a left adjoint
given by post-composition (the dependent sum) and, when it exists, a right
adjoint given by dependent product. In Sets the right adjoint sends a bundle to
the family of partial sections over each fibre; taking the base map to be the
unique map to a singleton, the composite of the two adjunctions is exactly the
currying adjunction. See
[nLab: dependent product](https://ncatlab.org/nlab/show/dependent+product) and
[nLab: base change](https://ncatlab.org/nlab/show/base+change).

## Current state in the library

Both endpoints of the *left* adjunction exist as functors; neither adjunction is
proved, and the right adjoint does not exist in any form.

- `Construction/Slice/Pullback.v:50` `Bang_Functor (f : a ~> b) : @Slice C a ⟶ @Slice C b`
  is post-composition, i.e. exactly the book's explicit left adjoint
  (`(o; h) ↦ (o; f ∘ h)`).
- `Construction/Slice/Pullback.v:67` `Star_Functor (f : c ~> a) : @Slice C a ⟶ @Slice C c`
  is base change by chosen pullback, under
  `Hypothesis pullbacks : ∀ X Y Z (f : Y ~> Z) (g : X ~> Z), Pullback f g` at
  `:63`.
- The adjunction between them is **dead code**: lines 121–127 are a fully
  commented-out `Base_Functor_Adjunction` stub, and — as the file's own header
  at lines 38–40 concedes — the stub even states the adjointness in the wrong
  direction. Lines 114–119 hold a similarly commented-out `Production` (the
  dependent-product candidate).
- There is no dependent product anywhere: searches for a Π functor on slices, a
  set of partial sections, or the fibre of a map return nothing;
  `Structure/Regular/Factorization.v` gives image factorizations of single
  morphisms only.
- The Sets specialization is unreachable: `Sets` has no `Pullback` instance
  (the only in-tree one is `Instance/FinSet/Classifier.v:264` for FinSet), so
  `Star_Functor`'s hypothesis is never discharged for Sets.
- The destination of the factorization *is* in tree —
  `Instance/Sets/Cartesian/Closed.v:38` `Sets_Closed` with
  `exp_iso {x y z} : x × y ~> z ≊ x ~> z^y` (`Structure/Cartesian/Closed.v:51`) —
  but it is a hom-setoid bijection, not an `Adjunction` record, so
  `Adjunction/Compose.v:173` `Adjunction_Compose` has nothing to consume.

## Work to be done

Suggested module paths: extend `Construction/Slice/Pullback.v`; add
`Construction/Slice/DependentProduct.v` and `Instance/Sets/Slice.v`.

- Give `Sets` a `HasPullbacks` instance (equalizer-of-a-product construction on
  setoids), discharging `Star_Functor`'s hypothesis.
- Replace the commented-out stub with a real, correctly-oriented
  `Bang_Star_Adjunction : Bang_Functor f ⊣ Star_Functor f`, and delete the dead
  code rather than leaving it in place.
- Construct the dependent product `Pi_Functor f : @Slice C c ⟶ @Slice C a` in
  Sets by the book's partial-sections formula, and prove
  `Star_Pi_Adjunction : Star_Functor f ⊣ Pi_Functor f`.
- Package the destination adjunction: turn `exp_iso` into a genuine
  `Adjunction` between the functors (− × A) and (−)^A on `Sets`, so it can be
  compared with a composite.
- Prove the factorization: over the terminal object the two slice adjunctions
  compose (`Adjunction/Compose.v:173`) to the currying adjunction, with the
  computations "sum of a constant family is a binary product" and "product of a
  constant family is an exponential" stated as named isomorphisms.
- Derive the stated consequence that base change preserves all limits and all
  colimits, by feeding the two adjunctions to `Adjunction/Continuity.v:202,223`.

## Definition of Done

- [ ] `HasPullbacks Sets` constructed
- [ ] `Bang_Functor f ⊣ Star_Functor f` proved, with the commented-out stub and
      its wrong-direction statement removed from `Construction/Slice/Pullback.v`
      (the file currently ships dead code that misstates the theorem)
- [ ] `Pi_Functor` constructed by partial sections and
      `Star_Functor f ⊣ Pi_Functor f` proved, matching Awodey §9.7
      Proposition 9.18 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The currying adjunction is available as an `Adjunction` record and is
      proved isomorphic to the composite through the slice
- [ ] Preservation of limits and colimits by base change derived, not restated
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for `Bang_Star_Adjunction`,
      `Star_Pi_Adjunction` and the factorization theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated — the slice entry currently
      advertises the adjoint triple that this issue is the first to prove

## Verification

```bash
coqc -R . Category Instance/Sets/Pullback.v
coqc -R . Category Construction/Slice/Pullback.v
coqc -R . Category Construction/Slice/DependentProduct.v
coqc -R . Category Instance/Sets/Slice.v

coqtop -R . Category -l Construction/Slice/DependentProduct.v <<< \
  'Print Assumptions Bang_Star_Adjunction. Print Assumptions Star_Pi_Adjunction.'

grep -n '(\*.*Base_Functor_Adjunction' Construction/Slice/Pullback.v   # must be empty

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Proposition 9.18 and the
explicit descriptions on p. 244; the right adjoint really is the partial-sections
construction; no commented-out adjunction stub survives in
`Construction/Slice/Pullback.v`.

## Dependencies

Depends on: #387
Depends on: awodey:9.7:remark21

<!-- catalog: {"ids":["awodey:9.7:prop18","awodey:9.7:construction-slice-adjoints-explicit","awodey:9.7:construction-product-exponential-factorization"],"deps":["#387","awodey:9.7:remark21"]} -->

---8<---

```yaml
title: "Awodey 9.7: Structure on slice categories — the domain functor, products from pullbacks, and C ≅ C/1"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:remark21]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7, Remark 9.21 — printed p. 247, PDF p. 256
(`awodey:9.7:remark21`).

## Background

The remark turns on two facts about slice categories that the rest of §9.7
uses constantly: a slice C/c always has a terminal object (the identity), it has
binary products exactly when C has pullbacks over c, and the slice over a
terminal object is isomorphic to C itself — which is why requiring a terminal
object in the definition of "locally cartesian closed" makes such a category
cartesian closed. See [nLab: over category](https://ncatlab.org/nlab/show/over+category)
and [Wikipedia: Cartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category).

## Current state in the library

The slice category exists; nothing structural is ever proved about it.

- `Construction/Slice.v:123` `Slice` and `:140` `Comma_Slice` (identifying the
  slice with a comma category), `:169` `Coslice`, `:181` `Comma_Coslice`. Plus
  `Construction/Slice/Pullback.v:50,67` (two functors between slices). **That is
  the entire slice development.**
- No slice carries a `Terminal`, `Cartesian` or `Closed` instance anywhere in
  the tree, and no file outside `Construction/Slice*` even uses the `Slice`
  constructor.
- The domain (forgetful) functor `C/c ⟶ C` is never defined:
  `Construction/Slice.v:39–41` says in prose that it "is the comma projection
  `comma_proj1` transported across `Comma_Slice`", and `comma_proj1` does exist
  (`Construction/Comma.v:196`), but the functor itself is never constructed.
- `C ≅ C/1` is likewise prose only: `Construction/Slice.v:67` asserts it in the
  background essay; no lemma states it, and `Instance/One.v` is never combined
  with `Construction/Slice.v`.

## Work to be done

Suggested module path: `Construction/Slice/Structure.v`.

- Define `Slice_Forget c : @Slice C c ⟶ C`, the domain functor, by transporting
  `comma_proj1` across `Comma_Slice` exactly as the header describes. This is a
  reusable API surface that several downstream results need, so give it a name
  and a `Proper` instance rather than inlining it.
- Prove `Slice_Terminal : @Terminal (@Slice C c)` with terminal object
  `(c; id[c])`.
- Prove `Slice_Cartesian : HasPullbacks C → @Cartesian (@Slice C c)`, the
  binary product of `(x; f)` and `(y; g)` being their pullback over c, with
  `ump_products` discharged from `ump_pullbacks`.
- Prove `Slice_Over_Terminal : @Terminal C → @Slice C terminal_obj ≅[Cat] C`,
  and record that it carries structure both ways (so a statement proved over an
  arbitrary base specializes to the absolute statement, which is the use the
  slice file's header advertises).
- Prove `Slice_of_Slice : @Slice (@Slice C c) (x; f) ≅[Cat] @Slice C x`, needed
  wherever an iterated slice appears.
- Update `Construction/Slice.v:39–41,67` so the prose points at real lemmas.

## Definition of Done

- [ ] `Slice_Forget`, `Slice_Terminal`, `Slice_Cartesian`, `Slice_Over_Terminal`
      and `Slice_of_Slice` are defined and proved, matching Awodey §9.7
      Remark 9.21 (setoid `≈` discipline; never `=` on morphisms)
- [ ] `Construction/Slice.v`'s header prose no longer asserts unformalized
      results (the domain functor and `C ≅ C/1` are currently claimed there with
      nothing behind them)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for each of the five principal artifacts
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated for the slice entry

## Verification

```bash
coqc -R . Category Construction/Slice/Structure.v

coqtop -R . Category -l Construction/Slice/Structure.v <<< \
  'Print Assumptions Slice_Cartesian. Print Assumptions Slice_Over_Terminal.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Remark 9.21; `Slice_Cartesian`
really is derived from pullbacks in the base; `C ≅ C/1` is an isomorphism in
`Cat`, not merely an equivalence.

## Dependencies

Depends on: #652

<!-- catalog: {"ids":["awodey:9.7:remark21"],"deps":["#652"]} -->

---8<---

```yaml
title: "Awodey 9.7: Locally cartesian closed categories, and the equivalence with slicewise cartesian closure"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:def19, awodey:9.7:prop20]
deps_item_ids: [awodey:9.7:prop18, awodey:9.7:remark21]
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7 "Locally cartesian closed categories".

- Definition 9.19 (locally cartesian closed category) — printed p. 246, PDF
  p. 255 (`awodey:9.7:def19`).
- Proposition 9.20 (locally cartesian closed iff every slice is cartesian
  closed) — printed p. 246, PDF pp. 255–256 (`awodey:9.7:prop20`).

## Background

A category with pullbacks is locally cartesian closed when base change along
every arrow has a right adjoint (a dependent product); equivalently, when every
slice is cartesian closed. This is the categorical home of dependent type
theory. See
[nLab: locally cartesian closed category](https://ncatlab.org/nlab/show/locally+cartesian+closed+category).

## Current state in the library

Absent in both directions, and absent as a predicate.

- There is no `LocallyCartesianClosed` class, definition or instance. Every
  occurrence of the phrase in the tree is header prose or an nLab URL:
  `Instance/Sets.v:97`, `Instance/Cat.v:129`, `Construction/Slice.v:47,91,97`,
  `Construction/Slice/Pullback.v:36`, `Structure/Pullback.v:126`.
- The right-hand side of the equivalence is equally unavailable: no slice
  category carries a `Terminal`, `Cartesian` or `Closed` instance anywhere.
- Of the three functors in the definition, two exist
  (`Construction/Slice/Pullback.v:50,67`) and the dependent product does not
  exist even as live code — the `Production` and `Base_Functor_Adjunction`
  candidates at lines 114–127 are entirely commented out.
- No slice of a slice is ever formed, so the proposition's proof strategy has no
  in-tree carrier.

Not out of scope: the library has universe polymorphism, `Slice`, and a live
cartesian-closed class (`Structure/Cartesian/Closed.v:43`, distinct from the
`Structure/Closed.v` Eilenberg–Kelly stub), so the definition is perfectly
statable here — it simply is not stated.

## Work to be done

Suggested module path: `Structure/LocallyCartesianClosed.v`.

- Define `Class LocallyCartesianClosed (C : Category)` carrying pullbacks and,
  for every arrow f, a right adjoint to base change along f, together with the
  terminal-object clause the book discusses.
- Prove the forward direction: local cartesian closure makes every slice
  cartesian closed. Products in the slice come from pullbacks in the base; the
  exponential in `C/c` of `(y; g)` by `(x; f)` is obtained by transporting the
  dependent product along the slice-of-a-slice isomorphism.
- Prove the converse: if every slice is cartesian closed then base change along
  every arrow has a right adjoint, constructed from the slice exponential.
- Record the corollary that a locally cartesian closed category with a terminal
  object is cartesian closed, using the slice-over-terminal isomorphism.
- Confirm the definition is inhabited by the in-tree witness noted under
  Dependencies before closing (`docs/INHABITATION.md` should gain a row, since
  an uninhabited class is exactly what that document exists to flag).

## Definition of Done

- [ ] `LocallyCartesianClosed` defined, matching Awodey §9.7 Definition 9.19
      (setoid `≈` discipline; never `=` on morphisms)
- [ ] Both directions of Proposition 9.20 proved as a named biconditional
- [ ] The corollary "locally cartesian closed + terminal ⇒ cartesian closed"
      recorded
- [ ] The class uses `Structure/Cartesian/Closed.v`'s live `Closed`, not the
      `Structure/Closed.v` stub, and the file header says so
- [ ] `docs/INHABITATION.md` updated with the class's witness status
- [ ] The stale "locally cartesian closed" prose in `Instance/Sets.v:97`,
      `Instance/Cat.v:129`, `Construction/Slice.v:47,91,97`,
      `Construction/Slice/Pullback.v:36` and `Structure/Pullback.v:126` updated
      to cite the new definition
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for the class's principal theorems
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated — this is a flagship-level
      addition

## Verification

```bash
coqc -R . Category Structure/LocallyCartesianClosed.v

coqtop -R . Category -l Structure/LocallyCartesianClosed.v <<< \
  'Print Assumptions lcc_iff_slices_closed.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Definition 9.19 and
Proposition 9.20; the equivalence is proved in both directions; the terminal
clause is handled exactly as the book's Remark 9.21 discusses.

## Dependencies

Depends on: #387
Depends on: awodey:9.7:prop18
Depends on: awodey:9.7:remark21

<!-- catalog: {"ids":["awodey:9.7:def19","awodey:9.7:prop20"],"deps":["#387","awodey:9.7:prop18","awodey:9.7:remark21"]} -->

---8<---

```yaml
title: "Awodey 9.7: A slice of a presheaf category is again a presheaf category"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:lem23]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7, Lemma 9.23 (with the accompanying comparison
functor) — printed pp. 247–248, PDF pp. 256–258 (`awodey:9.7:lem23`).

## Background

For a presheaf P on a small category C, the slice of the presheaf category over
P is equivalent to the presheaf category on the category of elements of P
(equivalently, on the Yoneda slice y/P): a bundle over P is the same thing as a
presheaf on the elements of P. The comparison functor sends a bundle to the
hom-presheaf of maps out of a representable element. See
[nLab: category of elements](https://ncatlab.org/nlab/show/category+of+elements)
and [nLab: presheaf topos](https://ncatlab.org/nlab/show/presheaf+topos).

## Current state in the library

Nothing of the lemma exists.

- The category of elements of a Sets-valued presheaf is not constructed:
  `Construction/Grothendieck.v:108` mentions it only in the background essay
  ("Restricting the fibres to sets, viewed as discrete categories, recovers the
  category of elements"). `Construction/Grothendieck.v` itself takes an
  `IndexedCat` (Cat-valued, with a coherence pack), and
  `Construction/Grothendieck/Strict.v`'s `IndexedCat_of_StrictFunctor` needs a
  strict functor into `Cat` under fibrewise UIP — neither is what a Sets-valued
  presheaf is packaged as, so the existing machinery cannot simply be
  instantiated.
- No slice of a functor category is ever formed: no file outside
  `Construction/Slice*` uses the `Slice` constructor at all.
- No theorem anywhere compares a slice of a functor category with a functor
  category.
- The left-Kan leg of the book's proof is independently unavailable:
  `LeftKan` has no instance in the tree.

## Work to be done

Suggested module path: `Construction/Presheaf/SliceElements.v`.

- Construct the category of elements of a Sets-valued presheaf directly (do not
  try to force it through `IndexedCat`), and prove it isomorphic to the Yoneda
  slice built from the dependency below.
- Define the comparison functor from the slice of the presheaf category to
  presheaves on the elements: a bundle over P goes to the presheaf sending an
  element to the set of maps into that bundle over P.
- Construct its quasi-inverse and prove the two are an equivalence
  (`Theory/Equivalence.v`), so the lemma is available in the form the locally
  cartesian closed corollary needs.
- State and prove the compatibility the book uses: the equivalence carries base
  change on the presheaf side to restriction on the elements side.

## Definition of Done

- [ ] The category of elements of a Sets-valued presheaf is constructed
- [ ] The comparison functor is defined and proved to be an equivalence,
      matching Awodey §9.7 Lemma 9.23 (setoid `≈` discipline; never `=` on
      morphisms)
- [ ] The equivalence's compatibility with base change/restriction is proved
- [ ] `Construction/Grothendieck.v:108` prose updated to point at the real
      construction instead of describing it as a would-be specialization
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for the comparison functor and the equivalence
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated

## Verification

```bash
coqc -R . Category Construction/Presheaf/SliceElements.v

coqtop -R . Category -l Construction/Presheaf/SliceElements.v <<< \
  'Print Assumptions presheaf_slice_equivalence.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Lemma 9.23; the comparison is
proved an equivalence (not merely fully faithful); the elements construction is
genuinely for a Sets-valued presheaf rather than a re-packaged `IndexedCat`.

## Dependencies

Depends on: #716
Depends on: #717
Depends on: #715

<!-- catalog: {"ids":["awodey:9.7:lem23"],"deps":["#716","#717","#715"]} -->

---8<---

```yaml
title: "Awodey 9.7: Presheaf categories are locally cartesian closed"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:example22, awodey:9.7:cor24]
deps_item_ids: [awodey:9.7:prop20, awodey:9.7:lem23]
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7.

- Example 9.22 (presheaf categories are locally cartesian closed) — printed
  p. 247, PDF p. 256 (`awodey:9.7:example22`).
- Corollary 9.24 (the same, now proved) — printed p. 249, PDF p. 258
  (`awodey:9.7:cor24`).

## Background

Every slice of a presheaf category is again a presheaf category, and presheaf
categories are cartesian closed; combined with the slicewise characterization of
local cartesian closure, this makes presheaf categories locally cartesian
closed — the standard source of models of dependent type theory. See
[nLab: presheaf topos](https://ncatlab.org/nlab/show/presheaf+topos) and
[nLab: locally cartesian closed category](https://ncatlab.org/nlab/show/locally+cartesian+closed+category).

## Current state in the library

Neither the conclusion nor any ingredient of it exists.

- No locally-cartesian-closed predicate exists to instantiate (all occurrences
  are header prose).
- Presheaf categories are not even shown *cartesian* closed: the only structural
  instance on a functor category is
  `Instance/Fun/Cartesian.v:111`
  `Instance Functor_Category_Cartesian (C D : Category) (_ : @Cartesian D) : @Cartesian (@Fun C D)`,
  which gives pointwise finite products and no exponentials. Enumerating every
  `@Closed` instance in the tree (Sets, Coq, FinSet, Cat, Props, Rel, Algs,
  Lambda, the AST hom, `Product_Closed`, and `Structure/Topos.v`'s
  `topos_closed` field) turns up no functor category.
- `Theory/Sheaf.v:124,127` define `Presheaf`/`Presheaves` as bare naming
  aliases; nothing structural is attached to them.
- `Structure/Topos.v`'s `ElementaryTopos` has exactly one in-tree witness,
  `Instance/FinSet/Topos.v`'s `FinSet_Topos`; presheaf categories are not shown
  to be a topos either.

## Work to be done

Suggested module path: `Instance/Fun/LocallyCartesianClosed.v`.

- Assemble the corollary from the two dependencies below: every slice of a
  presheaf category is a presheaf category, presheaf categories are cartesian
  closed, and slicewise cartesian closure is local cartesian closure.
- Verify the pullback hypothesis: give presheaf categories a `HasPullbacks`
  instance (pointwise), since local cartesian closure is stated over a category
  with pullbacks.
- Record the resulting `LocallyCartesianClosed` instance for `Presheaves` and
  add it to `docs/INHABITATION.md` as the first non-trivial witness of that
  class.
- Where the composite goes through the equivalence of the slice with a presheaf
  category, transport the closed structure along the equivalence using
  `Theory/Equivalence/Monoidal.v`'s transport machinery rather than rebuilding
  exponentials by hand.

## Definition of Done

- [ ] `Presheaves` carries `HasPullbacks` (pointwise) and
      `LocallyCartesianClosed`, matching Awodey §9.7 Corollary 9.24 (setoid `≈`
      discipline; never `=` on morphisms)
- [ ] The proof routes through the slicewise characterization and the
      slice-is-a-presheaf-category lemma, i.e. it is the book's proof and not an
      independent construction
- [ ] `docs/INHABITATION.md` records the witness
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` reported for the instance (if it depends on stdlib
      axioms through `Instance/`, that must be enumerated in `docs/AXIOMS.md`
      per its existing scoping)
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated — flagship-level

## Verification

```bash
coqc -R . Category Instance/Fun/LocallyCartesianClosed.v

coqtop -R . Category -l Instance/Fun/LocallyCartesianClosed.v <<< \
  'Print Assumptions Presheaves_LocallyCartesianClosed.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Example 9.22 / Corollary 9.24;
the instance is genuinely for `Presheaves`, not for a special base category;
`docs/INHABITATION.md` reflects the new witness.

## Dependencies

Depends on: #718
Depends on: awodey:9.7:prop20
Depends on: awodey:9.7:lem23

<!-- catalog: {"ids":["awodey:9.7:example22","awodey:9.7:cor24"],"deps":["#718","awodey:9.7:prop20","awodey:9.7:lem23"]} -->

---8<---

```yaml
title: "Awodey 9.7: Fibrations of posets — the category Fib, and Fib/P as a locally cartesian closed category"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.7:example25, awodey:9.7:lem26, awodey:9.7:cor27]
deps_item_ids: [awodey:9.7:prop20]
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.7.

- Example 9.25 (fibrations of posets and the category Fib) — printed p. 249,
  PDF p. 258 (`awodey:9.7:example25`).
- Lemma 9.26 (Fib/P is cartesian closed) — printed p. 249, PDF p. 258
  (`awodey:9.7:lem26`).
- Corollary 9.27 (Fib/P is locally cartesian closed) — printed p. 250, PDF
  p. 259 (`awodey:9.7:cor27`).

## Background

A monotone map of posets is a fibration when every inequality below the image of
a point lifts uniquely; these maps form a (non-full) subcategory of posets. The
slice of that subcategory over a fixed poset P is equivalent to presheaves on P,
hence cartesian closed, and iterating gives local cartesian closure — while
Fib itself lacks a terminal object, which is precisely why the book's definition
of local cartesian closure is worth stating without that clause. See
[nLab: discrete fibration](https://ncatlab.org/nlab/show/discrete+fibration) and
[nLab: Grothendieck construction](https://ncatlab.org/nlab/show/Grothendieck+construction).

## Current state in the library

Every ingredient is missing.

- There is no ambient category of posets, so there is no subcategory of it to
  cut out: `Instance/Poset.v:116` builds the thin category **of one** poset, and
  its header at line 22 names the category of posets only as prose.
- There is no unique-lifting notion for monotone maps. The tree's fibration
  vocabulary (`Theory/Fibration.v`: `DCartesian`, `Cleaving`,
  `CartesianMorphism`, `ClovenFibration`, `SplitCleaving`) is Grothendieck
  fibration of *categories* with chosen, non-unique cartesian lifts — a
  different notion. "Discrete fibration" occurs once, as an nLab pointer in a
  comment (`Theory/Displayed.v:135`).
- No `Fib` category exists, so no slice of it and no statement about it can
  exist.
- The target of the claimed equivalence is also missing: presheaf categories
  are nowhere shown cartesian closed.
- The nearest in-tree relative,
  `Construction/Grothendieck/RoundTrip.v:1638` `RoundTrip_Equivalence`, compares
  split opfibrations of categories with the Grothendieck construction of an
  indexed category — the categorified correspondence, silent about posets,
  unique lifting and cartesian closure.

## Work to be done

Suggested module paths: `Instance/Pos/Fibration.v` and
`Instance/Pos/FibSlice.v`, over whatever the category of posets lands as under
the dependency below.

- Define the unique-lifting property for a monotone map and prove it is closed
  under composition and contains the identities, so that `Fib` is a wide (but
  non-full) subcategory of posets — use `Construction/Subcategory.v` rather than
  building a bespoke category.
- Prove the equivalence between `Fib/P` and presheaves on P: a fibration over P
  gives the fibre family, and the projection from the category of elements gives
  the quasi-inverse.
- Transport cartesian closure across the equivalence to obtain
  `Fib/P` cartesian closed.
- Derive local cartesian closure of `Fib/P` from the slicewise
  characterization, using the slice-of-a-slice identification.
- Record explicitly that `Fib` has no terminal object, and that this is the
  motivation for stating local cartesian closure without the terminal clause.

## Definition of Done

- [ ] `Fib` is defined as a wide subcategory of posets, with closure under
      composition proved
- [ ] `Fib/P ≃ Presheaves P` proved, and cartesian closure transported across it
- [ ] `Fib/P` shown locally cartesian closed, matching Awodey §9.7
      Corollary 9.27 (setoid `≈` discipline; never `=` on morphisms)
- [ ] The absence of a terminal object in `Fib` is recorded as a proved remark,
      not asserted in prose
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed (or, for `Instance/`-layer axiom use, enumerated
      in `docs/AXIOMS.md` per its existing scoping) for the equivalence and the
      two closure results
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated if `Fib` is indexed

## Verification

```bash
coqc -R . Category Instance/Pos/Fibration.v
coqc -R . Category Instance/Pos/FibSlice.v

coqtop -R . Category -l Instance/Pos/FibSlice.v <<< \
  'Print Assumptions FibSlice_Presheaves_equivalence. Print Assumptions FibSlice_LocallyCartesianClosed.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.7 Examples 9.25–9.27; the
lifting condition is the *unique*-lifting one (not the library's chosen-lift
Grothendieck fibration); the terminal-object caveat is proved, not asserted.

## Dependencies

Depends on: #641
Depends on: #718
Depends on: awodey:9.7:prop20

<!-- catalog: {"ids":["awodey:9.7:example25","awodey:9.7:lem26","awodey:9.7:cor27"],"deps":["#641","#718","awodey:9.7:prop20"]} -->

---8<---

```yaml
title: "Awodey 9.8: Smallness discharges the solution-set condition — the adjoint functor theorem for small complete categories"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.8:cor31]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.8, Corollary 9.31 — printed p. 254, PDF p. 263
(`awodey:9.8:cor31`).

## Background

Freyd's adjoint functor theorem requires a solution set at every object; when
the source category is *small* the objects already form a set, so the condition
is automatic and a limit-preserving functor out of a small complete category
simply has a left adjoint. (The corollary is not vacuous but it is delicate:
Freyd's thinness theorem says such a category is a preorder.) See
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem)
and [nLab: solution set condition](https://ncatlab.org/nlab/show/solution+set+condition).

## Current state in the library

The general theorem is proved; the corollary's hypothesis cannot be expressed.

- `Adjunction/GAFT.v:241` —
  `Theorem GAFT (U : C ⟶ D) (comp : @Complete C) (cont : @PreservesImageLimit C D U) (sols : forall d : D, SolutionSet U d) : { F : D ⟶ C & F ⊣ U }`.
  The `sols` argument is exactly the hypothesis the corollary claims to
  eliminate.
- `Adjunction/GAFT.v:159` `Record SolutionSet` (with `sol_index : Type`,
  `sol_obj`, `sol_arr`, and a Σ-typed `sol_covers`).
- There is **no smallness or local-smallness predicate anywhere** in the tree
  (`Class Small`, `Record Small`, `LocallySmall`: zero hits). Size is carried
  implicitly by universe polymorphism, as `Structure/Complete.v:29–37` records.
- The only in-tree producer of a `SolutionSet` is `Adjunction/SAFT.v:252`
  `SAFT_solution_set`, which routes through a cogenerator and well-powered
  indexing rather than through smallness.
- The corollary itself — complete + small + limit-preserving ⇒ a left adjoint —
  is not stated anywhere. Every "small complete category" hit in the tree is
  prose (`Structure/Complete.v:64–76`, `Instance/Poset.v:83–86`,
  `Adjunction/GAFT.v:103–105`).

## Work to be done

Suggested module path: `Adjunction/GAFT/Small.v`.

- Introduce a smallness discipline the library can actually use. The cheapest
  honest option is a `SmallCategory` record pinning the object and hom types to
  a fixed universe (the tree's universe parameters `{o h p}` are already
  explicit, so this is bookkeeping rather than new mathematics); alternatively,
  parameterize over a `Type`-level enumeration of objects. Whichever is chosen,
  the file header must say precisely what "small" means here, in the style of
  `Structure/Complete.v`'s size note.
- Construct the tautological solution set from smallness:
  `sol_index := { c : C & d ~> U c }`, `sol_obj := projT1`,
  `sol_arr := projT2`, and `sol_covers` with the mediating arrow `id` and the
  factorization discharged by `id_left`/`fmap_id`.
- State and prove `GAFT_small : SmallCategory C → @Complete C → @PreservesImageLimit C D U → { F : D ⟶ C & F ⊣ U }`
  as an immediate corollary of `GAFT`.
- Record the sharpness caveat in the header: by Freyd's thinness result such a C
  is a preorder, so the corollary is delicate rather than a free strengthening.
  Cite the already-filed thinness issue rather than restating the argument.
- Preferably also add a worked application, however small, so the corollary is
  not left uninstantiated (`Adjunction/GAFT/Examples.v` is the natural home).

## Definition of Done

- [ ] A smallness notion is defined, with its universe bookkeeping documented in
      the file header
- [ ] `GAFT_small` proved, matching Awodey §9.8 Corollary 9.31 (setoid `≈`
      discipline; never `=` on morphisms)
- [ ] The tautological solution-set construction is a named, reusable definition
- [ ] The Freyd-thinness caveat is disclosed in the header
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for `GAFT_small` and the solution-set
      construction
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated under the `Adjunction/GAFT.v`
      entry

## Verification

```bash
coqc -R . Category Adjunction/GAFT/Small.v

coqtop -R . Category -l Adjunction/GAFT/Small.v <<< \
  'Print Assumptions GAFT_small. Print Assumptions small_solution_set.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.8 Corollary 9.31; the
preservation hypothesis is the cone-level one that `GAFT` actually consumes;
the universe story is explained rather than silently assumed.

## Dependencies

Depends on: #436
Depends on: #423

<!-- catalog: {"ids":["awodey:9.8:cor31"],"deps":["#436","#423"]} -->

---8<---

```yaml
title: "Awodey 9.8: The adjoint functor theorem for complete posets — a join-preserving monotone map has a right adjoint"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.8:example32]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.8, Example 9.32 — printed p. 254, PDF p. 263
(`awodey:9.8:example32`).

## Background

Between complete posets, a monotone map has a right adjoint exactly when it
preserves all joins, the right adjoint being the map sending q to the join of
everything whose image lies below q. This is the order-theoretic shadow of the
adjoint functor theorem and the classical criterion for a Galois connection. See
[nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection),
[nLab: complete lattice](https://ncatlab.org/nlab/show/complete+lattice) and
[Wikipedia: Galois connection](https://en.wikipedia.org/wiki/Galois_connection).

## Current state in the library

Only the easy direction exists, and only in its general categorical form.

- `Adjunction/Continuity.v:223`
  `left_adjoint_preserves_colimits (A : F ⊣ U) : PreservesAllColimits F` is
  "a left adjoint is cocontinuous" for arbitrary categories; it is never
  instantiated at a poset.
- The substantive direction — cocontinuous ⇒ a right adjoint exists, with the
  explicit join formula and the two-way verification — is absent.
- There is no notion of a complete poset or complete lattice: the two "complete
  lattice" hits (`Structure/Complete.v:72`, `Instance/Poset.v`) are prose, and
  searches for suprema, least upper bounds or join-preserving maps return
  nothing.
- No lemma identifies a colimit of a discrete diagram in `Instance/Proset.v`'s
  thin category with a join, so even the easy direction cannot be *read* as the
  book's statement about monotone maps and joins.
- Galois connections are named 16 times in the tree, every one inside a comment
  block; `Instance/Poset.v:80–86` states the poset adjoint functor theorem in
  prose only. The one concrete order-theoretic adjunction that does exist is
  `Instance/Props.v`'s conjunction/implication pair, a single instance rather
  than a criterion.

## Work to be done

Suggested module path: `Instance/Pos/AFT.v`.

- Define complete posets (all joins exist) and join-preserving monotone maps,
  reusing whatever complete-lattice vocabulary lands under the dependency below
  rather than introducing a second notion.
- Prove the identification lemma: in a thin category built by
  `Instance/Proset.v:33` `Proset`, a colimit of a discrete diagram is a join and
  a limit is a meet. This makes the general (co)continuity vocabulary usable at
  posets and is the reusable part of this issue.
- Prove the criterion in both directions:
  - a monotone map with a right adjoint preserves joins (instantiate
    `left_adjoint_preserves_colimits` through the identification lemma);
  - a join-preserving monotone map has a right adjoint, given by the explicit
    join formula, with the two-way rule verified directly.
- Package the conclusion as an `Adjunction` instance between the two `Proset`
  categories, so it composes with the rest of the library's adjunction API.

## Definition of Done

- [ ] Complete posets and join-preserving maps defined
- [ ] The colimit-is-a-join / limit-is-a-meet identification proved for `Proset`
- [ ] Both directions of the criterion proved, with the explicit right-adjoint
      formula, matching Awodey §9.8 Example 9.32 (setoid `≈` discipline; never
      `=` on morphisms)
- [ ] The result is an `Adjunction` instance, not a hand-rolled bi-implication
- [ ] `Instance/Poset.v:80–86` prose updated to cite the theorem instead of
      describing it as folklore
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for the criterion in both directions
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated if the poset adjoint functor
      theorem is indexed

## Verification

```bash
coqc -R . Category Instance/Pos/AFT.v

coqtop -R . Category -l Instance/Pos/AFT.v <<< \
  'Print Assumptions poset_right_adjoint_of_cocontinuous. Print Assumptions proset_colimit_is_join.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.8 Example 9.32 as a
biconditional; the easy direction is genuinely *derived* from the general
cocontinuity theorem via the identification lemma, not re-proved by hand.

## Dependencies

Depends on: #380
Depends on: #684
Depends on: #641

<!-- catalog: {"ids":["awodey:9.8:example32"],"deps":["#380","#684","#641"]} -->

---8<---

```yaml
title: "Awodey 9.8/9.9 Ex 10: Recursion from a natural numbers object — arithmetic, functor iteration, and exponentiation in a cartesian closed category"
labels: [book:awodey, kind:theory, coverage-gap]
projects: [5]
covers: [awodey:9.8:example39, awodey:9:ex10]
deps_item_ids: []
deps_pending: []
```

## Source

Awodey, *Category Theory*, Chapter 9.

- Example 9.39 (recursive definitions from a natural numbers object: addition,
  multiplication, iteration of an endofunctor) — printed p. 259, PDF
  pp. 268–270 (`awodey:9.8:example39`).
- Exercise 10 (exponentiation on a natural numbers object in a cartesian closed
  category) — printed p. 264, PDF p. 273 (`awodey:9:ex10`).

## Background

The universal property of a natural numbers object *is* definition by
recursion: from a point and an endomorphism one gets a unique arrow out of N.
Instantiating this gives addition and multiplication as arrows N × N ⟶ N; in a
cartesian closed category the exponential transpose lets the same recursion
define iteration of an endofunctor and, on the natural numbers object itself,
exponentiation. See
[nLab: natural numbers object](https://ncatlab.org/nlab/show/natural+numbers+object)
and [Wikipedia: Natural number object](https://en.wikipedia.org/wiki/Natural_number_object).

## Current state in the library

Absent, along with everything it is built on.

- There is no natural numbers object in the tree, in any category:
  `natural numbers object` and `NNO` return no relevant hits (the two
  case-insensitive matches are the word "cannot").
- The nearest structure is explicitly withheld:
  `Theory/Adamek/Corollaries.v:87` defines the option endofunctor and its header
  at lines 76–80 states that the initial-algebra theorem for it "is not stated in
  the tree — it is recorded here as the informal cross-reference … not as a
  proven result".
- No successor morphism on any categorical object exists; the `PeanoNat` hits
  are stdlib arithmetic used for arity bookkeeping.
- `Structure/Cartesian/Closed.v` has `curry`/`uncurry`/`eval`/`flip` and their
  laws, but no recursion combinator.
- The nearest relative of functor iteration is `Construction/Chain.v:33`
  `chain_obj`, which is the n-th iterate of an endofunctor *pinned at the initial
  object*, defined by Coq's own `Fixpoint` on `nat` and indexed by
  `Instance/Omega.v`'s thin order category — not obtained from a universal
  property, and therefore not this example's content.
- Nothing states that the discrete category on the naturals is a natural numbers
  object in `Cat`.

## Work to be done

Suggested module paths: `Structure/NNO/Recursion.v` and
`Structure/NNO/Exponentiation.v`, over whatever the natural numbers object lands
as under the dependency below.

- Derive the recursor from the universal property and give it a usable API
  (a `rec` combinator plus its two computation rules and its uniqueness lemma),
  in the style of `Theory/Recursion.v:63,72` `cata_commutes`/`cata_unique`.
- Define addition and multiplication as arrows N × N ⟶ N by recursion in the
  first argument, and prove the two recursion equations for each. Prove at least
  the associativity and unit laws so the API is demonstrably usable.
- In a cartesian closed category, define exponentiation N × N ⟶ N by recursion
  through the exponential transpose, and prove its recursion equations
  (Exercise 10).
- Define iteration of an endofunctor from the universal property (rather than by
  `Fixpoint`), and prove that the discrete category on the natural numbers is a
  natural numbers object in `Cat`, which is what makes the iteration a functor.
- Connect the new iteration to `Construction/Chain.v:33` `chain_obj`, showing
  the existing chain is the instance at the initial object.

## Definition of Done

- [ ] A recursor API is derived from the natural numbers object's universal
      property, with computation rules and uniqueness
- [ ] Addition, multiplication and exponentiation are defined by recursion and
      their equations proved, matching Awodey §9.8 Example 9.39 and §9.9
      Exercise 10 (setoid `≈` discipline; never `=` on morphisms)
- [ ] Functor iteration is obtained from the universal property, and the
      discrete category on the naturals is proved to be a natural numbers object
      in `Cat`
- [ ] `Construction/Chain.v`'s `Fixpoint`-defined chain is related to the new
      iteration
- [ ] `Theory/Adamek/Corollaries.v:76–80` updated once the initial-algebra
      reading is available
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` closed for the recursor and the three arithmetic
      operations
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated

## Verification

```bash
coqc -R . Category Structure/NNO/Recursion.v
coqc -R . Category Structure/NNO/Exponentiation.v

coqtop -R . Category -l Structure/NNO/Recursion.v <<< \
  'Print Assumptions nno_rec. Print Assumptions nno_add_succ.'
coqtop -R . Category -l Structure/NNO/Exponentiation.v <<< \
  'Print Assumptions nno_exp_succ.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.8 Example 9.39 and §9.9
Exercise 10; the operations are defined *by the universal property*, not by
Coq's `Fixpoint` and then transported; the exponentiation exercise genuinely
uses the exponential transpose.

## Dependencies

Depends on: #637

<!-- catalog: {"ids":["awodey:9.8:example39","awodey:9:ex10"],"deps":["#637"]} -->

---8<---

```yaml
title: "Awodey 9.9 Ex 8: Indexed sets, change of base, and Lawvere's hyperdoctrine diagram"
labels: [book:awodey, kind:exercise, coverage-gap]
projects: [5]
covers: [awodey:9:ex8]
deps_item_ids: [awodey:9.7:construction-change-of-base, awodey:9.7:prop18]
deps_pending: []
```

## Source

Awodey, *Category Theory*, §9.9, Exercise 8 — printed p. 263, PDF pp. 272–273
(`awodey:9:ex8`).

## Background

The exercise assembles the chapter's threads into Lawvere's hyperdoctrine
picture: the Yoneda embedding of a set regarded as a discrete category, the
compatibility of the left adjoint of reindexing with Yoneda, the passage from
indexed families to bundles, the powerset of a set as a full subcategory of the
slice with a left adjoint given by image, and the resulting diagram joining the
slice-level adjoint triple to the powerset-level one. See
[nLab: hyperdoctrine](https://ncatlab.org/nlab/show/hyperdoctrine) and
[nLab: indexed set](https://ncatlab.org/nlab/show/indexed+set).

## Current state in the library

Only the two base-change functors exist; not one arrow of the diagram is proved
adjoint to another.

- `Functor/Hom/Yoneda.v:231` `Yoneda_Embedding` gives full faithfulness of the
  Yoneda embedding for an arbitrary category, but it is never specialized to a
  discrete category, and there is no category of indexed sets. (It *is*
  expressible — `Instance/Discrete.v`'s `DiscreteCat` plus `Instance/Fun.v`
  give the functor category — but it is never instantiated;
  `DiscreteCat` is used in-tree only as a diagram shape for indexed products.)
- `Construction/Slice/Pullback.v:50` and `:67` give post-composition and base
  change on slices; the adjunction between them is the commented-out stub at
  lines 121–127, and the dependent product does not exist.
- The equivalence between indexed families and bundles is not stated anywhere:
  `Construction/Slice.v:73–76` asserts it in the background essay, citing
  Leinster and nLab, with no Coq statement.
- There is no powerset object in `Sets` and no inclusion of a powerset into a
  slice, hence no left adjoint given by image.
- The compatibility of the reindexing left adjoint with Yoneda has no
  counterpart at all.
- The powerset-level triple appears only as header prose
  (`Theory/Adjunction.v:75–76`, `Instance/Poset.v:70`).

## Work to be done

Suggested module path: `Instance/Sets/Hyperdoctrine.v`.

- Specialize the Yoneda embedding to a discrete category and identify the
  resulting presheaf category with the category of indexed sets.
- Prove the change-of-base compatibility: the left adjoint of reindexing,
  composed with the Yoneda embedding of the source, is naturally isomorphic to
  the Yoneda embedding of the target composed with the index map.
- Compose the Yoneda embedding with the families-to-bundles equivalence and read
  the change-of-base square in the slices.
- Define the powerset of a set as a preorder category, the inclusion into the
  slice sending a subset to its inclusion map, and prove it has a left adjoint
  given by image (equivalently, by the epi-mono factorization —
  `Instance/Sets/Image.v:143` `Sets_Image_Factorization` is the in-tree donor).
- Assemble the diagram and prove which squares commute: the slice-level triple
  and the powerset-level triple related by the image/inclusion adjunction at
  each index.

Because the exercise is one mathematical development it stays a single issue,
but it is genuinely gated on the change-of-base and dependent-product work
listed under Dependencies; do not start it before those land.

## Definition of Done

- [ ] Indexed sets presented as presheaves on a discrete category, with the
      Yoneda specialization stated
- [ ] The change-of-base/Yoneda compatibility proved as a natural isomorphism
- [ ] The powerset preorder, its inclusion into the slice, and the image left
      adjoint constructed and proved adjoint
- [ ] The commuting squares of the hyperdoctrine diagram stated and proved,
      matching Awodey §9.9 Exercise 8 (setoid `≈` discipline; never `=` on
      morphisms)
- [ ] No `Admitted`, `admit`, `Axiom` or `Parameter` in the new development
- [ ] `Print Assumptions` reported for each principal artifact (for
      `Instance/`-layer stdlib axiom use, enumerated in `docs/AXIOMS.md` per its
      existing scoping)
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds under the Coq 8.19 and 8.20 nix targets
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated if the hyperdoctrine diagram is
      indexed

## Verification

```bash
coqc -R . Category Instance/Sets/Hyperdoctrine.v

coqtop -R . Category -l Instance/Sets/Hyperdoctrine.v <<< \
  'Print Assumptions image_inclusion_adjunction. Print Assumptions shriek_yoneda_iso.'

make clean && make
nix build .#category-theory_8_19
nix build .#category-theory_8_20
make todo
```

Reviewer checklist: statement matches Awodey §9.9 Exercise 8 clause by clause
(a)–(f); the powerset really is a full subcategory of the slice; the claimed
commuting squares are each proved rather than asserted in a comment.

## Dependencies

Depends on: #709
Depends on: #382
Depends on: #384
Depends on: #387
Depends on: #717
Depends on: awodey:9.7:construction-change-of-base
Depends on: awodey:9.7:prop18

<!-- catalog: {"ids":["awodey:9:ex8"],"deps":["#709","#382","#384","#387","#717","awodey:9.7:construction-change-of-base","awodey:9.7:prop18"]} -->

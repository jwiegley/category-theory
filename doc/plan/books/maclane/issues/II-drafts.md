```yaml
title: "MacLane II.1: The ETAC statement language and the duality principle"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.1:def1, maclane:II.1:def2, maclane:II.1:thm1, maclane:II.1:remark2, maclane:II.2:lem1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (Springer GTM 5), §II.1 "Duality" and §II.2 "Contravariance and Opposites", book pp. 31–33 (PDF 41–43). Items: `maclane:II.1:def1` (the elementary first-order language of an abstract category), `maclane:II.1:def2` (the dual of a statement), `maclane:II.1:thm1` (the duality principle), `maclane:II.1:remark2` (extension to several categories with functors), `maclane:II.2:lem1` (statement duality is realized by the opposite category).

## Background

Mac Lane introduces a first-order language for category theory (atomic assertions about domains, codomains, identities, and composites), defines the syntactic dual of a statement by interchanging domain with codomain and reversing composites, and states the duality principle: whenever a statement follows from the category axioms, so does its dual. The bridge to semantics is the lemma that a statement holds of arrows in C exactly when its dual holds of the corresponding arrows in C^op. See nLab: [duality](https://ncatlab.org/nlab/show/duality) and Wikipedia: [Dual (category theory)](https://en.wikipedia.org/wiki/Dual_(category_theory)).

## Current state in the library

- `Theory/Metacategory.v:133` (`Metacategory`) and `Theory/Metacategory.v:261` (`FromArrows`) formalize the arrows-only first-order axioms shallowly, on the model side only; every model yields a `Category`.
- `Solver/Expr.v` deep-embeds a quantifier-free *equational* fragment of morphism expressions (reify/denote/decide) but has no connectives, quantifiers, or dual operator.
- The semantic content of dualization is realized concept-by-concept: `Construction/Opposite.v:106` (`Opposite`, with `op_invol` at line 126), `Structure/Initial.v:96` (`Initial C := Terminal (C^op)`), `Structure/Limit.v:158` (`Colimit := Limit (F^op)`), `Theory/Monad.v:144` (`Comonad := @Monad (C^op) (M^op)`), `Construction/Opposite.v:146` (`Isomorphism_Opposite`), and the book's own worked instance `Structure/Initial.v:112` (`zero_unique := one_unique` at C^op).
- Precise gap (all five covered items): there is no reified type of ETAC statements, hence no dualization operator on statements, no satisfaction relation, no involution theorem at statement level, no single lemma "Sigma holds in C^op iff Sigma* holds in C", and no quantified duality principle. Some dualization-table entries also lack named transfer lemmas: `Epic` is documented as "`Monic f` in `C^op`" (`Theory/Morphisms.v:104`) with no conversion lemma either way (searches for `Monic_op`/`Epic_op` return 0 hits).

## Work to be done

Suggested module: `Theory/Metacategory/ETAC.v` (with the transfer lemmas landing in `Theory/Morphisms.v` or `Construction/Opposite.v`).

1. Deep-embed the single-category ETAC language: an inductive syntax of formulas over object and arrow variables whose atoms express "a is the domain of f", "a is the codomain of f", "i is the identity arrow of a", and "h is the composite of g and f", closed under the propositional connectives and quantifiers over objects and arrows; define sentences (closed formulas).
2. Define a satisfaction relation between a `Category` (with a variable assignment) and a formula, rendering equality of arrows as the hom-setoid `≈`.
3. Define the syntactic dual operator on formulas (swap domain/codomain atoms, reverse composite atoms) and prove it involutive: dualizing twice is the identity on syntax.
4. Prove the semantic duality lemma (Mac Lane's II.2 lemma, by induction on formulas): C satisfies the dual of Sigma under an assignment iff C^op satisfies Sigma under the transported assignment; the strict involution `op_invol` keeps the statement transport-free.
5. Derive the duality principle in its semantic form: if a sentence holds in every category, its dual holds in every category.
6. Extension to functor statements (`maclane:II.1:remark2`): either extend the language with a functor symbol (two category sorts, atoms `T c = b`, `T f = h`) and show the functor axioms are self-dual under simultaneous dualization via `Opposite_Functor` — or, at minimum, record the one-functor case as a theorem about `F^op : C^op ⟶ D^op` and document the scoping in the file header.
7. Close the dualization table: named lemmas transferring `Monic`/`Epic` across `op` (both directions) and the left-inverse/right-inverse pair, alongside the existing `Isomorphism_Opposite`.

Donors: `Theory/Metacategory.v` (header essay and shallow axioms), `Solver/Expr.v` (reify/denote pattern), `Construction/Opposite.v`, `Functor/Opposite.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §§II.1–II.2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the satisfaction relation, the involution theorem, the semantic duality lemma, the duality principle)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Metacategory/ETAC.v
echo 'Require Import Category.Theory.Metacategory.ETAC. Print Assumptions duality_principle.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.1 (pp. 31–32) and §II.2 (p. 33), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.1:def1","maclane:II.1:def2","maclane:II.1:thm1","maclane:II.1:remark2","maclane:II.2:lem1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.2: The op involution as a functor on Cat"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.2:construction1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.2, book p. 33 (PDF 43). Item: `maclane:II.2:construction1` (the opposite functor T^op and the covariant op involution on Cat).

## Background

Sending each category to its opposite and each functor T to T^op (same object and arrow maps, read in the opposite categories) is a *covariant* endofunctor of the category of categories; combined with its action on 2-cells it is the duality involution on Cat. See nLab: [opposite category](https://ncatlab.org/nlab/show/opposite+category).

## Current state in the library

- `Functor/Opposite.v:31` (`Opposite_Functor`) constructs T^op : C^op ⟶ D^op with the same object/arrow maps, and `Functor/Opposite.v:49` proves `(F^op)^op = F` by reflexivity; `Natural/Transformation/Opposite.v:28` gives the 2-cell reversal.
- Precise gap: no bundled `Functor` instance has `Opposite` as its object map (search for `fobj := Opposite` and variants: 0 hits). The functoriality claims — (S ∘ T)^op agrees with S^op ∘ T^op and (Id)^op with Id — hold definitionally but are never packaged; the finer fact that op reverses 2-cells ("the 2-functor Cat^co ⟶ Cat") exists only as documentation (`Functor/Opposite.v:29`, `Natural/Transformation/Opposite.v:24`).

## Work to be done

Suggested module: `Instance/Cat/Opposite.v` (or extend `Functor/Opposite.v`).

1. Define `Op : Cat ⟶ Cat` with `fobj := Opposite` and `fmap := Opposite_Functor`; discharge `fmap_respects` (a natural isomorphism F ≅ G in [C, D] induces F^op ≅ G^op — the components are the inverse iso's components, since oppositization reverses 2-cells), `fmap_id`, and `fmap_comp`.
2. Prove the involution at the functor level: `Op ◯ Op ≈[Cat] Id`, riding `op_invol` / `Opposite_Functor_invol`.
3. Where the strict statement is wanted, add the `StrictCat` variant `Op_Strict : StrictCat ⟶ StrictCat`, whose laws hold on the nose.
4. Record in the header the 2-cell-reversal caveat (the honest formulation is Cat^co ⟶ Cat; the Cat-level instance works precisely because the hom-equivalence of Cat consists of invertible 2-cells).

Donors: `Construction/Opposite.v`, `Functor/Opposite.v`, `Natural/Transformation/Opposite.v`, `Instance/Cat.v`, `Instance/StrictCat.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (`Op`, the involution lemma)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Cat/Opposite.v
echo 'Require Import Category.Instance.Cat.Opposite. Print Assumptions Op.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.2 (p. 33), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.2:construction1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.2: Open(X) and the presheaf of continuous functions"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.2:construction7]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.2, book p. 35 (PDF 45). Item: `maclane:II.2:construction7` (the sheaf of germs of continuous functions as a contravariant functor on the open-set poset).

## Background

For a topological space X, the open sets ordered by inclusion form a poset, hence a thin category Open(X); assigning to each open U the set of continuous real-valued functions on U, with restriction as the arrow action, yields a contravariant functor Open(X)^op ⟶ Set — the standard first example of a presheaf, and of a sheaf. See nLab: [presheaf](https://ncatlab.org/nlab/show/presheaf) and Wikipedia: [Sheaf (mathematics)](https://en.wikipedia.org/wiki/Sheaf_(mathematics)).

## Current state in the library

- The general frame exists and is more general than the example: `Theory/Sheaf.v:124` (`Presheaf U C := U^op ⟶ C`, with the restriction-map reading in its header), sites and the sheaf condition (`Site` at line 159, `Sheaf` at line 192), and preorders-as-categories (`Instance/Proset.v:33`, `Proset`).
- Precise gap: the concrete example cannot currently be assembled — the tree has no topological spaces, no category Top, no Open(X) inclusion poset, and no continuous real-valued functions (verified searches: `TopologicalSpace`/`open_sets`/`germs`/`real-valued` all return prose-only or zero hits).

## Work to be done

Suggested module: `Instance/Top/Presheaf.v` (over the Top infrastructure of the referenced issue).

1. From the topological-space definition supplied by the Top issue, build `Open X` as the inclusion-ordered thin category of open subsets of a space X (donor: `Instance/Proset.v`).
2. Define the presheaf of continuous real-valued functions: object action U to the setoid of continuous maps U to R; arrow action restriction along an inclusion; contravariant functoriality (restriction composes and preserves identities).
3. Package it through the in-tree vocabulary as a `Presheaf (Open X) Sets` and note in the header the relation to `Theory/Sheaf.v`'s sheaf condition (with that file's disclosed per-leg limitation), leaving a full sheaf-condition verification to the sheaf-refoundation ledger item.
4. Header note on the smooth-manifold variant as an out-of-tree aside.

Donors: `Theory/Sheaf.v`, `Instance/Proset.v`, `Instance/Sets.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping; stdlib real-number axioms, if used, disclosed per the instance-layer policy of docs/AXIOMS.md)
- [ ] `Print Assumptions` run for each principal artifact, with any stdlib assumptions enumerated in the header
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Top/Presheaf.v
echo 'Require Import Category.Instance.Top.Presheaf. Print Assumptions ContinuousPresheaf.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.2 (p. 35), paraphrased.

## Dependencies

Depends on: #259

<!-- catalog: {"ids":["maclane:II.2:construction7"],"deps":["maclane:I.7:construction4"]} -->
---8<---
```yaml
title: "MacLane II.2: Restriction of scalars and the fibered category of all modules"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.2:construction8, maclane:II.2:construction9]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.2, book p. 35 (PDF 45). Items: `maclane:II.2:construction8` (restriction of scalars: Mod as a contravariant functor on rings), `maclane:II.2:construction9` (the category of all modules over all rings, fibered over rings).

## Background

A ring morphism rho : R -> S turns every right S-module into a right R-module by acting through rho; this makes module categories contravariantly functorial in the ring. Collecting all pairs (ring, module) into one category with a projection to rings is Mac Lane's preview of fibered categories: the fibre over R is Mod-R. See nLab: [Grothendieck fibration](https://ncatlab.org/nlab/show/Grothendieck+fibration) and Wikipedia: [Fibred category](https://en.wikipedia.org/wiki/Fibred_category).

## Current state in the library

- The general machinery the example previews is complete and strong: displayed categories (`Theory/Displayed.v`), the total category and projection (`Construction/Displayed/Total.v`), the Grothendieck construction over a coherent `IndexedCat` (`Construction/Grothendieck.v:406`, `Grothendieck`; `:409`, `Grothendieck_Proj`), the projection shown a split opfibration (`Construction/Grothendieck/Fibration.v:120`), fibre recovery (`Construction/Grothendieck/Fiber.v`), and both presentations of fibrations with the round-trip equivalence (`Theory/Fibration.v`, `Construction/Grothendieck/RoundTrip.v`). The `Construction/Grothendieck.v` header essay explicitly cites the modules-over-rings motivation (lines 114–115).
- Precise gap: the concrete witness is not constructible today — the library has no ring theory and no module theory (searches for `Ring`/`Rng`/`R-Mod`/`restriction of scalars` return prose or unrelated colour-base-change hits only). Absent are: the restriction-of-scalars functor between module categories, the contravariant (indexed) assignment from rings to categories, and its total category with projection.

## Work to be done

Suggested module: `Instance/Rng/Mod.v` (over the Rng and R-Mod infrastructure of the referenced issues).

1. Define the restriction-of-scalars functor along a ring morphism rho : R -> S, sending a right S-module to its R-module pull-back, functorial in the module and contravariantly functorial in rho (composition and identity laws).
2. Package the assignment R to Mod-R, rho to restriction, as a coherent `IndexedCat` over Rng^op (donor `Construction/Indexed.v`; or via `Construction/Grothendieck/Strict.v` if the fibrewise-UIP route applies).
3. Assemble the total category Mod of pairs (R, A) with morphisms (rho, f), as the Grothendieck construction; identify the projection with `Grothendieck_Proj` and the fibres with the module categories via `fiber_grothendieck_equiv`.
4. Record that this realizes Mac Lane's (rho, f)-morphism description on the nose (setoid rendering).

Donors: `Construction/Grothendieck.v` and satellites, `Construction/Indexed.v`, `Construction/Displayed/Total.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (restriction functor, the indexed category, the total category and projection)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Rng/Mod.v
echo 'Require Import Category.Instance.Rng.Mod. Print Assumptions ModTotal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.2 (p. 35), paraphrased.

## Dependencies

Depends on: #257
Depends on: #258

<!-- catalog: {"ids":["maclane:II.2:construction8","maclane:II.2:construction9"],"deps":["maclane:I.7:def1","maclane:I.7:construction3"]} -->
---8<---
```yaml
title: "MacLane II.3: Bifunctors and transformations from partial data (Propositions 1 and 2)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.3:prop1, maclane:II.3:def3, maclane:II.3:prop2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3, book pp. 37–38 (PDF 47–48). Items: `maclane:II.3:prop1` (Proposition 1: a bifunctor is determined by its partial functors), `maclane:II.3:def3` (naturality in one variable), `maclane:II.3:prop2` (Proposition 2: bifunctor naturality is componentwise naturality).

## Background

A bifunctor can be assembled from a family of functors in each separate variable, agreeing on objects, precisely when the two one-sided arrow actions commute (the interchange condition); and a family of arrows between two bifunctors is a natural transformation precisely when it is natural in each variable separately. See nLab: [bifunctor](https://ncatlab.org/nlab/show/bifunctor).

## Current state in the library

- The forward directions are present: for any `F : C ∏ D ⟶ E`, the partial actions are separately functorial and satisfy the commutation condition (`Functor/Bifunctor.v:80/91` `bimap_comp_id_left/right`, `:104/116` `bimap_id_right_left`/`bimap_id_left_right`); a `Transform` over a product category instantiated at (f, id) and (id, g) gives per-variable naturality (`Theory/Natural/Transformation.v:113`).
- A curried avatar of the Proposition 1 converse exists: `Instance/Cat/Cartesian/Closed.v:59` (`Cat_Closed`'s `exp_iso.from`) uncurries a functor `A ⟶ [B, C]` into a bifunctor using exactly the common-value formula, with round trips proven.
- Precise gaps: the two-family iff of Proposition 1 is never stated (no constructor from families L_c, M_b plus the interchange condition; searches for `Build_Bifunctor`/`bifunctor_from`/`from_partial`: 0 hits); there is no reusable one-variable-naturality predicate for families between bifunctors over distinct categories (`Theory/Naturality.v:165` `ArityTwo` covers only same-category object maps; the `PartialApply_*` functors are commented-out exploratory code); and neither direction of Proposition 2 is recorded, in particular no constructor assembling a `Transform` over `B ∏ C` from two per-variable natural families.

## Work to be done

Suggested module: `Functor/Bifunctor/Partial.v`.

1. Bundle the partial functors: for `F : B ∏ C ⟶ D` and objects c, b, the functors `F(-, c) : B ⟶ D` and `F(b, -) : C ⟶ D` as named `Functor` instances.
2. Proposition 1, converse: a constructor taking families `L c : B ⟶ D` and `M b : C ⟶ D` with `L c b = M b c` on objects and the commutation condition `M b' g ∘ L c f ≈ L c' f ∘ M b g`, producing a bifunctor `S : B ∏ C ⟶ D` whose partial functors are the given families; state the full iff and the uniqueness of S (up to natural isomorphism, the setoid rendering of Mac Lane's uniqueness).
3. Definition: `NaturalIn1`/`NaturalIn2` predicates on a family `alpha (b, c) : S (b, c) ~> S' (b, c)` between bifunctors — for fixed c the components form a `Transform` of the partial functors (and dually).
4. Proposition 2, both directions: `alpha` underlies a `Transform S S'` over `B ∏ C` iff it is natural in each variable separately; include the assembling constructor for the substantive direction.

Donors: `Functor/Bifunctor.v` (the four partial/commutation lemmas and `bimap_comp`), `Instance/Cat/Cartesian/Closed.v` (currying), `Theory/Naturality.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.3 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the Prop 1 constructor and iff; the Prop 2 iff)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Functor/Bifunctor/Partial.v
echo 'Require Import Category.Functor.Bifunctor.Partial. Print Assumptions Bifunctor_from_partial.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.3, Propositions 1 and 2 (pp. 37–38), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.3:prop1","maclane:II.3:def3","maclane:II.3:prop2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.3: The cylinder C x 2 and the universal natural transformation"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.3:construction5, maclane:II.4:ex8]
deps_item_ids: [maclane:II.4:construction1]
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3, book p. 39 (PDF 49), and §II.4 Exercise 8, book p. 42 (PDF 52). Items: `maclane:II.3:construction5` (the cylinder C x 2 and the universal natural transformation), `maclane:II.4:ex8` (relating the cylinder and arrow-category encodings of a natural transformation).

## Background

With 2 the walking arrow, the product C x 2 is a cylinder on C: two copies of C joined by connecting arrows, carrying a transformation mu between the two inclusion functors that is universal — every natural transformation between functors out of C factors through it by a unique functor on the cylinder. Under the exponential transpose of Cat this encoding corresponds to the functor-into-the-arrow-category encoding. See nLab: [natural transformation](https://ncatlab.org/nlab/show/natural+transformation).

## Current state in the library

- The ingredients exist: the walking arrow `_2` (`Instance/Two.v:134`), binary products of categories (`Construction/Product.v:95`), and the currying isomorphism of Cat (`Instance/Cat/Cartesian/Closed.v:47`, `Cat_Closed`, whose `exp_iso` at B := `_2` is exactly the transpose the exercise invokes).
- Precise gap (verified searches: `cylinder`, `universal natural transformation`: 0 hits): the endpoint functors, the transformation mu with components indexed by the walking arrow's non-identity morphism, the unique-factorization universal property, and any statement relating the C ∏ 2 encoding to the arrow-category/functor-category encoding are all absent. `Construction/Arrow.v:104–108` discloses that even the arrow-category side's classification is documentation-level (covered by the II.4 arrow-category issue below).

## Work to be done

Suggested module: `Construction/Cylinder.v`.

1. Define the endpoint functors `T0, T1 : C ⟶ C ∏ _2` (identity on the C component, constant at each end of the walking arrow) and the transformation `mu : T0 ⟹ T1` whose component at c is (id[c], the nonidentity arrow).
2. Universal property: for any `S T : C ⟶ B` and `tau : S ⟹ T`, construct `F : C ∏ _2 ⟶ B` with `F ◯ T0 ≈ S`, `F ◯ T1 ≈ T`, and the whiskered `mu` mapping to `tau` (component-wise `≈`); prove uniqueness of F up to `≈` among functors with these properties.
3. Exercise 8: with the classification of functors into the arrow category (dependency below), prove that `Cat_Closed`'s `exp_iso` at exponent `_2` carries the cylinder encoding `C ∏ _2 ⟶ B` to the arrow-category encoding `C ⟶ [_2, B]` of the same natural transformation, naturally in the triple (S, T, tau).

Donors: `Instance/Two.v`, `Construction/Product.v`, `Instance/Cat/Cartesian/Closed.v`, `Theory/Natural/Transformation.v` (whiskering).

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.3 (p. 39) and §II.4 Ex. 8 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (mu, the factorization functor, the uniqueness lemma, the transpose comparison)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Cylinder.v
echo 'Require Import Category.Construction.Cylinder. Print Assumptions cylinder_universal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.3 (p. 39, display (6)) and §II.4 Ex. 8 (p. 42), paraphrased.

## Dependencies

Depends on: maclane:II.4:construction1 (the arrow-category-as-[2,B] issue; resolved to an issue number in the dependency pass)

<!-- catalog: {"ids":["maclane:II.3:construction5","maclane:II.4:ex8"],"deps":["maclane:II.4:construction1"]} -->
---8<---
```yaml
title: "MacLane II.3: Product categories subsume products of monoids, groups, and sets"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.3:ex1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3 Exercise 1, book p. 39 (PDF 49). Item: `maclane:II.3:ex1`.

## Background

The product of categories restricts, along the standard embeddings, to the familiar products of algebraic structures: delooped monoids and groups multiply componentwise, and discrete categories multiply as sets. See nLab: [product category](https://ncatlab.org/nlab/show/product+category).

## Current state in the library

- The binary product of categories is present (`Construction/Product.v:95`), as is `DiscreteCat` (`Instance/Discrete.v`).
- Precise gap (verified): no delooping of a monoid or group into a one-object `Category` exists in-tree (only one-object prose in essays and the one-object *bi*category delooping of `Theory/Bicategory/OneObject.v`), and no lemma identifies `DiscreteCat (A * B)` with `DiscreteCat A ∏ DiscreteCat B`; none of the three specializations is formalized.

## Work to be done

Suggested module: `Construction/Product/Special.v` (or alongside the delooping construction of the dependency issue).

1. With the monoid/group deloopings from #220: an isomorphism (in Cat, i.e., up to natural isomorphism — or strict, in StrictCat) between the delooping of a product monoid and the product of the deloopings; note the group case is the same statement restricted to groups.
2. Discrete case: `DiscreteCat (A * B) ≅ DiscreteCat A ∏ DiscreteCat B`.
3. Header note: these three make Mac Lane's point that `∏` on Cat restricts to the classical products along the standard full embeddings.

Donors: `Construction/Product.v`, `Instance/Discrete.v`, the delooping construction from #220.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.3 Ex. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Product/Special.v
echo 'Require Import Category.Construction.Product.Special. Print Assumptions Discrete_Product.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.3 Ex. 1 (p. 39), paraphrased.

## Dependencies

Depends on: #219
Depends on: #220

<!-- catalog: {"ids":["maclane:II.3:ex1"],"deps":["maclane:I.2:construction2","maclane:I.2:construction3"]} -->
---8<---
```yaml
title: "MacLane II.3: Preorders are closed under products and functor categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.3:ex2, maclane:II.4:ex4]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3 Exercise 2, book p. 39 (PDF 49), and §II.4 Exercise 4, book p. 41 (PDF 51). Items: `maclane:II.3:ex2` (the product of two preorders is a preorder), `maclane:II.4:ex4` (the functor category between preorders is a preorder of monotone maps ordered pointwise).

## Background

Preorders are exactly the thin categories, and thinness is closed under the basic constructions: a product of thin categories is thin, and a functor category into a thin category is thin — for preorders P, Q the category of functors P ⟶ Q is the pointwise order on monotone maps. See nLab: [thin category](https://ncatlab.org/nlab/show/thin+category).

## Current state in the library

- `Instance/Proset.v:33` (`Proset`) renders any preorder as a category, and `Construction/Enriched/Two.v` identifies 2-enriched functors with monotone maps; `Instance/Fun.v` provides functor categories in general.
- Precise gap (verified): no thinness predicate exists as vocabulary (thin-ness appears only in file headers), so neither closure statement is even stateable; `Instance/Proset.v` has no product lemma, and no result describes `[P, Q]` for prosets or shows it thin (searches over `thin`, `Proset`, `pointwise.*order`, `monotone`: construction-level hits only).

## Work to be done

Suggested module: `Theory/Thin.v` (predicate) plus `Instance/Proset/Closure.v` (instances).

1. Define a thinness predicate on categories: any two parallel morphisms are `≈`-equal.
2. Prove `Proset P` is thin; prove thinness is closed under `∏` (covers II.3 Ex. 2 via Proset instances) and under functor categories `[C, D]` when D is thin (covers the structural half of II.4 Ex. 4).
3. For prosets P, Q: describe `[Proset P, Proset Q]` concretely — objects are monotone maps, and the hom-existence relation is the pointwise order; package as an equivalence (or isomorphism) with the Proset of the pointwise-ordered monotone-map preorder.

Donors: `Instance/Proset.v`, `Construction/Product.v`, `Instance/Fun.v`, `Construction/Enriched/Two.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.3 Ex. 2 and §II.4 Ex. 4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the thinness predicate lemmas, the pointwise-order description)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Thin.v Instance/Proset/Closure.v
echo 'Require Import Category.Instance.Proset.Closure. Print Assumptions Thin_Fun.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.3 Ex. 2 (p. 39) and §II.4 Ex. 4 (p. 41), paraphrased.

## Dependencies

Depends on: #223

<!-- catalog: {"ids":["maclane:II.3:ex2","maclane:II.4:ex4"],"deps":["maclane:I.2:construction7"]} -->
---8<---
```yaml
title: "MacLane II.3: Set-indexed products of categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.3:ex3]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3 Exercise 3, book p. 40 (PDF 50). Item: `maclane:II.3:ex3`.

## Background

For a set-indexed family of categories, the product category has as objects the choice functions of objects and as arrows the componentwise families of arrows, with projection functors satisfying the evident universal property: a family of functors into the components factors uniquely through the product. See nLab: [product category](https://ncatlab.org/nlab/show/product+category).

## Current state in the library

- The finite cases exist: binary `Product` (`Construction/Product.v:95`) with the full UMP as `Cat_Cartesian` (`Instance/Cat/Cartesian.v:39`, via `ump_products` at `Structure/Cartesian.v:136`), and the terminal category (`Cat_Terminal`).
- Precise gap (verified): no I-indexed product category construction — no `Category` whose objects are dependent functions `∀ i, C i` with componentwise morphisms — and hence no UMP for arbitrary set-indexed families (searches for dependent-function object fields and `PiCat`/`IndexedProduct`-style names: 0 relevant hits; `Structure/Limit/Product.v`'s indexed products are of *objects inside* one category, a different statement).

## Work to be done

Suggested module: `Construction/Product/Indexed.v`.

1. For `C : I → Category`, define the product category: objects `∀ i, C i`; homs the dependent families of component homs with componentwise `≈`, identity, and composition; mind the universe constraints (the library's `{o h p}` polymorphism).
2. Projection functors `P i`.
3. UMP: for any D and family `R i : D ⟶ C i`, a pairing functor with `P i ◯ ⟨R⟩ ≈ R i` for all i, unique up to `≈` (Cat's hom-equivalence, the setoid rendering of the book's on-the-nose uniqueness); note the binary case recovers `Cat_Cartesian`'s fork.

Donors: `Construction/Product.v`, `Instance/Cat/Cartesian.v`, `Structure/Limit/Product.v` (for the discrete-diagram vocabulary contrast, documented in the header).

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.3 Ex. 3 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the product category, the UMP)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Product/Indexed.v
echo 'Require Import Category.Construction.Product.Indexed. Print Assumptions PiCat_ump.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.3 Ex. 3 (p. 40), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.3:ex3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.3: The ring of continuous functions as a contravariant functor"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.3:ex5]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.3 Exercise 5, book p. 40 (PDF 50). Item: `maclane:II.3:ex5`.

## Background

Assigning to each topological space the ring of continuous real-valued functions on it, and to each continuous map the precomposition homomorphism, is a contravariant functor from spaces to rings — the basic object of function-algebra dualities. See nLab: [Top](https://ncatlab.org/nlab/show/Top) and Wikipedia: [Ring (mathematics)](https://en.wikipedia.org/wiki/Ring_(mathematics)).

## Current state in the library

- Precise gap (verified): no category Top and no category Rng exist in-tree (the algebra spine stops at commutative monoids, `Instance/CMon.v`), so neither the object assignment nor the functor exists in any form.

## Work to be done

Suggested module: `Instance/Top/ContinuousRing.v` (over the Top and Rng infrastructure of the referenced issues).

1. Define, for a space X, the ring C(X) of continuous real-valued functions (pointwise operations), as an object of the Rng category from #257.
2. Arrow action: precomposition along a continuous map is a ring homomorphism; contravariant functoriality.
3. Package as a functor `Top^op ⟶ Rng` (equivalently a contravariant functor on Top), the library's standard contravariance encoding (`Functor/Opposite.v:56`, `contramap` convention).

Donors: `Functor/Opposite.v` (contravariance convention), the Top and Rng issues' infrastructure.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.3 Ex. 5 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` in core-theory scope; any stdlib real-number assumptions disclosed per docs/AXIOMS.md instance-layer policy
- [ ] `Print Assumptions` run for the functor, with assumptions enumerated in the header
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Top/ContinuousRing.v
echo 'Require Import Category.Instance.Top.ContinuousRing. Print Assumptions ContinuousRingFunctor.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.3 Ex. 5 (p. 40), paraphrased.

## Dependencies

Depends on: #259
Depends on: #257

<!-- catalog: {"ids":["maclane:II.3:ex5"],"deps":["maclane:I.7:construction4","maclane:I.7:def1"]} -->
---8<---
```yaml
title: "MacLane II.4: Functor categories over discrete shapes and their size"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.4:remark1, maclane:II.4:ex2, maclane:II.4:remark2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4, book pp. 40–42 (PDF 50–52). Items: `maclane:II.4:remark1` (elementary computations: discrete function sets, the two-object case as a power set, B^1 iso B), `maclane:II.4:ex2` (B^X for a finite discrete X is a finite power of B), `maclane:II.4:remark2` (for a universe-sized discrete domain, the functor category outgrows the universe).

## Background

Functor categories out of discrete shapes are function spaces: over a discrete set they are powers of the target, over the terminal category they recover the target itself, and over a two-element target they compute power sets — which is also how the functor category escapes a fixed universe when the domain is as large as the universe. See nLab: [functor category](https://ncatlab.org/nlab/show/functor+category) and Wikipedia: [Functor category](https://en.wikipedia.org/wiki/Functor_category).

## Current state in the library

- `Structure/Cartesian/Closed.v:389` (`exp_one : x^1 ≅ x`) instantiated at `Cat_Closed` (`Instance/Cat/Cartesian/Closed.v:47`, exponent = `Fun`) yields [1, B] ≅ B in Cat — a one-step instantiation, but nowhere recorded as a named statement about `Fun`.
- `Instance/Discrete.v` provides `DiscreteCat` and `DiscreteCat_Functor` (an extension map only, no isomorphism).
- Precise gaps: the discrete computations are absent — no statement that `[DiscreteCat X, B]` is a power of B (finite or otherwise), no characteristic-function correspondence with subsets for a two-object discrete target, and no formalized counting statement behind the size remark (no Cantor-style comparison in-tree; the size conclusion is embodied only structurally in the universe discipline, `Theory/Category.v:111`, `Instance/Cat.v:22–26`).

## Work to be done

Suggested module: `Instance/Fun/Discrete.v`.

1. Record `[1, B] ≅ B` as a named statement about `Fun` (instantiating `exp_one` at `Cat_Closed`, or a direct construction).
2. For finite discrete shapes: an equivalence `[DiscreteCat (Fin n), B] ≅ B ∏ ... ∏ B` (n components; iterated binary product), covering Ex. 2; characterize morphisms over a discrete shape (no naturality constraint — componentwise families).
3. The power-set computation: functors from a discrete category into a two-object discrete category correspond to subsets (characteristic functions), packaged as a bijection/setoid isomorphism.
4. The size remark: prove the diagonal (Cantor) argument that no surjection exists from a type onto its predicate space, and add a header note connecting it to the correspondence of item 3 and to the library's structural universe-discipline rendering of "B^C need not lie within the universe" (`Instance/Cat.v` size note).

Donors: `Instance/Discrete.v`, `Instance/Fun.v`, `Structure/Cartesian/Closed.v`, `Instance/Cat/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the three computations and the diagonal lemma)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Fun/Discrete.v
echo 'Require Import Category.Instance.Fun.Discrete. Print Assumptions Fun_Discrete_power.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.4 (pp. 40–41) paraphrased, including Ex. 2.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.4:remark1","maclane:II.4:ex2","maclane:II.4:remark2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.4: The arrow category as [2, B] and the classification of natural transformations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.4:construction1, maclane:II.4:ex7]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4, book pp. 40–42 (PDF 50–52). Items: `maclane:II.4:construction1` (the arrow category B^2), `maclane:II.4:ex7` (functors into the arrow category are exactly natural transformations).

## Background

The functor category over the walking arrow is the category of arrows of B, whose morphisms are commuting squares; and a functor from C into it is precisely the data of two functors C ⟶ B together with a natural transformation between them — the arrow-category encoding of naturality. See nLab: [arrow category](https://ncatlab.org/nlab/show/arrow+category).

## Current state in the library

- The arrow category exists via the comma construction: `Construction/Arrow.v:110` (`Arrow := (Id[C] ↓ Id[C])`), with dom/cod as the comma projections and the generic arrow `comma_proj_nat` (`Construction/Comma.v:214`); the walking arrow `_2` exists (`Instance/Two.v:134`); whiskering supplies the forward-direction components.
- Precise gaps, disclosed by the file itself (`Construction/Arrow.v:104–108`): (i) no formal comparison between `Arrow B` and the functor category `[_2, B]` — the book's defining presentation — exists in-tree; (ii) the classification (Ex. 7) is stated only in the header essay: no lemma that H mapping to (dom ∘ H, cod ∘ H, whiskered generic arrow) is a bijection between functors `C ⟶ Arrow B` and triples (S, T, tau : S ⟹ T), no inverse construction, no round trips.

## Work to be done

Suggested module: `Construction/Arrow/Functor.v` (or extend `Construction/Arrow.v`).

1. Comparison functors `Arrow B ⟶ [_2, B]` and back, with both composites `≈`-identity (an isomorphism in Cat; note in the header whether the StrictCat form also holds).
2. Ex. 7 forward: from `H : C ⟶ Arrow B`, extract `S := dom ∘ H`, `T := cod ∘ H`, and `tau` by whiskering the generic arrow; record the section/boundary lemmas.
3. Ex. 7 inverse: from a triple (S, T, tau) construct `H_tau : C ⟶ Arrow B` (object action c to the arrow tau c; morphism action the naturality square).
4. Both round trips, giving the bijection (as a setoid isomorphism between the functor-hom setoid and the setoid of triples).

Donors: `Construction/Arrow.v`, `Construction/Comma.v` (`comma_proj_nat`), `Instance/Two.v`, `Instance/Fun.v`, `Theory/Natural/Transformation.v` (whiskering).

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the comparison isomorphism, the classification bijection)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (the header disclosure in `Construction/Arrow.v:104–108` must be updated to point at the new results)

## Verification

```
coqc -R . Category Construction/Arrow/Functor.v
echo 'Require Import Category.Construction.Arrow.Functor. Print Assumptions Arrow_Fun_iso.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.4 (pp. 40–42, incl. Ex. 7), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.4:construction1","maclane:II.4:ex7"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.4: Monoid and group actions as functor categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.4:construction2, maclane:II.4:ex5]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4, book pp. 41–42 (PDF 51–52). Items: `maclane:II.4:construction2` (functor categories over a delooped monoid are categories of actions), `maclane:II.4:ex5` (finite-set-valued functors on a finite group are permutation representations).

## Background

A functor from a one-object category (a delooped monoid M) into Set is exactly an M-action on a set, and natural transformations are the equivariant maps; with a group G and finite sets this specializes to permutation representations. See nLab: [action](https://ncatlab.org/nlab/show/action) and [G-set](https://ncatlab.org/nlab/show/G-set).

## Current state in the library

- Functor categories are fully general (`Instance/Fun.v:108`), and skeletal finite sets exist (`Instance/FinSet.v:116`).
- Precise gap (verified): no monoid or group delooping into a `Category` exists, so `Set^M` cannot even be formed; no M-Set/action category or equivariant-map characterization exists (the only "action" in-tree is the symmetric-group action on multicategory contexts).

## Work to be done

Suggested module: `Instance/Fun/Action.v` (with an `Instance/MSet.v` if a standalone action category is preferred).

1. Using the delooping B(M) from #220, define the category of M-actions (carrier setoid, action map, equivariant morphisms) — or take `[B(M), Sets]` as the definition and characterize it.
2. Prove the equivalence: `[B(M), Sets]` is equivalent to the category of M-actions with equivariant maps; unwind that a natural transformation is a single equivariant function.
3. Ex. 5: for a finite group G, specialize to `[B(G), FinSet]` and identify it with permutation representations of G (actions by bijections on finite sets).
4. Header note on the group-with-operators reading of `Grp^M` as an aside (no in-tree Grp; do not block on it).

Donors: `Instance/Fun.v`, `Instance/Sets.v`, `Instance/FinSet.v`, the delooping from #220.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the action category, the equivalence)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Fun/Action.v
echo 'Require Import Category.Instance.Fun.Action. Print Assumptions MSet_Fun_equiv.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.4 (pp. 41–42, incl. Ex. 5), paraphrased.

## Dependencies

Depends on: #220

<!-- catalog: {"ids":["maclane:II.4:construction2","maclane:II.4:ex5"],"deps":["maclane:I.2:construction3"]} -->
---8<---
```yaml
title: "MacLane II.4: Linear representations as the functor category (K-Mod)^G"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.4:construction3]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4, book p. 41 (PDF 51). Item: `maclane:II.4:construction3`.

## Background

For a commutative ring K and a group G, functors from the delooped G into K-modules are exactly K-linear representations of G, and natural transformations are the intertwining operators; the functor category is the representation category. See nLab: [representation](https://ncatlab.org/nlab/show/representation).

## Current state in the library

- Precise gap (verified): no module categories and no group delooping exist in-tree (`intertwin*` hits are metaphorical or operad-algebra morphisms; representation theory appears only in background essays), so the representation category has no counterpart in any form. The general functor category (`Instance/Fun.v`) is the only ingredient present.

## Work to be done

Suggested module: `Instance/Rep.v` (over the module-category and delooping infrastructure of the referenced issues).

1. With K-Mod from #258 and the group delooping from #220: define the category of K-linear representations of G — a module V with a homomorphism from G into the automorphisms of V — with intertwiners (linear maps commuting with the two actions) as morphisms.
2. Prove the equivalence with the functor category `[B(G), K-Mod]`: a functor is determined by the image module and the action homomorphism; a natural transformation is a single intertwining operator.

Donors: `Instance/Fun.v`, the module categories from #258, the delooping from #220.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Rep.v
echo 'Require Import Category.Instance.Rep. Print Assumptions Rep_Fun_equiv.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.4 (p. 41), paraphrased.

## Dependencies

Depends on: #258
Depends on: #220

<!-- catalog: {"ids":["maclane:II.4:construction3"],"deps":["maclane:I.7:construction3","maclane:I.2:construction3"]} -->
---8<---
```yaml
title: "MacLane II.4: R-Mod as an additive functor category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.4:ex1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4 Exercise 1, book p. 41 (PDF 51). Item: `maclane:II.4:ex1`.

## Background

A ring R is a one-object Ab-enriched category, and R-modules are the additive functors from it into abelian groups: R-Mod sits inside the functor category Ab^R as the full subcategory of additive functors. See nLab: [Ab-enriched category](https://ncatlab.org/nlab/show/Ab-enriched+category) and [Mod](https://ncatlab.org/nlab/show/Mod).

## Current state in the library

- Precise gap (verified): no category Ab, no rings, no modules, and no additive-functor vocabulary exist in-tree (`Structure/Preadditive.v` provides only commutative-monoid hom-enrichment; searches for `additive functor` and a one-object preadditive reading: 0 hits). Only the general functor category (`Instance/Fun.v`) is available.

## Work to be done

Suggested module: `Instance/Ab/ModFunctor.v` (over the Ab, R-Mod, and Ab-enrichment infrastructure of the referenced issues).

1. Present a ring R as a one-object Ab-enriched category (hom-group = additive group of R, composition = multiplication) — riding the delooping pattern from #220 and the Ab-enrichment vocabulary from #264.
2. Define additive functors between Ab-enriched categories (or at least from a one-object one into Ab), and the full subcategory of `Ab^R` they span.
3. Prove the equivalence of that full subcategory with R-Mod (from #258): an additive functor is exactly a module structure on its image group; natural transformations are module homomorphisms.

Donors: `Instance/Fun.v`, `Structure/Preadditive.v` (pattern), the Ab/R-Mod/Ab-category issues below.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.4 Ex. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Ab/ModFunctor.v
echo 'Require Import Category.Instance.Ab.ModFunctor. Print Assumptions RMod_AbFun_equiv.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.4 Ex. 1 (p. 41), paraphrased.

## Dependencies

Depends on: #256
Depends on: #258
Depends on: #264
Depends on: #220

<!-- catalog: {"ids":["maclane:II.4:ex1"],"deps":["maclane:I.7:construction1","maclane:I.7:construction3","maclane:I.8:def4","maclane:I.2:construction3"]} -->
---8<---
```yaml
title: "MacLane II.4: Graded abelian groups as Ab^N"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.4:ex3]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4 Exercise 3, book p. 41 (PDF 51). Item: `maclane:II.4:ex3`.

## Background

With the natural numbers as a discrete category, functors into abelian groups are just N-indexed families of abelian groups with degreewise homomorphisms — the category of graded abelian groups. See nLab: [graded object](https://ncatlab.org/nlab/show/graded+object).

## Current state in the library

- Precise gap (verified): "graded" appears in-tree only for monoid-graded monads (`Monad/Graded.v`, an unrelated concept), and no category Ab exists, so `Ab^N` has no counterpart in any form. `Instance/Discrete.v` (`DiscreteCat`) and `Instance/Fun.v` supply the frame.

## Work to be done

Suggested module: `Instance/Ab/Graded.v` (over the Ab infrastructure of #256).

1. Define the category of graded abelian groups directly (N-indexed families, degreewise homomorphisms, componentwise `≈`).
2. Prove the equivalence with `[DiscreteCat nat, Ab]` (functors over a discrete shape carry no constraint beyond the family itself; natural transformations are degreewise maps).

Donors: `Instance/Discrete.v`, `Instance/Fun.v`, the Ab category from #256.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.4 Ex. 3 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Ab/Graded.v
echo 'Require Import Category.Instance.Ab.Graded. Print Assumptions Graded_Fun_equiv.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.4 Ex. 3 (p. 41), paraphrased.

## Dependencies

Depends on: #256

<!-- catalog: {"ids":["maclane:II.4:ex3"],"deps":["maclane:I.7:construction1"]} -->
---8<---
```yaml
title: "MacLane II.4: Matrix equivalence and similarity via functor categories"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.4:ex6]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.4 Exercise 6, book p. 42 (PDF 52). Item: `maclane:II.4:ex6`.

## Background

In the functor category over the walking arrow with values in the matrix category, objects are matrices and isomorphic objects are exactly the equivalent matrices; over the delooped infinite cyclic monoid, objects are square matrices and isomorphic objects are exactly the similar matrices. See Wikipedia: [Matrix equivalence](https://en.wikipedia.org/wiki/Matrix_equivalence) and [Matrix similarity](https://en.wikipedia.org/wiki/Matrix_similarity).

## Current state in the library

- Precise gap (verified): no matrix category exists in-tree (`Matr`/`matrix` hits are essay prose only), no delooped infinite cyclic monoid, and hence neither functor-category characterization exists. `Instance/Fun.v` and `Instance/Two.v` supply the ambient frame.

## Work to be done

Suggested module: `Instance/Matr/FunExercises.v` (over the Matr_K infrastructure of #221).

1. With Matr_K from #221: identify the objects of `[_2, Matr_K]` with matrices (arrows of Matr_K), and prove that two objects are isomorphic iff the matrices are equivalent (invertible P, Q with Q A = B P — i.e., B = Q A P^{-1} in the usual formulation).
2. With the delooping of the free monoid on one generator (from #220): identify objects of the functor category over it, valued in Matr_K, with square matrices, and isomorphism with similarity (B = P A P^{-1}).
3. Header note connecting to the classical linear-algebra meaning.

Donors: `Instance/Fun.v`, `Instance/Two.v`, Matr_K from #221, delooping from #220.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.4 Ex. 6 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both characterizations)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Matr/FunExercises.v
echo 'Require Import Category.Instance.Matr.FunExercises. Print Assumptions matrix_similarity_iso.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.4 Ex. 6 (p. 42), paraphrased.

## Dependencies

Depends on: #221
Depends on: #220

<!-- catalog: {"ids":["maclane:II.4:ex6"],"deps":["maclane:I.2:construction5","maclane:I.2:construction3"]} -->
---8<---
```yaml
title: "MacLane II.5: Strict 2-categories, double categories, and Cat"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.5:thm1, maclane:II.5:def2, maclane:II.5:def3]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5, book pp. 43–44 (PDF 53–54). Items: `maclane:II.5:thm1` (Theorem 1: natural transformations carry two interchanging composition structures — Cat is a 2-category), `maclane:II.5:def2` (double categories, after Ehresmann), `maclane:II.5:def3` (2-categories as double categories whose horizontal identities are vertical identities).

## Background

Mac Lane's Theorem 1 organizes all natural transformations into two interlocking categories — vertical composition over functors, horizontal composition over categories — satisfying the interchange law; abstracting, a (strict) double category is one collection carrying two interchanging category structures, and a strict 2-category is a double category in which every identity for one composition is an identity for the other. See nLab: [strict 2-category](https://ncatlab.org/nlab/show/strict+2-category) and [double category](https://ncatlab.org/nlab/show/double+category).

## Current state in the library

- All the two-dimensional data and laws for Cat are formalized in weak packaging: vertical categories `[C, D]` (`Instance/Fun.v:108`), horizontal composition as the bifunctor `Cat_Hcompose` whose `fmap_comp` is the interchange law (`Instance/Cat/Bicategory.v:64`, comment at 59–60), and the assembled `Cat_Bicategory` with all coherence proven (`Instance/Cat/Bicategory.v:127`).
- The double-category side exists only as the PSEUDO (coherence-only) class `DoubleCategory` (`Theory/DoubleCategory.v:162`, `dinterchange` at 257) with the commuting-squares model `Sq C` (`Construction/Sq.v:47`).
- Precise gaps (verified): no strict 2-category interface anywhere (all "strict 2-category" mentions are prose: `Theory/Bicategory.v:53`, `Theory/Natural/Transformation.v:74`); no strict double category (single collection, everywhere-strict compositions); no lemma recording that `Cat_Bicategory`'s coherence cells have identity components; `StrictCat` (`Instance/StrictCat.v:56`) is strict at the 1-cell level only, with no 2-cells; and the negative example (commuting squares form a double category that is not a 2-category) is unstateable for want of the strictness vocabulary.

## Work to be done

Suggested module: `Theory/TwoCategory.v` (definitions) plus `Instance/Cat/TwoCategory.v` (the witness).

1. Define a strict double category: either Mac Lane's single-collection form (two everywhere-defined-on-matching-boundaries category structures on one collection of cells, satisfying interchange) or a typed variant with strict horizontal associativity/units; relate it in the header to the in-tree pseudo `DoubleCategory` (a strict one degenerates into it).
2. Define a strict 2-category: a strict double category in which every horizontal identity is a vertical identity (equivalently, present the Cat-enriched-category reading as documentation; no monoidal structure on Cat is required for the direct definition).
3. The Cat witness (Theorem 1): natural transformations under vertical composition (`nat_compose`) and horizontal composition (`nat_hcompose`) with the interchange law and the identity-coincidence condition, assembled as a strict 2-category instance; where on-the-nose equalities of functors are needed, work over `StrictCat`-style strict functor equality and record the identity-component lemmas for `Cat_Bicategory`'s unitors/associator that make the weak and strict packagings agree.
4. Negative example: show `Sq` (commuting squares) satisfies the double-category axioms but fails the 2-category condition.

Donors: `Instance/Cat/Bicategory.v`, `Instance/Fun.v`, `Theory/Natural/Transformation.v`, `Theory/DoubleCategory.v`, `Construction/Sq.v`, `Instance/StrictCat.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.5 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the two classes, the Cat instance, the Sq counterexample)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (likely: this is a headline II.5 result)

## Verification

```
coqc -R . Category Theory/TwoCategory.v Instance/Cat/TwoCategory.v
echo 'Require Import Category.Instance.Cat.TwoCategory. Print Assumptions Cat_TwoCategory.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.5, Theorem 1 and the double/2-category definitions (pp. 43–44), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.5:thm1","maclane:II.5:def2","maclane:II.5:def3"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.5: Naturality of the exponential laws"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.5:ex2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5 Exercise 2, book p. 44 (PDF 54). Item: `maclane:II.5:ex2`.

## Background

The exponential laws — a product target distributes over the exponent, and a product exponent curries into an iterated exponential — hold as isomorphisms natural in all variables; at Cat they are isomorphisms of functor categories, and the second is the internalization of the currying bijection. See nLab: [cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category).

## Current state in the library

- The pointwise isomorphisms are proven in any cartesian closed category: `exp_prod_r : (y × z)^x ≅ y^x × z^x` (`Structure/Cartesian/Closed.v:310`) and `exp_prod_l : z^(x × y) ≅ (z^y)^x` (`:257`); both elaborate at Cat via `Cat_Closed` (machine-checked during coverage verification).
- Precise gap (verified): naturality in the variables is not stated — neither side is packaged as a functor and no natural-isomorphism statement exists (only `exp_respects_iso` at `:209`); the requested comparison of the curried law with the external currying bijection (`exp_iso`) is also unrecorded.

## Work to be done

Suggested module: extend `Structure/Cartesian/Closed.v` or add `Structure/Cartesian/Closed/Natural.v`.

1. Package the two sides of each law as functors of each variable (donor: `Functor/Hom/Internal.v`'s `InternalHomFunctor` for exponent functoriality, `Functor/Product/Internal.v` for the product) and upgrade `exp_prod_r` and `exp_prod_l` to natural isomorphisms (per-variable naturality squares, or the joint form over the product category).
2. Record the comparison: the curried law is carried by `curry`/`uncurry` and commutes with the external bijection `exp_iso` (the triangle relating the internal iso to the hom-setoid bijection).
3. Note the Cat instantiation (isomorphisms of functor categories) as a corollary or example.

Donors: `Structure/Cartesian/Closed.v`, `Functor/Hom/Internal.v`, `Functor/Product/Internal.v`, `Instance/Cat/Cartesian/Closed.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.5 Ex. 2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both naturality upgrades)
- [ ] New files registered in `_CoqProject` (if a new file is added)
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Structure/Cartesian/Closed/Natural.v
echo 'Require Import Category.Structure.Cartesian.Closed.Natural. Print Assumptions exp_prod_l_natural.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.5 Ex. 2 (p. 44), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.5:ex2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.5: The abstract Eckmann-Hilton argument"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.5:ex5]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5 Exercise 5, book p. 45 (PDF 55). Item: `maclane:II.5:ex5` (the Hilton-Eckmann argument).

## Background

If one carrier bears two everywhere-defined binary operations sharing a two-sided unit and satisfying the interchange identity, the two operations coincide and are commutative (and associative). This is the engine behind commutativity of higher homotopy groups and of endomorphism monoids of identities. See nLab: [Eckmann-Hilton argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argument) and Wikipedia: [Eckmann–Hilton argument](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument).

## Current state in the library

- The argument is executed in full, but only instantiated at one operation pair: the two convolutions on hom-setoids in the semiadditive development — interchange (`Structure/Semiadditive.v:503`, `conv_interchange`), coincidence (`:515`, `conv_conv_pr`), commutativity (`:524`, `conv_comm`), associativity (`:534`, `conv_assoc`).
- Precise gap (verified): no abstract standalone theorem over an arbitrary setoid with two unital interchanging operations; `Structure/Monoid.v:90` and `Structure/Group.v` cite the principle in essays only.

## Work to be done

Suggested module: `Theory/EckmannHilton.v`.

1. State and prove the abstract theorem: over a `Setoid` carrier, given two binary operations that are `Proper` for `≈`, each with a two-sided unit, satisfying the interchange identity — then the units coincide, the operations coincide, and the (single) operation is commutative and associative.
2. Refactor (or corollary-bridge) the semiadditive convolution proofs to route through the abstract theorem, keeping their statements unchanged.
3. Header essay citing Eckmann-Hilton (1962) and pointing at the in-tree consumers (`Structure/Semiadditive.v`; the centre-of-a-category and fundamental-group issues that depend on this item).

Donors: `Structure/Semiadditive.v:489–543` (the concrete instance to abstract from), `Lib/Setoid.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.5 Ex. 5 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for the abstract theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/EckmannHilton.v
echo 'Require Import Category.Theory.EckmannHilton. Print Assumptions eckmann_hilton.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.5 Ex. 5 (p. 45), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.5:ex5"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.5: Loop interchange and the abelian fundamental group of a topological group"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.5:ex4, maclane:II.5:ex6]
deps_item_ids: [maclane:II.5:ex5]
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5 Exercises 4 and 6, book p. 45 (PDF 55). Items: `maclane:II.5:ex4` (interchange for loop concatenation and pointwise product in a topological group), `maclane:II.5:ex6` (hence the fundamental group of a topological group is abelian).

## Background

In a topological group, based loops at the unit carry two operations — concatenation of paths and pointwise group multiplication — which satisfy the interchange identity; the Eckmann-Hilton argument then forces the fundamental group to be abelian. See nLab: [topological group](https://ncatlab.org/nlab/show/topological+group) and [fundamental group](https://ncatlab.org/nlab/show/fundamental+group).

## Current state in the library

- Precise gap (verified): no topological spaces, no paths, no unit interval, and no fundamental group exist in-tree (all `topological group`/`homotopy`/`fundamental group` hits are background-essay prose; `Construction/Groupoid.v:58` names the fundamental groupoid as motivation only). The abstract interchange machinery exists (`bimap_comp`, `dinterchange`, `conv_interchange`) but the topological instance has no possible home yet.

## Work to be done

Suggested module: `Instance/Top/LoopSpace.v` (over the Top and fundamental-groupoid infrastructure of the referenced issues).

1. With Top from #259 and the fundamental groupoid from #249: define based loops at the unit of a topological group and the two operations (concatenation; pointwise multiplication), each respecting homotopy classes.
2. Prove the interchange identity between the two operations on homotopy classes (Ex. 4).
3. Apply the abstract Eckmann-Hilton theorem (dependency below) on the hom-setoid of the fundamental groupoid at the unit to conclude the fundamental group of a topological group is abelian (Ex. 6).
4. Honest scope note: this issue is blocked on substantial topology infrastructure; if the Top issue lands with a minimal open-set formulation, the interval and path-homotopy layer belongs here.

Donors: the abstract Eckmann-Hilton item of this chapter, `Construction/Groupoid.v` (vocabulary), the Top/#249 infrastructure.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.5 Ex. 4 and Ex. 6 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` in core-theory scope; any stdlib real/topology assumptions disclosed per docs/AXIOMS.md instance-layer policy
- [ ] `Print Assumptions` run for each principal artifact, with assumptions enumerated
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Top/LoopSpace.v
echo 'Require Import Category.Instance.Top.LoopSpace. Print Assumptions pi1_topgroup_abelian.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.5 Ex. 4 and Ex. 6 (p. 45), paraphrased.

## Dependencies

Depends on: #259
Depends on: #249
Depends on: maclane:II.5:ex5 (resolved to an issue number in the dependency pass)

<!-- catalog: {"ids":["maclane:II.5:ex4","maclane:II.5:ex6"],"deps":["maclane:I.7:construction4","maclane:I.5:construction1","maclane:II.5:ex5"]} -->
---8<---
```yaml
title: "MacLane II.5: The hom-action of a functor as a natural transformation"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.5:ex7]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5 Exercise 7, book p. 45 (PDF 55). Item: `maclane:II.5:ex7`.

## Background

The arrow functions of a functor T : A ⟶ D assemble into a single natural transformation between the hom-bifunctor of A and the hom-bifunctor of D restricted along T in both variables — the two-variable packaging of "fmap is natural". See nLab: [hom-functor](https://ncatlab.org/nlab/show/hom-functor).

## Current state in the library

- All ingredients exist: the hom bifunctor (`Functor/Hom.v:49`, `Hom : C^op ∏ C ⟶ Sets`), product functors `F ∏⟶ G` (`Functor/Construction/Product.v:34`), and the composite shape `Hom D ◯ (F^op ∏⟶ G)` in live use (`Theory/Profunctor.v:155`, `Repr_left`); the componentwise equation is `fmap_comp`/`comp_assoc`.
- Precise gap (verified): the transformation itself is nowhere defined — no `Hom A ⟹ Hom D ◯ (T^op ∏⟶ T)` with component f to `fmap[T] f`, and the same-functor-both-slots pattern `T^op ∏⟶ T` never occurs in-tree.

## Work to be done

Suggested module: `Functor/Hom/Induced.v`.

1. Define, for `T : A ⟶ D`, the transformation `hom_action T : Hom A ⟹ Hom D ◯ (T^op ∏⟶ T)` with component at (a, b) the setoid morphism sending f to `fmap[T] f`; prove joint naturality (discharged by `fmap_comp` and associativity).
2. Corollaries reading off the classical reformulations: T is faithful iff every component is injective (w.r.t. `≈`), full iff every component is surjective — connecting to `Theory/Functor.v:331` (`Full`) as sanity checks (optional but natural in the same file).

Donors: `Functor/Hom.v`, `Functor/Construction/Product.v`, `Theory/Profunctor.v`, `Functor/Opposite.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.5 Ex. 7 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for the principal artifact (`hom_action`)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Functor/Hom/Induced.v
echo 'Require Import Category.Functor.Hom.Induced. Print Assumptions hom_action.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.5 Ex. 7 (p. 45), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.5:ex7"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.5: The centre of a category"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.5:ex8]
deps_item_ids: [maclane:II.5:ex5]
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.5 Exercise 8, book p. 45 (PDF 55). Item: `maclane:II.5:ex8`.

## Background

The natural endotransformations of the identity functor of a category form a commutative monoid under (either) composition — the centre of the category; for familiar categories it computes to familiar commutative monoids. See nLab: [center of a category](https://ncatlab.org/nlab/show/center+of+a+category).

## Current state in the library

- Precise gap (verified): no development of endotransformations of the identity functor exists — the hom-setoid of `[C, C]` at (Id, Id) exists only implicitly through `Instance/Fun.v`, with no monoid structure or commutativity statement. All in-tree "centre" notions are different concepts (the premonoidal centre, `Structure/Premonoidal/Centre.v`/`Structure/Binoidal.v`; the Drinfeld centre, `Structure/Monoidal/Drinfeld.v`), and `Structure/Monoidal/Proofs.v:339` cites the neighbouring End(I) commutativity without proving it.

## Work to be done

Suggested module: `Theory/Centre.v`.

1. Define the centre of a category C as the setoid `Nat(Id[C], Id[C])` (the hom-setoid of `[C, C]` at the identity) with monoid structure by vertical composition.
2. Prove commutativity — either directly from naturality (each component of one transformation is natural against the other), or by exhibiting vertical and horizontal composition as two unital interchanging operations and invoking the abstract Eckmann-Hilton item of this chapter.
3. Identify the centre for at least one in-tree instance (e.g. Sets or Coq), as Mac Lane asks for Set (where it is trivial); record the Grp/Ab identifications as header remarks pending those categories.
4. Header note distinguishing this centre from the premonoidal and Drinfeld centres already in-tree.

Donors: `Instance/Fun.v`, `Theory/Natural/Transformation.v`, the abstract Eckmann-Hilton item.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.5 Ex. 8 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the monoid, commutativity, the Sets computation)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/Centre.v
echo 'Require Import Category.Theory.Centre. Print Assumptions centre_commutative.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.5 Ex. 8 (p. 45), paraphrased.

## Dependencies

Depends on: maclane:II.5:ex5 (resolved to an issue number in the dependency pass)

<!-- catalog: {"ids":["maclane:II.5:ex8"],"deps":["maclane:II.5:ex5"]} -->
---8<---
```yaml
title: "MacLane II.6: Comma-category specializations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.6:remark1, maclane:II.6:ex2]
deps_item_ids: [maclane:II.4:construction1]
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.6, book pp. 46–47 (PDF 56–57). Items: `maclane:II.6:remark1` (the comma category subsumes the earlier constructions; two objects give the discrete category on a hom-set; identities give the arrow category; origin of the notation), `maclane:II.6:ex2` (the slice over a terminal object is the whole category).

## Background

The general comma construction specializes to all the earlier under/over categories, to the arrow category at two identity functors, and — with both functors constant at objects — to the discrete category on a hom-set (the historical source of the comma notation); slicing over a terminal object recovers the category itself. See nLab: [comma category](https://ncatlab.org/nlab/show/comma+category) and Wikipedia: [Comma category](https://en.wikipedia.org/wiki/Comma_category).

## Current state in the library

- Proven specializations: `Comma_Slice` (`Construction/Slice.v:140`), `Comma_Coslice` (`:181`), `Arrow := (Id ↓ Id)` (`Construction/Arrow.v:110`), and objects-as-constant-functors `=(c)` in live use (`Theory/Universal/Arrow.v:127`).
- Precise gaps (verified): (i) no formal statement that for objects a, b the comma of the two constant functors is the discrete category on the hom-set C(b, a) — only prose (`Construction/Product/Comma.v:33–35`); (ii) no formal identification of the comma-built `Arrow` with the functor-category presentation over the walking arrow (`Construction/Arrow.v:104–108` discloses this; it is the dependency item below); (iii) the slice-over-terminal isomorphism `Slice C t ≅ C` exists only as header prose (`Construction/Slice.v:67–69`) — no formal statement anywhere.

## Work to be done

Suggested modules: `Construction/Comma/Special.v` and `Construction/Slice/Terminal.v`.

1. Discrete hom-set specialization: for objects a, b of C, an equivalence (or isomorphism in Cat) between `=(b) ↓ =(a)` and the discrete category on the carrier of the hom-setoid C(b, a) — mind the setoid-vs-Type packaging of `DiscreteCat` and document the choice.
2. Slice over a terminal object: `C ̸ t ≅[Cat] C` when t is terminal; dual coslice-under-initial statement by op-duality.
3. Header recap connecting the full family of specializations (slice, coslice, arrow, discrete hom-set, and the [2, C] reading via the dependency item), completing Mac Lane's remark as recorded statements rather than prose.

Donors: `Construction/Comma.v`, `Construction/Slice.v`, `Functor/Diagonal.v` (`=(c)`), `Instance/Discrete.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.6 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the discrete specialization, the slice-over-terminal iso)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Comma/Special.v Construction/Slice/Terminal.v
echo 'Require Import Category.Construction.Slice.Terminal. Print Assumptions Slice_Terminal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.6 (pp. 46–47, incl. Ex. 2), paraphrased.

## Dependencies

Depends on: maclane:II.4:construction1 (the arrow-category-as-[2,B] issue; resolved to an issue number in the dependency pass)

<!-- catalog: {"ids":["maclane:II.6:remark1","maclane:II.6:ex2"],"deps":["maclane:II.4:construction1"]} -->
---8<---
```yaml
title: "MacLane II.6: The comma diagram over the arrow category and its universal property"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.6:construction1, maclane:II.6:ex3, maclane:II.6:ex5]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.6, book pp. 47–48 (PDF 57–58). Items: `maclane:II.6:construction1` (the projections P, Q and the functor R into the arrow category, with the commuting diagram), `maclane:II.6:ex3` (their arrow-level definitions), `maclane:II.6:ex5` (the comma category as the universal such diagram — a pullback-style limit).

## Background

The comma category of two functors projects to its two source categories and maps to the arrow category of the target by picking out the mediating arrow; these fit into a commuting diagram over the domain/codomain functors, and the comma category is universal among categories carrying such a diagram — a strict comma object computed as a PIE-style limit. See nLab: [comma category](https://ncatlab.org/nlab/show/comma+category) and [arrow category](https://ncatlab.org/nlab/show/arrow+category).

## Current state in the library

- P and Q exist with full arrow-level definitions and laws: `comma_proj1`/`comma_proj2` (`Construction/Comma.v:196/204`), plus the pairing `comma_proj` (`:185`) and the canonical transformation `comma_proj_nat` (`:214`) which carries R's data in transformation form.
- Precise gaps (verified): no functor in the tree has the arrow category as codomain — R is absent, so its arrow action (Ex. 3's third part) and the commuting diagram over dom/cod are unstated; the domain/codomain functors of `Arrow` exist only implicitly as specialized comma projections, never named; and no unique-factorization statement exists (Ex. 5) — `Construction/Comma/Limit.v` is about limits *in* a comma category, a different theorem, and `Construction/Comma.v:104–108`'s comma-object/PIE-limit reading is an explicitly documentation-level citation.

## Work to be done

Suggested module: `Construction/Comma/Diagram.v`.

1. Name the domain and codomain functors `Arrow C ⟶ C` (the specialized comma projections).
2. Define `R : (S ↓ T) ⟶ Arrow C` — objects to their mediating arrow, morphisms to the commuting square — and prove the commuting-diagram equations relating S ∘ P, T ∘ Q with dom ∘ R, cod ∘ R (componentwise; on-the-nose where the constructions allow, otherwise up to `≈`).
3. Ex. 5, the universal property: for any category X with functors P', Q', R' commuting over the same cospan-of-five diagram, construct L : X ⟶ (S ↓ T) with P' ≈ P ∘ L, Q' ≈ Q ∘ L, R' ≈ R ∘ L, and prove uniqueness up to `≈`; consider the StrictCat variant for the on-the-nose form and document the choice.

Donors: `Construction/Comma.v`, `Construction/Arrow.v`, `Instance/Cat.v`/`Instance/StrictCat.v`.

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.6 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (R, the diagram lemmas, the factorization and uniqueness)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Comma/Diagram.v
echo 'Require Import Category.Construction.Comma.Diagram. Print Assumptions comma_diagram_ump.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.6 (pp. 47–48, displays (5)–(6), Ex. 3 and Ex. 5), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.6:construction1","maclane:II.6:ex3","maclane:II.6:ex5"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.6: The Huq correspondence is a bijection"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.6:ex4]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.6 Exercise 4, book p. 47 (PDF 57). Item: `maclane:II.6:ex4` (natural transformations are the common sections of the comma projections — S. A. Huq).

## Background

A natural transformation between two parallel functors is the same thing as a functor into their comma category that is a simultaneous section of both projections; the correspondence is bijective. See nLab: [comma category](https://ncatlab.org/nlab/show/comma+category).

## Current state in the library

- Both directions are constructed, in a file whose header cites this very exercise: `Comma_Functor` (`Construction/Comma/Natural/Transformation.v:42`) sends a transformation to its section functor, and `Comma_Transform` (`:53`) recovers a transformation from any functor with section witnesses up to natural isomorphism.
- Precise gap (verified): the bijectivity is not recorded — no round-trip lemma in either direction (`Comma_Transform (Comma_Functor F) ≈ F`; `Comma_Functor (Comma_Transform F p q) ≈[Cat] F`), and even the section property of `Comma_Functor` (it holds definitionally) is asserted only in a comment.

## Work to be done

Extend `Construction/Comma/Natural/Transformation.v`.

1. Record the section lemmas: `comma_proj1 ◯ Comma_Functor tau ≈[Cat] Id` and likewise for `comma_proj2`.
2. Prove both round trips, giving the bijection between the setoid of transformations `S ⟹ T` and the setoid of section functors (functors L with both projections `≈` Id), packaged as a setoid isomorphism.
3. Header note that `Comma_Transform`'s up-to-iso section witnesses generalize the book's on-the-nose sections; state the strict corollary for the definitional sections.

Donors: `Construction/Comma/Natural/Transformation.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.6 Ex. 4 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the two round trips)
- [ ] Any new files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Comma/Natural/Transformation.v
echo 'Require Import Category.Construction.Comma.Natural.Transformation. Print Assumptions Huq_roundtrip.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.6 Ex. 4 (p. 47), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.6:ex4"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.6: Functoriality of the comma construction"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.6:ex6]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.6 Exercise 6, book p. 48 (PDF 58). Item: `maclane:II.6:ex6`.

## Background

For fixed source and target categories, the comma construction is itself functorial: contravariantly in the first functor argument and covariantly in the second, giving a bifunctor from the (opposed) functor categories into Cat; a richer version lets the categories themselves vary. See nLab: [comma category](https://ncatlab.org/nlab/show/comma+category).

## Current state in the library

- The isomorphism-restricted action exists: `Comma_Iso` (`Construction/Comma/Isomorphism.v:147`) is a `Proper` instance sending natural isomorphisms of the two functor arguments to an isomorphism of comma categories in Cat, built from four one-sided constructions (`Comma_Iso_to_Left` at `:64` and siblings).
- Precise gap (verified): the actual functor of part (a) is absent — no action on arbitrary (non-invertible) natural transformations sigma : T' ⟹ T, tau : S ⟹ S' giving `(T ↓ S) ⟶ (T' ↓ S')`, no bifunctor `[E, C]^op ∏ [D, C] ⟶ Cat` with identity/composition laws, and nothing for part (b) (varying C, D, E).

## Work to be done

Suggested module: `Construction/Comma/Functorial.v`.

1. Generalize the one-sided constructions to arbitrary transformations: from sigma : S' ⟹ S a functor `(S ↓ T) ⟶ (S' ↓ T)` (postcompose the mediating arrow with the component), and dually on the T side; note the existing iso-restricted versions each use only one iso component and generalize directly.
2. Assemble the bifunctor `(Fun E C)^op ∏ (Fun D C) ⟶ Cat` with object action the comma construction and prove the functor laws up to Cat's hom-equivalence; check it restricts to `Comma_Iso` on isomorphisms.
3. Part (b): formalize a varying-categories version — e.g. action on a triple of functors between the index categories with compatible squares — or scope it precisely in the header as a documented stretch goal if the bookkeeping outgrows one PR (state which shape was chosen and why).

Donors: `Construction/Comma/Isomorphism.v`, `Construction/Comma.v`, `Instance/Cat.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.6 Ex. 6 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the bifunctor and its laws)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Comma/Functorial.v
echo 'Require Import Category.Construction.Comma.Functorial. Print Assumptions Comma_Bifunctor.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.6 Ex. 6 (p. 48), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.6:ex6"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.6: Commutative K-algebras as a coslice of commutative rings"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.6:ex1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.6 Exercise 1, book p. 47 (PDF 57). Item: `maclane:II.6:ex1`.

## Background

For a commutative ring K, the category of objects under K in commutative rings is exactly the category of commutative K-algebras — the standard coslice description of algebras. See nLab: [under category](https://ncatlab.org/nlab/show/under+category) and Wikipedia: [Associative algebra](https://en.wikipedia.org/wiki/Associative_algebra).

## Current state in the library

- The coslice construction is present and proven comma-equivalent (`Construction/Slice.v:169`, `Coslice`; `:181`, `Comma_Coslice`).
- Precise gap (verified): no category of (commutative) rings and no K-algebras exist in-tree (searches for `Rng`/`CRng`/`K-algebra`: prose-only hits; the nearest algebraic instance, `Instance/CMon.v`, cannot express this), so the identification has no counterpart.

## Work to be done

Suggested module: `Instance/Rng/Algebras.v` (over the Rng infrastructure of #257).

1. Define CRng, the full subcategory of commutative rings (over #257's ring category; donor `Construction/Subcategory.v`).
2. Define the category of commutative K-algebras directly (a commutative ring with a structural morphism from K; morphisms commuting with the structure maps).
3. Prove the isomorphism (in Cat) between K-Alg and the coslice `K ̸co CRng`, riding `Coslice`/`Comma_Coslice`.

Donors: `Construction/Slice.v`, `Construction/Subcategory.v`, the Rng issue's infrastructure.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.6 Ex. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Rng/Algebras.v
echo 'Require Import Category.Instance.Rng.Algebras. Print Assumptions KAlg_Coslice_iso.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.6 Ex. 1 (p. 47), paraphrased.

## Dependencies

Depends on: #257

<!-- catalog: {"ids":["maclane:II.6:ex1"],"deps":["maclane:I.7:def1"]} -->
---8<---
```yaml
title: "MacLane II.7: O-graphs, the composable-pairs product, and categories as monoids"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.7:def2, maclane:II.7:def3, maclane:II.7:remark1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.7, book pp. 48–49 (PDF 58–59). Items: `maclane:II.7:def2` (O-graphs and their identity-on-objects morphisms; the trivial O-graph), `maclane:II.7:def3` (the product over O: the composable-pairs graph, associative and unital up to isomorphism), `maclane:II.7:remark1` (a category with object set O is exactly a monoid-like object in O-graphs under this product).

## Background

Fixing the object collection O, graphs over O compose by pulling back over O — the graph of composable pairs — with the trivial O-graph as unit; a category structure on an O-graph is then precisely a pair of O-graph morphisms (composition, identities) satisfying the monoid diagrams: categories are monoids in O-graphs, the graph-side avatar of "monads are monoids". See nLab: [quiver](https://ncatlab.org/nlab/show/quiver) and [monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

- Quivers and their category exist (`Construction/Free/Quiver.v:54/205/358`), and the monoid-in-a-monoidal-category pattern is well developed elsewhere (`Theory/Algebra/Monoid.v`, `Structure/Monoid.v`, `Instance/StrictCat/Premonoid.v`).
- Precise gaps (verified): no fixed-O subcategory or node-identity morphism class, no trivial O-graph; no composable-pairs product A x_O B, nor its associativity/unit isomorphisms; and no statement identifying categories over O with monoid objects for that product (the nearest neighbours — `Theory/Metacategory/ArrowsOnly.v`'s composable-pairs table and `Construction/Free.v:76`'s paths-monad citation — carry different content).

## Work to be done

Suggested module: `Theory/OGraph.v` (or `Construction/Free/Quiver/Over.v`).

1. Define O-quivers (edge family over a fixed node type O) and their identity-on-nodes morphisms; the category O-Grph; the trivial O-graph (one edge per node, endpoints that node).
2. Define the composable-pairs product A x_O B and prove the associativity isomorphism and the two unit isomorphisms against the trivial O-graph (Mac Lane's displays; full monoidal-category packaging is optional — enough structure to state the monoid diagrams, with the packaging decision documented).
3. The identification (remark 1), both directions: a category with objects O yields composition/identity O-graph morphisms satisfying the associativity square and unit triangles; conversely such data on an O-graph assembles a `Category` — with the two constructions mutually inverse up to the evident equivalence.

Donors: `Construction/Free/Quiver.v`, `Theory/Algebra/Monoid.v` (diagram shapes), `Theory/Metacategory.v` (the arrows-only cousin, for the header essay).

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.7 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the product, its coherence isos, both directions of the identification)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Theory/OGraph.v
echo 'Require Import Category.Theory.OGraph. Print Assumptions category_is_monoid_in_OGrph.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.7 (pp. 48–49, display (3)), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.7:def2","maclane:II.7:def3","maclane:II.7:remark1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.7: Concrete free categories and free finite ordinals"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.7:remark3, maclane:II.7:ex2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.7, book pp. 50–51 (PDF 60–61). Items: `maclane:II.7:remark3` (worked examples of free categories: the loop, the single arrow, the composable pair), `maclane:II.7:ex2` (every finite ordinal is a free category).

## Background

The free category on one endo-arrow is the free monoid on one generator viewed as a one-object category; on a single arrow with distinct endpoints it is the walking arrow; on a linear chain it is a finite ordinal — every finite ordinal arises freely from its underlying linear graph. See nLab: [free category](https://ncatlab.org/nlab/show/free+category).

## Current state in the library

- The free-category construction is complete (`FreeOnQuiver`, `Construction/Free/Quiver.v:431`), and the loop example's carrier is built in a regression test (`Test/Issue138.v:87`, `B138_loop`, with only its object set computed by `eq_refl`); `ListMon` (`Construction/Funny/Comparison.v:81`) exhibits the free-monoid-as-one-object-category shape directly.
- Precise gaps (verified): no identification of the loop free category's endomorphism monoid with the free monoid on one generator (e.g. with nat under addition); the walking arrow and the composable-pair/triangle are never derived as free categories (in-tree `_2` etc. are hand-built); and no freeness theorem for finite ordinals exists (`FreeOnQuiver`'s only external use is the test file).

## Work to be done

Suggested module: `Construction/Free/Quiver/Examples.v`.

1. Loop: an isomorphism between hom(⋆,⋆) in `FreeOnQuiver` on the one-loop quiver and the free monoid on one generator (paths of length n correspond to n; concatenation to addition).
2. Walking arrow: `FreeOnQuiver` on the two-node one-edge quiver is isomorphic (in Cat or StrictCat) to `_2`.
3. Composable pair: `FreeOnQuiver` on the three-node chain has exactly the two generators, one composite, and three identities — the commutative-triangle category (compare with a direct finite presentation, or construct the ordinal 3 here if absent).
4. Ex. 2: every finite ordinal n (as a thin linear category) is free on its linear quiver — an isomorphism with `FreeOnQuiver` of the chain with n nodes.

Donors: `Construction/Free/Quiver.v`, `Test/Issue138.v` (loop quiver), `Instance/Two.v`, `Instance/Omega.v` (order vocabulary), `Lib/TList.v` (path induction).

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.7 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the four identifications)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Free/Quiver/Examples.v
echo 'Require Import Category.Construction.Free.Quiver.Examples. Print Assumptions ordinal_free.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.7 (p. 50, examples; p. 51, Ex. 2), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.7:remark3","maclane:II.7:ex2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.7: The free monoid and its universal property"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.7:cor2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.7 Corollary 2, book pp. 50–51 (PDF 60–61). Item: `maclane:II.7:cor2`.

## Background

For any set X there is a monoid of finite strings over X with a universal map from X: every function from X into (the underlying set of) a monoid extends uniquely to a monoid homomorphism — the free monoid, Mac Lane's one-object instance of the free-category theorem. See nLab: [free monoid](https://ncatlab.org/nlab/show/free+monoid) and Wikipedia: [Free monoid](https://en.wikipedia.org/wiki/Free_monoid).

## Current state in the library

- The generating theorem is fully in-tree (`FreeForgetfulAdjunction`, `Construction/Free/Quiver.v:550`); lists carry the sibling initial-algebra property (`list_initial`, `Instance/Coq/Lists.v:111`, axiom-free); monoids-in-a-category with homomorphisms and a faithful forgetful functor exist (`Mon`, `Theory/Algebra/Monoid/Hom.v:83`, `Mon_Forget` at `:93`).
- Precise gap (verified): the free-monoid universal property itself is never stated — no underlying-set functor from law-carrying monoids over Set/Coq with a free left adjoint or universal arrow; `Theory/Coq/Monoid.v` is ops-only; the one-point-O instantiation of the free-category theorem is not performed; and no bridge connects `list_initial`'s initial-algebra property to the free-monoid adjunction (lists-as-free-monoid is prose in `Theory/Coq/List/Proofs.v:21` and `Theory/Coq/Foldable.v:30`).

## Work to be done

Suggested module: `Instance/Coq/Monoid/Free.v` (or `Theory/Algebra/Monoid/Free.v` at `Mon(Sets)`).

1. Fix a concrete monoid category with underlying-set functor U — either `Mon` at a cartesian base instantiated to Sets/Coq, or a direct category of law-carrying monoids over Coq types.
2. Construct the free monoid on X as lists over X with concatenation, the unit map p : X to U(list X) by singletons.
3. Prove the universal property: for any monoid L and function h : X to U L, a unique monoid homomorphism h' with U h' ∘ p = h (uniqueness up to the ambient `≈`); package as a `UniversalArrow` against U (donor `Theory/Universal/Arrow.v`), and optionally assemble the free-forgetful adjunction over all X.
4. Bridge notes: derive or relate to `list_initial` (fold = the unique extension), and record the one-object-graph reading connecting to `FreeOnQuiver` (full transfer through delooping may be deferred with a header note).

Donors: `Theory/Algebra/Monoid/Hom.v`, `Instance/Coq/Lists.v`, `Theory/Universal/Arrow.v`, `Construction/Free/Quiver.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.7 Cor. 2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the universal arrow / adjunction)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Coq/Monoid/Free.v
echo 'Require Import Category.Instance.Coq.Monoid.Free. Print Assumptions free_monoid_universal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.7 Cor. 2 (pp. 50–51), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.7:cor2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.7: Opposite and product graphs"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.7:ex1]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.7 Exercise 1, book p. 51 (PDF 61). Item: `maclane:II.7:ex1`.

## Background

Graphs carry opposites (reverse every edge) and binary products (pairs of nodes, pairs of edges) defined so that the forgetful functor from categories to graphs preserves both. See nLab: [quiver](https://ncatlab.org/nlab/show/quiver).

## Current state in the library

- `Construction/Free/Quiver.v` supplies quivers, their category, and the forgetful functor (`Forgetful : StrictCat ⟶ QuiverCategory`, line 412) — and even Requires `Construction.Opposite` and `Construction.Product` without using them.
- Precise gap (verified): no opposite-quiver or product-quiver construction exists (searches for `QuiverOp`/`opposite quiver`/`QuiverProduct` and variants: 0 hits), and hence no preservation statements for the forgetful functor.

## Work to be done

Extend `Construction/Free/Quiver.v` (or add `Construction/Free/Quiver/Constructions.v`).

1. Define the opposite quiver (same nodes, edges x y := edges y x, transported setoids) and the product quiver (node pairs, edge pairs, componentwise setoid).
2. Prove the forgetful functor preserves them: the underlying quiver of C^op is the opposite of the underlying quiver of C, and likewise for binary products — on the nose where the encodings allow (the endpoint-indexed encoding should make both definitional or provable by `eq_refl`-style lemmas; document which).
3. Involution and symmetry sanity lemmas (opposite of opposite; product projections as quiver morphisms).

Donors: `Construction/Free/Quiver.v`, `Construction/Opposite.v`, `Construction/Product.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.7 Ex. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (both constructions, both preservation lemmas)
- [ ] Any new files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Construction/Free/Quiver/Constructions.v
echo 'Require Import Category.Construction.Free.Quiver.Constructions. Print Assumptions Forgetful_preserves_op.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.7 Ex. 1 (p. 51), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.7:ex1"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.7: The free groupoid on a graph and free groups"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.7:ex3]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.7 Exercise 3, book p. 51 (PDF 61). Item: `maclane:II.7:ex3`.

## Background

Every graph generates a free groupoid — the analogue of the free category in which the generated arrows are invertible, built from reduced zig-zag words — satisfying the corresponding universal property against groupoids; specializing to one object yields the free group on a set. See nLab: [free groupoid](https://ncatlab.org/nlab/show/free+groupoid) and Wikipedia: [Free group](https://en.wikipedia.org/wiki/Free_group).

## Current state in the library

- Precise gap (verified): no free groupoid and no free group exist in-tree (`free group`/`free groupoid` hits are historical essay prose in `Theory/Universal/Arrow.v` and `Structure/Terminal.v`). `Construction/Groupoid.v` is the *core* (maximal sub-groupoid) construction — the other adjoint — and its header records that no standalone category of groupoids exists in-tree; the localization development (`Construction/Localization.v`) is the orthogonal-subcategory form, not an inverting-all-arrows construction.

## Work to be done

Suggested module: `Construction/Free/Groupoid.v`.

1. Groupoid vocabulary (from #248's groupoid issue): the property/class of groupoids sufficient to state the UMP (a full category of groupoids is not required if the UMP is stated over categories-with-all-isos).
2. Construct the free groupoid on a quiver: arrows are words in the edges and their formal inverses, with the setoid quotient by the cancellation relations (a `HomCongruence`-style inductive equivalence — donor `Construction/Quotient.v`); prove the groupoid property.
3. Universal property, Theorem-1 style: every quiver morphism into (the underlying quiver of) a groupoid extends to a unique functor from the free groupoid.
4. Corollary: the free group on a set — the one-node case — with its universal property stated over group-like one-object groupoids (or over the group category of a delooping bridge, documented).

Donors: `Construction/Free/Quiver.v` (construction and UMP pattern), `Construction/Quotient.v`, `Construction/Groupoid.v` (vocabulary), `Theory/Universal/Arrow.v`.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.7 Ex. 3 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the free groupoid, its UMP, the free-group corollary)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (likely: a substantial new free construction)

## Verification

```
coqc -R . Category Construction/Free/Groupoid.v
echo 'Require Import Category.Construction.Free.Groupoid. Print Assumptions free_groupoid_universal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.7 Ex. 3 (p. 51), paraphrased.

## Dependencies

Depends on: #248

<!-- catalog: {"ids":["maclane:II.7:ex3"],"deps":["maclane:I.5:def9"]} -->
---8<---
```yaml
title: "MacLane II.8: The least congruence and presented categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:II.8:prop1, maclane:II.8:def1, maclane:II.8:def2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.8, book pp. 51–52 (PDF 61–62). Items: `maclane:II.8:prop1` (Proposition 1: the quotient category by an arbitrary relation family and its universal property), `maclane:II.8:def1` (congruences; the least congruence containing a family), `maclane:II.8:def2` (categories presented by generators and relations).

## Background

Any family of relations on the hom-sets of a category generates a least congruence, and quotienting by it yields a category with a projection functor that is universal among functors merging the related arrows; applied to a free category on a graph, this produces the category with given generators and relations — the categorical analogue of presented monoids. See nLab: [quotient category](https://ncatlab.org/nlab/show/quotient+category) and [congruence](https://ncatlab.org/nlab/show/congruence).

## Current state in the library

- For a relation family that is *already* a congruence, everything exists: `HomCongruence` (`Construction/Quotient.v:226`), the quotient `Quotient` (`:254`, hom-setoids coarsened, projection identity-on-objects `QuotientProj` at `:294`), and the factorization with uniqueness (`QuotientLift` `:313`, `QuotientLift_proj` `:322`, `QuotientLift_unique` `:334`).
- The free half exists (`FreeOnQuiver`, `Construction/Free/Quiver.v:431`), and the assembled free-quotient recipe is realized one level up for PROPs (`TermEqW`/`PresentedCat`, `Construction/PROP/Presentation.v:136/180`) — `Construction/Free.v:62`'s header explicitly cites Mac Lane II.7–II.8 for this pattern.
- Precise gaps (verified): no least-congruence closure operator from an arbitrary `HomRel` (congruence-generated closures exist only as bespoke inductives for signature term categories); consequently Proposition 1 in its arbitrary-R form is unstated (no functor-kernel lemma that a functor merging R also merges the closure); and the general "category with generators G and relations R" over a quiver is never assembled — `Quotient` is never applied to `FreeOnQuiver`.

## Work to be done

Extend `Construction/Quotient.v` and add `Construction/Free/Quiver/Presented.v`.

1. Define the inductive least-congruence closure of an arbitrary `HomRel` (constructors: embed R, embed `≈`, symmetry, transitivity, closure under composition on both flanks) and prove it is a `HomCongruence` containing R, least among such.
2. Proposition 1 in full: for arbitrary R, the quotient by the closure with (i) related arrows identified by the projection, and (ii) unique factorization of any functor merging R-related arrows (the kernel lemma: merging R implies merging the closure), riding the existing `QuotientLift` machinery.
3. Presented categories: for a quiver G and a family of path equations, define the presented category as the quotient of `FreeOnQuiver G` by the generated congruence, with its composite universal property; note the one-object case (presented monoids) and, as the book's example, present the ordinal 3 by a composable pair with one composite relation (may also be cited from the concrete-free-categories issue).
4. Header notes relating the general closure to the bespoke `TermEqW` of the PROP presentation layer.

Donors: `Construction/Quotient.v`, `Construction/Free/Quiver.v`, `Construction/PROP/Presentation.v` (closure-shape donor).

## Definition of Done

- [ ] Statements are faithful to Mac Lane §II.8 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the closure, Prop 1, the presented-category constructor)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level (likely: completes the II.7/II.8 free-and-quotient story the `Construction/Free.v` header narrates)

## Verification

```
coqc -R . Category Construction/Quotient.v Construction/Free/Quiver/Presented.v
echo 'Require Import Category.Construction.Free.Quiver.Presented. Print Assumptions presented_universal.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statements match Mac Lane §II.8, Proposition 1 and the congruence/presentation definitions (pp. 51–52), paraphrased.

## Dependencies

None.

<!-- catalog: {"ids":["maclane:II.8:prop1","maclane:II.8:def1","maclane:II.8:def2"],"deps":[]} -->
---8<---
```yaml
title: "MacLane II.8: The walking commutative square by generators and relations"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.8:ex1]
deps_item_ids: [maclane:II.8:def2]
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.8 Exercise 1, book p. 52 (PDF 62). Item: `maclane:II.8:ex1`.

## Background

Presenting the square-shaped graph (four vertices, two parallel composable pairs) with the single relation equating the two composites yields the walking commutative square: a finite category with four identities and exactly five non-identity arrows. See nLab: [commutative square](https://ncatlab.org/nlab/show/commutative+square).

## Current state in the library

- Precise gap (verified): no walking-commutative-square index category exists (finite shapes in `Instance/` are One, Two, Zero, Parallel, Roof, Omega), no presented finite category is built anywhere, and `Construction/Sq.v` is the commuting-squares *double* category over an ambient category — different content.

## Work to be done

Suggested module: `Instance/Square.v` (over the presented-category machinery of the dependency).

1. Present the square: the four-node quiver with edges f, g on two sides and f', g' on the others, one relation equating the two composites; form the presented category.
2. Prove the arrow count: decidable equality/normal forms for hom-sets, showing exactly four identities and five non-identity arrows (the four generators plus the common diagonal).
3. Record it as the index shape for commutative squares: functors out of it correspond to commuting squares in the target (a sanity corollary connecting to `Construction/Arrow.v` morphisms).

Donors: the presented-category machinery of this chapter's II.8 issue, `Construction/Free/Quiver.v`, `Instance/Two.v` (finite-shape style).

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.8 Ex. 1 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the presented square, the counting theorem)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Square.v
echo 'Require Import Category.Instance.Square. Print Assumptions square_arrow_count.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.8 Ex. 1 (p. 52), paraphrased.

## Dependencies

Depends on: maclane:II.8:def2 (resolved to an issue number in the dependency pass)

<!-- catalog: {"ids":["maclane:II.8:ex1"],"deps":["maclane:II.8:def2"]} -->
---8<---
```yaml
title: "MacLane II.8: Group congruences are normal subgroups"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:II.8:ex2]
deps_item_ids: []
```

## Source

Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §II.8 Exercise 2, book p. 52 (PDF 62). Item: `maclane:II.8:ex2`.

## Background

On a group regarded as a one-object category, congruences correspond exactly to normal subgroups — two arrows are related precisely when they differ by an element of the subgroup — recovering quotient groups as quotient categories. See Wikipedia: [Normal subgroup](https://en.wikipedia.org/wiki/Normal_subgroup).

## Current state in the library

- The general congruence-quotient machinery exists (`HomCongruence`/`Quotient`, `Construction/Quotient.v:226/254`).
- Precise gap (verified): "normal subgroup" has zero hits in-tree; `Structure/Group.v` is group *objects* in a cartesian category and `Instance/Comp.v`'s `Group` is an equational algebra for the computability development — neither carries a congruence correspondence, and no group delooping exists to state the exercise.

## Work to be done

Suggested module: `Instance/Group/Congruence.v` (over the delooping from #220).

1. Define normal subgroups (of the group notion accompanying #220's delooping).
2. The correspondence, both directions: a normal subgroup N yields a `HomCongruence` on the delooped group by f R g iff the combination of g-inverse with f lies in N; conversely every congruence arises this way from the class of the identity; the two maps are mutually inverse.
3. Corollary: the quotient category of the delooping by the congruence is the delooping of the quotient group.

Donors: `Construction/Quotient.v`, the delooping and group vocabulary from #220.

## Definition of Done

- [ ] Statement is faithful to Mac Lane §II.8 Ex. 2 (setoid `≈` discipline; never `=` on morphisms)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed for each principal artifact (the bijection, the quotient corollary)
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```
coqc -R . Category Instance/Group/Congruence.v
echo 'Require Import Category.Instance.Group.Congruence. Print Assumptions congruence_normal_subgroup.' | coqtop -R . Category
make && make todo
nix build .#category-theory_8_20
```
Review item: statement matches Mac Lane §II.8 Ex. 2 (p. 52), paraphrased.

## Dependencies

Depends on: #220

<!-- catalog: {"ids":["maclane:II.8:ex2"],"deps":["maclane:I.2:construction3"]} -->

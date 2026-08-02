```yaml
title: "Riehl 2.0/2.4: The n-colouring functor on graphs, its representing object K_n, and the category of n-coloured graphs"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.0:construction-ncolor, riehl:2.4:example3]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: chapter 2 roadmap (unnumbered prose preceding §2.1), printed p. 53 (PDF pp. 73–74); §2.4 Example 2.4.3, printed p. 73 (PDF p. 93).
- Items: `riehl:2.0:construction-ncolor`, `riehl:2.4:example3`.

## Background

A proper n-colouring of a simple graph assigns one of n colours to each vertex so that adjacent vertices differ; colourings pull back along graph homomorphisms, giving a contravariant set-valued functor on graphs, and that functor is represented by the complete graph on n vertices — a colouring of G is exactly a homomorphism G → K_n. Reading the colouring problem representably is what makes "there is no uniform way to turn an m-colouring into an n-colouring for m > n" a statement about the absence of homomorphisms K_m → K_n.

- nLab: <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/category+of+elements>
- Wikipedia: <https://en.wikipedia.org/wiki/Graph_coloring>

## Current state in the library

Absent, and the ambient category is absent too.

- `rg -i 'colou?r'` over `*.v` hits only `Construction/ColouredPROP/*` (the colours labelling the objects of a coloured PROP) and `Instance/ZX.v`'s spider colour-change rules; `rg -i 'coloring|colouring|chromatic|complete graph'` returns nothing relevant. There is no proper-colouring predicate and no K_n.
- The only graph-shaped construction in the tree is the quiver/free-category development, `Construction/Free/Quiver.v` (`Quiver`, `QuiverHomomorphism`, `QuiverCategory` at `:358`), a directed multigraph presented by an indexed family `edges : nodes → nodes → Type`. It carries no adjacency/incidence *predicate*, no symmetry, no irreflexivity — so Riehl's `Graph` (simple graphs and their homomorphisms) is not the in-tree `Quiv`, and a colouring cannot even be phrased against it.
- `Functor/Representable.v:46`'s `Class Representable` exists but has **zero instances tree-wide** (verified in Phase D), so the representing-object half of the construction has no precedent to imitate either.
- Consequently Example 2.4.3 — that the category of elements of the colouring functor is the category of n-coloured graphs and colour-preserving homomorphisms — has neither of its two ingredients.

## Work to be done

Suggested modules: `Instance/Graph.v` (new) and `Instance/Graph/Colouring.v` (new).

1. Define the category `Graph` of **simple** graphs: a setoid of vertices with a symmetric irreflexive adjacency relation respecting `≈`, and homomorphisms as adjacency-preserving maps. State in the header how this relates to the directed-graph presentation of #705 and to `Construction/Free/Quiver.v`'s `Quiver` — the two are different objects and the header must say so rather than let a reader assume `Quiv` is `Graph`.
2. Define `nColor n : Graph^op ⟶ Sets`, carrying G to the setoid of proper n-colourings of G and a homomorphism to restriction along it; prove functoriality (the well-definedness step is that a homomorphism preserves adjacency, so a proper colouring pulls back to a proper colouring).
3. Construct `K n` (vertices `Fin.t n`, adjacency `≠`) and prove `nColor n ≅ [Hom ─, K n]` as a **natural** isomorphism of presheaves, not a family of bijections; record the universal element (the identity colouring of K n).
4. Prove the two consequences the roadmap advertises: natural endomorphisms of `nColor n` are exactly the colour permutations, i.e. the automorphisms of `K n` (a corollary of the Yoneda embedding, `Functor/Hom/Yoneda.v:231`); and for m > n there is no natural transformation `nColor m ⟹ nColor n`, because there is no graph homomorphism `K m ⟶ K n`.
5. Example 2.4.3: instantiate the category of elements (#345) at `nColor n` and prove it isomorphic to the category of n-coloured graphs and colour-preserving homomorphisms, with the projection forgetting the colouring.

In-tree donors: `Functor/Hom/Yoneda.v` (Yoneda lemma and embedding), `Functor/Representable.v`, `Instance/FinSet.v` (`Fin.t`-indexed finite objects for `K n`), `Construction/Free/Quiver.v` (presentation to contrast with), and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl chapter 2's roadmap (printed p. 53) and Example 2.4.3 (printed p. 73); setoid `≈` discipline throughout — never `=` on morphisms
- [ ] `Graph` is defined for **simple** graphs, and the header states precisely how it differs from `Quiver`/`QuiverCategory` and from #705's directed graphs
- [ ] `nColor n` is a functor with proved functor laws, and `nColor n ≅ [Hom ─, K n]` is proved as a natural isomorphism
- [ ] The colour-permutation description of `End(nColor n)` is derived from the Yoneda embedding, not proved by hand
- [ ] The non-existence of a natural `nColor m ⟹ nColor n` for m > n is proved
- [ ] The category of elements of `nColor n` is identified with n-coloured graphs and colour-preserving homomorphisms
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Graph`, `nColor`, the representation, and the elements identification
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Graph.v
coqc -R . Category Instance/Graph/Colouring.v
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20 .#category-theory_8_19
```
```coq
Print Assumptions nColor_represented.
Print Assumptions nColor_elements_coloured_graphs.
```
Reviewer checklist: the representation is a natural isomorphism of presheaves (a per-object bijection is not the theorem); the colour-permutation corollary is obtained through the Yoneda embedding; statement matches Riehl chapter 2 roadmap (printed p. 53) and Example 2.4.3 (printed p. 73).

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #705 (the category of directed graphs as a functor category — the nearest in-tree graph development; this issue must build the *simple*-graph variant and relate the two)

<!-- catalog: {"ids":["riehl:2.0:construction-ncolor","riehl:2.4:example3"],"deps":["#345","#705"]} -->

---8<---

```yaml
title: "Riehl 2.1: The identity functor on Sets is represented by the singleton — the global-elements isomorphism"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example5]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1 ("Representable functors"), Example 2.1.5, clause (i) only, printed p. 56 (PDF p. 76).
- Items: `riehl:2.1:example5` (clause (i); the other thirteen clauses are covered elsewhere — see Dependencies).

## Background

The very first representable functor is the identity on sets: a map from a one-point set to X is the same thing as an element of X, so `Set(∗, −) ≅ Id`. Small as it is, this is the bridge between the *element* language of the Yoneda lemma and the *arrow* language of category theory, and every "an element of F c is a map out of the terminal object" step in the book passes through it.

- nLab: <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/terminal+object>

## Current state in the library

The isomorphism is not stated anywhere, and its absence has already blocked three other results.

- `Instance/Sets.v:248` gives `Sets_Terminal : @Terminal Sets` (the singleton setoid), and `Functor/Hom.v:60` gives `Curried_Hom C : C^op ⟶ [C, Sets]`, so `[Hom 1,─] : Sets ⟶ Sets` is expressible; but there is no lemma or instance relating it to the identity functor. Phase D searched `Instance/Sets.v` explicitly and found only `Sets_Terminal` — no global-elements isomorphism.
- The consequence is recorded three times in the Chapter 2 verification: the universal-element criterion of Riehl §2.4 cannot be specialized from the comma-category form to an arbitrary `F : C ⟶ Sets` because there is no `Hom_Sets(1, X) ≅ X` to rewrite along (`Structure/UniversalProperty/Universal/Arrow.v:61` fixes `repr_functor := (Curried_Hom C c) ◯ U`, i.e. `d ↦ Hom_C(c, U d)`, which is *not* `F` without this lemma); the same obstruction blocks the "elements are arrows out of ∗" step of the comma description of the category of elements.
- `Functor/Representable.v:46`'s `Class Representable` has zero instances in the tree, so this would also be its first.

## Work to be done

Suggested module: extend `Instance/Sets.v`, or add `Instance/Sets/GlobalElements.v` if the section context there is awkward.

1. Prove `global_elements {X : Sets} : (1 ~{Sets}~> X) ≊ X` — an isomorphism of setoids, with `to` evaluation at the point of the singleton and `from` the constant map.
2. Upgrade to a **natural** isomorphism `[Hom 1,─] ≅ Id[Sets]` in `[Sets, Sets]`; naturality is the statement that evaluation commutes with post-composition.
3. Register the resulting `Representable Id[Sets]` instance (representing object the terminal setoid), giving `Functor/Representable.v`'s class its first inhabitant.
4. Export the rewriting lemma in the form downstream consumers need: for `F : C ⟶ Sets` and `c : C`, `Hom_Sets(1, F c) ≊ F c` naturally in `c`, so that a statement about `d ↦ Hom_Sets(1, F d)` transports to one about `F`.
5. State the same for `Coq` if it is free there, and note in the header which one the downstream issues should consume.

In-tree donors: `Instance/Sets.v:248` (`Sets_Terminal`), `Functor/Hom.v:60` (`Curried_Hom`), `Functor/Representable.v:46`, `Instance/Fun.v` (the functor category in which the natural iso lives).

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.5(i), printed p. 56; setoid `≈` discipline — never `=` on morphisms
- [ ] The isomorphism is proved **naturally** in the varying setoid, not only pointwise
- [ ] A `Representable` instance for the identity functor on `Sets` is registered
- [ ] The transport lemma `Hom_Sets(1, F −) ≅ F` is exported for reuse (this is the form Riehl §2.4's universal-element criterion needs)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for the isomorphism and the naturality
- [ ] Any new file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Sets.v
make && make todo
```
```coq
Print Assumptions global_elements.
Print Assumptions Sets_Id_Representable.
```
Reviewer checklist: the isomorphism is stated in `[Sets, Sets]` (a family of setoid isomorphisms is not the theorem); statement matches Riehl Example 2.1.5(i), printed p. 56.

## Dependencies

None. (The remaining clauses of Example 2.1.5 are covered by separate issues: clauses (ii) and (xiv) with the `Top` development, clauses (iii) and (vi)–(vii) with `Grp`, clauses (iv)–(v) by #309, clause (viii) with `Rng`, clauses (ix)–(xii) with `Cat`, clause (xiii) with pointed objects.)

<!-- catalog: {"ids":["riehl:2.1:example5"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 2.1/2.4: Initial and terminal objects as representations of the constant singleton functor"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:def3, riehl:2.4:remark-every-category-is-elements]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1 ("Representable functors"), Definition 2.1.3, printed p. 55 (PDF p. 75); §2.4, the unnumbered remark between Example 2.4.12 and Definition 2.4.13, printed p. 77 (PDF p. 97).
- Items: `riehl:2.1:def3`, `riehl:2.4:remark-every-category-is-elements`.

## Background

Initiality and terminality are the degenerate representability statements: c is initial exactly when the covariant hom-functor C(c,−) is naturally isomorphic to the constant singleton-valued functor, and terminal exactly when C(−,c) is. Read through the category of elements, this says every category E is the category of elements of the constant functor at a point, and a representation of that functor is precisely an initial object of E.

- nLab: <https://ncatlab.org/nlab/show/initial+object>, <https://ncatlab.org/nlab/show/terminal+object>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

The elementary form is present in both variances; the representable form is present in neither, and the constant singleton functor is never used as a representation target.

- `Structure/Terminal.v:107` is `Class Terminal := { terminal_obj : C; one {x} : x ~> terminal_obj; one_unique {x} (f g : x ~> terminal_obj) : f ≈ g }` — pointwise, exactly the assertion that each hom-setoid into 1 is a singleton up to `≈` — with `:119` `one_comp : one ∘ f ≈ one`, which is the naturality square of the isomorphism that is never assembled. `Structure/Initial.v:109/112` (`zero`, `zero_unique`) is the `C^op` dual.
- Neither direction of the biconditional exists. Verified negatives: no declaration anywhere pairs `Terminal`/`Initial` with a hom-functor or with the constant functor at 1; the constant singleton functor occurs only as a **weight**, in `Structure/Limit/Weighted.v:145` (`cone_of_nat`) and `:157` (`nat_of_cone`), both over `Delta[J](@terminal_obj Sets Sets_Terminal)`.
- The generic representability packaging `Structure/UniversalProperty.v:41` (`Class IsUniversalProperty`) is instantiated for binary products (`Structure/UniversalProperty/Cartesian.v:60`) and for limits (`Structure/UniversalProperty/Limit.v:141`) but **not** for terminal or initial objects.
- The nearest in-tree statement in the same spirit is `Structure/Limit/Terminal.v:33`, `Terminal_Limit (C : Category) (F : 0 ⟶ C) : Limit F ↔ @Terminal C` — terminality as a limit, not as representability.
- For the §2.4 remark, both clauses are missing: there is no `E ≅ ∫(Δ1)` statement (there is no `∫` at all — #345), and no lemma "a is initial iff `[Hom a,─]` is naturally isomorphic to the constant singleton functor". Phase D confirmed the *vocabulary* is present — `Functor/Diagonal.v:55` provides the notation `=( c ) := Diagonal 1 c` — so what is missing is the two assertions, not the machinery.

## Work to be done

Suggested modules: extend `Structure/Terminal.v` and `Structure/Initial.v`; put the elements half in a satellite of whichever file #345 lands the category of elements in.

1. Build the constant singleton copresheaf `Δ1 : C ⟶ Sets` (via `Functor/Diagonal.v` at `Sets_Terminal`) and prove `initial_iff_hom_constant : @Initial C ↔ { c : C & [Hom c,─] ≅ Δ1 }` in `[C, Sets]` — both directions, with the reverse direction extracting the initial object from the representation (transport the unique point of `Δ1 d` across the isomorphism).
2. Derive the terminal/contravariant clause **by duality** at `C^op` rather than re-proving it; the library's `C^op^op = C` by reflexivity (`Construction/Opposite.v:126` `op_invol`) makes this cheap, and exercising it is part of the point of Riehl §2.1.
3. Instantiate `Structure/UniversalProperty.v:41`'s `IsUniversalProperty` at the terminal and initial predicates, joining the two existing instantiations (products at `Structure/UniversalProperty/Cartesian.v:60`, limits at `.../Limit.v:141`); this is what makes `univ_property_unique_up_to_unique_iso` (`:175`) applicable to them.
4. Prove the §2.4 remark: for any category E, `E ≅[Cat] ∫(Δ1)` over E (the projection being an isomorphism onto E), and a representation of `Δ1 : E ⟶ Sets` is exactly an initial object of E — i.e. the general elements picture degenerates to initiality when the functor is constant at a point.
5. Cross-reference `Structure/Limit/Terminal.v:33` in the header so a reader sees the two readings (terminality as a limit, terminality as representability) side by side.

In-tree donors: `Structure/Terminal.v`, `Structure/Initial.v`, `Functor/Diagonal.v:55`, `Functor/Hom.v`, `Structure/UniversalProperty.v`, `Instance/Sets.v:248`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Definition 2.1.3 (printed p. 55) and the §2.4 remark (printed p. 77); setoid `≈` discipline — never `=` on morphisms
- [ ] Both directions of both biconditionals proved; the isomorphism is stated in the functor category, not as a family of bijections
- [ ] The terminal/contravariant clause is obtained by duality from the initial/covariant one, not re-proved
- [ ] `IsUniversalProperty` instantiated at the terminal and initial predicates
- [ ] `E ≅[Cat] ∫(Δ1)` proved, and the identification of representations of `Δ1` with initial objects of E
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New/edited files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Terminal.v
coqc -R . Category Structure/Initial.v
make && make todo
```
```coq
Print Assumptions initial_iff_hom_constant.
Print Assumptions terminal_iff_hom_constant.
Print Assumptions category_is_elements_of_constant.
```
Reviewer checklist: the representable characterization is stated as a natural isomorphism in `[C, Sets]`; the dual is derived, not duplicated; statement matches Riehl Definition 2.1.3 (printed p. 55).

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor — needed only for the §2.4 remark)

<!-- catalog: {"ids":["riehl:2.1:def3","riehl:2.4:remark-every-category-is-elements"],"deps":["#345"]} -->

---8<---

```yaml
title: "Riehl 2.1/2.2: The objects, morphisms and isomorphisms functors on Cat and their representing categories"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example5, riehl:2.2:example9, riehl:2.2:exiv, riehl:2.3:exi]
deps_item_ids: [riehl:2.1:exiv]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1, Example 2.1.5, clauses (ix)–(xii), printed p. 56 (PDF pp. 76–77); §2.2, Example 2.2.9 and Exercise 2.2.iv, printed pp. 65–66 (PDF pp. 85–86); §2.3, Exercise 2.3.i clause (i), printed p. 71 (PDF p. 91).
- Items: `riehl:2.1:example5` (clauses (ix)–(xii) only), `riehl:2.2:example9`, `riehl:2.2:exiv`, `riehl:2.3:exi` (clause (i) only).

## Background

The set-valued functors on Cat that read off a small category's objects, morphisms, isomorphisms and composable strings are all representable, by the terminal category, the walking arrow, the walking isomorphism and the ordinals respectively. Yoneda then computes the natural transformations between them: there are exactly three from objects to morphisms (identity, domain, codomain), because there are exactly three functors between the representing categories.

- nLab: <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/Yoneda+embedding>, <https://ncatlab.org/nlab/show/subfunctor>

## Current state in the library

The representing objects exist; the functors they represent do not, so no clause of the example is statable.

- **No set-valued functor out of `Cat` exists at all.** `rg 'Cat ⟶ Sets|Cat ⟶ Set\b'` returns 0 hits; `rg 'Cat ⟶'` yields only `Instance/StrictCat/ToCat.v`'s `StrictCat_to_Cat`, `Functor/Construction/Product.v`'s `Cat ∏ Cat ⟶ Cat`, and `Test/Issue138.v`'s deliberate `Fail Check`. `Instance/Cat.v`'s only top-level constants are `Cat` itself (`:142`) and the `Cat_Iso_*` full/faithful lemmas (`:165`–`:252`) — no `ob`, no `mor`, no forgetful functor.
- Two of the four representing categories are in tree: `Instance/One.v`'s `_1` and `Instance/Two.v:134`'s `_2` (the walking arrow). The **walking isomorphism** appears only as header prose (`Construction/Funny.v:41`, `Instance/StrictCat/Funny.v:39–42`) and is never constructed; neither is the ordinal `3` or a general `n+1` as a category (`Instance/Omega.v` is the whole of ω, not its finite truncations). Note the trap: `Instance/Two.v:174`'s `_2_as_Set : _2 ⟶ Sets` is a functor *out of* the walking arrow, not the morphisms functor *into* it.
- Exercise 2.2.iv needs a componentwise-monic natural transformation; `rg 'Monic'` over `Instance/Fun.v`, `Instance/Fun/*.v` and `Theory/Natural/*.v` returns 0 hits, so `Monic` is never applied in a functor category and "subfunctor" is not expressible (this is the gap filed as `riehl:2.1:exiv`).
- For Exercise 2.3.i clause (i): the representation whose universal element is asked for does not exist. `Construction/Arrow.v:104–108` states verbatim that "no formal comparison with a functor category over the walking arrow `_2` of `Instance/Two.v` is developed in-tree" — so even the `[2, C] ≃ Arrow C` reading is documentation-level.

## Work to be done

Suggested module: `Instance/Cat/Representables.v` (new), with the walking isomorphism in `Instance/Iso.v` (new) or alongside `Instance/Two.v`.

1. Build the missing representing categories: the walking isomorphism (two objects, a mutually inverse pair) and the finite ordinals `[n]` as categories (`Instance/Omega.v`'s `le_t` order truncated, or directly), noting that `[n+1]` represents strings of n composable morphisms.
2. Define `ob : Cat ⟶ Sets`, `mor : Cat ⟶ Sets`, `iso : Cat ⟶ Sets` and `cpair : Cat ⟶ Sets` (composable pairs), being explicit in the header about the size discipline the library's universe polymorphism imposes on "the set of objects of a small category".
3. Prove each is representable, as a **natural** isomorphism: `ob ≅ [Hom _1,─]`, `mor ≅ [Hom _2,─]`, `iso ≅ [Hom WalkingIso,─]`, `cpair ≅ [Hom [3],─]`, and the general `[n+1]` statement. Record each universal element (Exercise 2.3.i clause (i) asks precisely for the one belonging to `mor`: the non-identity arrow of `_2`).
4. Example 2.2.9: enumerate the functors `_1 ⟶ _2` (there are exactly two) and `_2 ⟶ _1` (exactly one), and conclude through the Yoneda embedding (`Functor/Hom/Yoneda.v:253` `Covariant_Yoneda_Embedding`) that `Nat(ob, mor)` has exactly three elements — identity-assigning, domain and codomain — and `Nat(mor, ob)` exactly one. State it as an isomorphism of setoids with a three-element setoid, so "exactly three" is a theorem rather than three existence facts plus prose.
5. Exercise 2.2.iv: build the functor `_2 ⟶ WalkingIso` and show the induced natural transformation `iso ⟹ mor` is componentwise monic, exhibiting `iso` as a subfunctor of `mor` in the sense of the subfunctor issue below.
6. While here, close the documentation gap `Construction/Arrow.v:104–108` records, by relating `mor C` to `Construction/Arrow.v:110`'s `Arrow C` — the representation makes the comparison available.

In-tree donors: `Instance/Cat.v`, `Instance/One.v`, `Instance/Two.v`, `Instance/Omega.v`, `Construction/Arrow.v`, `Functor/Hom/Yoneda.v:231/253`, `Theory/Isomorphism.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.5 clauses (ix)–(xii) (printed p. 56), Example 2.2.9 and Exercise 2.2.iv (printed pp. 65–66) and Exercise 2.3.i clause (i) (printed p. 71); setoid `≈` discipline — never `=` on morphisms
- [ ] The walking isomorphism and the finite ordinals are constructed as categories
- [ ] `ob`, `mor`, `iso`, `cpair` are defined with proved functor laws, and each representation is a **natural** isomorphism with its universal element named
- [ ] "Exactly three natural transformations `ob ⟹ mor`" is proved as an isomorphism with a three-element setoid, derived through the Yoneda embedding
- [ ] `iso ⟹ mor` is proved componentwise monic and exhibited as a subfunctor
- [ ] The `mor`/`Arrow C` comparison that `Construction/Arrow.v:104–108` records as missing is supplied, and that header note is updated
- [ ] The size discipline for "the set of objects of a small category" is disclosed in the header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each representation and for the counting theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Cat/Representables.v
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20
```
```coq
Print Assumptions mor_represented.
Print Assumptions nat_ob_mor_three.
Print Assumptions iso_subfunctor_mor.
```
Reviewer checklist: each representation is a natural isomorphism in `[Cat, Sets]`; the counting result is derived from the Yoneda embedding rather than by an ad-hoc enumeration of natural transformations; statement matches Riehl Example 2.2.9 (printed p. 65).

## Dependencies

- Depends on: `riehl:2.1:exiv` (subfunctors of a represented functor — supplies the componentwise-monic notion Exercise 2.2.iv needs)

<!-- catalog: {"ids":["riehl:2.1:example5","riehl:2.2:example9","riehl:2.2:exiv","riehl:2.3:exi"],"deps":["riehl:2.1:exiv"]} -->

---8<---

```yaml
title: "Riehl 2.1: Subfunctors of a represented functor and the sieve condition"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:2.1:exiv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1 ("Representable functors"), Exercise 2.1.iv, printed p. 59 (PDF p. 79).
- Items: `riehl:2.1:exiv`.

## Background

A subfunctor of G is a functor equipped with a natural transformation into G whose components are all monomorphisms; for a set-valued G this is a choice of subset of each G c stable under the functor's action. Applied to a represented presheaf C(−,c), the stable families of subsets of the hom-sets are exactly the **sieves** on c — the sets of arrows into c closed under precomposition — which is the definition on which Grothendieck topologies rest.

- nLab: <https://ncatlab.org/nlab/show/subfunctor>, <https://ncatlab.org/nlab/show/sieve>

## Current state in the library

Neither the general notion nor its instance exists, and the sheaf development deliberately took a different route.

- `rg -i 'sieve|subfunctor|subpresheaf'` over `*.v` returns exactly two hits, both prose in header comments: `Theory/Sheaf.v:80` ("through sieves in SGA 4") and `Construction/Localization.v:101` ("orthogonal to the covering sieves"). Nothing is ever defined.
- `Theory/Sheaf.v:159` `Class Site (C : Category)` axiomatizes Grothendieck topologies by **covering families** with a pullback-stability axiom, not by sieves — so the sheaf layer contains no sieve object to reuse.
- The prerequisite is missing too: there is no notion of a componentwise-monic natural transformation. `rg 'Monic'` over `Theory/Natural/Transformation.v` and `Instance/Fun.v` returns 0 hits, so `Theory/Morphisms.v:116`'s `Class Monic` is never applied in a functor category.
- `Construction/Subcategory.v` provides full subcategories of a category, which is a different construction and does not give subobjects of a functor.

## Work to be done

Suggested module: `Theory/Subfunctor.v` (new), with the sieve corollary either there or in a satellite feeding `Theory/Sheaf.v`.

1. Define `Subfunctor (G : C ⟶ D)` as a functor F together with `α : F ⟹ G` all of whose components are `Monic` in D, with the induced ordering/equivalence on subfunctors (two subfunctors are the same when the monos factor through each other, mirroring `Theory/Subobject.v`'s treatment of subobjects — reuse that pattern rather than inventing a second one).
2. Specialize to `D := Sets`: prove that a subfunctor of `G : C^op ⟶ Sets` is equivalently a family of `≈`-closed subsetoids `F c ⊆ G c` such that each `G f` restricts, and give both directions of the translation.
3. Prove the exercise: subfunctors of the represented presheaf `[Hom ─, c]` correspond bijectively to sieves on c — families `S c'` of arrows `c' ⟶ c` closed under precomposition (`f ∈ S c'` and `g : c'' ⟶ c'` imply `f ∘ g ∈ S c''`). State it as an isomorphism of setoids, and record the maximal sieve (all arrows) and the empty sieve as the extremes.
4. Note in the header the relation to `Theory/Sheaf.v:159`'s covering-family presentation of a `Site`, so a future sheaf refactor can see that the sieve vocabulary now exists.

In-tree donors: `Theory/Natural/Transformation.v`, `Theory/Morphisms.v:116` (`Monic`), `Theory/Subobject.v` (the subobject-as-quotient-of-monos pattern), `Functor/Hom.v:60` (`Curried_Hom`), `Instance/Sets.v:369` (`injectivity_is_monic`), `Theory/Sheaf.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 2.1.iv, printed p. 59; setoid `≈` discipline — never `=` on morphisms
- [ ] `Subfunctor` is defined generally (componentwise monic natural transformation), with the subobject-style equivalence, and reuses `Theory/Subobject.v`'s pattern rather than duplicating it
- [ ] The `Sets`-valued reformulation (a stable family of subsetoids) is proved in both directions
- [ ] The sieve characterization of subfunctors of `[Hom ─, c]` is proved as a bijection, with the maximal and empty sieves exhibited
- [ ] The header records the relation to `Theory/Sheaf.v:159`'s covering-family `Site`
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Subfunctor` and the sieve bijection
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Theory/Subfunctor.v
make && make todo
```
```coq
Print Assumptions Subfunctor.
Print Assumptions subfunctors_of_representable_are_sieves.
```
Reviewer checklist: the monic condition is componentwise in the target category (not `Monic` of the whole natural transformation in the functor category); the sieve condition is closure under **pre**composition; statement matches Riehl Exercise 2.1.iv, printed p. 59.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:2.1:exiv"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 2.1: Representable functors preserve monomorphisms"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:2.1:exii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1 ("Representable functors"), Exercise 2.1.ii, printed p. 59 (PDF p. 79).
- Items: `riehl:2.1:exii`.

## Background

A representable functor carries monomorphisms to injections, because a monomorphism is exactly an arrow whose post-composition action on every hom-set is injective; contrapositively, a set-valued functor that destroys a monomorphism cannot be representable — the cheapest available non-representability test.

- nLab: <https://ncatlab.org/nlab/show/monomorphism>, <https://ncatlab.org/nlab/show/representable+functor>

## Current state in the library

Nothing states it, and the vocabulary it would be stated in does not exist either.

- `rg -i 'PreservesMonos|preserves.*mono|preserve monomorphism'` finds only `Theory/Adjunction.v:310` (`adj_monic`: a *faithful left adjoint* transposes a mono) and `Construction/Reflective/Idempotent.v:137`; neither concerns representable or hom-functors. `Functor/` contains no occurrence of `Monic` at all, so there is no `PreservesMonos` predicate.
- The two ingredients are present and exact: `Theory/Morphisms.v:116` `Class Monic {x y} (f : x ~> y) := { monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2 }`, and `Instance/Sets.v:369` `injectivity_is_monic`, the bi-implication between pointwise injectivity and `Monic` in `Sets`.
- **Sizing note carried from verification:** for `F = [Hom c,─]` the exercise is definitionally immediate here — `fmap[[Hom c,─]] m` *is* post-composition by m, `Monic m` *is* its injectivity, and `injectivity_is_monic` converts that to monicity in `Sets`. The only real formalization content is (a) transporting mono-preservation across a natural isomorphism `F ≅ [Hom c,─]`, and (b) the counterexample functor. This should therefore be a small issue, needing no new vocabulary beyond a `PreservesMonos` predicate.

## Work to be done

Suggested module: `Functor/Preservation/Monos.v` (new), or extend `Theory/Morphisms.v` if the predicate is better placed with the morphism classes.

1. Define `PreservesMonos (F : C ⟶ D) := ∀ x y (f : x ~> y), Monic f → Monic (fmap[F] f)`.
2. Prove `hom_preserves_monos {c : C} : PreservesMonos [Hom c,─]` — the immediate step described above, going through `Instance/Sets.v:369`.
3. Prove the transport lemma `preserves_monos_iso : F ≅ G → PreservesMonos G → PreservesMonos F` (an isomorphism in `[C, Sets]`), and conclude `representable_preserves_monos : Representable F → PreservesMonos F` for `Functor/Representable.v:46`'s class.
4. Give the contrapositive as a usable non-representability test, and exhibit at least one concrete witness: a set-valued functor on an in-tree category that destroys a monomorphism, hence is not representable. Pick a category the library actually has (e.g. a functor on `Sets` or on a small shape from `Instance/Shapes.v`) and prove both the mono-destruction and the resulting non-representability, so the exercise's second half is a theorem rather than a remark.

In-tree donors: `Theory/Morphisms.v:116`, `Instance/Sets.v:369`, `Functor/Hom.v:60`, `Functor/Representable.v:46`, `Theory/Natural/Transformation.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 2.1.ii, printed p. 59; setoid `≈` discipline — never `=` on morphisms
- [ ] `PreservesMonos` defined and `hom_preserves_monos` proved
- [ ] Transport along a natural isomorphism proved, and `representable_preserves_monos` stated over `Functor/Representable.v`'s class
- [ ] A concrete non-representable set-valued functor is exhibited **and** its non-representability proved via the contrapositive (not merely asserted)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `representable_preserves_monos` and the counterexample
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Functor/Preservation/Monos.v
make && make todo
```
```coq
Print Assumptions representable_preserves_monos.
```
Reviewer checklist: the counterexample is a genuine proof of non-representability, not a plausibility argument; statement matches Riehl Exercise 2.1.ii, printed p. 59.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:2.1:exii"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 2.1: Transporting representability along natural isomorphisms and equivalences of categories"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:2.1:exiii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1 ("Representable functors"), Exercise 2.1.iii, printed p. 59 (PDF p. 79).
- Items: `riehl:2.1:exiii`.

## Background

Representability is a property of a functor's isomorphism class, so it transports along natural isomorphism; the exercise asks how far that extends when the *domains* are only equivalent — given an equivalence H : C ≃ D and G ∘ H ≅ F, does representability of one of F, G force the other?

- nLab: <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/equivalence+of+categories>

## Current state in the library

Absent, in the strongest sense the tree admits: the representability class is inert.

- `Functor/Representable.v:46` `Class Representable (F : C ⟶ Sets) := { repr_obj : C; represented : [Hom repr_obj,─] ≅ F }` is **referenced nowhere else in the tree** — verified by `rg 'Representable' -g '*.v'`, whose only hits are that file and the unrelated `RepresentableMulticategory` of `Theory/Multicategory/Representable.v` plus prose. There is not even the trivial `F ≅ G → Representable G → Representable F`.
- What equivalences *are* shown to transport in tree is limits, adjunctions and monoidal structure: `Theory/Equivalence/Limit.v`, `Theory/Equivalence/Adjunction.v`, `Theory/Equivalence/Monoidal.v`. Representability is not among them; enumerating the top-level declarations of `Theory/Equivalence.v` and its satellites confirms this.
- The nearest in-tree analogue is `Structure/UniversalProperty.v:163` `univ_property_respects_iso`, which transports a universal property along an isomorphism of **objects inside one category** — a different statement.

## Work to be done

Suggested module: `Functor/Representable/Transport.v` (new), or extend `Functor/Representable.v` directly.

1. Prove the base case `representable_respects_iso : F ≅ G → Representable G → Representable F` (isomorphism in `[C, Sets]`), and register it as a `Proper` instance so `rewrite` works on representability.
2. Prove the direction the exercise's part (i) asks about: given an equivalence `H : C ⟶ D` (donor: `Theory/Equivalence.v`'s quasi-inverse class) with `G ◯ H ≅ F`, representability of G gives representability of F, with the representing object transported by H's quasi-inverse.
3. Settle part (ii) honestly: representability of F gives representability of G, using that the quasi-inverse of an equivalence is again one and that `[Hom H c,─] ≅ [Hom c,─] ◯ H⁻¹` up to the equivalence's unit/counit — the point being that an equivalence is invertible, so the implication runs both ways. Prove it rather than assert it, and record in the header that a bare *fully faithful* functor would not suffice.
4. Give the corresponding statement for universal elements: the transported representation carries the universal element across, so the two representations agree under the equivalence.
5. Since `Representable` currently has zero consumers, this issue is also its first: state in the header that the class is now exercised, and check the class's own header cross-references while there (Phase D flagged a header cross-reference defect at `Functor/Representable.v` whose text did not survive into the coverage record — re-derive and fix it).

In-tree donors: `Functor/Representable.v:46`, `Functor/Hom.v`, `Theory/Equivalence.v`, `Theory/Equivalence/FullFaithful.v`, `Theory/Functor.v:227` (`fobj_iso`), `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 2.1.iii, printed p. 59, with **both** parts answered and proved (not one direction plus a remark); setoid `≈` discipline — never `=` on morphisms
- [ ] `representable_respects_iso` proved and registered as a `Proper` instance
- [ ] Transport along an equivalence proved in both directions, with the representing object transported explicitly
- [ ] The universal element is shown to transport with the representation
- [ ] The header records that fully faithful alone is insufficient
- [ ] `Functor/Representable.v` gains at least one consumer, and its header cross-references are checked and corrected
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each transport lemma
- [ ] New/edited files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Functor/Representable/Transport.v
make && make todo
```
```coq
Print Assumptions representable_respects_iso.
Print Assumptions representable_along_equivalence.
```
Reviewer checklist: both implications of the exercise are proved; the isomorphisms are natural isomorphisms in the relevant functor category; statement matches Riehl Exercise 2.1.iii, printed p. 59.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:2.1:exiii"],"deps":[]} -->


---8<---

```yaml
title: "Riehl 2.1/2.4: Representable functors on Grp and Rng — free and cyclic groups, tuples, units, and their universal elements"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example5, riehl:2.1:exi, riehl:2.4:example12]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1, Example 2.1.5 clauses (iii), (vi), (vii) and (viii), printed p. 56 (PDF pp. 76–77); §2.1 Exercise 2.1.i, printed p. 59 (PDF p. 79); §2.4 Example 2.4.12 clauses (iv) and (vi), printed pp. 75–77 (PDF pp. 95–97).
- Items: `riehl:2.1:example5` (clauses (iii), (vi), (vii), (viii) only), `riehl:2.1:exi`, `riehl:2.4:example12` (clauses (iv) and (vi) only).

## Background

"Free" is Riehl's name for a universal property expressed by a *covariant* represented functor: the underlying-set functor of groups is represented by ℤ (the free group on one generator), its n-th power by the free group on n generators, a presentation by the presented group, and the units functor on rings by the Laurent polynomial ring. Read through the category of elements, the free object on n generators is the initial object among groups-with-an-n-tuple.

- nLab: <https://ncatlab.org/nlab/show/free+object>, <https://ncatlab.org/nlab/show/free+group>, <https://ncatlab.org/nlab/show/representable+functor>

## Current state in the library

No clause is statable today, because the ambient categories do not exist; and the one nearby forgetful functor that does exist is easy to misdescribe.

- There is **no category of groups** and no category of rings. `Structure/Group.v:109` declares only `Class GroupObject (grp : C)` — a group object internal to a cartesian monoidal category, with no hom-set computation, no presentation, no free or cyclic construction. `Instance/Comp.v:382` has an elementwise `Group := Algebra GroupOp GroupEq` and a category `Algs` (`:151`), but `Algs` is over algebras *without* equations, so the category of groups is still never formed. `rg -i 'cyclic|free group|group of units|unital ring|Laurent'` returns nothing.
- **Correction carried from Phase D, because a draft written from the Phase-C log would state something false:** the coverage log claimed that none of the in-tree forgetful functors lands in `Sets`. That is wrong — `Instance/CMon.v:169` defines `CMon_Forget : CMon ⟶ Sets`, the forgetful functor from commutative monoids to setoids. It is nevertheless not coverage for any clause here: commutative monoids are not among Riehl's clauses, `CMon_Forget` is nowhere claimed representable, and there is no free commutative monoid in tree (`grep -ci 'free' Instance/CMon.v` = 0). `Instance/CMon.v` is the closest *pattern* to imitate, not evidence.
- `Functor/Representable.v:46`'s `Representable` class has zero instances tree-wide, and there is no universal-element structure (that is #303), so even once the categories land, the vocabulary for "is represented by, with universal element" has to be assembled.

## Work to be done

Suggested modules: `Instance/Grp/Representables.v` and `Instance/Rng/Representables.v` (new), aligned with the layout #255 and #257 introduce.

1. Over #255's `Grp` and its forgetful functor, prove `U : Grp ⟶ Sets` is represented by ℤ, with universal element the generator 1 — clause (iii); the representation is the statement that a homomorphism out of ℤ is freely determined by the image of the generator.
2. Prove the n-th power `Uⁿ : Grp ⟶ Sets` is represented by the free group on n generators (clause (vi)), and the abelian analogue (the direct sum of n copies of ℤ) over whatever abelian-group layer #255/#256 provide.
3. Clause (vii): for a finite presentation ⟨generators | relations⟩, define the functor sending G to the setoid of tuples in G satisfying the relations, and prove it represented by the presented group. Instantiate at one concrete presentation the library can compute with (Riehl uses the symmetric group on three letters), so the clause has a witness rather than only a general theorem.
4. Exercise 2.1.i: identify the functor represented by ℤ/n — groups equipped with an element whose n-th power is the unit — and characterize `Grp(ℤ/n, ℤ/m)` as the elements of ℤ/m killed by n, i.e. the subgroup generated by m/gcd(n,m). Both parts must be theorems.
5. Clause (viii): over #257's `Rng`, define the units functor `(−)ˣ : Rng ⟶ Sets` (which needs the group-of-units construction) and prove it represented by ℤ[x, x⁻¹].
6. Example 2.4.12 clauses (iv) and (vi): instantiate the category of elements (#345) at `Uⁿ : Grp ⟶ Sets` and at `U : Rng ⟶ Sets`, and prove that the free group on n generators (with its generating tuple) is initial in the first and that ℤ[x] (with x) is initial in the second. Also prove the Yoneda corollary Riehl draws in clause (vi): every natural endomorphism of `U : Rng ⟶ Sets` has components r ↦ p(r) for an integer polynomial p, because `End(U) ≅ Rng(ℤ[x], ℤ[x]) ≅ U(ℤ[x])`.
7. Riehl's clauses (iv) and (v) — the free R-module on one generator and ℤ[x] as representing objects — are **not** in this issue's scope: #309 already promises the free R-module and the polynomial ring as universal arrows, and #303 the universal-element packaging. This issue only adds the representability reading for the clauses #309 does not carry.

In-tree donors: `Instance/CMon.v` (the pattern for a concrete algebraic category over setoids, including `CMon_Forget`), `Functor/Representable.v`, `Functor/Hom/Yoneda.v:253`, `Structure/UniversalProperty.v`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.5 clauses (iii), (vi), (vii), (viii) (printed p. 56), Exercise 2.1.i (printed p. 59) and Example 2.4.12 clauses (iv), (vi) (printed pp. 75–77); setoid `≈` discipline — never `=` on morphisms
- [ ] Each representation is a **natural** isomorphism with its universal element named, not a family of bijections
- [ ] Clause (vii) is instantiated at one concrete presentation, not left as a general theorem
- [ ] Both parts of Exercise 2.1.i are proved, including the description of `Grp(ℤ/n, ℤ/m)`
- [ ] The units functor is constructed and its representation by ℤ[x, x⁻¹] proved
- [ ] The initial objects of the two categories of elements are identified, and the integer-polynomial description of `End(U : Rng ⟶ Sets)` is derived through the Yoneda embedding
- [ ] The header records that clauses (iv)–(v) are #309's, and does not restate the false claim that no in-tree forgetful functor lands in `Sets` (`Instance/CMon.v:169` does)
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for each representation and each initiality result
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Grp/Representables.v
coqc -R . Category Instance/Rng/Representables.v
make && make todo
```
```coq
Print Assumptions Grp_Forget_represented.
Print Assumptions units_represented.
Print Assumptions Rng_natural_endos_are_polynomials.
```
Reviewer checklist: every representation is stated in the relevant functor category; the natural-endomorphism computation is derived from Yoneda; statement matches Riehl Example 2.1.5 (printed p. 56) and Example 2.4.12 (printed pp. 75–77).

## Dependencies

- Depends on: #255 (Grp, the category of groups)
- Depends on: #257 (Rng, the category of rings)
- Depends on: #303 (universal elements as first-class structures)
- Depends on: #309 (free modules and polynomial rings as universal arrows — supplies clauses (iv)–(v) and ℤ[x])
- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #442 (the free group functor)

<!-- catalog: {"ids":["riehl:2.1:example5","riehl:2.1:exi","riehl:2.4:example12"],"deps":["#255","#257","#303","#309","#345","#442"]} -->

---8<---

```yaml
title: "Riehl 2.1/2.2/2.4: Representable functors on Top — underlying sets, opens and closeds, paths and reparameterizations"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example5, riehl:2.1:example6, riehl:2.2:exvi, riehl:2.2:exvii, riehl:2.3:exi, riehl:2.4:exv]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1, Example 2.1.5 clauses (ii) and (xiv), printed p. 56 (PDF pp. 76–77); Example 2.1.6 clauses (ii) and (iii), printed p. 57 (PDF pp. 77–78); §2.2 Exercises 2.2.vi and 2.2.vii part (i), printed p. 66 (PDF p. 86); §2.3 Exercise 2.3.i clauses (ii) and (iii), printed p. 71 (PDF p. 91); §2.4 Exercise 2.4.v, printed p. 78 (PDF p. 98).
- Items: `riehl:2.1:example5` (clauses (ii), (xiv) only), `riehl:2.1:example6` (clauses (ii), (iii) only), `riehl:2.2:exvi`, `riehl:2.2:exvii` (part (i) only), `riehl:2.3:exi` (clauses (ii), (iii) only), `riehl:2.4:exv`.

## Background

Several of the standard set-valued functors on spaces are representable: the underlying-set functor by the one-point space, the open-subset functor and the closed-subset functor both by the Sierpiński space (whence they are naturally isomorphic, by complementation), and the path functor by the unit interval — so self-homeomorphisms of the interval are exactly the natural automorphisms of the path functor, the reparameterizations.

- nLab: <https://ncatlab.org/nlab/show/Sierpinski+space>, <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/interval+object>

## Current state in the library

There is no point-set topology in the library at all, so none of these clauses has an ambient category.

- `rg -i 'topological space|homeomorph|continuous map|open set|unit interval|Sierpinski'` over `*.v` returns nothing topological: every "continuous" hit is the limit-preservation sense (`Adjunction/Continuity.v:24`, `Structure/Limit/Preservation.v:15`), and the only `Top` tokens are the `Shape` constructor at `Instance/Shapes.v:135` and `Solver/Expr.v:74`. `Top` is named only in bibliographic prose (`Structure/Complete.v:55`, `Structure/Group.v:46`).
- Consequently there is no opens functor, no closeds functor, no Sierpiński space, no path functor, and nothing about reparameterizations; and there is no computation of `End(U)` or `End(Id)` for any functor in the tree (`rg 'Id ⟹|⟹ Id'` returns only adjunction units and counits; the in-tree "centre" notions in `Binoidal/Central.v`, `Premonoidal/Centre.v` and `Monoidal/Drinfeld.v` are premonoidal and Drinfeld centres, unrelated to `End(Id)`).
- Phase D examined and rejected the one tempting near-miss: `Structure/SubobjectClassifier.v`'s Ω classifies **subobjects in a topos**, whereas the Sierpiński space classifies **opens in Top**; the two are different classification theorems and the former is not evidence for the latter.
- These items are ABSENT rather than out of scope: a category of spaces is perfectly formalizable in this setoid setting (the library already carries `Sets`, `FinSet`, `CMon`, `Poset`, `Proset`, `Rel`); it simply has no point-set layer.

## Work to be done

Suggested module: `Instance/Top/Representables.v` (new), over the `Top` of #259 and the Sierpiński space of #888.

1. Prove `U : Top ⟶ Sets` is represented by the one-point space, with universal element its point (Example 2.1.5(ii)).
2. Define the opens functor `O : Top^op ⟶ Sets` and the closeds functor `C : Top^op ⟶ Sets`, and prove each represented by the Sierpiński space (Example 2.1.6(ii)–(iii)): a continuous map into it corresponds to the preimage of the open point, respectively of the closed point. Derive `O ≅ C` as a natural isomorphism and identify it with complementation.
3. Exercise 2.3.i clauses (ii)–(iii): name the universal elements of those two representations — the open point's own open set, and the closed point's own closed set — and prove they are universal.
4. Exercise 2.4.v: state and prove in what sense the Sierpiński space is the universal space equipped with an open subset, i.e. that the pair (Sierpiński, its open point) is terminal in the category of elements of `O`. Route it through the universal-element criterion rather than re-proving the universal property by hand.
5. Define the path functor `Path : Top ⟶ Sets` and prove it represented by the unit interval; on based spaces, the loop functor represented by the based circle (Example 2.1.5(xiv)). Constructing a usable unit interval is the real cost here — state in the header which real-number/interval development is used and why.
6. Exercise 2.2.vi: conclude through the Yoneda embedding that natural automorphisms of `Path` correspond exactly to self-homeomorphisms of the interval, which is what "reparameterization" means.
7. Exercise 2.2.vii part (i): compute `End(U : Top ⟶ Sets)` by Yoneda (it is the underlying set of the one-point space, hence trivial), refine to `End(Id[Top])`, and settle the question the exercise poses — whether there is a natural family of continuous self-maps of every space, not all identities — with a proof either way.
8. Record explicitly in the header that Example 2.1.6 clauses (vi) and (vii) — singular cohomology represented by Eilenberg–MacLane spaces, and classifying spaces for principal bundles — are **out of reach** for this library (no CW complexes, no cohomology, no bundles) and are deliberately not part of this issue.

In-tree donors: the `Top` construction of #259, the Sierpiński space of #888, `Functor/Hom/Yoneda.v:231/253`, `Functor/Representable.v:46`, `Structure/UniversalProperty.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.5 clauses (ii), (xiv) (printed p. 56), Example 2.1.6 clauses (ii), (iii) (printed p. 57), Exercises 2.2.vi and 2.2.vii(i) (printed p. 66), Exercise 2.3.i clauses (ii), (iii) (printed p. 71) and Exercise 2.4.v (printed p. 78); setoid `≈` discipline — never `=` on morphisms
- [ ] `U`, `O`, `C` and `Path` are defined with proved functor laws, and each representation is a **natural** isomorphism with a named universal element
- [ ] `O ≅ C` is proved and identified with complementation
- [ ] The Sierpiński space is proved terminal in the category of elements of `O`, via the universal-element criterion
- [ ] The reparameterization correspondence is derived from the Yoneda embedding
- [ ] `End(U : Top ⟶ Sets)` and `End(Id[Top])` are computed, and Exercise 2.2.vii(i)'s question is answered with a proof
- [ ] The header states which interval construction is used, and records that Example 2.1.6 clauses (vi)–(vii) are out of scope for this library
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for each representation and for the reparameterization theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Top/Representables.v
make && make todo
```
```coq
Print Assumptions opens_represented_by_sierpinski.
Print Assumptions path_represented_by_interval.
Print Assumptions reparameterizations_are_self_homeomorphisms.
```
Reviewer checklist: the opens/closeds representations are natural isomorphisms of presheaves; the Sierpiński universal property is obtained from the universal-element criterion rather than re-proved; statement matches Riehl Example 2.1.6 (printed p. 57) and Exercise 2.2.vi (printed p. 66).

## Dependencies

- Depends on: #259 (Top, the category of topological spaces)
- Depends on: #888 (the Sierpiński space, its opens and its sheaves)
- Depends on: #345 (the category of elements — Exercise 2.4.v is a terminal-object statement there)

<!-- catalog: {"ids":["riehl:2.1:example5","riehl:2.1:example6","riehl:2.2:exvi","riehl:2.2:exvii","riehl:2.3:exi","riehl:2.4:exv"],"deps":["#259","#888","#345"]} -->

---8<---

```yaml
title: "Riehl 2.1/2.2/2.4: Representable functors on Vect_k — the dual-space functor and natural endomorphisms of the underlying-set and identity functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example6, riehl:2.2:exvii, riehl:2.4:example12]
deps_item_ids: [riehl:2.4:example6]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1, Example 2.1.6 clause (v), printed p. 57 (PDF pp. 77–78); §2.2 Exercise 2.2.vii part (ii), printed p. 66 (PDF p. 86); §2.4 Example 2.4.12 clauses (ii) and (v), printed pp. 75–77 (PDF pp. 95–97).
- Items: `riehl:2.1:example6` (clause (v) only), `riehl:2.2:exvii` (part (ii) only), `riehl:2.4:example12` (clauses (ii) and (v) only).

## Background

The dual-space functor on vector spaces is the contravariant functor represented by the ground field, so a functional on V is exactly a linear map V → k; its category of elements is the slice over k, in which the identity of k is terminal, and Yoneda then computes all natural endomorphisms of the underlying-set and identity functors on Vect_k.

- nLab: <https://ncatlab.org/nlab/show/dual+vector+space>, <https://ncatlab.org/nlab/show/representable+functor>, <https://ncatlab.org/nlab/show/over+category>

## Current state in the library

There is no category of vector spaces, so no clause is statable.

- `rg -i 'Vect'` returns 69 hits, every one either Coq's `Vector.t` (`Theory/Sheaf.v`, `Instance/Shapes.v`; note `Instance/Shapes.v:404`'s `Vectors (a : Type)` is the length-indexed-vector category with `obj := nat`, not linear algebra) or prose about vector spaces. `rg -i 'vector space|linear map|k-vector'` returns header prose only. There is no ground field, no dual space, no linear map.
- No natural-endomorphism computation exists for any functor: `rg 'Id ⟹|⟹ Id'` returns only adjunction units and counits, and the in-tree "centre" notions are premonoidal and Drinfeld centres, unrelated to `End(Id)`.
- Example 2.4.12 clause (ii) — that (k, 1) is initial in the category of elements of the underlying-set functor, but **not uniquely so**, since every (k, c) with c a nonzero scalar and more generally every one-dimensional space with a nonzero vector is initial — has no subject either; and clause (v)'s identification of the category of elements of the dual-space functor with the slice `Vect_k/k` needs both the elements construction (#345) and the slice-as-elements identification of Riehl Example 2.4.6.

## Work to be done

Suggested module: `Instance/Vect/Representables.v` (new), over whatever `Vect_k` the free-vector-space issue introduces.

1. Define the dual-space functor `(−)^* : Vect_k^op ⟶ Sets` (functionals as a setoid) and prove it represented by k, with universal element the identity functional — Example 2.1.6(v). The representation must be a natural isomorphism of presheaves.
2. Example 2.4.12 clause (ii): instantiate the category of elements at `U : Vect_k ⟶ Sets` and prove (k, 1) initial; then prove the non-uniqueness Riehl stresses — (k, c) is initial for every nonzero scalar c, and more generally (V, v) is initial for every one-dimensional V and nonzero v — so "the" initial object is only determined up to isomorphism.
3. Example 2.4.12 clause (v): prove the category of elements of `(−)^*` is isomorphic to the slice `Vect_k/k` over k, and that `id_k` is terminal there (as is any nonzero scalar multiple), giving the universal dual vector. Route the identification through the general slice-as-elements statement rather than re-proving it.
4. Exercise 2.2.vii part (ii): compute `End(U : Vect_k ⟶ Sets)` by Yoneda and refine to `End(Id[Vect_k])` (scalar multiplications), then answer the exercise's question — whether there is a natural family of linear self-maps not all identities — with a proof.
5. Record in the header that the ground field is a parameter and which in-tree field/ring layer supplies it.

In-tree donors: the `Vect_k` layer of #305, `Functor/Hom/Yoneda.v:231/253`, `Functor/Representable.v:46`, `Construction/Slice.v:123`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.6(v) (printed p. 57), Exercise 2.2.vii(ii) (printed p. 66) and Example 2.4.12 clauses (ii), (v) (printed pp. 75–77); setoid `≈` discipline — never `=` on morphisms
- [ ] The dual-space functor is defined and proved represented by k, as a natural isomorphism with a named universal element
- [ ] (k, 1) is proved initial in the category of elements of `U`, **and** the non-uniqueness clause is proved (every one-dimensional space with a nonzero vector)
- [ ] The category of elements of `(−)^*` is proved isomorphic to `Vect_k/k`, with `id_k` terminal
- [ ] `End(U)` and `End(Id[Vect_k])` are computed by Yoneda and Exercise 2.2.vii(ii)'s question answered with a proof
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the representation and both category-of-elements results
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Vect/Representables.v
make && make todo
```
```coq
Print Assumptions dual_represented_by_field.
Print Assumptions elements_dual_is_slice.
```
Reviewer checklist: the non-uniqueness clause of Example 2.4.12(ii) is proved, not remarked; the slice identification is derived from the general statement; statement matches Riehl Example 2.4.12 (printed pp. 75–77).

## Dependencies

- Depends on: #305 (the free vector space on a set as a universal arrow — supplies `Vect_k`)
- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: `riehl:2.4:example6` (slice categories as categories of elements of represented functors)

<!-- catalog: {"ids":["riehl:2.1:example6","riehl:2.2:exvii","riehl:2.4:example12"],"deps":["#305","#345","riehl:2.4:example6"]} -->

---8<---

```yaml
title: "Riehl 2.3/2.4: Unit, associativity and commutativity of the tensor product from its universal property"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.3:prop10, riehl:2.3:remark12, riehl:2.3:exii, riehl:2.4:example12]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.3 ("Universal properties and universal elements"), Proposition 2.3.10 and Remark 2.3.12, printed p. 70 (PDF pp. 90–91); Exercise 2.3.ii, printed p. 71 (PDF p. 91); §2.4 Example 2.4.12 clause (iii), printed pp. 75–77 (PDF pp. 95–97).
- Items: `riehl:2.3:prop10`, `riehl:2.3:remark12`, `riehl:2.3:exii`, `riehl:2.4:example12` (clause (iii) only).

## Background

Once the tensor product is *defined* by representing the bilinear-maps functor, its whole coherence structure is forced: the swap of the bilinear-maps functors gives commutativity, the representing objects then correspond by uniqueness of representations, and the Yoneda lemma even names the isomorphism explicitly as the unique linear map with w ⊗ v ↦ v ⊗ w. Unit and associativity come out the same way.

- nLab: <https://ncatlab.org/nlab/show/tensor+product>, <https://ncatlab.org/nlab/show/universal+element>

## Current state in the library

Absent, and deliberately so: the near-misses in the tree are structurally different statements and Phase D confirmed that declining them is the right call.

- `rg -i 'bilinear'` returns 7 hits, all header prose (`Structure/Additive.v:30`, `Theory/Algebra/Frobenius.v:56`, `Theory/Displayed.v:49`, `Construction/Enriched.v:28/67`, `Construction/Indexed.v:121`, `Structure/Preadditive.v:16`). There is no `Bilin` functor and no category of vector spaces or modules, so neither side of the isomorphism is expressible.
- The declined near-misses, verified: `Structure/Monoidal.v` posits `unit_left`/`unit_right`/`tensor_assoc` as **class fields**, i.e. they are assumed rather than derived from any universal property; `Structure/Cartesian.v:479` `prod_comm` (and `:451/:465/:485` `prod_one_l`/`prod_one_r`/`prod_assoc`) are genuinely derived, but from the universal property of the **categorical product**, not from a representation of bilinear maps. Riehl's point is precisely that these laws follow from the *representation*, so neither substitutes.
- The general technique the remark applies — evaluate a natural isomorphism at the identity to compute it explicitly — does exist (`Structure/UniversalProperty.v:54` `preyoneda`, and the `to` direction of `Functor/Hom/Yoneda.v:133`); it is simply never applied to a tensor product.

## Work to be done

Suggested module: `Instance/Vect/Tensor/Laws.v` (new), a satellite of the tensor-product construction of #306.

1. Over #306's `Bilin(V, W; −)` and its representing object `V ⊗ W` with universal bilinear map, prove Proposition 2.3.10: the swap `f ↦ f̂`, `f̂(w, v) := f(v, w)`, is a natural isomorphism `Bilin(V, W; −) ≅ Bilin(W, V; −)`, hence `V ⊗ W ≅ W ⊗ V` by uniqueness of representing objects. The proof must go through the representable route (essential uniqueness of representations), not by constructing an inverse pair by hand — that is the content of the proposition.
2. Remark 2.3.12: compute the isomorphism explicitly by chasing the identity through the composite, and prove it is the unique linear map with `w ⊗ v ↦ v ⊗ w`. Use the evaluate-at-the-identity lemma (`Structure/UniversalProperty.v:54` `preyoneda`) rather than an ad-hoc calculation.
3. Exercise 2.3.ii: prove `k ⊗_k V ≅ V` and `U ⊗_k (V ⊗_k W) ≅ (U ⊗_k V) ⊗_k W`, again **only** from the defining universal property (the associativity step goes through trilinear maps, or through iterated representations — say in the header which route was taken).
4. Example 2.4.12 clause (iii): instantiate the category of elements at `Bilin(V, W; −)` and prove the universal bilinear map is its initial object, exhibiting Riehl's Example 2.3.8 as an initiality statement.
5. Optional but worth stating: assemble the three isomorphisms into a monoidal structure on the module category, and note in the header the contrast with `Structure/Monoidal.v`, where those isomorphisms are class fields.

In-tree donors: the tensor product of #306, `Structure/UniversalProperty.v:54/175`, `Functor/Hom/Yoneda.v:133`, the elements construction of #345, `Structure/Monoidal.v` (for the comparison note).

## Definition of Done

- [ ] Statement fidelity to Riehl Proposition 2.3.10, Remark 2.3.12 (printed p. 70), Exercise 2.3.ii (printed p. 71) and Example 2.4.12(iii) (printed pp. 75–77); setoid `≈` discipline — never `=` on morphisms
- [ ] Commutativity is derived from the natural isomorphism of the bilinear-maps functors plus essential uniqueness of representations, **not** by an ad-hoc inverse pair
- [ ] The explicit commutativity isomorphism is computed by evaluating at the identity, and its uniqueness characterization `w ⊗ v ↦ v ⊗ w` proved
- [ ] Unit and associativity are proved from the universal property alone
- [ ] The universal bilinear map is proved initial in the category of elements of `Bilin(V, W; −)`
- [ ] The header contrasts these derived laws with `Structure/Monoidal.v`'s assumed class fields
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the three structural isomorphisms and the initiality result
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Vect/Tensor/Laws.v
make && make todo
```
```coq
Print Assumptions tensor_comm.
Print Assumptions tensor_comm_explicit.
Print Assumptions tensor_assoc_from_ump.
```
Reviewer checklist: each law is derived from the representation (a reviewer should be able to see the universal property being used, not a hand-built inverse); statement matches Riehl Proposition 2.3.10 (printed p. 70) and Exercise 2.3.ii (printed p. 71).

## Dependencies

- Depends on: #306 (the tensor product as a universal element of the bilinear-maps functor)
- Depends on: #345 (the category of elements of a set-valued functor)

<!-- catalog: {"ids":["riehl:2.3:prop10","riehl:2.3:remark12","riehl:2.3:exii","riehl:2.4:example12"],"deps":["#306","#345"]} -->


---8<---

```yaml
title: "Riehl 2.2/2.3/2.4: Natural endomorphisms of the power-set functor, its category of elements, and the non-uniqueness of universal elements"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:2.2:exv, riehl:2.3:exiv, riehl:2.4:example12]
deps_item_ids: [riehl:2.4:prop8]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.2 ("The Yoneda lemma"), Exercise 2.2.v, printed p. 66 (PDF p. 86); §2.3 Exercise 2.3.iv, printed p. 71 (PDF p. 91); §2.4 Example 2.4.12 clause (i), printed pp. 75–77 (PDF pp. 95–97).
- Items: `riehl:2.2:exv`, `riehl:2.3:exiv`, `riehl:2.4:example12` (clause (i) only).

## Background

Because the contravariant power-set functor is represented by the two-element set of truth values, Yoneda says its natural endomorphisms are exactly the four self-maps of that set; the same representation makes the pair (Ω, {⊤}) a terminal object of the functor's category of elements — but not the *only* one, which is Riehl's illustration that universal elements are unique only up to isomorphism.

- nLab: <https://ncatlab.org/nlab/show/power+set>, <https://ncatlab.org/nlab/show/subobject+classifier>, <https://ncatlab.org/nlab/show/universal+element>

## Current state in the library

The representation itself is filed elsewhere (see Dependencies); none of the three deliverables here has any in-tree assertion.

- `rg -i 'natural endomorphism'` returns 0 hits: nothing in the tree computes `End(F)` for any functor, so the bijection `Nat(P, P) ≅ Set(2, 2)` and the description of its four elements have no counterpart.
- The nearest concrete truth object is real and should be the starting point rather than dismissed: `Instance/FinSet/Classifier.v:353` is `FinSet_Classifier : @SubobjectClassifier FinSet FinSet_Terminal` with `Ω := 2%nat` and `truth := fun _ => fin_true`, assembled into `FinSet_Topos` (`Instance/FinSet/Topos.v:38`), so subsets of a finite set genuinely do correspond to maps into a two-element truth object. Phase D flagged that the Phase-C framing ("no Ω anywhere in a Sets-like category") understates what exists.
- What is *not* in tree is any naturality: `Structure/SubobjectClassifier.v:187` `classifier_classifies (x : C) : @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}` is per-object; enumerating every top-level declaration of that file (lines 44, 64, 72, 82, 108, 143, 159, 174, 187) shows there is **no** lemma `char (sub_reindex f s) ≈ char s ∘ f`, so `Sub ≅ [Hom ─, Ω]` is never stated even though `Sub : C^op ⟶ Sets` exists at `Theory/Subobject/Functor.v:180`. That naturality upgrade is #721's obligation and is a prerequisite here.
- On multiplicity of universal elements: `rg -i 'universal element'` returns 6 hits (`Functor/Representable.v`, `Structure/UniversalProperty.v`, `Structure/UniversalProperty/Universal/Arrow.v`), every one about the element↔representation correspondence; nothing discusses two distinct universal elements for the same functor.

## Work to be done

Suggested module: `Instance/Sets/Powerset/Yoneda.v` (new), a satellite of the power-set functor of #704.

1. Exercise 2.2.v: over #704's `P : Sets^op ⟶ Sets` and the representation `P ≅ [Hom ─, Ω]` supplied by #311/#721, prove `Nat(P, P) ≅ Sets(Ω, Ω)` by the Yoneda embedding, and **describe each of the four transformations explicitly**: identity, complementation, the constant-empty and the constant-total families. Each description must be a proved equation on components, not prose.
2. Second half of Exercise 2.2.v: determine which of the four induce natural endomorphisms of the **covariant** power-set functor (#227) and prove both the positive and the negative cases; complementation is not natural for direct images, and that failure should be a theorem with a witness, not an assertion.
3. Example 2.4.12 clause (i): instantiate the category of elements at `P` and prove that ({⊤} ⊆ Ω) is a terminal object, using the universal-element criterion rather than a bare terminality argument. Then prove Riehl's non-uniqueness point: ({⊥} ⊆ Ω) is an isomorphic terminal object, and so is any singleton subset of any two-element set.
4. Exercise 2.3.iv: state the general fact that a functor may admit several distinct universal elements, and give the two instances Riehl names — the alternate universal elements for `P` (item 3 above) and, once the Grp/Rng representability issue lands, for the underlying-set functor of rings. Prove the general statement in the form "the universal elements of F are exactly the objects of a contractible groupoid" only if that issue is already available; otherwise state and prove the two instances and cross-reference it.
5. Use `Instance/FinSet/Classifier.v:353` as the computable sanity check: on finite sets the four transformations should compute, mirroring the `eq_refl`-level examples of `Instance/FinSet/Topos.v`.

In-tree donors: `Structure/SubobjectClassifier.v:187`, `Theory/Subobject/Functor.v:180`, `Instance/FinSet/Classifier.v:353`, `Instance/FinSet/Topos.v:38`, `Functor/Hom/Yoneda.v:231`, plus the power-set functors of #704 and #227.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 2.2.v (printed p. 66), Exercise 2.3.iv (printed p. 71) and Example 2.4.12(i) (printed pp. 75–77); setoid `≈` discipline — never `=` on morphisms
- [ ] `Nat(P, P) ≅ Sets(Ω, Ω)` is proved via the Yoneda embedding, and all four transformations are described by proved component equations
- [ ] The covariant-lifting question is answered with proofs in both directions, including a witness for the failure case
- [ ] ({⊤} ⊆ Ω) is proved terminal in the category of elements of `P`, and the non-uniqueness clause is proved
- [ ] Exercise 2.3.iv's general point (universal elements need not be unique) is stated, with at least the power-set instance proved
- [ ] The finite-set instance computes, mirroring `Instance/FinSet/Topos.v`'s `eq_refl` examples
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the endomorphism bijection and the terminality result
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Sets/Powerset/Yoneda.v
make && make todo
```
```coq
Print Assumptions powerset_endomorphisms.
Print Assumptions powerset_elements_terminal.
```
Reviewer checklist: the four natural transformations are identified by proved equations; the covariant-lifting failure is witnessed; statement matches Riehl Exercise 2.2.v (printed p. 66).

## Dependencies

- Depends on: #704 (the contravariant powerset functor on Sets)
- Depends on: #227 (the covariant power-set functor)
- Depends on: #311 (a universal element for the contravariant power-set functor)
- Depends on: #721 (the subobject functor is representable — the naturality upgrade this issue's Yoneda argument consumes)
- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: `riehl:2.4:prop8` (universal elements are exactly the initial/terminal objects of the category of elements)

<!-- catalog: {"ids":["riehl:2.2:exv","riehl:2.3:exiv","riehl:2.4:example12"],"deps":["#704","#227","#311","#721","#345","riehl:2.4:prop8"]} -->

---8<---

```yaml
title: "Riehl 2.2: The Yoneda lemma and embedding computed directly at the ordinal category omega"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.2:example1, riehl:2.2:exiii]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.2 ("The Yoneda lemma"), Example 2.2.1, printed p. 60 (PDF p. 80); Exercise 2.2.iii, printed p. 66 (PDF p. 86).
- Items: `riehl:2.2:example1`, `riehl:2.2:exiii`.

## Background

Riehl motivates the Yoneda lemma by computing it by hand at the ordinal category ω, where a diagram is a sequence of sets and transition maps and the representable ω(k, −) is empty below k and a point at and above k; a natural transformation out of it is then visibly nothing but an element of the k-th set. The exercise asks for the Yoneda embedding at ω to be proved full and faithful *directly*, without invoking the general lemma.

- nLab: <https://ncatlab.org/nlab/show/Yoneda+lemma>, <https://ncatlab.org/nlab/show/thin+category>

## Current state in the library

The general theorem and the shape both exist; the instantiation and the concrete computation do not.

- `Functor/Hom/Yoneda.v:182` `Covariant_Yoneda_Lemma (C : Category) (F : C ⟶ Sets) : ∀ A : C, Copresheaves [Hom A,─] F ≅ F A` and `:231` `Yoneda_Embedding` hold for an arbitrary category, so instantiating at ω gives the exercise's *conclusion* for free — which is exactly the appeal the exercise forbids.
- `Instance/Omega.v:72` defines `Omega` with `hom := le_t` and `homset := Morphism_equality`. But `rg '\bOmega\b' -g '*.v'` outside that file returns **only** `Construction/Chain.v`, `Construction/FAlg.v`, `Theory/Adamek.v` and `Theory/Adamek/Corollaries.v` — all the initial-algebra chain. ω is never fed to a hom-functor, a representable or a presheaf.
- The concrete computation is missing: there is no lemma that `le_t j k` is inhabited exactly when j ≤ k and is a subsingleton, i.e. that ω is thin, so "the ω-indexed family of sets" the example writes down does not exist in tree. Thinness appears only as header prose (`Instance/Omega.v:6`). Phase D corrected one detail worth carrying: `Instance/Omega.v` *does* carry `le_t` lemmas (`le_t_trans_id_l`/`le_t_trans_id_r` at `:51`/`:55`, `le_t_trans_assoc` at `:63`) — the true statement is that none of them concerns proof-uniqueness.

## Work to be done

Suggested module: `Instance/Omega/Yoneda.v` (new).

1. Prove ω is thin: `le_t j k` is a subsingleton (any two proofs are equal, or `≈` under `Morphism_equality`), and it is inhabited exactly when j ≤ k. This is the missing computation and the prerequisite for everything else; it also gives `Instance/Omega.v` the proof-uniqueness lemma its existing `le_t` lemmas do not cover.
2. Compute the representable: prove `[Hom k,─] : Omega ⟶ Sets` is (isomorphic to) the functor sending n to the empty setoid for n < k and to the singleton for n ≥ k, with all transition maps forced.
3. Example 2.2.1: prove directly that for any `F : Omega ⟶ Sets`, evaluation at the identity is a bijection `Copresheaves [Hom k,─] F ≅ F k`, by the argument the book gives (naturality forces `α_{n+1}` to be the transition image of `α_n`, so `α` is determined by `α_k(id)`, and every element of `F k` arises). State it as its own theorem, then prove it agrees with the instantiation of `Covariant_Yoneda_Lemma` at ω — the agreement is what makes the warm-up honest.
4. Exercise 2.2.iii: describe the Yoneda embedding of ω into presheaves on ω concretely (the ω^op-indexed family of representables and the transition transformations) and prove it **full and faithful directly**, without invoking `Yoneda_Embedding`; then record the comparison with the general instance.
5. State in the header that the direct proofs are deliberately redundant with the general theorem, and why (they are the book's pedagogical point and a check on the general statement).

In-tree donors: `Instance/Omega.v:72` (and `:85` `omega_step`), `Functor/Hom.v`, `Functor/Hom/Yoneda.v:182/231`, `Theory/Sheaf.v:127/133` (`Presheaves`/`Copresheaves`), `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.2.1 (printed p. 60) and Exercise 2.2.iii (printed p. 66); setoid `≈` discipline — never `=` on morphisms
- [ ] Thinness/proof-uniqueness of `le_t` is proved, closing the gap that `Instance/Omega.v`'s existing `le_t` lemmas leave open
- [ ] The representable `[Hom k,─]` on ω is computed explicitly (empty below k, a point at and above k)
- [ ] The Yoneda bijection at ω is proved **directly**, and then shown to agree with the instantiation of the general lemma
- [ ] Full faithfulness of the Yoneda embedding at ω is proved without invoking `Yoneda_Embedding`, as the exercise requires, with the comparison recorded
- [ ] The header explains why the direct proofs are kept alongside the general theorem
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the thinness lemma, the direct bijection and the direct full faithfulness
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Omega/Yoneda.v
make && make todo
```
```coq
Print Assumptions omega_thin.
Print Assumptions omega_yoneda_direct.
Print Assumptions omega_yoneda_embedding_direct.
```
Reviewer checklist: the direct proofs genuinely do not route through `Functor/Hom/Yoneda.v`'s general instances (grep the proof scripts); the agreement lemmas are stated; statement matches Riehl Example 2.2.1 (printed p. 60) and Exercise 2.2.iii (printed p. 66).

## Dependencies

None.

<!-- catalog: {"ids":["riehl:2.2:example1","riehl:2.2:exiii"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 2.2: The Yoneda lemma for a group — equivariant maps out of the regular representation"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.2:example2, riehl:2.2:prop3]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.2 ("The Yoneda lemma"), Example 2.2.2, printed p. 60 (PDF p. 80), and Proposition 2.2.3, printed p. 61 (PDF p. 81).
- Items: `riehl:2.2:example2`, `riehl:2.2:prop3`.

## Background

A group regarded as a one-object category has exactly one covariant and one contravariant representable functor — the underlying set of the group with its left, respectively right, translation action. Naturality of a transformation out of the covariant one is exactly equivariance, so equivariant maps G → X correspond bijectively to elements of X, evaluation at the identity; freeness of the left regular action is what makes every element admissible.

- nLab: <https://ncatlab.org/nlab/show/action+groupoid>, <https://ncatlab.org/nlab/show/Yoneda+lemma>
- Wikipedia: <https://en.wikipedia.org/wiki/Group_action>

## Current state in the library

Nothing in the tree can state the example: there is no delooping, no G-sets, and no notion of equivariance outside multicategory symmetry.

- `rg -i 'deloop|one-object|one object|single object|BG'` finds only `Theory/Bicategory/OneObject.v` (a **monoidal category** as a one-object *bicategory*, one level up) and `Theory/Multicategory/Operad.v` (an operad as a one-object multicategory), plus header prose. Nothing turns a group or monoid into a one-object category.
- `rg -i 'G-set|group action|left regular|stabilizer|torsor'` yields nothing: the five apparent `G-set` hits are substring matches inside "underlyin(g-set) functor" in `Structure/Closed.v` and `Theory/Lawvere/Sets.v`, and every `equivariant` hit is the symmetric-group equivariance of multicategory composition (`Theory/Multicategory*.v`).
- `Structure/Group.v:109` declares only `Class GroupObject (grp : C)` — a group object internal to a cartesian monoidal category, with inverse and the two antipode laws — which is neither a delooping nor an action.
- `Construction/Cayley.v` is the nearest relative and is correctly not evidence: it consumes `Covariant_Yoneda_Embedding` (lines 209, 213, 216) but states nothing about groups, actions, equivariance, or evaluation at a group identity.

## Work to be done

Suggested module: `Instance/Grp/Yoneda.v` (new), over the delooping of #220 and the G-set layer of #464.

1. Over `B G` (the one-object category of #220) and G-sets presented as functors `B G ⟶ Sets` (#464 gives the equivalent monad-algebra presentation — say in the header which presentation is primary and prove the bridge if both are used), identify the unique covariant representable `[Hom ∗,─]` with G acting on itself by left translation, and the unique contravariant one with the right translation action. Both identifications are theorems, not definitions.
2. Prove that a natural transformation from the covariant representable to `X : B G ⟶ Sets` is exactly a G-equivariant map, i.e. that the naturality condition unfolds to equivariance — this is Example 2.2.2's content and needs to be an `iff` between the two data, not a remark.
3. Proposition 2.2.3: prove the bijection between G-equivariant maps `G ⟶ X` and elements of X, given by evaluation at the identity, **as an instance of** `Functor/Hom/Yoneda.v:182`'s `Covariant_Yoneda_Lemma` at `C := B G`. Deriving it rather than re-proving it is the point of the proposition.
4. Prove the freeness observation the book's footnote isolates: the left action of G on itself has trivial stabilizers, which is why every element of X can be prescribed as the image of the identity without contradiction.

In-tree donors: the delooping of #220, the G-set layer of #464, `Functor/Hom/Yoneda.v:182`, `Functor/Hom.v:60`, `Structure/Group.v:109`, `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.2.2 (printed p. 60) and Proposition 2.2.3 (printed p. 61); setoid `≈` discipline — never `=` on morphisms
- [ ] The two representables on `B G` are identified with the left and right translation actions, as proved theorems
- [ ] Naturality is proved equivalent to equivariance, in both directions
- [ ] Proposition 2.2.3 is **derived** from `Covariant_Yoneda_Lemma` at `B G`, not re-proved
- [ ] Freeness of the left regular action is proved and its role in the argument recorded
- [ ] The header states which presentation of G-sets is primary and, if two are used, the bridge is proved
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the equivariance equivalence and the classification bijection
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Grp/Yoneda.v
make && make todo
```
```coq
Print Assumptions naturality_is_equivariance.
Print Assumptions equivariant_maps_are_elements.
```
Reviewer checklist: Proposition 2.2.3 is obtained by instantiating the general Yoneda lemma (grep the proof); statement matches Riehl Example 2.2.2 (printed p. 60) and Proposition 2.2.3 (printed p. 61).

## Dependencies

- Depends on: #220 (delooping monoids and groups into one-object categories)
- Depends on: #464 (the group-action monad and G-sets)

<!-- catalog: {"ids":["riehl:2.2:example2","riehl:2.2:prop3"],"deps":["#220","#464"]} -->

---8<---

```yaml
title: "Riehl 2.3/2.4: Torsors — representable G-sets are the free transitive actions, and the category of elements is the action groupoid"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.3:example7, riehl:2.4:example10]
deps_item_ids: [riehl:2.4:prop9]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.3 ("Universal properties and universal elements"), Example 2.3.7, printed p. 68 (PDF pp. 88–89); §2.4 Example 2.4.10, printed p. 75 (PDF p. 95).
- Items: `riehl:2.3:example7`, `riehl:2.4:example10`.

## Background

A G-set is representable exactly when it is isomorphic to G with its left translation action; the data of such an isomorphism is a single universal element, so a representable G-set is "a group that has forgotten its identity" — a torsor. The converse is proved through the category of elements: it is the action groupoid, and representability is exactly contractibility of that groupoid, i.e. freeness plus transitivity plus non-emptiness.

- nLab: <https://ncatlab.org/nlab/show/torsor>, <https://ncatlab.org/nlab/show/action+groupoid>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

Nothing: neither the statement's subject nor any of its ingredients exists.

- `rg -i 'torsor'`, `rg -i 'principal homogeneous'`, `rg -i 'free.*transitive'`, `rg -i 'orbit'`, `rg -i 'stabilizer'` (over `*.v`) all return nothing relevant — the single `stabilizer` hit is a bibliography line in `Instance/ZX.v:137` about stabilizer quantum mechanics.
- `rg -i 'action groupoid|translation groupoid'` returns 0 hits. `Construction/Groupoid.v:103` is the **core** (maximal subgroupoid) of an existing category, a different construction; `Construction/Cayley.v:114` is the Cayley/Yoneda-style embedding of an arbitrary category, not the delooping of a group; `Theory/Bicategory/OneObject.v` deloops a monoidal category into a bicategory.
- `ls Instance/` confirms there is no category of groups and no G-sets (Adj, Adjoints, AST, Cat, CMon, Comp, Cones, Coq, Discrete, Ens, Fact, FinSet, Fun, Lambda, Omega, One, Parallel, Poset, Props, Proset, Rel, Roof, Sets, Shapes, StrictCat, Two, Zero, ZX), and `Structure/Group.v` defines only an internal `GroupObject` with no action.
- There is likewise no notion of a contractible groupoid: `rg -i 'contractible'` yields only remarks that `poly_unit` is a contractible **type** (`Instance/One.v:18`, `Instance/StrictCat/Terminal.v:20/27/33`, `Theory/Multicategory/Operad.v:61`) plus prose in `Structure/Terminal.v`.

## Work to be done

Suggested module: `Instance/Grp/Torsor.v` (new), over the action groupoid of #923.

1. Define a G-torsor: a G-set that is non-empty, free (trivial stabilizers) and transitive; give the equivalent "the shear map (g, x) ↦ (g·x, x) is an isomorphism" formulation if it is cheaper to use, and prove the two agree.
2. Example 2.3.7 forward direction: a representable G-set is isomorphic (as a G-set) to G with its left action, hence non-empty, free and transitive. The data of a representation is precisely a universal element — the image of the group identity — so the isomorphism is determined by that choice.
3. Example 2.4.10: prove that the category of elements of `X : B G ⟶ Sets` is isomorphic to the action groupoid `X // G` of #923 (objects the elements of X, a morphism x ⟶ y for each g with g·x ≈ y), over `B G`.
4. Prove the converse of Example 2.3.7 the way Riehl does: by the universal-element criterion, X is representable iff its category of elements has a terminal (equivalently, since the elements category here is a groupoid, an initial) object; combined with item 3 and the empty-or-contractible-groupoid criterion of Riehl Proposition 2.4.9, X is representable iff `X // G` is a contractible groupoid, iff the action is free, transitive and X is non-empty.
5. Record the affine-space illustration in the header (n-dimensional affine space is a torsor for the additive group of the vector space; choosing an origin is choosing the universal element) — as a documented example, only if the ambient linear algebra is available; otherwise state that it is deliberately omitted.

In-tree donors: the action groupoid of #923, the delooping of #220, the G-set layer of #464, the category of elements of #345, `Construction/Groupoid.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.3.7 (printed p. 68) and Example 2.4.10 (printed p. 75); setoid `≈` discipline — never `=` on morphisms
- [ ] A torsor is defined and the two formulations (free+transitive+non-empty; shear map invertible) proved equivalent
- [ ] Representable ⇒ torsor is proved, with the universal element exhibited as the choice of "identity"
- [ ] The category of elements of a G-set is proved isomorphic to the action groupoid over `B G`
- [ ] Torsor ⇒ representable is proved **through** the universal-element criterion and the contractible-groupoid criterion, not independently
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for both directions and for the action-groupoid identification
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Grp/Torsor.v
make && make todo
```
```coq
Print Assumptions representable_gset_is_torsor.
Print Assumptions torsor_is_representable.
Print Assumptions elements_gset_is_action_groupoid.
```
Reviewer checklist: the converse direction is routed through the elements criterion (grep the proof); statement matches Riehl Example 2.3.7 (printed p. 68) and Example 2.4.10 (printed p. 75).

## Dependencies

- Depends on: #220 (delooping monoids and groups into one-object categories)
- Depends on: #464 (the group-action monad and G-sets)
- Depends on: #923 (the action groupoid and the categorified orbit-stabilizer theorem)
- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: `riehl:2.4:prop9` (the subcategory of representations is empty or a contractible groupoid)

<!-- catalog: {"ids":["riehl:2.3:example7","riehl:2.4:example10"],"deps":["#220","#464","#923","#345","riehl:2.4:prop9"]} -->

---8<---

```yaml
title: "Riehl 2.2: Row operations are left multiplication by a matrix"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.2:cor10]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.2 ("The Yoneda lemma"), Corollary 2.2.10, printed p. 65 (PDF p. 85).
- Items: `riehl:2.2:cor10`.

## Background

In the category whose objects are natural numbers and whose arrows m ⟶ n are n×m matrices over a ring, the matrices with n rows are the elements of a represented functor, and a row operation is a natural endomorphism of it; the Yoneda lemma therefore says every row operation is left multiplication by a single matrix, obtained by applying the operation to the identity matrix.

- nLab: <https://ncatlab.org/nlab/show/Yoneda+lemma>
- Wikipedia: <https://en.wikipedia.org/wiki/Elementary_matrix>

## Current state in the library

Absent; the only in-tree trace is the library's own background essay stating Riehl's corollary as motivation.

- `rg -i 'row operation|elementary matrix|left multiplication'` returns 4 hits, all comments: `Functor/Hom/Yoneda.v:88–89`, where the background essay states this very corollary in prose as motivation for `Covariant_Yoneda_Embedding`, and `Construction/Cayley.v:18,56`. A background essay is not an assertion.
- `rg -i 'matrix|matrices'` returns 21 hits, every one header or background prose (`Theory/Profunctor.v` "matrix of sets", `Structure/Semiadditive.v`, `Structure/Abelian.v`, `Structure/Bicartesian.v`, `Instance/ZX.v`, `Structure/Monoidal/CompactClosed.v`, `Theory/Equivalence.v`, `Structure/Monoidal/Traced.v`, `Structure/Monoidal/Braided.v`). There is no category whose morphisms are matrices, and no ring structure to build one over.

## Work to be done

Suggested module: `Instance/Matr/Yoneda.v` (new), a satellite of the matrix category of #221.

1. Over #221's `Matr_K` (objects natural numbers, arrows n×m matrices) and #257's rings, fix n and consider the represented functor `[Hom ─, n] : Matr_K^op ⟶ Sets`, whose value at m is the setoid of n×m matrices.
2. Define a row operation on matrices with n rows as a natural endomorphism of that functor, and prove that naturality is exactly the linearity of matrix multiplication (this is the step the corollary's proof turns on and it should be a stated lemma).
3. Prove the corollary through the Yoneda embedding (`Functor/Hom/Yoneda.v:231`): every such natural endomorphism is left multiplication by the n×n matrix obtained by applying the operation to the identity matrix, and this matrix is unique. Deriving it from `Yoneda_Embedding` rather than by a direct computation is the point.
4. Give at least one worked elementary row operation (swap two rows, scale a row, add a multiple of one row to another) as a computing instance, so the corollary has a concrete witness.
5. Update the background essay at `Functor/Hom/Yoneda.v:88–92` to point at the new theorem instead of describing it in prose.

In-tree donors: the matrix category of #221, the ring layer of #257, `Functor/Hom/Yoneda.v:231/253`, `Functor/Hom.v:60`.

## Definition of Done

- [ ] Statement fidelity to Riehl Corollary 2.2.10, printed p. 65; setoid `≈` discipline — never `=` on morphisms
- [ ] "Row operation" is defined as a natural endomorphism of the represented functor, and naturality is proved equivalent to the linearity property
- [ ] The corollary is derived from `Yoneda_Embedding`, with the representing matrix identified as the operation applied to the identity, and its uniqueness proved
- [ ] At least one elementary row operation is instantiated and computes
- [ ] `Functor/Hom/Yoneda.v:88–92`'s prose statement of this corollary is updated to cite the theorem
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for the corollary
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Matr/Yoneda.v
make && make todo
```
```coq
Print Assumptions row_operations_are_left_multiplication.
```
Reviewer checklist: the proof goes through the Yoneda embedding rather than a direct matrix computation; statement matches Riehl Corollary 2.2.10, printed p. 65.

## Dependencies

- Depends on: #221 (the matrix category Matr_K)
- Depends on: #257 (Rng, the category of rings)

<!-- catalog: {"ids":["riehl:2.2:cor10"],"deps":["#221","#257"]} -->


---8<---

```yaml
title: "Riehl 2.3: Representably isomorphic objects — isomorphism of objects is natural isomorphism of represented functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.3:def-representable-isomorphism, riehl:2.3:prop1]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.3 ("Universal properties and universal elements"), the unnumbered definition of "representably isomorphic" opening the section, and Proposition 2.3.1, both printed p. 67 (PDF p. 87).
- Items: `riehl:2.3:def-representable-isomorphism`, `riehl:2.3:prop1`.

## Background

Two objects are representably isomorphic when their represented functors are naturally isomorphic in either variance; Proposition 2.3.1 says the three kinds of data — an isomorphism x ≅ y, a natural isomorphism C(−,x) ≅ C(−,y), and a natural isomorphism C(y,−) ≅ C(x,−) — correspond, because the Yoneda embeddings preserve, reflect **and create** isomorphisms, the explicit mutually inverse pair being α_x(id_x) and (α⁻¹)_y(id_y).

- nLab: <https://ncatlab.org/nlab/show/Yoneda+embedding>, <https://ncatlab.org/nlab/show/representable+functor>

## Current state in the library

Both halves are present as general lemmas plus the instances that make them apply to the Yoneda embedding, but the composite is never taken, and the "creates" strength is absent.

- `Theory/Functor.v:355` `Lemma FullyFaithful (F : C ⟶ D) {Full F} {Faithful F} : ∀ x y, F x ≅ F y → x ≅ y`; `Functor/Hom.v:85` `Yoneda_Faithful (C : Category) : Faithful (Curried_Hom C)` and `:96` `Yoneda_Full`; `Theory/Functor.v:227` `fobj_iso (F : C ⟶ D) : Proper (Isomorphism ==> Isomorphism) (fobj[F])` gives the forward direction.
- `rg 'FullyFaithful (Curried_Hom'` returns **0 hits**: the instantiation is never taken, so no in-tree lemma states `x ≅ y ↔ [Hom ─,x] ≅ [Hom ─,y]` in either variance.
- No name or predicate exists for "representably isomorphic": `rg -i 'representably'` returns 0 hits. The notion exists only as the ad-hoc term `Isomorphism [Hom ─,x] [Hom ─,y]`, and Riehl's conjunction of the two variances is never stated together.
- The "creates isomorphisms" strength — that the reflected isomorphism *is* α_x(id_x) with inverse (α⁻¹)_y(id_y), so the three kinds of data correspond bijectively — is genuinely absent; only the one-way reflection `F x ≅ F y → x ≅ y` is available. The explicit construction does occur once, inlined and unexposed, at `Structure/UniversalProperty.v:118–121` (`two_sided_inverse (Yoneda_Embedding' C v c) (from b1 ∘ to b2)`).
- **Library defect to close while here:** `Functor/Hom/Yoneda.v:76` asserts in header prose that full faithfulness "yields that `[Hom ─,A] ≅ [Hom ─,B]` exactly when `A ≅ B`" — the library documents the corollary it does not state.

## Work to be done

Suggested module: `Functor/Hom/Yoneda/Iso.v` (new), or extend `Functor/Hom/Yoneda.v`.

1. Define the predicate `RepresentablyIsomorphic (x y : C)` as Riehl does — a natural isomorphism `[Hom ─,x] ≅ [Hom ─,y]` **and** a natural isomorphism `[Hom x,─] ≅ [Hom y,─]` — and the notion of a representable isomorphism (a natural isomorphism of either shape).
2. Prove `iso_iff_representably_iso : (x ≅ y) ↔ ([Hom ─,x] ≅ [Hom ─,y])` and the covariant twin, by instantiating `FullyFaithful` at `Curried_Hom`/`Curried_CoHom` — the composite that is currently never taken.
3. Strengthen to Riehl's "creates" form: give a bijection (an isomorphism of setoids) between the setoid of isomorphisms `x ≅ y` and the setoid of natural isomorphisms `[Hom ─,x] ≅ [Hom ─,y]`, with the forward map `fmap[Curried_Hom]` and the backward map `α ↦ α_x(id_x)`, and both round trips proved. This is what makes the proposition a statement about *data*, not merely about existence.
4. Derive that isomorphic objects are representably isomorphic in both variances directly from the embedding (`Theory/Functor.v:227` instantiated), and record that the two variances therefore agree.
5. Expose the explicit inverse pair as a reusable lemma so `Structure/UniversalProperty.v:118–121` can consume it instead of inlining the construction.
6. Fix `Functor/Hom/Yoneda.v:76` to cite the new theorem rather than assert the corollary in prose.

In-tree donors: `Functor/Hom.v:85/96/109`, `Functor/Hom/Yoneda.v:231/253`, `Theory/Functor.v:227/355`, `Theory/Equivalence/Limit.v:335` (`ff_reflects_isos`), `Structure/UniversalProperty.v:118–121`.

## Definition of Done

- [ ] Statement fidelity to Riehl's §2.3 opening definition and Proposition 2.3.1, printed p. 67; setoid `≈` discipline — never `=` on morphisms
- [ ] `RepresentablyIsomorphic` is a named predicate covering both variances
- [ ] Both biconditionals proved by instantiating `FullyFaithful` at the Yoneda embeddings
- [ ] The **creates**-isomorphisms form is proved: a bijection of setoids between isomorphisms and natural isomorphisms, with the explicit inverse pair and both round trips
- [ ] The explicit inverse pair is exported and `Structure/UniversalProperty.v:118–121` consumes it instead of inlining it
- [ ] `Functor/Hom/Yoneda.v:76`'s prose claim is replaced by a citation of the new theorem
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each biconditional and for the data-level bijection
- [ ] New/edited files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Functor/Hom/Yoneda/Iso.v
coqc -R . Category Structure/UniversalProperty.v
make && make todo
```
```coq
Print Assumptions iso_iff_representably_iso.
Print Assumptions yoneda_creates_isos.
```
Reviewer checklist: the data-level bijection (not merely the biconditional) is proved, since that is what Riehl's "creates isomorphisms" means; statement matches Riehl Proposition 2.3.1, printed p. 67.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:2.3:def-representable-isomorphism","riehl:2.3:prop1"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 2.1/2.4: Pointed objects as the category of elements of an underlying-set functor"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.1:example5, riehl:2.4:example4]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.1, Example 2.1.5 clause (xiii), printed p. 56 (PDF pp. 76–77); §2.4 Example 2.4.4, printed p. 73 (PDF p. 93).
- Items: `riehl:2.1:example5` (clause (xiii) only), `riehl:2.4:example4`.

## Background

For a concrete category with underlying-set functor U, the category of elements of U is the category of *pointed objects*: an object together with a chosen element of its underlying set, and morphisms preserving the choice. In the case of sets this is the category of pointed sets, whose own underlying-set functor is represented by the two-element based set.

- nLab: <https://ncatlab.org/nlab/show/pointed+object>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

Neither the general construction nor the concrete instance exists, and the tempting shortcut is mathematically wrong.

- `rg -i 'pointed'` finds only the endofunctor classes `Pointed`/`WellPointed` (`Instance/Fun.v:230/240`), the "well-pointed topos" phrase (`Structure/Terminal.v:66`), and prose remarks — `Construction/Slice.v:82` ("pointed sets are the coslice of Set under the one-point set") and `Instance/Coq/Par.v:34`. There is no category of pointed objects.
- **The coslice shortcut is Set-specific and must not be used as the definition.** Phase D checked this: for C = Group, the category of elements of U is groups-with-a-chosen-element, while the coslice `1/Group` is `Group` itself (the trivial group has a unique homomorphism into every group). So `C_∗ ≅ 1/C` holds for sets but not in general, and it is nowhere stated in tree.
- There is no notion of a concrete category or an underlying-set functor in general; the one concrete forgetful functor in the tree is `Instance/CMon.v:169` `CMon_Forget : CMon ⟶ Sets`, which is the pattern to imitate.

## Work to be done

Suggested module: `Construction/Pointed.v` (new).

1. Define `Pointed (U : C ⟶ Sets)` as the category of elements of U (instantiating the construction of #345), with the accessors Riehl uses: an object is a pair of an object of C and an element of its underlying set, a morphism is a morphism of C whose underlying function preserves the chosen element.
2. Prove the projection `Pointed U ⟶ C` is the elements projection, and record the notation `C_∗` for the case where U is a designated underlying-set functor.
3. Prove the Set-specific coincidence `Sets_∗ ≅[Cat] 1/Sets` (using the global-elements isomorphism of Riehl Example 2.1.5(i)) **and state in the header, with the Group counterexample, that this coincidence does not generalize** — this is the point at which a reader is most likely to over-generalize.
4. Example 2.1.5(xiii): prove the underlying-set functor of pointed sets is represented by the two-element based set, with the non-basepoint element as universal element.
5. Instantiate the general construction at `Instance/CMon.v:169`'s `CMon_Forget` to give a second, non-Set witness that the construction is usable.

In-tree donors: the elements construction of #345, `Instance/CMon.v:169`, `Construction/Slice.v:169` (`Coslice`), `Instance/Sets.v:248`, and the pointed-set category of #708.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.1.5(xiii) (printed p. 56) and Example 2.4.4 (printed p. 73); setoid `≈` discipline — never `=` on morphisms
- [ ] `Pointed U` is defined as the category of elements of U, with object/morphism accessors and the projection
- [ ] `Sets_∗ ≅[Cat] 1/Sets` is proved, **and** the header records the Group counterexample showing the coincidence is Set-specific
- [ ] The underlying-set functor of pointed sets is proved represented by the two-element based set, with its universal element named
- [ ] A second instance (over `CMon_Forget`) is provided
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for `Pointed`, the Sets coincidence and the representation
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Pointed.v
make && make todo
```
```coq
Print Assumptions Pointed.
Print Assumptions pointed_sets_is_coslice.
Print Assumptions pointed_sets_forget_represented.
```
Reviewer checklist: the coslice identification is proved only for `Sets` and the header states why it does not generalize; statement matches Riehl Example 2.4.4, printed p. 73.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #708 (the category of pointed sets)
- Related (NOT blocking): #526 also proposes to create `Construction/Pointed.v`. The two are **different constructions of the same notation**: #526 packages `C_∗` as the coslice under the terminal object, while this issue builds it as the category of elements `∫U` of an underlying-set functor. They agree over `Sets` and **not** in general — `∫U` over `Grp` has objects `(G, g ∈ G)`, whereas `1/Grp ≅ Grp` because the trivial group is a zero object. Whichever lands first owns the file and the other extends it; the header must state both constructions and the counterexample separating them, so that #526's gloss "pointed sets = coslice under the terminal" is not read as a general fact. Neither issue blocks the other, but they must not be worked in the same parallel wave.

<!-- catalog: {"ids":["riehl:2.1:example5","riehl:2.4:example4"],"deps":["#345","#708"]} -->

---8<---

```yaml
title: "Riehl 2.4: The category of elements over a discrete base — dependent sums, dependent products and sections"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.4:example5]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Example 2.4.5, printed p. 73 (PDF p. 93).
- Items: `riehl:2.4:example5`.

## Background

When the indexing category is discrete, a set-valued functor is just an indexed family of sets, its category of elements is again discrete with object set the dependent sum, and the projection has the family members as its fibres; the dependent product is then the set of sections of that projection. This is the categorical reading of dependent pairs and dependent functions.

- nLab: <https://ncatlab.org/nlab/show/dependent+sum>, <https://ncatlab.org/nlab/show/dependent+product>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

The two sides exist separately and are never connected to the elements construction or to each other.

- The dependent-product side is present in categorical form: `Structure/Limit/Product.v:105` `iprod_ump (f : A → C) (L : Limit (DiscreteCat_Functor f)) (c : C) (pi : ∀ a, c ~> f a) : ∃! u : c ~> iprod f L, ∀ a, iprod_proj f L a ∘ u ≈ pi a` — the indexed product over a `Type` index with its universal property. It is conditional on a supplied `Limit (DiscreteCat_Functor f)`, and `HasIndexedProducts` (`Structure/Limit/Product.v:128`) has **zero instances tree-wide**, so no concrete indexed product is available either.
- The dependent-sum side appears only as the object type of a displayed total category: `Construction/Displayed/Total.v:42` `Total (D : Displayed C)` has `obj := ∃ x : C, dobj x`. No discrete instance is taken, and the statement that the elements category of a discrete base is again discrete is not made.
- The fibre description has no counterpart for this case: `Construction/Grothendieck/Fiber.v:269` `fiber_grothendieck_equiv` is the analogous statement for the `IndexedCat` Grothendieck construction only.
- The characterization of the dependent product as the set of **sections** of the projection is absent entirely: `rg -i 'sections of'` returns 3 prose hits, none about this. The only in-tree `Definition`s in the neighbourhood are `Bang_Functor`/`Star_Functor` (`Construction/Slice/Pullback.v:50/68`), which are slice base-change, a different construction.

## Work to be done

Suggested module: `Construction/Elements/Discrete.v` (new).

1. Prove that for a discrete base (`Instance/Discrete.v:37`'s `DiscreteCat`, or the setoid-quotient discrete category if the strict-equality homs are an obstruction — say which in the header and why) the category of elements of `F : C ⟶ Sets` is again discrete, with object setoid the dependent sum `Σ_{c} F c`.
2. Prove the fibre description: the fibre of the projection over c is (isomorphic to) `F c`, the analogue for this case of `Construction/Grothendieck/Fiber.v:269`.
3. Define the set of **sections** of the projection and prove it isomorphic to the indexed product `Π_{c} F c` — the identification of the dependent product with dependent functions, which is the part of the example with no in-tree counterpart at all.
4. Supply the missing instance the statement needs to be non-vacuous: prove `HasIndexedProducts Sets` (or, if the universe placement forbids it at full generality, prove it at the level the library can and disclose the restriction in the header). `Structure/Limit/Product.v:128` currently has no instances, so an issue that only states a conditional would leave the example uninhabited.
5. Record in the header the relation to `Construction/Slice/Pullback.v`'s `Bang_Functor`/`Star_Functor` and to the dependent-product-as-right-adjoint reading of #730, so a reader can see which notion is which.

In-tree donors: `Structure/Limit/Product.v:105/128`, `Instance/Discrete.v:37`, `Construction/Displayed/Total.v:42`, `Construction/Grothendieck/Fiber.v:269`, `Instance/Sets.v`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.4.5, printed p. 73; setoid `≈` discipline — never `=` on morphisms
- [ ] The elements category over a discrete base is proved discrete, with the dependent sum as its object setoid
- [ ] The fibre description of the projection is proved
- [ ] The dependent product is proved isomorphic to the set of sections of the projection
- [ ] A concrete `HasIndexedProducts` instance is supplied (or the restriction disclosed in the header), so the statement is not vacuous
- [ ] The header distinguishes this dependent product from the base-change right adjoint of #730
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the discreteness result, the fibre lemma and the sections isomorphism
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Elements/Discrete.v
make && make todo
```
```coq
Print Assumptions elements_discrete.
Print Assumptions dependent_product_is_sections.
Print Assumptions Sets_HasIndexedProducts.
```
Reviewer checklist: the sections isomorphism is proved (it is the clause with no in-tree relative); the indexed-product instance is real, so `iprod_ump` is applicable; statement matches Riehl Example 2.4.5, printed p. 73.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #730 (the dependent product as the right adjoint to base change — related reading, distinguished in the header)

<!-- catalog: {"ids":["riehl:2.4:example5"],"deps":["#345","#730"]} -->

---8<---

```yaml
title: "Riehl 2.4: Slice and coslice categories as the categories of elements of represented functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.4:example6]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Example 2.4.6, printed p. 73 (PDF p. 93).
- Items: `riehl:2.4:example6`.

## Background

The category of elements of a represented functor is a slice: elements of C(c, x) are arrows out of c, and a morphism of elements is an arrow under c, so ∫C(c,−) is the coslice c/C and ∫C(−,c) is the slice C/c, with the elements projection becoming the codomain, respectively domain, functor.

- nLab: <https://ncatlab.org/nlab/show/over+category>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

The two categories exist in exactly the described form, with their comma identifications proved; what is missing is the identification with the elements construction, and a named projection.

- `Construction/Slice.v:123` `Slice (C : Category) (c : C)` with `obj := ∃ a : C, a ~> c` and `hom := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x`; `:169` `Coslice` with `obj := ∃ a : C, c ~> a` and `hom := ∃ f, `2 y ≈ f ∘ `2 x`. Both hom conditions agree clause by clause with Riehl's ("under c", "over c"), with the commuting triangle as a proof-irrelevant `≈` equation.
- `Construction/Slice.v:140` `Comma_Slice : C ̸ c ≅[Cat] (Id ↓ =(c))` and `:181` `Comma_Coslice : c ̸co C ≅[Cat] (=(c) ↓ Id)` are genuinely proved (no `Admitted` in the file), so the comma readings are available.
- Missing: the example's actual claim, `C/c ≅ ∫C(−,c)` and `c/C ≅ ∫C(c,−)`, which cannot be stated because there is no elements construction (#345).
- Also missing: a **named** projection functor. `Construction/Slice.v:39–41` records only that the projection "is the comma projection `comma_proj1` transported across `Comma_Slice`" — it is never defined, and `rg 'Slice_Proj|slice projection'` returns 0 hits. `Construction/Slice/Pullback.v` contains only `Bang_Functor` (`:50`) and `Star_Functor` (`:67`).
- The in-tree precedent for the missing statement is `Instance/Cones/Comma.v:73` `Cones_Comma (F : [J, C]) : Cones F ≅[Cat] (Δ ↓ =(F))` — the same shape of theorem, already carried out for cones.

## Work to be done

Suggested module: extend `Construction/Slice.v`, or add `Construction/Elements/Slice.v` as a satellite of #345.

1. Define the projection functors `Slice_Proj : C/c ⟶ C` (domain) and `Coslice_Proj : c/C ⟶ C` (codomain) as first-class functors, replacing the `Construction/Slice.v:39–41` comment that currently only describes them; prove they agree with the transported comma projections.
2. Prove `Coslice_Elements : c/C ≅[Cat] ∫[Hom c,─]` and `Slice_Elements : C/c ≅[Cat] ∫[Hom ─,c]`, following the `Cones_Comma` precedent, and prove each isomorphism **commutes with the projections** to C — the compatibility is what makes the identification useful downstream.
3. Record the contravariant orientation explicitly: for the contravariant representable, the elements category is defined so that the projection stays covariant, and the resulting hom condition `g ∘ h ≈ f` is exactly the slice's.
4. Update `Construction/Slice.v:39–41` to cite the new functors and theorems.

In-tree donors: `Construction/Slice.v:123/140/169/181`, `Instance/Cones/Comma.v:73` (precedent), `Construction/Comma.v:204` (`comma_proj2`), `Functor/Hom.v:60`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Example 2.4.6, printed p. 73; setoid `≈` discipline — never `=` on morphisms
- [ ] `Slice_Proj` and `Coslice_Proj` are defined as functors and proved to agree with the transported comma projections
- [ ] Both identifications with categories of elements are proved as isomorphisms of categories
- [ ] Each identification is proved to commute with the projections to C
- [ ] `Construction/Slice.v:39–41`'s descriptive comment is replaced by a citation of the new definitions
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the two projections and the two identifications
- [ ] New/edited files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Construction/Slice.v
make && make todo
```
```coq
Print Assumptions Slice_Elements.
Print Assumptions Coslice_Elements.
Print Assumptions Slice_Elements_over_C.
```
Reviewer checklist: the isomorphisms are proved compatible with the projections (an isomorphism of the bare categories is weaker than the example's claim); statement matches Riehl Example 2.4.6, printed p. 73.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Related (NOT blocking): #716 also proposes to create `Construction/Elements/Slice.v`. It proves the equivalence `el(P) ≃ y/P` for an **arbitrary presheaf** `P`; this issue proves the **representable** case, `c/C ≅[Cat] ∫[Hom c,─]` and `C/c ≅[Cat] ∫[Hom ─,c]`, together with compatibility with the projections to `C`. Neither statement is derived from the other in tree and both depend only on #345, so there is no precedence between them — but they target one file and must not be worked in the same parallel wave.

<!-- catalog: {"ids":["riehl:2.4:example6"],"deps":["#345"]} -->

---8<---

```yaml
title: "Riehl 2.4: Universal elements are exactly the initial (resp. terminal) objects of the category of elements"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.4:prop8, riehl:2.4:exiv]
deps_item_ids: [riehl:2.1:example5]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Proposition 2.4.8, printed p. 74 (PDF pp. 94–95), and Exercise 2.4.iv, printed p. 78 (PDF p. 98).
- Items: `riehl:2.4:prop8`, `riehl:2.4:exiv`.

## Background

This is the hinge of §2.4: an element x of F c is universal exactly when (c, x) is initial in the category of elements of a covariant F, and exactly when it is terminal for a contravariant F; hence a set-valued functor is representable precisely when its category of elements has an initial (resp. terminal) object. The exercise asks for the contravariant half to be obtained by duality rather than re-proved.

- nLab: <https://ncatlab.org/nlab/show/universal+element>, <https://ncatlab.org/nlab/show/category+of+elements>, <https://ncatlab.org/nlab/show/initial+object>

## Current state in the library

The general "universal ⟺ initial in a comma category" packaging is present and proven; the proposition's own statement is not, for two precise reasons.

- `Theory/Universal/Arrow.v:127` is literally `Class UniversalArrow (c : C) (F : D ⟶ C) := { arrow_initial : @Initial (=(c) ↓ F); arrow_obj := ...; arrow := ... }`, with `:139` `ump_universal_arrows` and `:158` `universal_arrow_from_UMP` giving both directions, all proved.
- **Verifier correction to the coverage record, which a draft must not repeat:** it is *not* true that universal arrows are never connected to representability. `Structure/UniversalProperty/Universal/Arrow.v:61` `UniversalArrowIsUniversalProperty` instantiates `IsUniversalProperty` at `P := AUniversalArrow c U` with `repr_functor := (Curried_Hom C c) ◯ U`, i.e. `d ↦ Hom_C(c, U d)` — so "initial object of the comma ⟺ representable" **is** available in that form. What is genuinely missing is (a) any link to `Functor/Representable.v:46`'s `Class Representable` itself, which remains unconnected to `Initial`, and (b) the `Sets` specialization: at `C := Sets`, `c := 1` the statement is about representability of `d ↦ Hom_Sets(1, F d)`, and there is no in-tree isomorphism `Hom_Sets(1, X) ≅ X` to identify that with `F` (searched; none exists — that is the gap filed as Riehl Example 2.1.5(i)).
- The contravariant/terminal dual is **not defined at all**: there is no couniversal-arrow class and no `Terminal (F ↓ =(c))`; the only trace is the comment at `Theory/Universal/Arrow.v:23–24` ("The dual notion, a universal arrow from F to c, is a terminal object of `F ↓ =(c)`") — a comment, not an assertion.
- And the category of elements itself is absent (#345), so the proposition is never stated in the book's form.

## Work to be done

Suggested module: `Construction/Elements/Universal.v` (new), a satellite of #345.

1. Define the universal-element predicate for `F : C ⟶ Sets` in the elementary form Riehl uses (an element x of F c such that the induced `Ψ(x) : [Hom c,─] ⟹ F` is a natural isomorphism), reusing #303's universal-element structure rather than introducing a second one.
2. Prove the covariant half: `x` is universal iff `(c, x)` is initial in `∫F`. The proof is Riehl's — universality says each component of `Ψ(x)` is a bijection, which is exactly unique existence of a morphism `(c,x) ⟶ (d,y)` for every object of `∫F`.
3. Derive the corollary `Representable F ↔ Initial (∫F)`, connecting `Functor/Representable.v:46`'s class to `Initial` for the first time.
4. Exercise 2.4.iv: obtain the contravariant/terminal half **by duality** at `C^op`, not by a second proof — the library's `C^op^op = C` by reflexivity makes this the intended route, and the exercise is precisely about exercising it. Provide the `CouniversalElement` accessors so consumers never see `op`.
5. Bridge to the existing comma packaging: prove that at `C := Sets`, `c := 1` the general `UniversalArrow`/`UniversalArrowIsUniversalProperty` statement specializes to this one, using the global-elements isomorphism `Hom_Sets(1, X) ≅ X` (Riehl Example 2.1.5(i)). This closes the gap the verifier identified and makes the two developments one.
6. Fill in `Theory/Universal/Arrow.v:23–24`: replace the comment describing the dual with a reference to the now-defined dual.

In-tree donors: `Theory/Universal/Arrow.v:127/139/158`, `Structure/UniversalProperty/Universal/Arrow.v:61`, `Structure/UniversalProperty.v:72` (`representability_by_yoneda`), `Functor/Representable.v:46`, `Construction/Opposite.v:126` (`op_invol`), and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Proposition 2.4.8 (printed p. 74) and Exercise 2.4.iv (printed p. 78); setoid `≈` discipline — never `=` on morphisms
- [ ] Both directions of the covariant biconditional proved (universal element ⟺ initial object of `∫F`)
- [ ] `Representable F ↔ Initial (∫F)` stated, connecting `Functor/Representable.v`'s class to `Initial`
- [ ] The contravariant/terminal half is **derived by duality**, not re-proved, and covariant accessors are exported
- [ ] The specialization of the existing comma packaging at `C := Sets`, `c := 1` is proved, via the global-elements isomorphism
- [ ] `Theory/Universal/Arrow.v:23–24`'s comment is replaced by a reference to the defined dual
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for both halves and the representability corollary
- [ ] New/edited files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated — this is the statement that ties representability, universal elements and the category of elements together

## Verification

```bash
coqc -R . Category Construction/Elements/Universal.v
coqc -R . Category Theory/Universal/Arrow.v
make && make todo
```
```coq
Print Assumptions universal_element_iff_initial.
Print Assumptions representable_iff_elements_initial.
Print Assumptions universal_element_iff_terminal.
```
Reviewer checklist: the contravariant half is obtained by instantiating at `C^op` (grep the proof — a second hand proof does not satisfy Exercise 2.4.iv); the `Sets` specialization of the comma packaging is proved rather than asserted; statement matches Riehl Proposition 2.4.8, printed p. 74.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #303 (universal elements as first-class structures)
- Depends on: `riehl:2.1:example5` (the global-elements isomorphism `Hom_Sets(1, X) ≅ X`, Example 2.1.5(i) — needed for the `Sets` specialization)

<!-- catalog: {"ids":["riehl:2.4:prop8","riehl:2.4:exiv"],"deps":["#345","#303","riehl:2.1:example5"]} -->


---8<---

```yaml
title: "Riehl 2.4: The subcategory of representations is empty or a contractible groupoid"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.4:prop9]
deps_item_ids: [riehl:2.4:prop8]
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Proposition 2.4.9, printed p. 75 (PDF p. 95).
- Items: `riehl:2.4:prop9`.

## Background

The full subcategory of the category of elements spanned by the universal elements is either empty or a contractible groupoid: there is exactly one morphism between any two of its objects and it is invertible. That is the precise sense in which a representation, though not unique as a set-theoretic datum, is unique category-theoretically — and it rests on the general fact that the initial objects of any category span an empty-or-contractible groupoid.

- nLab: <https://ncatlab.org/nlab/show/groupoid>, <https://ncatlab.org/nlab/show/initial+object>, <https://ncatlab.org/nlab/show/universal+element>

## Current state in the library

The "unique isomorphism between any two representations" half exists in the representability packaging; the proposition's three other clauses do not.

- `Structure/UniversalProperty.v:175` `univ_property_unique_up_to_unique_iso (c d : C) (t : P c) (s : P d) : Unique (fun p : (c ≅ d) => univ_property_respects_iso c d p t ≈ s)` and `:112` `univ_property_unique`. `Unique` really is unique existence (`Lib/Setoid.v:97–100`), and the predicate carries the compatibility condition, so this is a genuine statement — but note precisely what it quantifies over.
- **The "no other morphisms" clause is genuinely not proved.** The `Unique` in `:175` ranges over `p : c ≅ d`, i.e. over *isomorphisms*, not over `c ~> d`. Riehl asserts there are no non-invertible morphisms between universal elements at all, which the in-tree statement does not say.
- The statement is over the representability packaging, not over the full subcategory of `∫F` spanned by universal elements — and `∫F` does not exist (#345). `Construction/Subcategory.v` has full subcategories but no such instance.
- There is no notion of contractibility for a category: `rg -i 'contractible'` returns only remarks that `poly_unit` is a contractible **type** (`Instance/One.v:18`, `Instance/StrictCat/Terminal.v:20/27/33`, `Theory/Multicategory/Operad.v:61`) plus prose in `Structure/Terminal.v`.
- The general lemma the proposition invokes (Riehl Lemma 1.6.16: the initial objects of any category span an empty-or-contractible groupoid) is absent too — verified independently: `Structure/Initial.v` carries only `initial_obj:106`, `zero:109`, `zero_unique:112`, `zero_comp:124`, and `Structure/Terminal.v` only `Terminal:107`, `one_comp:119`, `const:129`.

## Work to be done

Suggested module: `Structure/Contractible.v` (new) for the general lemma, plus a satellite of #345 for the elements statement.

1. Define contractibility for a category: non-empty and every hom-setoid a singleton up to `≈` (equivalently, the unique-map-between-any-two-objects condition). Define "empty or contractible" as the disjunction the proposition uses, and prove a contractible category is a groupoid.
2. Prove the general lemma: the full subcategory of any category spanned by its initial objects is empty or contractible — including the **"no other morphisms"** clause, which the existing `univ_property_unique_up_to_unique_iso` does not give (its uniqueness is quantified over isomorphisms, not over all morphisms). Do the dual for terminal objects.
3. Instantiate `Construction/Subcategory.v` to form the full subcategory of `∫F` spanned by the universal elements, and prove Proposition 2.4.9 by combining item 2 with the universal-element criterion of Riehl Proposition 2.4.8 (universal elements = initial objects of `∫F`).
4. Derive Riehl's reading as a corollary: any two representations of F are connected by a unique isomorphism, and that isomorphism is compatible with the universal elements — relating the new statement back to `Structure/UniversalProperty.v:175` so the two do not drift apart.
5. Record in the header that the in-tree `univ_property_unique_up_to_unique_iso` is the weaker isomorphism-quantified form, and that this issue supplies the stronger morphism-quantified one.

In-tree donors: `Structure/UniversalProperty.v:112/175`, `Lib/Setoid.v:97–100` (`Unique`), `Construction/Subcategory.v:50/59`, `Structure/Initial.v`, `Structure/Terminal.v`, `Construction/Groupoid.v`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Proposition 2.4.9, printed p. 75; setoid `≈` discipline — never `=` on morphisms
- [ ] Contractibility of a category is defined and a contractible category proved to be a groupoid
- [ ] The general lemma (initial objects span an empty-or-contractible full subcategory) is proved **including** the "no other morphisms" clause, with the terminal dual
- [ ] The full subcategory of `∫F` spanned by universal elements is formed and Proposition 2.4.9 proved from the general lemma plus the universal-element criterion
- [ ] The relation to the weaker `Structure/UniversalProperty.v:175` is stated in the header and the two are connected by a lemma
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for the general lemma and for Proposition 2.4.9
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Structure/Contractible.v
make && make todo
```
```coq
Print Assumptions initial_objects_contractible.
Print Assumptions representations_contractible.
```
Reviewer checklist: the "no other morphisms" clause is proved (quantified over all morphisms, not only isomorphisms — this is exactly where the existing in-tree lemma stops short); statement matches Riehl Proposition 2.4.9, printed p. 75.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #247 (uniqueness of terminal, initial and zero objects — the weaker in-tree statement this issue strengthens)
- Depends on: `riehl:2.4:prop8` (universal elements are exactly the initial/terminal objects of the category of elements)

<!-- catalog: {"ids":["riehl:2.4:prop9"],"deps":["#345","#247","riehl:2.4:prop8"]} -->

---8<---

```yaml
title: "Riehl 2.4: Discrete fibrations and the characterization of categories of elements"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:2.4:prop14, riehl:2.4:exviii, riehl:2.4:exix]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Proposition 2.4.14, printed p. 77 (PDF pp. 97–98); Exercises 2.4.viii and 2.4.ix, printed p. 79 (PDF p. 99).
- Items: `riehl:2.4:prop14`, `riehl:2.4:exviii`, `riehl:2.4:exix`.

## Background

The category-of-elements construction is a fully faithful functor from set-valued functors on C into categories over C, and its essential image is exactly the discrete fibrations: a functor over C arises from a set-valued functor precisely when every morphism of the base lifts uniquely from a given lift of its domain (covariant case) or codomain (contravariant case). Under full faithfulness, natural transformations become functors over C, and the fibres of a discrete fibration are discrete categories.

- nLab: <https://ncatlab.org/nlab/show/discrete+fibration>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

Neither the functor nor the characterization exists, and the one near-miss is genuinely a different theorem.

- There is no `∫(−)` whose functoriality, let alone full faithfulness, could be stated: `rg -il 'category of elements'` returns only the prose comment `Construction/Grothendieck.v:108`. `CAT/C` is expressible (`Construction/Slice.v:123` plus `Instance/Cat.v`) but is never formed.
- No discrete-(op)fibration predicate exists. `rg -in 'discrete_?(left|right|op)?_?fibration|DiscreteFib'` returns exactly two prose sites: `Construction/Grothendieck.v:109` and — a Phase-D correction to the coverage log, which listed only one — `Structure/Factorization.v:98`, which mentions the "(fully faithful functor, discrete fibration)" orthogonal factorization system on `Cat`. Neither defines anything; the second is worth knowing because `Structure/Factorization.v` is a plausible second home for the notion.
- `Theory/Fibration.v` carries `DCartesian:75`, `Cleaving:85`, `CartesianMorphism:96`, `CartesianLift:107`, `ClovenFibration:123`, `SplitCleaving:139`, `Displayed_op:223`, `OpCleaving:272` — and every one of these requires lifts to be **cartesian** (unique factorization *through* the lift, via `dcart_factor`/`cart_factor`), never **unique themselves**. That is exactly the extra demand of a discrete fibration, so `Cleaving` is a genuinely weaker condition, not a rephrasing.
- The nearest tempting relative is `Construction/Grothendieck/RoundTrip.v` (`IndexedCat_of_SplitCleaving:1601`, `RoundTrip_Comparison:1608`, `RoundTrip_Full:1624`, `RoundTrip_Faithful:1631`, `RoundTrip_Equivalence:1638`, plus `Construction/Grothendieck/Fibration.v:223` `Grothendieck_Split`). It is not this proposition: (a) the in-tree indexing is `IndexedCat B`, Cat-valued coherent pseudofunctor data, not `Set^C` — `Construction/Grothendieck.v` and `Construction/Indexed.v` contain the string `Sets` zero times; (b) the fibred side is a cloven/split **opfibration**, never a discrete one; (c) `RoundTrip_Full`/`Faithful` qualify a comparison functor between two categories built from **one** cleaving, not a functor `Set^C ⟶ CAT/C`.
- For Exercise 2.4.ix both halves of the vocabulary exist separately and are never combined: `Structure/Discrete.v:28` `Definition Discrete (C : Category) := ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id`, `Construction/Grothendieck/Fiber.v:95` `Fiber : Category`, `Construction/Grothendieck/RoundTrip.v:131` `StrictFiber`; `grep -n 'Discrete' Construction/Grothendieck/Fiber.v` returns 0 hits. **Caveat carried from verification:** `Structure/Discrete.v:28` is the discrete-**and-skeletal** predicate (it demands `x = y`, and its own header flags this as violating the principle of equivalence), so it is not automatically the right target — the setoid-faithful statement of "the fibres are discrete categories" may need an iso-based variant, which this issue must supply or justify not supplying.

## Work to be done

Suggested modules: `Construction/Elements/Fibration.v` (new), with the discrete-fibration predicate wherever #809 lands it.

1. Over the discrete-(op)fibration predicate of #809, add the **left/right** distinction Riehl needs (unique lift of a morphism from a lift of its domain, respectively of its codomain), and give the equivalent lifting-diagram formulation against the functor `_1 ⟶ _2` picking out either endpoint, using `Theory/Orthogonality.v:43`'s `Class Orthogonal` in `Cat`.
2. Make `∫(−)` a functor `[C, Sets] ⟶ CAT/C` (and the contravariant twin), acting on a natural transformation by the evident functor over C; form `CAT/C` as `Slice Cat C`.
3. Exercise 2.4.viii: prove `∫(−)` is fully faithful, and derive the corollary that `F ≅ G` iff `∫F ≅ ∫G` over C.
4. Proposition 2.4.14: prove the projection `∫F ⟶ C` is a discrete left fibration for covariant F (and a discrete right fibration for contravariant F), and conversely that a discrete left fibration `Π : E ⟶ C` arises from the functor `F c := the objects of E over c`, `F f := codomain of the unique lift`, with `E ≅ ∫F` over C — i.e. the essential image is exactly the discrete fibrations. Prove functoriality of the reconstructed F from uniqueness of lifts, as the book's proof does.
5. Exercise 2.4.ix: prove the fibres of a discrete left or right fibration are discrete categories. State this in the setoid-faithful form (only identity morphisms up to `≈`); if `Structure/Discrete.v:28`'s skeletal predicate is used instead, justify it in the header, and otherwise supply the iso-based variant.
6. Record in the header the relation to `Structure/Factorization.v:98`'s mention of the (fully faithful, discrete fibration) factorization system, and to the cloven/split opfibration development of `Theory/Fibration.v`, stating explicitly that cartesian lifts are weaker than unique lifts.

In-tree donors: `Theory/Fibration.v`, `Construction/Grothendieck/Fibration.v`, `Construction/Grothendieck/RoundTrip.v` (as a contrast, not a donor of statements), `Construction/Slice.v:123`, `Instance/Cat.v`, `Structure/Discrete.v:28`, `Theory/Orthogonality.v:43`, `Instance/Two.v:134`, `Instance/One.v`, and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Proposition 2.4.14 (printed p. 77) and Exercises 2.4.viii, 2.4.ix (printed p. 79); setoid `≈` discipline — never `=` on morphisms
- [ ] Discrete **left** and **right** fibrations are distinguished, with the lifting-diagram formulation proved equivalent to the elementary one
- [ ] `∫(−)` is a functor into `CAT/C` and is proved fully faithful, with the `F ≅ G ⟺ ∫F ≅ ∫G` corollary
- [ ] Both directions of the essential-image characterization are proved, including functoriality of the reconstructed set-valued functor
- [ ] The fibres of a discrete fibration are proved discrete, in the setoid-faithful sense (or the use of `Structure/Discrete.v:28`'s skeletal predicate is justified in the header)
- [ ] The header states that cartesian lifts (`Theory/Fibration.v`) are strictly weaker than unique lifts, so a reader cannot mistake `Cleaving` for this notion
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for full faithfulness, both directions of the characterization, and the fibre lemma
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated — the discrete-fibration characterization is flagship-level

## Verification

```bash
coqc -R . Category Construction/Elements/Fibration.v
make && make todo
nix build .#category-theory_9_1 .#category-theory_8_20
```
```coq
Print Assumptions elements_functor_fully_faithful.
Print Assumptions elements_proj_discrete_left_fibration.
Print Assumptions discrete_fibration_is_elements.
Print Assumptions discrete_fibration_fibres_discrete.
```
Reviewer checklist: the reconstruction direction really produces a functor (functoriality from uniqueness of lifts) and an isomorphism **over C**; the discreteness condition is uniqueness of lifts, not cartesianness; statement matches Riehl Proposition 2.4.14, printed p. 77.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #809 (discrete opfibrations and the elements/fibration round trips — this issue supplies the left/right distinction and the fully faithful `Set^C ⟶ CAT/C` statement that #809 explicitly scopes out)

<!-- catalog: {"ids":["riehl:2.4:prop14","riehl:2.4:exviii","riehl:2.4:exix"],"deps":["#345","#809"]} -->

---8<---

```yaml
title: "Riehl 2.4: The functor of preorders on a set and its category of elements"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:2.4:exvi]
deps_item_ids: []
deps_pending: []
```

## Source

- Book: Emily Riehl, *Category Theory in Context*, 2nd edition.
- Section: 2.4 ("The category of elements"), Exercise 2.4.vi, printed p. 79 (PDF p. 99).
- Items: `riehl:2.4:exvi`.

## Background

Preorders on a set pull back along functions, giving a contravariant set-valued functor on sets; its category of elements is the category of preordered sets and order-preserving maps that are *order-reflecting on the nose*, and the exercise asks whether that functor is representable.

- nLab: <https://ncatlab.org/nlab/show/preorder>, <https://ncatlab.org/nlab/show/category+of+elements>

## Current state in the library

The library turns a preorder into a category; the exercise needs the opposite direction, and nothing does that.

- `Instance/Proset.v:33` `Program Definition Proset {A R} (P : PreOrder R) : Category` builds the thin category of **one** preorder. The exercise needs the set of **all** preorders on a given set assembled into a `Sets`-valued presheaf; nothing in tree does that.
- There is no relations functor and no power-set functor on `Sets` either against which the construction could be modelled (the only `power` hit is `Structure/Topos.v`'s internal `Pow a := Ω ^ a`), so both the functor and its category of elements have to be built.
- `Instance/Poset.v` and `Instance/Props.v` supply order material but no functor of orders.
- **Library defect to fix while here:** `Instance/Proset.v` carries a dangling "See also [Ord]" cross-reference — `grep -rn '\bOrd\b' --include='*.v'` over the whole tree returns exactly that one comment line and no definition. Either supply the referenced development or correct the comment.

## Work to be done

Suggested module: `Instance/Sets/Preorders.v` (new).

1. Define `Pre : Sets^op ⟶ Sets`, sending a setoid to the setoid of preorders on it (reflexive transitive `≈`-closed relations, compared by mutual containment) and a function to the pullback preorder `x ≤' y := f x ≤ f y`; prove the functor laws, minding that the relation setoid lives one universe up (follow the discipline `Instance/Sets/Classifier.v` and #227 record for the same situation, and disclose the choice in the header).
2. Describe its category of elements: objects are preordered setoids, morphisms are functions with `x ≤ y ↔ f x ≤ f y`, i.e. order-reflecting as well as order-preserving. Prove that description as a theorem, not as a comment, and compare it with `Instance/Poset.v`'s category of posets and monotone maps (#641) — the hom conditions differ, and the header must say so.
3. Answer the representability question with a proof: decide whether `Pre` is representable and prove the verdict. If it is not, the clean route is the mono-preservation test (a representable functor preserves monomorphisms) or a cardinality/size obstruction — state which, and make it a theorem rather than a remark.
4. Relate the thin-category construction: for a fixed element of `Pre X`, `Instance/Proset.v:33`'s `Proset` produces its thin category, so the elements category maps to `Cat`; record that functor if it is cheap.
5. Fix the dangling `Ord` cross-reference in `Instance/Proset.v`.

In-tree donors: `Instance/Proset.v:33`, `Instance/Poset.v`, `Instance/Props.v`, `Instance/Sets.v`, `Instance/Sets/Classifier.v` (universe discipline for a relation setoid), and the elements construction of #345.

## Definition of Done

- [ ] Statement fidelity to Riehl Exercise 2.4.vi, printed p. 79; setoid `≈` discipline — never `=` on morphisms
- [ ] `Pre : Sets^op ⟶ Sets` is defined with proved functor laws and its universe placement disclosed in the header
- [ ] The description of its category of elements (order-preserving **and** order-reflecting maps) is proved, and contrasted with the category of posets and monotone maps of #641
- [ ] The representability question is answered **with a proof**, not a remark
- [ ] The dangling `Ord` cross-reference in `Instance/Proset.v` is fixed
- [ ] No `Admitted`, `admit`, or new `Axiom` beyond the `Instance/`-layer stdlib axioms enumerated in docs/AXIOMS.md
- [ ] `Print Assumptions` reported for `Pre` and for the representability verdict
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits

## Verification

```bash
coqc -R . Category Instance/Sets/Preorders.v
coqc -R . Category Instance/Proset.v
make && make todo
```
```coq
Print Assumptions Pre.
Print Assumptions Pre_elements_description.
Print Assumptions Pre_representability.
```
Reviewer checklist: the elements description distinguishes order-reflecting from merely monotone maps; the representability verdict is proved; statement matches Riehl Exercise 2.4.vi, printed p. 79.

## Dependencies

- Depends on: #345 (the category of elements of a set-valued functor)
- Depends on: #641 (Pos, the category of posets and monotone maps — the contrast the description needs)

<!-- catalog: {"ids":["riehl:2.4:exvi"],"deps":["#345","#641"]} -->

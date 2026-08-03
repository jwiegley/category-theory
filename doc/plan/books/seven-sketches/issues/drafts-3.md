```yaml
title: "Seven Sketches 3.2: The free category on a single loop is the additive naturals, and free categories have only identity isomorphisms"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.2.1:example3.13, 7sketches:3.2.1:ex3.15, 7sketches:3.2.5:ex3.33]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality: An Invitation to Applied Category
Theory* (Cambridge University Press, 2019), §3.2.1 Example 3.13 and Exercise 3.15
(printed p. 83, PDF p. 95), and §3.2.5 Exercise 3.33 (printed p. 89, PDF p. 101).
Items covered: `7sketches:3.2.1:example3.13`, `7sketches:3.2.1:ex3.15`,
`7sketches:3.2.5:ex3.33`.

## Background

The free category on a quiver has the vertices as objects and the finite paths as
morphisms ([nLab: free category](https://ncatlab.org/nlab/show/free+category)); on the
quiver with one vertex and one loop the paths are indexed by their length, so the
hom-set is in bijection with the natural numbers and concatenation is addition — the
delooping of the free monoid on one generator
([Wikipedia: Free monoid](https://en.wikipedia.org/wiki/Free_monoid)). Because path
length is additive under concatenation, an invertible path must have length zero, which
is why a free category has no isomorphisms beyond its identities.

## Current state in the library

The ingredients exist but are never assembled.

- `Construction/Free/Quiver.v:431` defines `FreeOnQuiver` with `hom := tlist edges`, so
  morphisms really are paths.
- `Lib/TList.v:81` defines `tlist_length` and `Lib/TList.v:323` proves
  `tlist_app_length : tlist_length (xs +++ ys) = tlist_length xs + tlist_length ys` —
  exactly the additivity both results need.
- `Test/Issue138.v:87` builds the one-vertex one-loop quiver, but the only statement
  made about it is `Test/Issue138.v:95`, which pins the *object* type of
  `FreeOnQuiver` of it to `unit`. Nothing says `tlist_length` is injective or
  surjective on that hom-set, so "the paths *are* the natural numbers" is not
  established, and the monoid (ℕ, +, 0) is nowhere identified as a free monoid on one
  generator — the only free-monoid content in tree is the free *category* adjunction at
  `Construction/Free/Quiver.v:550` plus prose in `Theory/Coq/List.v`.
- The one-object-category-as-monoid pattern is instantiated by hand exactly once, at
  `Construction/Funny/Comparison.v:81` (`ListMon`, lists of booleans under
  concatenation).
- No statement anywhere characterises the isomorphisms of a free category. Searching
  the tree for a rigidity result of that shape returns nothing.

## Work to be done

Suggested module: `Construction/Free/Quiver/Loop.v` (new), plus a small extension to
`Construction/Free/Quiver.v`.

1. **The loop quiver and its counting bijection.** Define `LoopQuiver` (one node, one
   edge) as a reusable `Quiver`, and prove that `tlist_length` on
   `hom[FreeOnQuiver LoopQuiver] tt tt` is a bijection onto `nat`: give the inverse that
   builds the `n`-fold path and prove both round trips (`≈` on the hom-setoid in one
   direction, `=` on `nat` in the other). Donor: `Lib/TList.v`.
2. **The monoid reading.** Transport the bijection to the monoid level: the empty path
   corresponds to `0` and concatenation to `+`, so the hom-monoid at the unique object
   is (ℕ, +, 0). State this against the free monoid delivered by #296 and the delooping
   construction of #220, rather than re-deriving a bespoke monoid record here. This is
   the content of Exercise 3.15.
3. **Isomorphism rigidity in any free category.** In `Construction/Free/Quiver.v`
   (extend), prove that for every quiver `G` an isomorphism of `FreeOnQuiver G` is an
   identity: from `g ∘ f ≈ id` and additivity of `tlist_length`, both lengths are zero,
   hence both paths are `tnil`. State the endpoint condition honestly (paths of length
   zero exist only when source and target coincide), since hom-setoids at distinct
   endpoints are distinct types. This is Exercise 3.33, answered in the affirmative.
4. **Corollary.** The loop category has exactly one isomorphism, its identity; record
   this as the categorical statement that the additive naturals are not a group, which
   is the negative half the §3.2.5 group exercise consumes.

In-tree donors: `Construction/Free/Quiver.v` (`FreeOnQuiver`, `InducedFunctor`,
`FreeForgetfulAdjunction`), `Lib/TList.v`, `Theory/Isomorphism.v`,
`Construction/Funny/Comparison.v:81` as a worked precedent for a one-object category.

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.2.1 (Example 3.13, Exercise 3.15) and
      §3.2.5 (Exercise 3.33), paraphrased, with setoid `≈` discipline throughout — never
      `=` on morphisms
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact:
      the loop bijection, the monoid identification, and the free-category isomorphism
      rigidity lemma
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Construction/Free/Quiver/Loop.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions loop_hom_nat_iso.
Print Assumptions loop_monoid_is_free_on_one_generator.
Print Assumptions free_iso_is_id.
```

Review items: the bijection is proved in both directions (not only the forward map);
the rigidity lemma quantifies over an arbitrary quiver, not just the loop; the
statements match Seven Sketches §3.2.1 and §3.2.5 as paraphrased above.

## Dependencies

Depends on: #296
Depends on: #220

<!-- catalog: {"ids":["7sketches:3.2.1:example3.13","7sketches:3.2.1:ex3.15","7sketches:3.2.5:ex3.33"],"deps":["#296","#220"]} -->

---8<---

```yaml
title: "Seven Sketches 3.2.3: The preorder reflection of a category, and its left adjointness to the preorder inclusion"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.2.3:construction-preorder-reflection, 7sketches:3.2.3:prop-preorder-reflection-adjunction, 7sketches:3.2.3:ex3.21, 7sketches:3.2.3:ex3.22, 7sketches:3.2.3:remark3.23]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.2.3, printed p. 86 (PDF p. 98): the unnumbered construction "the preorder reflection
of a category", the unnumbered (and deliberately unproved) claim that the inclusion of
preorders is right adjoint to it, Exercises 3.21 and 3.22, and Remark 3.23. Items
covered: `7sketches:3.2.3:construction-preorder-reflection`,
`7sketches:3.2.3:prop-preorder-reflection-adjunction`, `7sketches:3.2.3:ex3.21`,
`7sketches:3.2.3:ex3.22`, `7sketches:3.2.3:remark3.23`.

## Background

The preorder reflection of a category forgets *how many* morphisms there are between two
objects while remembering *whether* there is one; it is the left adjoint of the inclusion
of preorders, regarded as thin categories, into all categories
([nLab: thin category](https://ncatlab.org/nlab/show/thin+category)), and is the
category-level analogue of the posetal reflection of a preorder
([nLab: posetal reflection](https://ncatlab.org/nlab/show/posetal+reflection)). Every
presentation of a category by a graph and path equations lies between the free category
on that graph (no equations) and its preorder reflection (all parallel paths identified).

## Current state in the library

- `Theory/Category.v:282` declares `hom_preorder {C : Category} : PreOrder (@hom C)`,
  reflexivity from `id` and transitivity from composition. It is `Type`-valued, so it
  *remembers which* morphism witnesses the relation — precisely the information the
  reflection is supposed to destroy — and the header itself notes the `Type`-valued
  reading. It is declared `#[export]` and consumed nowhere in the tree.
- `Instance/Proset.v:33` turns any `PreOrder R` into a thin category (`hom := R`,
  hom-setoid `equiv := fun _ _ => True`), so the *inclusion* half of the adjunction is
  available; `Instance/Proset.v:47` instantiates it at (`nat`, `≤`).
- `Construction/Quotient.v:226` (`HomCongruence`) and `:254` (`Quotient`) provide the
  quotient of a category by a hom-congruence, and `:294` (`QuotientProj`) the projection
  with a universal property. The only in-tree `HomCongruence` instances are the PROP and
  coloured-PROP term congruences; the *total* congruence, which identifies all parallel
  morphisms, has never been declared.

So neither the truncation, nor the reflection as a construction on categories, nor its
functoriality, nor the adjunction exists; consequently Remark 3.23's "spectrum" reading
has only its lower bound in tree, as `HomCongruence`'s `cong_incl` field.

## Work to be done

Suggested module: `Construction/PreorderReflection.v` (new).

1. **The total hom-congruence.** Declare the relation identifying every pair of parallel
   morphisms and prove it is a `HomCongruence` (all five fields are immediate). Define
   `PreorderReflect C := Quotient C <that congruence>` and prove the result is thin
   (every pair of parallel morphisms is `≈`).
2. **The truncated object preorder.** Define `c ≤ c' := inhabited (c ~> c')` as a
   `Prop`-valued relation — proof-irrelevant, so it genuinely forgets how many parallel
   morphisms there are — prove it a `PreOrder`, and prove that `Proset` of it agrees
   with `PreorderReflect C`. Record in the header why `Theory/Category.v:282` is *not*
   this relation.
3. **Functoriality.** Make `PreorderReflect` a functor on `Cat` (a functor `F : C ⟶ D`
   descends, because it sends parallel morphisms to parallel morphisms), with
   `QuotientProj` as the unit component.
4. **The adjunction.** Prove that `PreorderReflect` is left adjoint to the inclusion of
   thin categories into `Cat` — equivalently that preorders form a reflective subcategory
   of categories, which is the unproved claim the book sets off in §3.2.3. The
   transposition is "a functor into a thin category factors uniquely through the
   projection"; build it through `Theory/Universal/Arrow.v`'s
   `AdjunctionFromUniversalArrows` rather than by hand, and use
   `Construction/Subcategory.v` / `Construction/Reflective.v` for the packaging.
5. **Exercise 3.21.** Prove that the preorder reflection of `FreeOnQuiver G` is the
   reachability preorder of `G`, and instantiate at the four small graphs of the
   exercise (two parallel arrows; a loop plus an isolated vertex; the four-arrow square;
   the square with one side removed). In each case the presenting equations are exactly
   "all parallel paths are equal", which is the general theorem specialised, not four
   separate calculations.
6. **Exercise 3.22.** The reflection of the one-object loop category (the loop category
   requested in the Seven Sketches §3.2.1 issue) is the terminal preorder — isomorphic
   to `Instance/One.v:25`'s `_1`.
7. **Remark 3.23.** Record the interval: congruences on `FreeOnQuiver G` are bounded
   below by `≈` (already `cong_incl`) and above by the total congruence of item 1, so
   every category presented by `G` sits between the free category on `G` and its
   preorder reflection. State this as a two-sided containment lemma about `HomRel`s, not
   as prose.

In-tree donors: `Construction/Quotient.v`, `Instance/Proset.v`,
`Construction/Free/Quiver.v`, `Theory/Universal/Arrow.v`, `Construction/Reflective.v`.

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.2.3 (paraphrased), with setoid `≈`
      discipline throughout — never `=` on morphisms
- [ ] The reflection is proved to *truncate*: the order relation is `Prop`-valued, and a
      lemma records that two parallel morphisms of `C` become equal in
      `PreorderReflect C`
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for the reflection, its
      functoriality, the adjunction, and the Exercise 3.21 reachability theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level
- [ ] **Library-defect cleanup while in these files:** the header pointer at
      `Instance/Proset.v:19` ("See also [Ord], for the category of preordered sets") and
      the matching "[Pos]" pointer at `Instance/Poset.v:21` both name modules that do not
      exist anywhere in the tree. Either supply the referenced category or correct the
      prose; do not leave a dangling cross-reference in a file this issue touches.

## Verification

```bash
coqc -R . Category Construction/PreorderReflection.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
rg -n '\[Ord\]|\[Pos\]' --glob '*.v'   # must not resurface as dangling pointers
```

```coq
Print Assumptions PreorderReflect.
Print Assumptions preorder_reflection_adjunction.
Print Assumptions free_reflection_is_reachability.
```

Review items: the order relation is `Prop`-valued (a `Type`-valued relation would not be
a reflection); the adjunction is stated in the book's orientation (inclusion on the
right); statement matches Seven Sketches §3.2.3.

## Dependencies

Depends on: #299
Depends on: #223

<!-- catalog: {"ids":["7sketches:3.2.3:construction-preorder-reflection","7sketches:3.2.3:prop-preorder-reflection-adjunction","7sketches:3.2.3:ex3.21","7sketches:3.2.3:ex3.22","7sketches:3.2.3:remark3.23"],"deps":["#299","#223"]} -->

---8<---

```yaml
title: "Seven Sketches 3.2.2/3.3.2: The free square category, its comparison with the commutative square, and the failure of the reverse comparison"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.2.2:construction-square-categories, 7sketches:3.2.2:ex3.16, 7sketches:3.2.2:ex3.17, 7sketches:3.3.2:example3.38, 7sketches:3.3.2:ex3.39, 7sketches:3.3.2:example3.41]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.2.2 (the unnumbered "free square" and "commutative square" presentations, and
Exercises 3.16 and 3.17), printed p. 84 (PDF p. 96); and §3.3.2 Example 3.38, Exercise
3.39 and Example 3.41, printed pp. 91–92 (PDF pp. 103–104). Items covered:
`7sketches:3.2.2:construction-square-categories`, `7sketches:3.2.2:ex3.16`,
`7sketches:3.2.2:ex3.17`, `7sketches:3.3.2:example3.38`, `7sketches:3.3.2:ex3.39`,
`7sketches:3.3.2:example3.41`.

## Background

The free category on the four-vertex square graph has ten morphisms — four identities,
four generators, and two *distinct* parallel composites — while imposing the single path
equation that the two composites agree collapses it to the walking commutative square
with nine ([nLab: free category](https://ncatlab.org/nlab/show/free+category),
[nLab: commutative diagram](https://ncatlab.org/nlab/show/commutative+diagram)). The pair
is the book's running illustration that a functor may exist and be unique in one
direction while no functor at all exists in the other.

## Current state in the library

Neither category is built the way the book builds it, and no morphism count is stated.

- `Construction/Funny.v:138` defines `FunHom` as an inductive of one-sided step words,
  so `_2 □ _2` is *not* `FreeOnQuiver` of the square quiver, and no in-tree lemma
  identifies the two. No square-shaped quiver exists anywhere.
- `Construction/Funny/Comparison.v:144` proves `funny_diagonals_distinct`: the two
  diagonals `diagLR` and `diagRL`, both of type `FunHom TwoX TwoX TwoY TwoY`, are
  distinct — which is exactly clause 2 of Exercise 3.16 (two distinct *parallel* paths)
  and exactly the contradiction Example 3.41 needs. `:69` `FunnyToProduct_Full` and
  `:154` `FunnyToProduct_not_faithful` show the comparison into `_2 ∏ _2` is full but
  not faithful; nothing shows the *only* identification it makes is the square equation.
- No enumeration or count exists for either category. `FunHom` is an inductive of
  unbounded-length words whose quotient by `feq` is never normalised, so "ten morphisms"
  and "nine morphisms" are not statable today. Clause 3 of Exercise 3.16 (two distinct
  *non-parallel* paths) is not even expressible in that encoding, since morphisms with
  different endpoints inhabit different types.
- `Construction/PROP/Tietze.v:395` `AddEqn_derivable_conservative` is the Tietze move
  Exercise 3.17 needs — an equation already forced by the imposed ones may be added or
  removed without changing the presented object — but it is developed only for
  symmetric monoidal theories over `Term Σ m n`, never for a presentation of a bare
  category by a graph and path equations.

## Work to be done

Suggested module: `Instance/Square.v` (new), sitting alongside the commutative square
delivered by #300 and over the presented-category machinery of #299.

1. **The free square.** Define the four-vertex square quiver and
   `FreeSquare := FreeOnQuiver SquareQuiver`. Give decidable normal forms for its
   hom-setoids and prove the enumeration: exactly ten morphisms, namely four identities,
   the four generators, and the two distinct composites. This is
   Exercise 3.16 clause 1 and the missing half of the §3.2.2 construction.
2. **Parallel and non-parallel witnesses.** From the enumeration, exhibit two distinct
   parallel paths (clause 2) and a pair of distinct non-parallel paths (clause 3);
   phrase the latter over the endpoint indices, since a hom-setoid comparison is not
   available across different endpoints. Record that reading explicitly in the header.
3. **The unique object-preserving functor.** Build the functor `FreeSquare ⟶ CommSquare`
   fixing the four objects, by `Construction/Free/Quiver.v:464` `InducedFunctor`, and
   prove it is the *only* such functor: once the object action is fixed, thinness of the
   relevant hom-sets of the commutative square forces every one of the ten images
   (Example 3.38). Tabulate the image of each of the ten morphisms as a proved lemma
   (Exercise 3.39).
4. **The failure in the reverse direction.** Prove there is *no* functor
   `CommSquare ⟶ FreeSquare` fixing the four objects and sending the four generators to
   the four generators: functoriality would force the two diagonals to agree, which
   `funny_diagonals_distinct` (or its `FreeSquare` analogue from item 1) refutes
   (Example 3.41).
5. **The square with a diagonal.** Present the square graph augmented with an arrow
   `j : A ⟶ D` and the two equations identifying both composites with `j`, and prove it
   presents the same category as the commutative square: derive the equation between the
   two composites, then discharge the redundant generator. This is the general-category
   analogue of Tietze move 1, and the issue should record whether the PROP-level proof at
   `Construction/PROP/Tietze.v:395` can be reused or must be re-proved at the category
   level (Exercise 3.17).

In-tree donors: `Construction/Free/Quiver.v`, `Construction/Quotient.v`,
`Construction/Funny/Comparison.v` (the diagonals lemma), `Instance/Two.v`,
`Construction/PROP/Tietze.v` (as a template for the Tietze argument).

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.2.2 and §3.3.2 (paraphrased), with
      setoid `≈` discipline throughout — never `=` on morphisms
- [ ] Both morphism counts are *proved* (ten for the free square, nine for the
      commutative square as delivered by the dependency), as enumerations with a decision
      procedure, not as prose counts
- [ ] The uniqueness clause of Example 3.38 and the non-existence of Example 3.41 are
      both theorems, the second stated as a refutation (`... → False`)
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for the enumeration, the
      comparison functor, its uniqueness, the non-existence result, and the
      square-with-diagonal equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Square.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions free_square_ten_morphisms.
Print Assumptions free_to_comm_square.
Print Assumptions free_to_comm_square_unique.
Print Assumptions no_object_preserving_comm_to_free.
Print Assumptions square_with_diagonal_presents_comm_square.
```

Review items: the counts are proved rather than asserted; the non-parallel-paths clause
is stated over endpoint indices with the reason documented; statement matches Seven
Sketches §3.2.2 and §3.3.2.

## Dependencies

Depends on: #300
Depends on: #299

<!-- catalog: {"ids":["7sketches:3.2.2:construction-square-categories","7sketches:3.2.2:ex3.16","7sketches:3.2.2:ex3.17","7sketches:3.3.2:example3.38","7sketches:3.3.2:ex3.39","7sketches:3.3.2:example3.41"],"deps":["#300","#299"]} -->

---8<---

```yaml
title: "Seven Sketches 3.1/3.3: Database schemas as finitely presented categories, and instances as Set-valued functors"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.1:ex3.3, 7sketches:3.2.2:remark3.20, 7sketches:3.3.3:def3.44]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.1 Exercise 3.3 (printed p. 78, PDF p. 90); §3.2.2 Remark 3.20 (printed p. 85, PDF
p. 97); §3.3.3 Definition 3.44 (printed p. 93, PDF p. 105). Items covered:
`7sketches:3.1:ex3.3`, `7sketches:3.2.2:remark3.20`, `7sketches:3.3.3:def3.44`.

## Background

The organising idea of the chapter is that a database schema *is* a finitely presented
category — a finite graph of tables and foreign keys together with path equations
expressing the business rules — and that a state of the database is a functor from that
category to sets, so the business rules are enforced automatically by functoriality
([nLab: quotient category](https://ncatlab.org/nlab/show/quotient+category),
[Wikipedia: Applied category theory](https://en.wikipedia.org/wiki/Applied_category_theory)).

## Current state in the library

The library already *narrates* this identification but does not implement any part of it.

- `Construction/Free.v:87` contains a header sentence citing this very book — that a
  database schema is a finitely presented category, a free category on tables and
  foreign keys quotiented by path equations, with instances as functors to sets and data
  migration by adjoints. It is an essay, not a definition.
- `Structure/Pullback.v:50` uses "primary key" and "foreign key" only as an analogy in a
  comment. Searching the tree for a relational table, a column, or an attribute finds no
  Coq object at all — the other hits on "table" are composition tables
  (`Theory/Metacategory.v:96`) and Ltac hint databases.
- `Construction/Free/Quiver.v:431` (`FreeOnQuiver`) and `Construction/Quotient.v:254`
  (`Quotient`, with `QuotientProj` at `:294`) are both present, but the *only* place they
  are composed is `Construction/PROP/Presentation.v:180` (`PresentedCat`), which
  quotients the free PROP on a monoidal signature — objects are natural numbers, terms
  carry a tensor — rather than a free category on a graph.
- Nothing constrains a set-valued functor to send designated "attribute" objects to
  fixed value sets, and nothing states that such a functor automatically satisfies the
  schema's equations.

## Work to be done

Suggested module: `Construction/Schema.v` (new), built directly on the presented-category
construction delivered by #299.

1. **Schemas.** Define `Schema` as a finite quiver together with a finite set of path
   equations between *parallel* paths, plus the presented category it generates (the
   quotient of the free category on the quiver by the congruence the equations
   generate). Carry the entity/attribute split as a predicate marking designated
   attribute nodes.
2. **Instances.** Define an instance of a schema as a functor from the presented category
   to `Sets`, and impose the attribute discipline of Definition 3.44 — an instance must
   send each attribute node to a fixed value setoid — as a comma-style condition over a
   chosen typing functor rather than as an ad-hoc side condition, so that instances
   still form a category.
3. **Automatic satisfaction.** Prove the theorem the book leaves implicit: every instance
   satisfies the schema's path equations, because a functor out of a quotient respects
   the imposed congruence. Route it through `QuotientProj`/`QuotientLift` so it is a
   consequence of the universal property, not a re-proof.
4. **Remark 3.20.** Write down the two running schemas of §3.1 as `Schema` values — the
   equation-free employee/department schema, and the variant whose two business rules are
   path equations — and prove they are well formed (all imposed equations are between
   parallel paths).
5. **Exercise 3.3.** State the counting observation as a lemma about the schema, not as a
   coincidence: for a schema presented from tables, the non-identity columns of a table
   are in bijection with the edges of the quiver out of the corresponding node
   (attribute columns included). With the definition of item 1 this is definitional, and
   the issue should say so.

In-tree donors: `Construction/Free/Quiver.v`, `Construction/Quotient.v`,
`Construction/PROP/Presentation.v` (as a worked precedent for a presentation layer),
`Instance/Sets.v`, `Instance/FinSet.v` for finite value sets.

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.1, §3.2.2 Remark 3.20 and §3.3.3
      Definition 3.44 (paraphrased), with setoid `≈` discipline throughout — never `=` on
      morphisms
- [ ] Finiteness is carried as *data* (an enumeration of nodes, edges and equations), not
      as an existence claim, so no choice principle is needed
- [ ] The automatic-satisfaction theorem is proved, not left implicit
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for `Schema`, the presented
      category, the instance category, and the satisfaction theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated — and the essay at `Construction/Free.v:87`
      amended to point at the implementation instead of describing it as an outside idea

## Verification

```bash
coqc -R . Category Construction/Schema.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions Schema.
Print Assumptions SchemaCat.
Print Assumptions instance_satisfies_equations.
Print Assumptions employee_schema.
```

Review items: attribute objects are genuinely pinned (an instance that sends an attribute
node elsewhere must not typecheck); the satisfaction theorem is derived from the
quotient's universal property; statement matches Seven Sketches §3.1/§3.3.3.

## Dependencies

Depends on: #299

<!-- catalog: {"ids":["7sketches:3.1:ex3.3","7sketches:3.2.2:remark3.20","7sketches:3.3.3:def3.44"],"deps":["#299"]} -->

---8<---

```yaml
title: "Seven Sketches 3.3.3: Instances on small presented schemas — idempotent endofunctions, involutions, and an equalizing pair"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.3.3:example3.46, 7sketches:3.3.3:ex3.48]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.3.3 Example 3.46 and Exercise 3.48, printed p. 94 (PDF p. 106). Items covered:
`7sketches:3.3.3:example3.46`, `7sketches:3.3.3:ex3.48`.

## Background

A set-valued functor on a one-object category presented by a single generator subject to
one equation is exactly a set carrying an operation satisfying that equation: the
walking idempotent classifies idempotent endofunctions
([nLab: idempotent](https://ncatlab.org/nlab/show/idempotent)) and the walking involution
classifies involutions ([nLab: involution](https://ncatlab.org/nlab/show/involution)).
The book uses this to make "an instance on a schema" concrete before any general theory
is developed.

## Current state in the library

Only the codomain-side notions exist, and nothing connects them to a functor category.

- `Theory/Morphisms.v:22` defines `Idempotent` (`f ∘ f ≈ f`) and `:32` `Involutive`
  (`f ∘ f ≈ id`), both as classes on a morphism of an arbitrary category.
- `Instance/Sets/Karoubi.v:80` splits an idempotent of `Sets` and `:113` proves `Sets` is
  Cauchy complete, so idempotents of `Sets` are well developed as *data in* `Sets`.
- Nothing in the tree deloops a presented one-object category, so the walking idempotent
  and the walking involution do not exist as categories, and neither direction of the
  identification "functor on that schema ↔ set with the corresponding structure" is
  stated.
- For the second schema of Exercise 3.48, `Instance/Parallel.v:80` gives only the bare
  parallel pair; the three-object shape with an incoming leg and the agreement equation
  is not in tree. `Structure/Equalizer/Fork.v:176` (`fork_cone`) carries the same data in
  cone form but is never presented as a diagram category.
- No `Sets`-level instance of `Involutive` exists at all.

## Work to be done

Suggested module: `Instance/Schema/Small.v` (new), over the one-object presented
categories delivered by #666 and the delooping of #220.

1. **The walking idempotent classifies idempotents.** Prove that a functor from the
   one-object category presented by `⟨s | s ; s = s⟩` into `Sets` is the same thing as a
   setoid `Z` together with an `Idempotent` endomorphism of it: give both constructions
   and both round trips, and package them as an equivalence of categories between the
   functor category and the category of idempotent endomorphisms with equivariant maps.
2. **The walking involution.** The same, for `⟨s | s ; s = id⟩` and `Involutive` — this
   is clause 1 of Exercise 3.48 — together with at least one concrete `Sets` witness
   (e.g. negation on the integers or swap on a two-element setoid), since the tree has no
   `Involutive` instance anywhere.
3. **The equalizing-pair schema.** Build the three-object schema with one arrow into a
   node carrying two parallel arrows out, subject to the equation that the two composites
   agree, and prove that its set-valued functors are exactly triples of setoids with maps
   satisfying that agreement (clause 2 of Exercise 3.48). Record the relationship to
   `Structure/Equalizer/Fork.v:176`: the same data read as a fork.
4. **Concrete models for Example 3.46.** Instantiate at two of the book's four idempotent
   models, choosing the computable ones — the constant-zero map on the naturals, and the
   smallest-prime-factor map on integers at least 2 — with the idempotence proved rather
   than asserted, and keep them axiom-free (`eq_refl`-checkable where the carrier is
   finite).

In-tree donors: `Theory/Morphisms.v`, `Instance/Sets.v`, `Instance/Sets/Karoubi.v`,
`Instance/Fun.v`, `Structure/Equalizer/Fork.v`, `Instance/Parallel.v`.

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.3.3 Example 3.46 and Exercise 3.48
      (paraphrased), with setoid `≈` discipline throughout — never `=` on morphisms
- [ ] Each identification is delivered in *both* directions with the round trips proved,
      not as a one-way construction
- [ ] At least one concrete `Sets` involution and two concrete idempotent models are
      built and their laws proved
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for the three identifications
      and the concrete models
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Schema/Small.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions walking_idempotent_instances.
Print Assumptions walking_involution_instances.
Print Assumptions equalizing_pair_instances.
```

Review items: both round trips are present for each identification; the concrete models
compute; statement matches Seven Sketches §3.3.3.

## Dependencies

Depends on: #666
Depends on: #299
Depends on: #220

<!-- catalog: {"ids":["7sketches:3.3.3:example3.46","7sketches:3.3.3:ex3.48"],"deps":["#666","#299","#220"]} -->

---8<---

```yaml
title: "Seven Sketches 3.4.1: The one-loop schema — its instances are discrete dynamical systems, and migration along a schema functor"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.4.1:construction-dds-schema-functor, 7sketches:3.4.1:ex3.67]
deps_item_ids: [7sketches:3.2.1:example3.13]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.4.1: the unnumbered construction of the schema with one object and one loop, the
schema functor from the graph schema into it, and Exercise 3.67 — printed pp. 100–101
(PDF pp. 112–113). Items covered: `7sketches:3.4.1:construction-dds-schema-functor`,
`7sketches:3.4.1:ex3.67`.

## Background

The free category on a one-vertex one-loop graph has instances that are exactly sets
equipped with an endofunction — a deterministic discrete dynamical system in the
discrete-time sense ([nLab: dynamical system](https://ncatlab.org/nlab/show/dynamical+system),
[nLab: free category](https://ncatlab.org/nlab/show/free+category)). Restricting such an
instance along a functor from the graph schema turns the dynamical system into a graph,
in two different ways depending on which endpoint map is sent to the loop.

## Current state in the library

- `Theory/Kan/Extension.v:127` defines `Induced : [B, C] ⟶ [A, C]` by precomposition —
  the restriction operation the section calls Δ. It is never applied to a concrete
  `Sets`-valued functor anywhere in the tree.
- `Instance/Parallel.v:129` defines `APair {C} {x y} (f g : x ~> y) : Parallel ⟶ C`,
  which already builds a functor out of the graph schema from any parallel pair. Both
  schema functors this section needs are therefore one line each once the loop category
  exists — the functor sending one endpoint map to the identity and the other to the
  loop, and its mirror image. Neither is written down.
- The identification of instances on the loop schema with sets-carrying-an-endofunction
  is absent. `Construction/FAlg.v` would give that category as the algebras of the
  identity endofunctor on `Sets`, but `FAlg` is never related to any functor category;
  searching for a transition function, a state machine, or an endofunction finds only
  prose in `Comonad/Core.v`, `Construction/Cayley.v` and `Instance/Lambda/Eval.v`.
- The section's concrete seven-state instance does not exist, and no worked migration of
  any kind exists.

Note for the implementer: an earlier reading of this gap claimed that the schema functor
could not be built because the in-tree graph schema is not constructed as a free category
on a quiver. That is wrong and was corrected during verification — functors *out of*
`Parallel` are routinely built by direct case analysis, and `APair` is precisely such a
functor. No re-foundation of `Parallel` is a prerequisite.

## Work to be done

Suggested module: `Instance/DDS.v` (new).

1. **The schema.** Define the loop schema as the free category on the loop quiver
   requested by the Seven Sketches §3.2.1 issue, and prove the identification: the
   functor category from it to `Sets` is equivalent to the category of setoids equipped
   with an endomorphism (equivalently, the algebras of the identity endofunctor on
   `Sets`). Deliver both functors and both natural isomorphisms.
2. **The two schema functors.** Define the functor from the graph schema to the loop
   schema sending both objects to the single object, one endpoint map to the identity and
   the other to the loop, as an application of `APair`; and its mirror image, which
   Exercise 3.67 asks for. Record the action on the two generators as lemmas so the two
   functors are distinguishable by their statements, not only by their definitions.
3. **A worked migration.** Build a concrete instance of the loop schema on a
   seven-element state setoid with an explicit transition function, then compute both
   restrictions along the two schema functors with `Induced`, and prove the resulting
   endpoint tables by computation (`eq_refl` where the carriers are finite). This is the
   first application of `Induced` to a concrete `Sets`-valued functor in the tree, and
   the issue should say so in the header.
4. **The reading.** Record, as a short lemma rather than prose, that the two restrictions
   are the two graphs on the same vertex set that present the transition function in the
   two orientations — which is exactly what makes Exercise 3.67 the mirror image of the
   worked example.

In-tree donors: `Construction/Free/Quiver.v`, `Instance/Parallel.v` (`APair`),
`Theory/Kan/Extension.v` (`Induced`), `Construction/FAlg.v`, `Instance/Sets.v`,
`Instance/FinSet.v`.

## Definition of Done

- [ ] Statements are faithful to Seven Sketches §3.4.1 (paraphrased), with setoid `≈`
      discipline throughout — never `=` on morphisms
- [ ] The instances-are-dynamical-systems identification is delivered as an equivalence
      with both round trips, not as a one-way construction
- [ ] The worked migration is *computed*, with the resulting endpoint tables proved
      rather than asserted
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for the equivalence, both
      schema functors, and the two migrated instances
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/DDS.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions dds_instances_are_endofunctions.
Print Assumptions graph_to_dds_forward.
Print Assumptions graph_to_dds_mirror.
Print Assumptions dds_example_migration.
```

Review items: the two schema functors are genuinely distinct and are proved so; the
migration is computed and not stipulated; statement matches Seven Sketches §3.4.1.

## Dependencies

Depends on: #705
Depends on: 7sketches:3.2.1:example3.13

<!-- catalog: {"ids":["7sketches:3.4.1:construction-dds-schema-functor","7sketches:3.4.1:ex3.67"],"deps":["#705","7sketches:3.2.1:example3.13"]} -->

---8<---

```yaml
title: "Seven Sketches 3.5.2: A product is exactly a terminal object in the category of cones"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:3.5.2:ex3.91]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.5.2 Exercise 3.91, printed p. 110 (PDF p. 122). Item covered:
`7sketches:3.5.2:ex3.91`.

## Background

A cone over a diagram is an object equipped with compatible maps into the diagram
([nLab: cone](https://ncatlab.org/nlab/show/cone)); a limit is precisely a terminal
object of the category of such cones
([nLab: terminal object](https://ncatlab.org/nlab/show/terminal+object)), and the binary
product is the special case of a two-object discrete shape. The exercise asks for the
identification in both directions, not merely for one implication.

## Current state in the library

The identification exists in one direction only.

- `Instance/Cones.v:29` builds `Cones F`, the category of cones over `F`.
- `Instance/Cones/Limit.v:37` proves `Limit_Cones`: from a terminal object of `Cones F`
  one obtains a `Limit F`. That file contains nothing else — it is 44 lines long.
- The converse is missing: nothing constructs a `@Terminal (Cones F)` from a `Limit F` or
  from `IsALimit F c` (`Structure/Limit.v:113,129`). So "a product *is* a terminal cone"
  is available only as the implication terminal-cone ⇒ product, never as the
  identification the exercise asks the reader to check.
- `Instance/Cones/Comma.v:73` proves `Cones F ≅[Cat] (Δ ↓ =(F))` but says nothing about
  terminality, so it does not supply the missing direction.
- `Structure/Limit/Cartesian.v:39` proves `Cartesian_Limit`, relating `Cartesian C` to
  the existence of limits of two-object discrete diagrams; with the missing direction in
  place, the exercise's binary-product reading becomes a corollary of it rather than a
  fresh proof.

## Work to be done

Suggested module: extend `Instance/Cones/Limit.v` (with the cartesian corollary next to
`Structure/Limit/Cartesian.v`).

1. **The converse.** Prove `Cones_Limit : ∀ (F : J ⟶ C), Limit F → @Terminal (Cones F)`
   — the mediating map of the limit is the unique cone morphism, and its uniqueness is
   the limit's `ump_limits` uniqueness clause read in the cone category.
2. **Round trip.** Prove the two constructions mutually inverse: composing `Limit_Cones`
   with `Cones_Limit` returns a limit whose cone is isomorphic to the one started from,
   and dually for cones. State the round trips honestly (an isomorphism of cones, not an
   equality of records).
3. **Predicate form.** Give the same statement for `IsALimit F c` (`Structure/Limit.v:129`),
   which is the form the universal-property machinery of
   `Structure/UniversalProperty/Limit.v` consumes, so the result is usable there.
4. **The exercise's instance.** For objects `x` and `y` of `C`, conclude that a terminal
   object of the cone category over the two-object discrete diagram is exactly a
   cartesian product of `x` and `y`, by composing item 3 with
   `Structure/Limit/Cartesian.v:39` rather than re-proving the product laws.

In-tree donors: `Instance/Cones.v`, `Instance/Cones/Limit.v`, `Structure/Cone.v`,
`Structure/Limit.v`, `Structure/Limit/Cartesian.v`, `Structure/Terminal.v`.

## Definition of Done

- [ ] Statement is faithful to Seven Sketches §3.5.2 Exercise 3.91 (paraphrased), with
      setoid `≈` discipline throughout — never `=` on morphisms
- [ ] The identification is delivered in *both* directions, with the round trips stated
- [ ] The binary-product case is derived from the general statement, not re-proved
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for `Cones_Limit`, the round
      trips, and the cartesian corollary
- [ ] New/changed files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Instance/Cones/Limit.v
coqc -R . Category Structure/Limit/Cartesian.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions Cones_Limit.
Print Assumptions cones_limit_roundtrip.
Print Assumptions product_is_terminal_cone.
```

Review items: the new direction is genuinely proved rather than restated from
`Limit_Cones`; the corollary consumes `Cartesian_Limit`; statement matches Seven Sketches
§3.5.2.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:3.5.2:ex3.91"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 3.5.3: Restriction along a functor is a pullback of categories of elements"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:3.5.3:remark3.100]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* (Cambridge University Press, 2019),
§3.5.3 Remark 3.100, printed p. 113 (PDF p. 125). Item covered:
`7sketches:3.5.3:remark3.100`.

## Background

The chapter uses "pullback" in two senses — the limit of a cospan, and restriction of a
set-valued functor along a functor — and the remark reconciles them: restriction really
*is* a special case, once a set-valued functor is presented by its category of elements
([nLab: category of elements](https://ncatlab.org/nlab/show/category+of+elements)), whose
projection is a discrete opfibration
([nLab: discrete fibration](https://ncatlab.org/nlab/show/discrete+opfibration)). The
book states this without proof and explicitly declines to develop it.

## Current state in the library

Both notions are present; nothing relates them.

- `Theory/Kan/Extension.v:127` (`Induced`) is restriction along a functor.
- `Theory/Morphisms/Stability.v:53` defines the apex-pinned `IsPullback` for the
  limit-of-a-cospan sense, with the pasting toolkit around it.
- `Construction/Grothendieck.v:406` builds `Grothendieck` (the total category) and `:409`
  `Grothendieck_Proj`; `Construction/Grothendieck/Fibration.v` proves the projection is a
  split opfibration. But there is no *discrete* opfibration predicate anywhere, no
  category-of-elements construction specialised to a `Sets`-valued functor, and no
  statement relating the total category of a restricted functor to a pullback of
  categories.
- Consequently the remark's reconciling claim has no in-tree counterpart in any form.

## Work to be done

Suggested modules: `Construction/Elements.v` and `Construction/Elements/Pullback.v` (new).

1. **The category of elements.** Define the category of elements of a functor
   `I : D ⟶ Sets` — objects are pairs of an object of `D` and an element of its image,
   morphisms are morphisms of `D` carrying one element to the other — together with its
   projection to `D`. Build it either directly or as the `Grothendieck` construction of
   the indexed category induced by `I`, and say in the header which route was taken and
   why.
2. **Discrete opfibrations.** Define `IsDiscreteOpfibration` (each lift is unique, not
   merely cartesian) and prove the elements projection is one. Give the converse
   construction — a discrete opfibration over `D` yields a `Sets`-valued functor — and the
   round trips. Scope this honestly: the pair of constructions with round trips is the
   deliverable; the full 2-categorical equivalence is out of scope and should be
   disclosed as such in the header.
3. **The reconciliation.** For `F : C ⟶ D` and `I : D ⟶ Sets`, prove that the square whose
   corners are the elements of the restricted functor, `C`, the elements of `I`, and `D`
   is a pullback in `Cat` — i.e. an `IsPullback` at the level of categories, over the
   pullbacks supplied by #337. This is the remark's claim, stated and proved.
4. Record in the header the terminological warning the remark exists to give: the two
   uses of "pullback" in this chapter are distinct notions that the theorem of item 3
   relates, and the library should not silently conflate them.

In-tree donors: `Construction/Grothendieck.v`, `Construction/Grothendieck/Fibration.v`,
`Construction/Indexed.v`, `Theory/Fibration.v`, `Theory/Morphisms/Stability.v`,
`Theory/Kan/Extension.v`, `Instance/Sets.v`.

## Definition of Done

- [ ] Statement is faithful to Seven Sketches §3.5.3 Remark 3.100 (paraphrased), with
      setoid `≈` discipline throughout — never `=` on morphisms
- [ ] `IsDiscreteOpfibration` is a genuine uniqueness condition on lifts, and the
      elements projection is proved to satisfy it
- [ ] The scope of the discrete-opfibration correspondence (constructions plus round
      trips, not the 2-categorical equivalence) is disclosed in the file header
- [ ] No `Admitted`/`admit`/`Axiom` (zero axioms in core theory per docs/AXIOMS.md
      scoping)
- [ ] `Print Assumptions` closed under the global context for the elements construction,
      the discrete-opfibration result, and the pullback theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (`nix build .#category-theory_8_19 .#category-theory_8_20`)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated if the result is flagship-level

## Verification

```bash
coqc -R . Category Construction/Elements.v
coqc -R . Category Construction/Elements/Pullback.v
make
make todo
nix build .#category-theory_8_19 .#category-theory_8_20
```

```coq
Print Assumptions Elements.
Print Assumptions elements_proj_discrete_opfibration.
Print Assumptions restriction_is_elements_pullback.
```

Review items: the pullback is stated in `Cat`, with the cone legs identified (an
apex-only statement would not be the theorem); the discreteness condition is uniqueness
of lifts; statement matches Seven Sketches §3.5.3 Remark 3.100.

## Dependencies

Depends on: #345
Depends on: #337

<!-- catalog: {"ids":["7sketches:3.5.3:remark3.100"],"deps":["#345","#337"]} -->

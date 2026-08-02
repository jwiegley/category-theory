```yaml
title: "MacLane App.1: Natural-numbers object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:App.1:def-nno]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician* (2nd ed.), Appendix
"Foundations", §App.1, book p. 291 (PDF p. 297). Item covered:
`maclane:App.1:def-nno`.

## Background

A natural-numbers object (NNO) is the category-theoretic axiomatization of the
natural numbers by their recursion principle: an object `N` with a global
element (zero) and an endomorphism (successor) that is initial for the
"point-plus-endomap" data, so every primitive-recursive definition determines a
unique arrow out of `N`. It is the third of the three properties Mac Lane adds
to an elementary topos to pin down a category of sets. See nLab:
https://ncatlab.org/nlab/show/natural+numbers+object and Wikipedia:
https://en.wikipedia.org/wiki/Natural_numbers_object .

## Current state in the library

The recursion universal property exists only in its general initial-algebra
form, and no natural-numbers object is defined or exhibited:

- `Theory/Recursion.v:57` provides `cata` with `cata_commutes` and
  `cata_unique` — the fold/recursor for the initial algebra `μ` of an arbitrary
  endofunctor `F`. For `F = 1 + (−)` this is exactly NNO recursion, but the
  specialization is never taken.
- `Theory/Adamek/Corollaries.v:87` defines the endofunctor `NatF := option`
  (i.e. `X ↦ 1 + X`), but its header (`:78`) explicitly disclaims the
  initial-algebra theorem: `nat ≅ μ NatF` "is not stated in the tree", so Coq's
  `nat` is never exhibited as an initial `(1 + X)`-algebra.
- `Instance/Coq/Lists.v` gives the fully worked, A-parametrized cousin
  `list A` as the initial `ListF`-algebra (`ListF A X := 1 + A × X`), of which
  `nat` is the `A := unit` reading, left un-instantiated.

A whole-tree search found no NNO object or class anywhere: no object `N` with
`zero : 1 ~> N`, `succ : N ~> N`, and the recursion universal property, in
either an arbitrary category/topos or concretely. The gap is the
natural-numbers object itself (an abstract structure plus a concrete witness),
not the recursion principle, which is already present in general form.

## Work to be done

- Define an abstract natural-numbers object in a category with a terminal object
  (suggested `Structure/NaturalNumbers.v`, new): a structure carrying `N : C`,
  `zero : 1 ~> N`, `succ : N ~> N`, and the recursion universal property — for
  every `b` with `h : 1 ~> b` and `k : b ~> b`, a unique `rec : N ~> b` with
  `rec ∘ zero ≈ h` and `rec ∘ succ ≈ k ∘ rec` (setoid `≈`, never `=`). Provide
  existence and uniqueness accessors mirroring the `cata`/`cata_unique` shape.
- Record the identification with initial `(1 + X)`-algebras: an NNO is exactly
  an initial algebra of the endofunctor `X ↦ 1 + X`, reusing
  `Theory/Recursion.v` and `Construction/FAlg.v`; give the bridge in at least
  the direction that produces the recursor.
- Exhibit a concrete witness: `Coq` (or `Sets`) has an NNO on `nat`, obtained
  from `nat` as the initial `NatF`-algebra (the result requested by Mac Lane
  I.5, filed as #252), by instantiating the `ListF` development of
  `Instance/Coq/Lists.v` at `A := unit`.
- In-tree donors: `Theory/Recursion.v` (`cata`, `cata_unique`),
  `Theory/Adamek/Corollaries.v` (`NatF`), `Construction/FAlg.v` /
  `Theory/Lambek.v`, `Structure/Terminal.v`, and `Structure/Cartesian.v` for the
  optional parametrized (topos-strength) recursion. Mac Lane states only the
  simple, non-parametrized recursion; a parametrized NNO is a reasonable
  follow-up but is out of scope here.

## Definition of Done

- [ ] Statement matches Mac Lane §App.1's NNO (zero, successor, unique
  primitive-recursion arrow), with setoid `≈` discipline and no `=` on
  morphisms.
- [ ] Abstract NNO structure defined; existence and uniqueness of the recursion
  arrow available as lemmas.
- [ ] The NNO ⟺ initial `(1 + X)`-algebra identification stated and proved (at
  least the direction giving the recursor).
- [ ] A concrete NNO witness on `Coq`/`Sets` `nat` compiles.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` reported for each
  principal artifact (concrete-instance stdlib axioms per docs/AXIOMS.md are
  acceptable in the `Instance/` witness only).
- [ ] File registered in `_CoqProject`; `make todo` adds no new hits.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- Single-file compile: `coqc -R . Category Structure/NaturalNumbers.v` and the
  witness file.
- `Print Assumptions` on the NNO structure and the concrete witness — confirm
  closed under the global context modulo the declared `Instance/` axioms.
- `make` on Rocq 9.1, plus `nix build .#category-theory_8_20`.
- Review item: the recursion equations `rec ∘ zero ≈ h` and
  `rec ∘ succ ≈ k ∘ rec` match Mac Lane §App.1 and the uniqueness clause is
  present.

## Dependencies

Depends on: #252 (Mac Lane I.5 — natural numbers as an initial algebra: supplies
the concrete `nat` witness reused here; the abstract NNO structure can be
defined independently of it).

<!-- catalog: {"ids":["maclane:App.1:def-nno"],"deps":["#252"]} -->

---8<---

```yaml
title: "MacLane App.1: ETCS — well-pointed topos with choice and a natural-numbers object"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:App.1:def5, maclane:App.1:def-well-pointed, maclane:App.1:def-ac]
deps_item_ids: [maclane:App.1:def-nno]
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician* (2nd ed.), Appendix
"Foundations", §App.1, book pp. 290-291 (PDF pp. 296-297). Items covered:
`maclane:App.1:def5` (category of sets = ETCS umbrella),
`maclane:App.1:def-well-pointed` (well-pointed topos), `maclane:App.1:def-ac`
(categorical axiom of choice).

## Background

Mac Lane defines a "category of sets" as an elementary topos with three further
properties: it is well-pointed (the terminal object is a generator — two arrows
that agree at every global point are equal), it satisfies the categorical axiom
of choice (every epimorphism/surjection splits), and it has a natural-numbers
object; together these recover Lawvere's Elementary Theory of the Category of
Sets (ETCS). See nLab: https://ncatlab.org/nlab/show/ETCS ,
https://ncatlab.org/nlab/show/well-pointed+topos ,
https://ncatlab.org/nlab/show/axiom+of+choice ; Wikipedia:
https://en.wikipedia.org/wiki/Elementary_Theory_of_the_Category_of_Sets ,
https://en.wikipedia.org/wiki/Axiom_of_choice .

## Current state in the library

The elementary-topos genus is present and even witnessed, but none of the three
ETCS differentiae is formalized, and no structure bundles them:

- Genus (present): `Structure/Topos.v:112` `ElementaryTopos` (terminal +
  cartesian + pullbacks + closed + subobject classifier), witnessed concretely
  by `Instance/FinSet/Topos.v` `FinSet_Topos`. The ETCS reference at
  `Theory/Metacategory.v:78-80` is Lawvere-1964 background prose, not structure.
- Well-pointedness (terminal object a generator/separator): missing. The only
  `WellPointed` in-tree is `Instance/Fun.v:240`, a well-pointed pointed
  *endofunctor* — an unrelated false friend. `Structure/Terminal.v:66-68`
  mentions "1 is a generator" only in its background essay. No
  `Separator`/`Generator` class exists; `Adjunction/SAFT.v:99` `Cogenerator`
  (`cog_separates`) is the *dual* notion, over a *family* of objects, not the
  terminal-object separator.
- Categorical axiom of choice (every epi splits): only the per-morphism
  vocabulary exists — `Theory/Morphisms.v:70` `Retraction`
  (`retract_comp : f ∘ retract ≈ id`), `:126` `SplitEpi := Retraction`, `:162`
  `retractions_are_epic`. There is no category-level statement or class
  `∀ x y (f : x ~> y), Epic f -> Retraction f`, and no choice-satisfying-category
  structure.
- Natural-numbers object: only partial (general recursion plus the list initial
  algebra); this is the subject of the dependency issue below.

The whole compound "category of sets"/ETCS structure — bundling the topos with
well-pointedness, choice, and an NNO — is absent (a structural sweep for
`ETCS`/`CategoryOfSets`/well-pointed-topos classes returned nothing but the
prose above).

## Work to be done

- Define a general separator/generator and well-pointedness (suggested
  `Structure/Separator.v`, new, or folded into the ETCS file): `Separator G` —
  for parallel `f g : x ~> y`, if `f ∘ e ≈ g ∘ e` for all `e : G ~> x` then
  `f ≈ g`; then `WellPointed C := Separator 1` for the terminal object `1`.
  (Coordinate the vocabulary with #447, which requests a separating *family*;
  well-pointedness is the single-object, terminal-object case — reuse a shared
  `Separator` where practical rather than duplicating it.)
- Define the categorical axiom of choice as a category-level property (suggested
  `Structure/Choice.v`, new, or folded in): `InternalAC C :=
  ∀ x y (f : x ~> y), Epic f -> Retraction f` (every epi splits), reusing the
  existing `Retraction`/`Epic` vocabulary from `Theory/Morphisms.v`.
- Bundle the ETCS structure (suggested `Structure/CategoryOfSets.v`, new):
  `CategoryOfSets C := ElementaryTopos C + WellPointed C + InternalAC C +
  NaturalNumbersObject C` (the NNO from the dependency issue), with accessors
  and setoid `≈` throughout.
- In-tree donors: `Structure/Topos.v` (`ElementaryTopos`), `Theory/Morphisms.v`
  (`Retraction`, `Epic`, `SplitEpi`), `Adjunction/SAFT.v` (`Cogenerator`, the
  dual pattern to mirror), `Structure/Terminal.v`.
- A concrete `CategoryOfSets` witness is not required by this issue (the full
  category of sets faces the documented predicative size obstruction at
  `Instance/Sets/Classifier.v`); state the structure and, where feasible,
  sanity-check the individual differentiae against an available topos witness.

## Definition of Done

- [ ] Statements match Mac Lane §App.1: well-pointed (1 separates parallel
  arrows), AC (every epi has a section), and the ETCS bundle (topos + those two
  + NNO); setoid `≈` discipline, never `=` on morphisms.
- [ ] `Separator`/`WellPointed` defined; `InternalAC` defined; `CategoryOfSets`
  bundles topos + well-pointed + choice + NNO.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` reported for each
  principal artifact (closed under the global context).
- [ ] Files registered in `_CoqProject`; `make todo` adds no new hits.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- Single-file compile of each new file: `coqc -R . Category
  Structure/Separator.v`, `.../Choice.v`, `.../CategoryOfSets.v`.
- `Print Assumptions CategoryOfSets.` (and `WellPointed`, `InternalAC`) —
  closed under the global context.
- `make` on Rocq 9.1; `nix build .#category-theory_8_20`.
- Review items: `WellPointed` = "1 is a separator" matches §App.1(a);
  `InternalAC` = "every epi splits" matches §App.1(b); the bundle's fourth
  conjunct is the NNO of the dependency, matching §App.1(c).

## Dependencies

Depends on: maclane:App.1:def-nno (the natural-numbers object — ETCS's third
differentia, drafted as a separate issue in this batch).

<!-- catalog: {"ids":["maclane:App.1:def5","maclane:App.1:def-well-pointed","maclane:App.1:def-ac"],"deps":["maclane:App.1:def-nno"]} -->

---8<---

```yaml
title: "MacLane App.1: A two-valued subobject classifier is a Boolean algebra"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:App.1:remark-boolean]
deps_item_ids: []
deps_pending: []
```

## Source

Mac Lane, *Categories for the Working Mathematician* (2nd ed.), Appendix
"Foundations", §App.1, book p. 291 (PDF p. 297). Item covered:
`maclane:App.1:remark-boolean`.

## Background

In an elementary topos the subobject classifier `Ω` carries an internal
Heyting-algebra structure. Mac Lane remarks that when `Ω` has just two global
elements (`Ω ≅ 1 + 1`, i.e. the topos is two-valued) this internal algebra is
Boolean — the topos is classical. See nLab:
https://ncatlab.org/nlab/show/Boolean+topos and
https://ncatlab.org/nlab/show/two-valued+topos .

## Current state in the library

No object in the library carries an internal lattice/Heyting/Boolean-algebra
structure, and the theorem is absent:

- The classifier is present as a bare object: `Structure/SubobjectClassifier.v:44`
  `SubobjectClassifier` gives `Ω`, `truth : 1 ~> Ω`, `char`, `char_pullback`,
  `char_unique` — but `Ω` carries no internal algebraic operations.
- `Structure/Topos.v:81` states in prose only that a topos's subobjects "form a
  Heyting algebra rather than a Boolean one"; `Instance/Sets/Par.v:18` says
  "(a Boolean topos)" in passing. Neither formalizes anything.
- `Instance/Two.v:85-87` treats the two-element Boolean algebra as an
  *enriching base* concept, not as structure on a classifier.
- Whole-tree searches for `Boolean`/`Heyting`/`Lattice` *classes* or a
  "two-valued `Ω` ⇒ Boolean" theorem returned nothing (only the prose above,
  plus `Instance/FinSet/Classifier.v`'s decidable/boolean-valued `char`, which
  is the characteristic map — not `Ω`-as-Boolean-algebra).

## Work to be done

- Introduce internal (bounded) lattice / Heyting / Boolean-algebra structure on
  an object of a cartesian(-closed) category (suggested
  `Structure/BooleanAlgebra.v` and/or `Structure/HeytingAlgebra.v`, new, or
  `Structure/Topos/InternalLogic.v`): the internal operations `⊤`, `⊥`, `∧`,
  `∨`, `⇒`, `¬` with their equational laws stated via `≈`.
- Equip the classifier `Ω` with its internal Heyting operations (from the
  subobject-lattice / classifying-map structure), giving the internal logic of
  the topos.
- Define "two-valued classifier" (`Ω ≅ 1 + 1` through `truth` and a
  `false : 1 ~> Ω`) and prove that then the internal algebra on `Ω` satisfies
  the Boolean laws (complementation / excluded middle: `¬¬ ≈ id`,
  `x ∨ ¬x ≈ ⊤`).
- In-tree donors: `Structure/SubobjectClassifier.v` (`Ω`, `truth`, `char`),
  `Structure/Cartesian.v` and `Structure/Cartesian/Closed.v` (products,
  exponentials for `⇒`), `Structure/Cocartesian.v` (for `1 + 1`),
  `Structure/Topos.v` (the ambient topos), `Instance/Two.v` (the external
  two-element Boolean algebra as a sanity target).

## Definition of Done

- [ ] Statement matches Mac Lane §App.1's remark: a two-valued classifier (`Ω`
  with exactly two global elements) is a Boolean algebra; setoid `≈` discipline,
  never `=` on morphisms.
- [ ] Internal Heyting/Boolean-algebra structure on an object defined; `Ω`
  equipped with its internal operations.
- [ ] "Two-valued ⇒ Boolean" proved (excluded middle / double-negation).
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` reported for each
  principal artifact (closed under the global context).
- [ ] File(s) registered in `_CoqProject`; `make todo` adds no new hits.
- [ ] Full `make` green on Rocq 9.1; builds on Coq 8.19/8.20 (nix targets).
- [ ] CLAUDE.md Key Files index updated if judged flagship-level.

## Verification

- Single-file compile: `coqc -R . Category Structure/BooleanAlgebra.v` and the
  `Ω`-internal-logic / two-valued file.
- `Print Assumptions` on the internal-algebra structure and the "two-valued ⇒
  Boolean" theorem — closed under the global context.
- `make` on Rocq 9.1; `nix build .#category-theory_8_20`.
- Review item: the hypothesis is exactly "`Ω` has two global elements"
  (`Ω ≅ 1 + 1`) and the conclusion is the Boolean-algebra laws, matching
  §App.1.

## Dependencies

None (builds on the in-tree `SubobjectClassifier`, which is already present).

<!-- catalog: {"ids":["maclane:App.1:remark-boolean"],"deps":[]} -->

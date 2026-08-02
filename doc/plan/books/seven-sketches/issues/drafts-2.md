```yaml
title: "Seven Sketches 2.2: Symmetric monoidal preorders — the class, strict versus weak axioms, and the thin-category reading of the induced equivalence"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.1:def2, 7sketches:2.2.1:remark3]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.1 "Symmetric monoidal
preorders" — Definition 2.2 and Remark 2.3. Printed pp. 41–42; PDF pp. 53–54.
Items covered: `7sketches:2.2.1:def2`, `7sketches:2.2.1:remark3`.

## Background

A monoidal preorder is a preordered set carrying a unit element and a monotone
binary operation that is unital, associative and (in the symmetric case)
commutative; because the underlying category is thin, no coherence data is
carried and the monoidal axioms degenerate to properties
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[nLab: thin category](https://ncatlab.org/nlab/show/thin+category)). It is the
base of enrichment for the whole of Chapter 2, and is the (0,1)-truncation of a
symmetric monoidal category
([nLab: symmetric monoidal category](https://ncatlab.org/nlab/show/symmetric+monoidal+category)).

## Current state in the library

All four ingredients exist separately, and nothing assembles them:

- `Structure/Monoidal.v:125` — `Class Monoidal`, with `unit_left`, `unit_right`
  and `tensor_assoc` stated as *isomorphisms* at lines 129–132, plus the
  triangle and pentagon laws. Clause (a) of the book's definition (monotonicity
  in both arguments) is exactly bifunctoriality of the tensor,
  `Functor/Bifunctor.v:38` (`bimap`).
- `Structure/Monoidal/Strict.v:52` — `Class StrictMonoidal`, which adds the
  *object* equalities `strict_assoc_obj` (:56), `strict_unit_left_obj`,
  `strict_unit_right_obj`, together with `strict_assoc_to` (:73) and the two
  unitor counterparts identifying the weak structure's isomorphisms with
  transported identities. There is **no object-level commutativity field**, so
  clause (d) of the book's definition (`x ⊗ y = y ⊗ x` on the nose) cannot be
  demanded of any in-tree class.
- `Structure/Monoidal/Symmetric.v:103` — `Class SymmetricMonoidal`, symmetry as
  an involutive braiding, i.e. weaker than the book's element equality.
- `Instance/Proset.v:33` — `Proset`, a preorder as a thin category
  (`hom x y := R x y`, all parallel arrows identified);
  `Instance/Poset.v:116` for the poset variant.

Gap, precisely: there is no `MonoidalPreorder` / `SymmetricMonoidalPreorder`
notion, and no `Monoidal` instance over any `Proset`. The only thin categories
that carry a monoidal structure are `_2` (`Instance/Two/Monoidal.v:105`,
`Two_Monoidal := @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal`) and, only
implicitly, `Props` (`Instance/Props.v:69,53`) — both cartesian, tensor = meet,
unit = top. No non-cartesian monoidal preorder exists anywhere, and neither
instance is declared `SymmetricMonoidal` (`CC_SymmetricMonoidal`,
`Structure/Monoidal/Internal/Product.v:314`, would supply it but is never
applied to a thin category). For Remark 2.3: the library's *primary* class is
already the weak (up-to-isomorphism) notion the remark endorses, but nothing
proves the remark's claim that weak and strict are interchangeable — there is no
monoidal strictification/coherence theorem (Mac Lane coherence is cited in prose
only, `Structure/Monoidal.v:43`, `Structure/Monoidal/Proofs.v:16`) — and no
lemma anywhere states that in a thin category an isomorphism `x ≅ y` is exactly
the pair `x ≤ y`, `y ≤ x` (`Instance/Proset.v:25` says it in a comment).

## Work to be done

Suggested module: `Structure/Monoidal/Preorder.v`.

1. Define the class of a (symmetric) monoidal preorder over a thin base. Two
   presentations are wanted, matching the book's Definition 2.2 and its
   Remark 2.3 relaxation:
   - the **strict** form, whose unit/associativity/commutativity clauses are
     equalities of elements — this requires adding an object-level
     commutativity field for clause (d), which `StrictMonoidal`
     (`Structure/Monoidal/Strict.v:52`) does not have; add it there as an
     optional mixin (e.g. `StrictSymmetricMonoidal`) rather than to the base
     class, so existing instances are unaffected;
   - the **weak** form, obtained by instantiating `Monoidal` +
     `SymmetricMonoidal` at a `Proset`, where every coherence law is
     automatically satisfied because the base is thin.
2. Prove the bridge Remark 2.3 asserts: over a thin category the two forms
   agree, i.e. a strict monoidal preorder yields the weak one, and the weak one
   yields the strict one after passing to the quotient by mutual `≤`
   (equivalently: strictness is recovered on a skeletal preorder). Note that the
   general monoidal strictification theorem is a separate, much larger obligation
   (#609) and is deliberately *not* a prerequisite here: over a thin base the
   comparison is elementary.
3. Prove the missing thinness lemma the whole reading rests on: in a thin
   category `x ≅ y` iff `x ~> y` and `y ~> x` are both inhabited, so an
   isomorphism *is* the preorder's induced equivalence. Site it with the
   thinness machinery (`Instance/Two/Monoidal.v:26` `two_thin` is the two-object
   special case) or in `Instance/Proset.v` next to the comment at line 25.
4. Provide the smart constructor that takes a preorder, a unit, a binary
   operation and clauses (a)–(d) and returns the packaged structure, so the
   downstream instances (the reals, ℕ, divisibility, Cost, Bool, the powerset)
   are one-liners.

In-tree donors: `Instance/Proset.v:33`, `Structure/Monoidal.v:125`,
`Structure/Monoidal/Strict.v:52`, `Structure/Monoidal/Symmetric.v:103`,
`Structure/Monoidal/Internal/Product.v:54,314` (`CC_Monoidal` /
`CC_SymmetricMonoidal` for the cartesian case), `Construction/PROP.v:119–127`
(an existing in-tree precedent for object-level strictness equalities).

## Definition of Done

- [ ] Class fields correspond one-to-one to clauses (a)–(d) of Seven Sketches
      Definition 2.2 (printed p. 41), with the setoid discipline respected:
      `≈` on morphisms, never `=`.
- [ ] Both the strict and the weak presentation exist, and the comparison
      between them (Remark 2.3, printed p. 42) is proved, not asserted.
- [ ] The thin-category lemma "`x ≅ y` iff `x ≤ y` and `y ≤ x`" is proved and
      exported.
- [ ] A smart constructor builds the structure from a preorder plus clauses
      (a)–(d), and is exercised on at least one witness (`_2` with meet/top is
      acceptable as the smoke test).
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the new class and on the comparison theorem
      reports "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md "Key Files and Concepts" updated — this is flagship-level: it
      opens the monoidal-preorder/enrichment spine that the rest of Seven
      Sketches Chapter 2 hangs off.

## Verification

```
coqc -R . Category Structure/Monoidal/Preorder.v
```
then, in `coqtop -R . Category`:
```
Require Import Category.Structure.Monoidal.Preorder.
Print Assumptions SymmetricMonoidalPreorder.
```
followed by `make` and `nix build .#category-theory_8_20`. Reviewer checklist:
(i) the class demands monotonicity, unitality, associativity and commutativity
and nothing else — no coherence data, as Seven Sketches Definition 2.2 requires;
(ii) the strict/weak comparison really is a two-way statement; (iii) the thin-iso
lemma is stated for an arbitrary thin category, not just `_2`.

## Dependencies

Depends on: #223 (preorders as thin categories, which supplies the thin-category
vocabulary this class is stated over).

<!-- catalog: {"ids":["7sketches:2.2.1:def2","7sketches:2.2.1:remark3"],"deps":["#223"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Every commutative monoid is a symmetric monoidal preorder on its discrete order"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.1:example6, 7sketches:2.2.1:ex8]
deps_item_ids: [7sketches:2.2.1:def2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.1 — Example 2.6 (the
recollection of "monoid" and the discrete-preorder construction) and
Exercise 2.8 (verify it). Printed pp. 42–43; PDF pp. 54–55. Items covered:
`7sketches:2.2.1:example6`, `7sketches:2.2.1:ex8`.

## Background

On a discrete preorder (`m ≤ n` iff `m = n`) monotonicity of any operation is
automatic, so a commutative monoid structure on the carrier is *exactly* a
symmetric monoidal preorder structure
([nLab: commutative monoid](https://ncatlab.org/nlab/show/commutative+monoid),
[nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder)).
This is the degenerate end of the spectrum whose other end is Cost, and it is
the cheapest witness that the monoidal-preorder axioms are satisfiable.

## Current state in the library

Both halves exist and are never joined:

- `Instance/CMon.v:32` — `Record CMonObject`, a setoid-level commutative monoid
  with `cmon_plus_assoc`, `cmon_plus_comm`, `cmon_plus_zero_l` and the derived
  `cmon_plus_zero_r` (`Instance/CMon.v:49`). These are literally clauses
  (b), (c), (d) of the book's Definition 2.2, available as proved laws.
- `Instance/Discrete.v:37` — `DiscreteCat A` with `hom x y := x = y`, certified
  discrete by `DiscreteCat_Discrete` (`Instance/Discrete.v:65`);
  `DiscreteCat_Functor` (`Instance/Discrete.v:52`) is the in-tree form of
  clause (a): every object assignment out of a discrete category is
  automatically functorial.
- `Structure/Monoid.v:124` — `Class MonoidObject`, the internal
  (cartesian-monoidal) monoid.

Gap: no `Monoidal` (nor `StrictMonoidal` / `SymmetricMonoidal`) structure is
built on `DiscreteCat A` from a monoid; `DiscreteCat` is used only for discrete
diagrams (`Structure/Limit/Product.v`, `Theory/WeaklyInitial.v`,
`Functor/Diagonal.v`). Three concrete obstructions: (i) the tensor needs either a
comparison `DiscreteCat (A * A) ≅ DiscreteCat A ∏ DiscreteCat A` or a direct
bifunctor — neither exists, `DiscreteCat_Functor` handling only a single
discrete source; (ii) clause (d) would be the object equality `m * n = n * m`,
for which `StrictMonoidal` (`Structure/Monoidal/Strict.v:52`) has no field;
(iii) `CMonObject`'s laws hold up to the carrier setoid's `≈` while
`DiscreteCat`'s homs are Leibniz equalities, so the carrier must be transported
first (or the construction stated for a monoid on a `Type` with Leibniz
equality).

## Work to be done

Suggested module: `Instance/Discrete/Monoidal.v` (or a section of
`Instance/CMon.v` if the transport is done there).

1. Build the bifunctor `DiscreteCat A ∏ DiscreteCat A ⟶ DiscreteCat A` for a
   commutative monoid operation on `A`, either directly or through a
   `DiscreteCat (A * A) ≅ DiscreteCat A ∏ DiscreteCat A` comparison worth having
   on its own.
2. Assemble the strict symmetric monoidal preorder of Seven Sketches §2.2.1 on
   the discrete order: unit the monoid unit, tensor the monoid operation,
   clauses (b)/(c)/(d) as the object-level equalities. This exercises the
   object-level commutativity field requested by the monoidal-preorder class
   issue.
3. Resolve the setoid-vs-Leibniz mismatch explicitly: either state the
   construction for a commutative monoid over a `Type` with Leibniz equality and
   derive the `CMonObject` case by transport along the carrier setoid, or build
   the discrete category of a setoid.
4. Record Exercise 2.8's four checks as named lemmas (monotonicity, unit,
   associativity, commutativity) so the verification the exercise asks for is
   visible rather than hidden inside a `Program` obligation.

In-tree donors: `Instance/CMon.v:32,49`, `Instance/Discrete.v:37,52,65`,
`Structure/Monoidal/Strict.v:52`, `Construction/PROP.v:119–127` (object-level
strictness equalities already carried in-tree).

## Definition of Done

- [ ] The construction matches Example 2.6 (printed p. 42): discrete order,
      monoid unit, monoid operation, and monotonicity discharged because the
      order is discrete.
- [ ] Exercise 2.8's clauses (a)–(d) appear as named, individually citable
      lemmas.
- [ ] The setoid/Leibniz transport is performed, not assumed away.
- [ ] Statements use `≈` on morphisms, never `=` (object-level equalities are of
      course allowed, being the point of strictness).
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the resulting instance reports "Closed under the
      global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Discrete/Monoidal.v
```
then
```
Require Import Category.Instance.Discrete.Monoidal.
Print Assumptions Discrete_SymmetricMonoidalPreorder.
```
plus `make` and `nix build .#category-theory_8_19`. Reviewer checklist: the
tensor really is the monoid operation (not a product), the unit really is the
monoid unit, and the statement matches Seven Sketches Example 2.6/Exercise 2.8
(printed pp. 42–43).

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the symmetric monoidal preorder class, whose
object-level commutativity field this instance needs).

<!-- catalog: {"ids":["7sketches:2.2.1:example6","7sketches:2.2.1:ex8"],"deps":["7sketches:2.2.1:def2"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Refuting a proposed monoidal structure — the failure of monotonicity for poker hands and for multiplication on the reals"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.1:example9, 7sketches:2.2.1:ex5]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.2.1:example4]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.1 — Exercise 2.5
(multiplication is not a monoidal product for the usual order on the reals) and
Example 2.9 (the poker-hand non-example). Printed pp. 42–43; PDF pp. 54–55.
Items covered: `7sketches:2.2.1:ex5`, `7sketches:2.2.1:example9`.

## Background

Clause (a) of a monoidal preorder — monotonicity of the tensor in both arguments
— is the one clause that is not automatic, and the book makes the point twice
with refutations: multiplying by a negative real reverses the order, and the
"best five of ten cards" operation on poker hands is not monotone for the
beats-or-ties order
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[Wikipedia: List of poker hands](https://en.wikipedia.org/wiki/List_of_poker_hands)).

## Current state in the library

There is no in-tree idiom for refuting a proposed structure at all. Searches for
`counterexample`/`countermodel`/`non-example` return five hits
(`Construction/Indexed.v:59`, `Construction/Funny/Bifunctor.v:26`,
`Structure/Terminal.v:79`, `Structure/Monoidal.v:74`, `Adjunction/GAFT.v:121`)
and every one is prose; none refutes a proposed tensor, and there is no
statement of the form `¬ @Monoidal C` anywhere. The nearest formal precedents are
`Instance/Sets/Par.v:240,269` (`to_from_impossible` / `from_to_impossible`,
refuting one candidate currying pair for `Par` under inhabitance hypotheses) and
the 2-cocycle countermodel of `Theory/Displayed.v` — both useful patterns, neither
about monoidality. Neither carrier exists either: the library imports no real
numbers (0 hits for `Reals`, `Rdefinitions`, `Rplus`, `Rle`, `QArith`) and has no
playing-card or poker vocabulary (every `card` hit is `cardinal`/`discard`/
`wildcard`).

## Work to be done

Suggested modules: `Instance/Poker.v` for the poker carrier and its refutation;
the reals refutation belongs next to the real-ordered-carrier instance requested
by the Seven Sketches §2.2.1 reals issue.

1. Fix the shape of a refutation. The cleanest form that avoids quantifying over
   the whole class is a lemma refuting *the monotonicity clause for a named
   operation*: `¬ ∀ x1 y1 x2 y2, x1 ≤ y1 → x2 ≤ y2 → op x1 x2 ≤ op y1 y2`,
   exhibited by an explicit witness. Add, in the same place, the derived
   statement that no `Monoidal` structure on the thin category of the preorder
   has that operation as its tensor (bifunctoriality would give monotonicity).
2. Multiplication on the ordered reals: refute monotonicity with the book's
   witness (`-1 ≤ 0` twice, whence `1 ≤ 0` would follow).
3. Poker hands: define a five-card-hand carrier over a 52-card deck with a
   decidable beats-or-ties preorder and the "best five of the ten cards, with
   duplicates discarded" operation, then refute monotonicity with the book's
   explicit pair of hands. Build the preorder through `Instance/Proset.v:33`
   from a decidable relation; keep the hand-ranking function separate and
   total so the refutation is a computation.
4. State once, as the moral of both, that clause (a) of Seven Sketches
   Definition 2.2 is independent of the remaining clauses.

In-tree donors: `Instance/Proset.v:33`, `Functor/Bifunctor.v:38` (`bimap`, the
in-tree form of monotonicity), `Instance/Sets/Par.v:240,269` (the impossibility
idiom), `Instance/FinSet.v` and `Instance/FinSet/Topos.v` (precedents for
finite, `eq_refl`-computing examples).

## Definition of Done

- [ ] The reals refutation matches Exercise 2.5 (printed p. 42), and the poker
      refutation matches Example 2.9 (printed p. 43), including the book's
      witnesses.
- [ ] Both refutations are stated as theorems about a named operation, with the
      corollary that no monoidal structure on the corresponding thin category
      has that operation as its tensor.
- [ ] The poker preorder is proved reflexive and transitive, and its hand
      comparison is decidable so the counterexample computes.
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] Any use of `Coq.Reals` is confined to the `Instance/` layer, and
      docs/AXIOMS.md is extended with the stdlib axioms it introduces (the
      core-theory zero-axiom scope must stay untouched); `Print Assumptions`
      output for the affected artifacts is recorded there.
- [ ] `Print Assumptions` on the poker refutation reports "Closed under the
      global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Poker.v
```
then
```
Require Import Category.Instance.Poker.
Print Assumptions poker_tensor_not_monotone.
Compute (* the two witness hands and their combination *).
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
counterexamples are the book's; the refutations are genuine negations, not
hypotheses; and the reals file's axiom footprint is disclosed in docs/AXIOMS.md.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class the refutations are
stated against).
Depends on: 7sketches:2.2.1:example4 (the ordered additive reals, whose carrier
the multiplication refutation needs).

<!-- catalog: {"ids":["7sketches:2.2.1:example9","7sketches:2.2.1:ex5"],"deps":["7sketches:2.2.1:def2","7sketches:2.2.1:example4"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: The ordered-commutative-monoid recipe, and the reals under addition as a symmetric monoidal preorder"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.1:example4]
deps_item_ids: [7sketches:2.2.1:def2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.1 — Example 2.4, the
reals with their usual order, unit `0` and product `+`. Printed p. 42; PDF
p. 54. Item covered: `7sketches:2.2.1:example4`.

## Background

Every commutative monoid whose operation is monotone for a given preorder is a
symmetric monoidal preorder; the ordered additive reals are the book's leading
example and the ancestor of Cost
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[nLab: symmetric monoidal category](https://ncatlab.org/nlab/show/symmetric+monoidal+category)).
Formalizing the recipe once pays for the numeric instances of §2.2.4, for Cost,
and for the metric-space material of §2.3.3.

## Current state in the library

The library imports no real numbers and no rationals at all: searches for
`Reals`, `Rdefinitions`, `Rplus`, `Rle`, `R_scope`, `QArith` return 0 hits, and
the only textual occurrences of "reals" are background prose
(`Construction/Enriched.v:74`, `Instance/Poset.v:75`,
`Construction/Karoubi.v:87`). The order-theoretic carriers that do exist —
`Instance/Proset.v:47` (`LessThanEqualTo_Category := @Proset nat Nat.le _`),
`Instance/Poset.v:120`, `Instance/Omega.v:72` (`Omega`, ℕ under a Type-valued
`le_t`) — carry no monoidal structure: `Monoidal` has no instance over any of
them. Nor is there a generic "ordered commutative monoid ⇒ symmetric monoidal
preorder" construction under any name (0 hits for `OrderedMonoid`,
`ordered monoid`, `PoMonoid`, `monoidal preorder`). So neither the recipe nor the
instance exists; only the preorder-as-thin-category machinery does
(`Instance/Proset.v:33`). Note the near-miss to avoid crediting: `(ℕ, +, 0)` does
appear as a symmetric monoidal structure on nat-*objects*
(`Instance/FinSet.v:250` `FinSet_Cocartesian`, `Instance/Shapes.v:429`
`Vectors_Cartesian`), but those categories' morphisms are functions and vectors,
not `≤`.

## Work to be done

Suggested modules: `Structure/Monoidal/Preorder/OrderedMonoid.v` for the recipe,
`Instance/Reals/Order.v` for the carrier and the instance.

1. State and prove the recipe: given a preorder on `A`, a unit `e : A`, an
   operation `op : A → A → A` that is monotone in both arguments, and the
   unit/associativity/commutativity equations, produce the symmetric monoidal
   preorder of Seven Sketches §2.2.1. This is the smart constructor the class
   issue calls for, specialized to the "ordered commutative monoid" packaging,
   and it is the dependency target for every numeric base later in the chapter.
2. Introduce the ordered additive reals as an `Instance/` carrier
   (`Coq.Reals.Rdefinitions` + `RIneq`), with `Rle` as the preorder relation,
   and derive the thin category through `Instance/Proset.v:33`.
3. Instantiate the recipe at `(ℝ, ≤, 0, +)` and record the four clauses of
   Definition 2.2 as named lemmas, so Example 2.4's verification is visible.
4. Disclose the axiom footprint. Coq's stdlib reals are axiomatic; the file must
   live in the `Instance/` layer, which docs/AXIOMS.md already scopes as
   permitted to use stdlib axioms, and docs/AXIOMS.md must be extended with the
   axioms this pulls in. The core-theory zero-axiom claim must remain literally
   true.

In-tree donors: `Instance/Proset.v:33`, `Structure/Monoidal.v:125`,
`Structure/Monoidal/Symmetric.v:103`, `Structure/Monoidal/Internal/Product.v:54`
(the cartesian analogue of the recipe), `Instance/Omega.v:72` (the existing
numeric preorder, as a style precedent).

## Definition of Done

- [ ] The recipe is stated for an arbitrary ordered commutative monoid and
      proved once; the reals are an instance of it, not a bespoke construction.
- [ ] `(ℝ, ≤, 0, +)` satisfies clauses (a)–(d) of Seven Sketches Definition 2.2
      (printed p. 41), each recorded as a named lemma, matching Example 2.4
      (printed p. 42).
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` written by hand in the new files.
- [ ] The reals file lives under `Instance/`; docs/AXIOMS.md is extended with
      the stdlib axioms it introduces and with the `Print Assumptions` output of
      the new instance; the recipe itself (which is axiom-free) is verified
      "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md "Key Files and Concepts" updated: the arrival of a numeric,
      non-cartesian base changes what the enrichment layer can witness.

## Verification

```
coqc -R . Category Structure/Monoidal/Preorder/OrderedMonoid.v
coqc -R . Category Instance/Reals/Order.v
```
then
```
Require Import Category.Structure.Monoidal.Preorder.OrderedMonoid.
Print Assumptions OrderedMonoid_SymmetricMonoidalPreorder.
Require Import Category.Instance.Reals.Order.
Print Assumptions Reals_Additive_MonoidalPreorder.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
recipe's hypotheses are exactly clauses (a)–(d); the reals instance adds no
axioms beyond those recorded in docs/AXIOMS.md; nothing under `Theory/`,
`Structure/` or `Construction/` acquires a real-number dependency.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class this recipe
produces).
Depends on: #759 (the reals as an ordered carrier).

<!-- catalog: {"ids":["7sketches:2.2.1:example4"],"deps":["7sketches:2.2.1:def2","#759"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Monoidal structures on the arithmetic preorders — ℕ with + and ·, divisibility with ·, and the failures for + on divisibility and · on ℤ"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.4:example30, 7sketches:2.2.4:ex31, 7sketches:2.2.4:example32, 7sketches:2.2.4:ex33, 7sketches:2.2.5:ex45]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.2.1:example4, 7sketches:2.2.5:def41]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.4 — Example 2.30
(ℕ with addition), Exercise 2.31 (ℕ with multiplication), Example 2.32
(divisibility with multiplication), Exercise 2.33 (divisibility with addition is
not monoidal) — and §2.2.5 Exercise 2.45 (the multiplicative preorders on ℕ and
ℤ, and a monoidal monotone between the two structures on ℕ). Printed
pp. 53–54, 56; PDF pp. 65–66, 68. Items covered: `7sketches:2.2.4:example30`,
`7sketches:2.2.4:ex31`, `7sketches:2.2.4:example32`, `7sketches:2.2.4:ex33`,
`7sketches:2.2.5:ex45`.

## Background

One preorder can carry several monoidal structures, and one operation can be
monoidal for one order and not another: `(ℕ, ≤)` carries both `+` (unit 0) and
`·` (unit 1); `·` is also monoidal for divisibility (unit 1), while `+` is not;
and on `ℤ` multiplication fails monotonicity outright
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[Wikipedia: Divisibility](https://en.wikipedia.org/wiki/Divisibility_(ring_theory))).

## Current state in the library

Only the carrier `(ℕ, ≤)` exists, twice over: `Instance/Proset.v:47`
(`LessThanEqualTo_Category := @Proset nat PeanoNat.Nat.le Nat.le_preorder`), the
poset twin at `Instance/Poset.v:120`, and `Instance/Omega.v:72` (`Omega`, with a
Type-valued `le_t`). None of them carries a tensor: there is no bifunctor
`Omega ∏ Omega ⟶ Omega` with `fobj := Nat.add` or `Nat.mul`, no unit object, and
no `@Monoidal` instance — outside its own file `Omega` is used only as the ω-chain
shape (`Construction/Chain.v`, `Theory/Adamek*.v`, `Construction/FAlg.v`).
Monotonicity of `+` or `·` with respect to `≤` is never stated: `add_le_mono`,
`mul_le_mono`, `le_mono` all return 0 hits. Divisibility does not exist at all
(`Nat.divide`: 0 hits; `gcd`/`lcm`: 0 hits; the two `divis`/`divide` hits are
unrelated prose at `Instance/Coq.v:72` and `Structure/Cartesian.v:70`), and
neither do the integers (`ZArith`, `BinInt`: 0 hits). `LaxMonoidalFunctor`
(`Functor/Structure/Monoidal.v:110`) exists but is instantiated only at `Id`
(`Functor/Structure/Monoidal/Id.v:73`) and `Compose`
(`Functor/Structure/Monoidal/Compose.v:291`), so Exercise 2.45's requested map
has no in-tree relatives either. Near-miss to avoid crediting: `(ℕ, +, 0)` is a
monoidal structure on nat-*objects* in `Instance/FinSet.v:250` and
`Instance/Shapes.v:429`, but those homs are functions and vectors, not `≤`.

## Work to be done

Suggested modules: `Instance/Nat/Monoidal.v` (both structures on `(ℕ, ≤)`),
`Instance/Nat/Divisibility.v` (the divisibility base and the `+` non-example),
`Instance/Int/Order.v` (the ℤ clause of Exercise 2.45).

1. Prove monotonicity of `Nat.add` and `Nat.mul` for `≤` (from
   `PeanoNat.Nat.add_le_mono` / `mul_le_mono`) and feed both into the
   ordered-commutative-monoid recipe to get `(ℕ, ≤, 0, +)` and `(ℕ, ≤, 1, ·)`.
   State explicitly that these are two distinct monoidal structures on one
   preorder — the point Example 2.30 and Exercise 2.31 make jointly.
2. Put the divisibility preorder (from the issue that files it, see
   Dependencies) into the recipe with unit 1 and tensor `·`, proving
   monotonicity by the book's argument (`x₁ · p₁ = y₁`, `x₂ · p₂ = y₂` give
   `(x₁·x₂) · (p₁·p₂) = y₁·y₂`).
3. Refute Exercise 2.33: `+` is not monotone for divisibility — a named negation
   with an explicit witness, in the refutation shape set by the non-examples
   issue.
4. Exercise 2.45: (i) the multiplicative structure on ℕ from step 1;
   (ii) exhibit a monoidal monotone `(ℕ, ≤, 0, +) → (ℕ, ≤, 1, ·)` (e.g.
   `n ↦ 2^n`, which is strict) using the preorder-level monoidal-monotone
   notion; (iii) introduce the ordered integers and refute monotonicity of `·`
   for `≤` on ℤ with the book's negative-multiplier witness.

In-tree donors: the ordered-commutative-monoid recipe from the Seven Sketches
§2.2.1 reals issue, `Instance/Proset.v:33,47`, `Instance/Omega.v:72`,
`Functor/Structure/Monoidal.v:110`, `Coq.Arith.PeanoNat` for the arithmetic
lemmas.

## Definition of Done

- [ ] `(ℕ, ≤, 0, +)` and `(ℕ, ≤, 1, ·)` are both built, and a statement records
      that they are two different monoidal structures on the same preorder
      (Example 2.30, Exercise 2.31; printed p. 53).
- [ ] `(ℕ, |, 1, ·)` is built, with monotonicity proved by the book's witness
      argument (Example 2.32; printed p. 53).
- [ ] Exercise 2.33 is discharged as a refutation with an explicit witness
      (printed p. 54).
- [ ] Exercise 2.45 is discharged in all three clauses, including an exhibited
      monoidal monotone between the additive and multiplicative structures on ℕ
      and the ℤ refutation (printed p. 56).
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the ℕ and divisibility instances reports "Closed
      under the global context"; if `ZArith` introduces stdlib axioms, the ℤ
      file stays under `Instance/` and docs/AXIOMS.md is extended accordingly.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Nat/Monoidal.v
coqc -R . Category Instance/Nat/Divisibility.v
coqc -R . Category Instance/Int/Order.v
```
then
```
Require Import Category.Instance.Nat.Monoidal.
Print Assumptions Nat_Add_MonoidalPreorder.
Print Assumptions Nat_Mul_MonoidalPreorder.
Print Assumptions divides_add_not_monotone.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the two
ℕ structures share one carrier object; the divisibility monotonicity proof is the
book's; the two refutations are genuine negations with computable witnesses.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: 7sketches:2.2.1:example4 (the ordered-commutative-monoid recipe
introduced with the reals).
Depends on: 7sketches:2.2.5:def41 (the preorder-level monoidal monotone that
Exercise 2.45(2) asks for).
Depends on: #758 (the divisibility preorder on the naturals).
Depends on: #759 (the integers as an ordered carrier).

<!-- catalog: {"ids":["7sketches:2.2.4:example30","7sketches:2.2.4:ex31","7sketches:2.2.4:example32","7sketches:2.2.4:ex33","7sketches:2.2.5:ex45"],"deps":["7sketches:2.2.1:def2","7sketches:2.2.1:example4","7sketches:2.2.5:def41","#758","#759"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Wiring diagrams over a monoidal preorder — validity, the graphical-proof theorem, and the crossing-free fragment"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.2:def-valid-wiring-diagram, 7sketches:2.2.2:example14, 7sketches:2.2.2:construction-graphical-proof, 7sketches:2.2.2:example19, 7sketches:2.2.2:ex20]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.2.1:example4]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.2 "Introducing wiring
diagrams" — the unnumbered definition of a wiring diagram and of validity
(printed pp. 44–45; PDF pp. 56–57), Example 2.14 (diagrams over the additive
reals; printed p. 45, PDF p. 57), the unnumbered construction "wiring diagrams
as graphical proofs" and Example 2.19 (printed p. 47, PDF p. 59), and
Exercise 2.20 (printed pp. 47–48, PDF pp. 59–60). Items covered:
`7sketches:2.2.2:def-valid-wiring-diagram`, `7sketches:2.2.2:example14`,
`7sketches:2.2.2:construction-graphical-proof`, `7sketches:2.2.2:example19`,
`7sketches:2.2.2:ex20`.

## Background

A wiring diagram over a monoidal preorder is a piece of two-dimensional
notation: parallel wires denote the tensor of their labels, a wire labelled by
the unit is no wire at all, and a box is *valid* exactly when the tensor of its
left labels is below the tensor of its right labels; reading a nested diagram
slice by slice turns it into a derivation using monotonicity, transitivity and
reflexivity
([nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram),
[nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder)).

## Current state in the library

The diagram *syntax* is in-tree, in a stronger, proof-relevant form, but the
preorder reading and the validity biconditional are not:

- `Construction/ColouredPROP/Signature.v:139` — `Inductive CTerm` with `CT_id`
  (a wire), `CT_braid` (a crossing), `CT_comp` (series), `CT_tens` (parallel,
  by list concatenation) and `CT_gen` (a box); `CT_nothing := CT_id []` at
  line 181.
- `Construction/ColouredPROP.v:109` — `Class ColouredPROP`, whose fields
  `cprop_unit_nil : I = cprop_of_list nil` (:128) and
  `cprop_tensor_app` (:132) are exactly the book's two labelling conventions,
  as strict object equalities.
- `Construction/ColouredPROP/Interp.v:857` — `cinterp`, one clause per rule of
  the book's slice-by-slice reading, over `CValuation` (:845);
  `Construction/ColouredPROP/Universal.v:170` `CInterpF` and :568
  `CInterpF_Symmetric` are the soundness statement (a valuation extends to a
  strict symmetric monoidal functor), and :648 `cinterp_unique` pins it
  uniquely.
- `Theory/Category.v:282` — `hom_preorder`, which records the correspondence the
  graphical reading rests on: reflexivity *is* `id` (the bare wire) and
  transitivity *is* composition (boxes in series);
  `Functor/Bifunctor.v:68` `bimap_comp` is the middle-four interchange that
  licenses cutting a diagram into vertical slices;
  `Structure/Monoidal.v:132` `tensor_assoc` with `strict_assoc_obj`
  (`Structure/Monoidal/Strict.v:56`) is the bracketing subtlety Exercise 2.20
  opens with.

Three precise gaps. (1) No validity predicate and no biconditional: nothing
states "the diagram with inputs `cs` and outputs `ds` is valid iff the tensor of
`cs` is below the tensor of `ds`". Over a proof-relevant base that biconditional
is false, and no thin instantiation of `CTerm`/`ColouredPROP` exists — `_2` is
never used as a (coloured) PROP. (2) The in-tree language is inherently
symmetric (`CT_braid` is a constructor, `cprop_symmetric` a field), so the
crossing-free fragment that Exercise 2.20(3) is about — a diagram that needs no
appeal to clause (d) — is inexpressible; the only trace of the point is that
`Class Monoidal` is independent of `Class SymmetricMonoidal`. (3) The worked
derivations are absent: neither Exercise 2.20's entailment
(`t ≤ v ⊗ w`, `w ⊗ u ≤ x ⊗ z`, `v ⊗ x ≤ y` imply `t ⊗ u ≤ y ⊗ z`) nor
Example 2.19's five-box recipe diagram is derived anywhere, and no monoidal
preorder of resources exists to read Example 2.19 in.

## Work to be done

Suggested modules: `Construction/ColouredPROP/Planar.v` (the crossing-free
fragment), `Structure/Monoidal/Preorder/Diagram.v` (validity over a thin base
and the graphical-proof theorem), plus a small examples file.

1. Add a planar (crossing-free) fragment of the diagram language: either a
   predicate on `CTerm` cutting out `CT_braid`, or a separate inductive family
   interpreted into a merely monoidal (non-symmetric) target. This is what makes
   Exercise 2.20(3) statable.
2. Define validity for a diagram over a monoidal preorder and prove the
   biconditional of the unnumbered definition: a diagram is valid iff the fold
   of its input labels is below the fold of its output labels. Instantiate the
   existing interpretation machinery at a thin base to get it, and prove the two
   labelling conventions there (unit-labelled wire = no wire; parallel wires =
   tensor, in either bracketing).
3. Prove the graphical-proof theorem in the book's form: given an assertion for
   each interior box, every diagram built from them yields the exterior
   assertion. Over a thin base this is an implication between inequalities, which
   is precisely the reading the existing soundness functor does not give.
4. Derive Exercise 2.20's entailment from clauses (a)–(d) alone, with the
   reflexivity and transitivity steps named, and show the derivation goes through
   without the symmetry clause by carrying it out in the planar fragment.
5. Exhibit Example 2.19 (a five-generator recipe signature, the composite
   diagram, the resulting availability implication) and Example 2.14 (diagrams
   over the additive reals: the box `4 ≤ 7` and the box with inputs `2, 5` and
   outputs `-1, 5, 3`).

In-tree donors: `Construction/ColouredPROP/Signature.v:139`,
`Construction/ColouredPROP.v:109`, `Construction/ColouredPROP/Interp.v:845,857`,
`Construction/ColouredPROP/Universal.v:170,568,648`, `Theory/Category.v:282`,
`Functor/Bifunctor.v:68`, `Theory/Multicategory/Representable.v:55,113`
(`tensor_list`, `tfold_app`), `Construction/PROP/Tietze.v:716` (an in-tree
worked diagram-as-derivation example).

## Definition of Done

- [ ] Validity is defined and the biconditional of the §2.2.2 definition
      (printed p. 45) is proved over a monoidal preorder.
- [ ] Both labelling conventions (unit wire = no wire; parallel = tensor,
      bracketing-independent) are proved, not assumed.
- [ ] The graphical-proof theorem is stated as an implication between
      inequalities over a thin base (printed p. 47).
- [ ] A crossing-free fragment exists, and Exercise 2.20 is discharged in it,
      with the reflexivity/transitivity uses named and no appeal to clause (d)
      (printed pp. 47–48).
- [ ] Example 2.19's five-box recipe diagram and Example 2.14's two real-labelled
      boxes are exhibited.
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the validity biconditional and on the
      graphical-proof theorem reports "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md "Key Files and Concepts" updated: a planar fragment and a
      preorder-level soundness reading are both new capabilities of the PROP
      spine.

## Verification

```
coqc -R . Category Construction/ColouredPROP/Planar.v
coqc -R . Category Structure/Monoidal/Preorder/Diagram.v
```
then
```
Require Import Category.Structure.Monoidal.Preorder.Diagram.
Print Assumptions diagram_valid_iff.
Print Assumptions graphical_proof.
Print Assumptions exercise_2_20.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: validity
is a biconditional, not a one-way soundness statement; the Exercise 2.20
derivation type-checks in the planar fragment; the recipe example uses five
generators as the book's diagram does.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class the diagrams are
read over).
Depends on: 7sketches:2.2.1:example4 (the additive reals, for Example 2.14).

<!-- catalog: {"ids":["7sketches:2.2.2:def-valid-wiring-diagram","7sketches:2.2.2:example14","7sketches:2.2.2:construction-graphical-proof","7sketches:2.2.2:example19","7sketches:2.2.2:ex20"],"deps":["7sketches:2.2.1:def2","7sketches:2.2.1:example4"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: The chemistry monoidal preorder of material collections, and catalysis"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.3:construction-mat, 7sketches:2.2.3:ex21, 7sketches:2.2.3:def-catalysis, 7sketches:2.5.1:example86]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.5.1:def79]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.3 "Applied examples" —
the unnumbered construction of the chemistry monoidal preorder of material
collections (printed pp. 48–49; PDF pp. 60–61), Exercise 2.21 (its axioms;
printed p. 49, PDF p. 61), and the unnumbered definition of a catalyst (printed
p. 49, PDF p. 61). Also §2.5.1 Example 2.86 (the resource-theoretic reading of
monoidal closure, concluding that the chemistry preorder is *not* closed; printed
p. 70, PDF p. 82), which is a further theorem about the same object and is
therefore scoped here rather than with the closure definition. Items covered:
`7sketches:2.2.3:construction-mat`, `7sketches:2.2.3:ex21`,
`7sketches:2.2.3:def-catalysis`, `7sketches:2.5.1:example86`.

## Background

Material collections — formal non-negative-integer combinations of substances —
ordered by derivable reactions, with the empty collection as unit and formal sum
as tensor, form a symmetric monoidal preorder; a catalyst is an element `k` such
that `x ⊗ y ⊗ k ≤ z ⊗ k` holds although `x ⊗ y ≤ z` does not, so tensoring can
create relations
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[Wikipedia: Chemical reaction network theory](https://en.wikipedia.org/wiki/Chemical_reaction_network_theory),
[Wikipedia: Catalysis](https://en.wikipedia.org/wiki/Catalysis)). The same
preorder is the book's standing example of a monoidal preorder that is *not*
closed: no material collection acts as a residual `c ⊸ d`, because the would-be
element is a potential reaction rather than a substance
([nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category)).

## Current state in the library

The construction *shape* exists as the free coloured PROP, one level up in
proof-relevance:

- `Construction/ColouredPROP/Free.v:148` — `CFreeCat_Tensor`, objects
  `list Colour` (collections of typed wires), tensor = concatenation, with
  bifunctoriality (the book's clause (a)) discharged by `CTE_tens_cong`,
  `CTE_tens_id`, `CTE_interchange`.
- `Construction/ColouredPROP/Monoidal.v:512` — `CFreeCat_Monoidal`, unit `[]`
  (clauses (b), (c)); `Construction/ColouredPROP/Instance.v:166`
  `CFreeCat_Strict` makes those object equalities;
  `Construction/ColouredPROP/Braided.v:390` `CFreeCat_Symmetric` gives
  clause (d) as an involutive braiding.
- `Construction/ColouredPROP/Signature.v:52` — `CSignature`, a family of
  generators indexed by input/output collections: exactly the slot the reaction
  equations go into.

Gaps. (1) The homs of the free coloured PROP are proof-relevant terms recording
*how* a reaction was derived, not a preorder relation, and the object monoid is
the free monoid on colours (commutativity only up to braiding) rather than the
free *commutative* monoid of material collections; `Construction/Quotient.v`
provides generic hom-congruence quotients but no monoidal-preserving quotient by
the total relation, so derivability is never a preorder in-tree. (2) There is no
monoidal preorder notion at all, and the only `Monoidal` structure on a thin
category is `Two_Monoidal` (`Instance/Two/Monoidal.v:105`). (3) No chemistry
instance: `chemistr|reaction|molecul|material collection` finds a single
background comment (`Construction/DecoratedCospan.v:90`), and `catalys` finds 0
hits; nothing isolates the catalysis phenomenon, and there is no statement
anywhere that tensoring can create morphisms (`cancellat`: 0 hits).

## Work to be done

Suggested modules: `Instance/Materials.v` (the carrier and its monoidal preorder),
`Structure/Monoidal/Preorder/Catalysis.v` (the definition and its derivation).

1. Build the carrier: the free commutative monoid on a set of substances
   (finitely-supported ℕ-valued functions, or multisets with a decidable carrier),
   with the empty collection as unit and pointwise addition as tensor. Prove the
   commutative-monoid laws as object equalities so the strict form of the
   monoidal-preorder class applies.
2. Define the preorder: given a set of reactions (pairs of collections), take the
   reflexive-transitive, tensor-closed relation they generate, and prove it is a
   preorder monotone in both arguments — this discharges Exercise 2.21's four
   clauses, each as a named lemma. Reuse the reachability closure machinery
   (`Instance/Lambda/Multi.v:46,61,74`) for the reflexive-transitive part.
3. Define catalysis over an arbitrary monoidal preorder: `k` catalyses
   `x ⊗ y ≤ z` when `x ⊗ y ⊗ k ≤ z ⊗ k` holds and `x ⊗ y ≤ z` does not. Prove
   the book's derivation as a lemma (from `y ⊗ k ≤ y' ⊗ k'`, `x ⊗ y' ≤ z'` and
   `z' ⊗ k' ≤ z ⊗ k` conclude `x ⊗ y ⊗ k ≤ z ⊗ k` by monotonicity and
   transitivity), and exhibit a concrete catalyst in the chemistry instance,
   which requires proving a *negative* fact (`x ⊗ y ≤ z` fails) about the
   generated preorder — so the generation must come with an inversion principle.
4. Record the general moral: tensoring with a fixed object need not reflect the
   order.
5. Prove Example 2.86: the chemistry preorder is not monoidal closed. With the
   hom-element notion of the closure issue in scope, show that for a suitable
   pair of collections no element satisfies the residuation biconditional — the
   argument runs through the inversion principle of step 3, since it needs a
   negative fact about derivability for every candidate residual. This is the
   library's second non-closedness statement (the first being the join structure
   on the Booleans), so the negated-closedness statement shape introduced there
   should be reused rather than re-invented.

In-tree donors: `Construction/ColouredPROP/Free.v:148`,
`Construction/ColouredPROP/Monoidal.v:512`,
`Construction/ColouredPROP/Instance.v:166`,
`Construction/ColouredPROP/Braided.v:390`,
`Construction/ColouredPROP/Signature.v:52`, `Construction/Quotient.v`,
`Instance/Lambda/Multi.v:46,61,74`, `Instance/Proset.v:33`.

## Definition of Done

- [ ] The chemistry monoidal preorder is built with reaction arrows as the order,
      the empty collection as unit and formal sum as tensor, matching the §2.2.3
      construction (printed p. 48).
- [ ] Exercise 2.21's clauses (a)–(d) are named lemmas (printed p. 49).
- [ ] Catalysis is defined over an arbitrary monoidal preorder, the book's
      derivation chain is proved, and a concrete catalyst is exhibited — including
      the negative half, `x ⊗ y ≤ z` failing.
- [ ] The generated preorder comes with an inversion/no-junk principle strong
      enough to prove that negative half.
- [ ] The chemistry preorder is proved *not* monoidal closed (Example 2.86;
      printed p. 70), reusing the negated-closedness statement shape rather than
      introducing a second one.
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the chemistry instance and on the catalysis
      derivation reports "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Materials.v
coqc -R . Category Structure/Monoidal/Preorder/Catalysis.v
```
then
```
Require Import Category.Instance.Materials.
Print Assumptions Mat_SymmetricMonoidalPreorder.
Require Import Category.Structure.Monoidal.Preorder.Catalysis.
Print Assumptions catalysis_derivation.
Print Assumptions water_sodium_catalyst_example.
Print Assumptions Mat_not_closed.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the order
really is reaction derivability (a proposition, not a term), the tensor really is
formal sum on collections, and the catalysis witness proves both halves of the
definition.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: 7sketches:2.5.1:def79 (the hom-element / closedness notion that
Example 2.86 negates).

<!-- catalog: {"ids":["7sketches:2.2.3:construction-mat","7sketches:2.2.3:ex21","7sketches:2.2.3:def-catalysis","7sketches:2.5.1:example86"],"deps":["7sketches:2.2.1:def2","7sketches:2.5.1:def79"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2/2.5: The two-element base Bool — both monoidal structures, closedness by implication, and Bool as a quantale"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.4:ex29, 7sketches:2.5.1:ex84, 7sketches:2.5.1:example85, 7sketches:2.5.2:ex92, 7sketches:2.5.2:ex93]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.5.1:def79, 7sketches:2.5.2:def90]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.4 Exercise 2.29 (the
second monoidal structure on the Booleans; printed p. 53, PDF p. 65), §2.5.1
Exercise 2.84 (Bool is monoidal closed) and Example 2.85 (the join structure is
*not* closed) — printed p. 70, PDF p. 82 — and §2.5.2 Exercise 2.93 (Bool is a
unital commutative quantale; printed p. 72, PDF p. 84). Exercise 2.92 (printed
p. 72, PDF p. 84) is a two-base exercise; its Boolean clauses (1a) and (2a) — the
empty join and the binary join in `Bool` — are covered here, while its `Cost`
clauses (1b) and (2b) are covered by the `Cost`-quantale issue of §2.5.2. Items
covered: `7sketches:2.2.4:ex29`, `7sketches:2.5.1:ex84`,
`7sketches:2.5.1:example85`, `7sketches:2.5.2:ex92` (Boolean clauses),
`7sketches:2.5.2:ex93`.

## Background

The two-element order carries two symmetric monoidal structures — meet with unit
`true`, and join with unit `false`; the first is closed, its hom-element being
implication, and with all joins it is the smallest interesting quantale, while
the second is not closed at all
([nLab: quantale](https://ncatlab.org/nlab/show/quantale),
[nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category)).

## Current state in the library

The meet structure on the genuinely two-element base exists:
`Instance/Two/Monoidal.v:80` `Two_Cartesian` (`product_obj := two_meet`, i.e.
AND), :98 `Two_Terminal` (`terminal_obj := TwoY`, i.e. `true`), :105
`Two_Monoidal := @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal`, over `_2`
(`Instance/Two.v:134`), with thinness at `Instance/Two/Monoidal.v:26`.

What is missing:

- The join structure. `Two_Cocartesian` and `Two_Initial` do not exist (the only
  `Two_*` symbols are `Two_Cartesian`, `Two_Terminal`, `Two_Monoidal`,
  `Two_Discrete`), and there is no `Cocartesian` + `Initial` ⇒ `Monoidal`
  bridge: only the cartesian direction exists
  (`Structure/Monoidal/Internal/Product.v:54` `CC_Monoidal`, :314
  `CC_SymmetricMonoidal`), so even where joins do exist — on `Props`
  (`Instance/Props.v:80` `Props_Cocartesian` with `product_obj := or`, :61
  `Props_Initial` with `terminal_obj := False`) — they are never packaged as a
  monoidal structure.
- Closedness of the two-element base. `Two_Closed` does not exist (0 hits);
  the only *thin* closed instance is `Instance/Props.v:94` `Props_Closed`
  (`exponent_obj := Basics.impl`, `exp_iso` the currying bijection) over `Props`
  (`Instance/Props.v:39`, `hom := Basics.impl`, hom-setoid `equiv := True`) —
  the right argument, but for Coq's `Prop` (a large intuitionistic prealgebra)
  rather than the two-element `B`, and `Props` is never given a
  `Monoidal`/`SymmetricMonoidal` structure, so "monoidal closed" is not
  literally predicated of it either.
- All joins. Only binary joins and the empty join exist, on `Props`;
  `Structure/Complete.v:119` `Cocomplete` has no instance anywhere, and there is
  no indexed-coproduct dual of `Structure/Limit/Product.v`'s `iprod`.
- Non-closedness. There is no formal non-closedness statement for any category
  (0 hits for a negated `Closed`/`ClosedMonoidal`/`SymMonClosed`); the nearest
  formal relatives are `Instance/Sets/Par.v:240,269`.

## Work to be done

Suggested modules: `Instance/Two/Join.v` (the join structure),
`Instance/Two/Closed.v`, `Instance/Two/Quantale.v`.

1. Build `Two_Initial` and `Two_Cocartesian` on `_2` (bottom `TwoX`, join
   `two_join`), then supply the missing general bridge: binary coproducts plus an
   initial object give a symmetric monoidal structure. The dualization route
   exists in principle — `Cocartesian C` is notation for `@Cartesian (C^op)`
   (`Structure/Cocartesian.v:115–117`) and `Initial C` for `@Terminal (C^op)`
   (`Structure/Initial.v:96–98`), so `CC_Monoidal` at `C^op` followed by
   `Monoidal_op` (`Construction/Opposite/Monoidal.v:92`) does it — but nothing
   takes it; take it once, generically.
2. Record Exercise 2.29's conclusion: the unit for the join structure must be
   the bottom element, and with that choice all four clauses hold, so the
   Boolean preorder carries two distinct symmetric monoidal structures.
3. Exercise 2.84: give `_2` a `Closed` instance whose exponential is the
   implication table, and prove the residuation biconditional
   `(a ∧ p) ≤ q ⟺ a ≤ (p ⊸ q)` in the preorder form the book states.
4. Example 2.85: prove the join structure is *not* closed, with the book's
   argument (the bottom element is below every candidate hom-element, and
   `a = false`, `p = true`, `q = false` refutes the biconditional). This
   requires the negated-closedness statement shape, which the library does not
   yet have — introduce it here.
5. Exercise 2.92's Boolean clauses: identify `⋁∅` as the bottom element `false`
   and the binary join `x ∨ y` as `two_join`, as named lemmas about `_2` rather
   than as remarks — the first is `Two_Initial` read as a join, the second
   `Two_Cocartesian`.
6. Exercise 2.93: assemble "Bool is a unital commutative quantale" — the meet
   structure, closedness, and *all* joins (not merely binary and empty). Since
   `_2` is finite with decidable equality, arbitrary subset-indexed joins can be
   computed directly; state them in the form the quantale class requires.

In-tree donors: `Instance/Two.v:134`, `Instance/Two/Monoidal.v:26,80,98,105`,
`Instance/Props.v:39,53,61,69,80,94`,
`Structure/Monoidal/Internal/Product.v:54,314`,
`Construction/Opposite/Monoidal.v:92`, `Structure/Complete.v:119`.

## Definition of Done

- [ ] Both monoidal structures on `_2` exist, and a statement records that they
      are distinct (Exercise 2.29; printed p. 53).
- [ ] A generic "coproducts + initial ⇒ symmetric monoidal" bridge is added
      (dual of `CC_Monoidal`), not a bespoke `_2` construction.
- [ ] `_2` is shown monoidal closed with the implication hom-element, in the
      biconditional form of Equation (2.80) (Exercise 2.84; printed p. 70).
- [ ] The join structure is proved *not* closed, by the book's argument
      (Example 2.85; printed p. 70).
- [ ] The empty and binary joins in `Bool` are identified by name
      (Exercise 2.92 clauses (1a)/(2a); printed p. 72).
- [ ] `_2` is shown to be a unital commutative quantale with all joins
      (Exercise 2.93; printed p. 72).
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the closedness instance, the non-closedness theorem
      and the quantale instance reports "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md "Key Files and Concepts" updated: the first in-tree quantale.

## Verification

```
coqc -R . Category Instance/Two/Join.v
coqc -R . Category Instance/Two/Closed.v
coqc -R . Category Instance/Two/Quantale.v
```
then
```
Require Import Category.Instance.Two.Quantale.
Print Assumptions Two_Quantale.
Print Assumptions Two_join_not_closed.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
closedness statement is a biconditional over the two-element base (not over
`Props`); the non-closedness statement is a genuine negation; "all joins" means
arbitrary subsets, not just binary and empty.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: 7sketches:2.5.1:def79 (the closed monoidal preorder notion).
Depends on: 7sketches:2.5.2:def90 (the quantale class).
Depends on: #756 (Cocartesian and Initial structure on `_2`, and the boolean
reading of meet and join — the join/bottom data this issue packages
monoidally).
Depends on: #490 (cocartesian monoidal structure from finite coproducts — the
generic bridge this issue needs in order to package the join structure as a
`Monoidal` instance).
Depends on: #389 (powerset lattices and Boolean algebras are cartesian closed —
the two-element Boolean algebra is the closure result Exercise 2.84 asks for, and
should be consumed here rather than reproved).

<!-- catalog: {"ids":["7sketches:2.2.4:ex29","7sketches:2.5.1:ex84","7sketches:2.5.1:example85","7sketches:2.5.2:ex92","7sketches:2.5.2:ex93"],"deps":["7sketches:2.2.1:def2","7sketches:2.5.1:def79","7sketches:2.5.2:def90","#756","#490","#389"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2/2.3: The three-element chain with min as a monoidal preorder, and categories enriched in it"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.4:ex34, 7sketches:2.3.4:ex61]
deps_item_ids: [7sketches:2.2.1:def2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.4 Exercise 2.34 (the
three-element preorder no → maybe → yes with unit `yes` and product `min`;
printed p. 54, PDF p. 66) and §2.3.4 Exercise 2.61 (what a category enriched in
it is; printed p. 63, PDF p. 75). Items covered: `7sketches:2.2.4:ex34`,
`7sketches:2.3.4:ex61`.

## Background

A finite chain with meet as tensor and its top as unit is a symmetric monoidal
preorder; enriching in the three-element chain grades hom-objects by three
degrees of certainty, the three-valued analogue of enrichment in the Booleans
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category)).

## Current state in the library

The carrier chain exists, but only through the arrows-only encoding:
`Theory/Metacategory.v:413` `Three := FromArrows ThreeArrows` with the arrow
table at :395 — three objects with `0 → 1`, `1 → 2` and their composite. Nothing
states that `Three` is thin, and nothing identifies it with the ordinal-3 chain;
the only such identification in-tree is at `n = 2`
(`Theory/Metacategory/ArrowsOnly.v:523` `Two_iso_2`). The *pattern* of the
answer is fully built one size down — `Instance/Two/Monoidal.v:80,98,105`
(meet as tensor, top as unit) — and available generically at
`Structure/Monoidal/Internal/Product.v:54,314` (`CC_Monoidal`,
`CC_SymmetricMonoidal`: binary products plus a terminal object give a symmetric
monoidal structure). What is missing for the three-element chain: a `min`
bifunctor, a `Cartesian`/`Terminal` instance, hence no `Monoidal` structure
(`@Cartesian Three`, `@Terminal Three`, `Monoidal Three`: 0 hits each), and no
`min` operation anywhere in the tree (`two_meet`,
`Instance/Two/Monoidal.v:37`, is the only meet). The enrichment side has no
instance either: the only monoidal base ever used for enrichment is `_2`
(`Construction/Enriched/Two.v`).

## Work to be done

Suggested modules: `Instance/Three.v` (the chain as a `Proset`, with its meet
and top), `Instance/Three/Monoidal.v`, `Construction/Enriched/Three.v`.

1. Present the three-element chain as a preorder in the library's order-theoretic
   idiom, i.e. through `Instance/Proset.v:33` on a three-element carrier with a
   decidable relation, and prove it thin. Relate it to the existing
   `Theory/Metacategory.v:413` `Three` by an isomorphism of categories, following
   the `n = 2` precedent, so the two presentations are not left disconnected.
2. Define `min` by its full 3×3 table — the first half of Exercise 2.34 — and
   prove it is the categorical meet, with the top element terminal; obtain the
   symmetric monoidal structure through `CC_SymmetricMonoidal` rather than by
   hand, and record the four clauses of Definition 2.2 as named lemmas.
3. Instantiate the enrichment class at this base and unpack it: what the
   hom-objects mean, and what the two enrichment axioms say (`yes ≤ X(x,x)`
   forces the diagonal to be `yes`; `min(X(x,y), X(y,z)) ≤ X(x,z)` is a
   three-valued transitivity). Give at least one small worked example, in the
   style of the Boolean case, with its 3×3 or 4×4 hom matrix.

In-tree donors: `Instance/Proset.v:33`, `Theory/Metacategory.v:413`,
`Theory/Metacategory/ArrowsOnly.v:523`, `Instance/Two/Monoidal.v:37,80,98,105`,
`Structure/Monoidal/Internal/Product.v:54,314`, `Construction/Enriched.v:111`,
`Construction/Enriched/Two.v`.

## Definition of Done

- [ ] The three-element chain is a `Proset`, proved thin, and connected by an
      isomorphism to the existing arrows-only `Three`.
- [ ] `min` is defined by the full table Exercise 2.34 asks for and proved to be
      the meet, with the top as unit; the symmetric monoidal preorder is
      assembled from the general cartesian bridge (printed p. 54).
- [ ] The enrichment class is instantiated at this base and the two axioms are
      unpacked into their three-valued readings, with one worked example
      (Exercise 2.61; printed p. 63).
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the monoidal instance and the enrichment example
      reports "Closed under the global context".
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Three.v
coqc -R . Category Instance/Three/Monoidal.v
coqc -R . Category Construction/Enriched/Three.v
```
then
```
Require Import Category.Instance.Three.Monoidal.
Print Assumptions Three_Monoidal.
Compute (* the 3x3 min table *).
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the min
table is the book's; the monoidal structure comes from the generic
products+terminal bridge; the enrichment reading names both axioms.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: #765 (finite chains as preorders).

<!-- catalog: {"ids":["7sketches:2.2.4:ex34","7sketches:2.3.4:ex61"],"deps":["7sketches:2.2.1:def2","#765"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2/2.5: The powerset monoidal preorder — intersection with the whole set as unit, indexed predicates, and whether it is a quantale"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.4:ex35, 7sketches:2.2.4:ex36, 7sketches:2.5.2:ex94]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.5.2:def90]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.4 Exercise 2.35 (the
powerset ordered by inclusion, with intersection as product and the whole set as
unit) and Exercise 2.36 (a monoidal structure on predicates over the naturals) —
printed p. 54, PDF p. 66 — and §2.5.2 Exercise 2.94 (is the powerset monoidal
preorder a quantale?; printed p. 72, PDF p. 84). Items covered:
`7sketches:2.2.4:ex35`, `7sketches:2.2.4:ex36`, `7sketches:2.5.2:ex94`.

## Background

The powerset of a set, ordered by inclusion, with intersection as tensor and the
whole set as unit, is a symmetric monoidal preorder; because it is a complete
lattice in which intersection distributes over arbitrary unions, it is also
closed and hence a quantale
([nLab: power set](https://ncatlab.org/nlab/show/power+set),
[nLab: quantale](https://ncatlab.org/nlab/show/quantale)).

## Current state in the library

The general *reason* the exercise's answer is yes exists —
`Structure/Monoidal/Internal/Product.v:54,314` turn binary products plus a
terminal object into a symmetric monoidal structure — and the meet-with-top
instance is realized on the thin category `Props` (`Instance/Props.v:39`, homs
`Basics.impl`, hom-setoid `equiv := True`) with `Props_Cartesian` (:69,
`product_obj := and`) and `Props_Terminal` (:53, `terminal_obj := True`).
`Instance/Fun/Cartesian.v:111` supplies pointwise products in a functor category.

There is, however, **no powerset-of-a-set preorder in-tree** (0 hits for
`powerset`/`power set` outside `Structure/Topos.v`'s internal power *object*
`Pow a := Ω ^ a`, :129, and 0 hits for `Included`, `Ensembles.Intersection`,
`inclusion order`). `Instance/Ens.v:56` `EnsT T` has subsets as objects, but a
morphism is a *function* `f : T → T` with `∀ x, x ∈ A ↔ f x ∈ B` — a preimage
condition, not an inclusion — and it carries no `Terminal`/`Cartesian` instance.
`Theory/Subobject.v:59,62,67` gives the inclusion preorder on subobjects
(`sub_le`, `sub_le_refl`, `sub_le_trans`) but constructs no meet
(intersection-as-pullback appears only in a comment,
`Structure/Pullback.v:94`) and no top. For Exercise 2.36 the indexed case is
missing as well: `Functor_Category_Terminal`/`_Monoidal`/`_Cocartesian` do not
exist (only `Functor_Category_Cartesian`), so pointwise conjunction over an
index has no unit object and no monoidal packaging, and there is no
`(ℕ → Prop, pointwise implication)` preorder anywhere. For Exercise 2.94, no
quantale class exists (`quantale`: one prose hit,
`Construction/Enriched.v:78`), so the question is not even statable.

## Work to be done

Suggested modules: `Instance/Powerset.v`, `Instance/Powerset/Quantale.v`.

1. Introduce the powerset preorder `(P(S), ⊆)` as a thin category via
   `Instance/Proset.v:33` on `S → Prop` (or `Ensemble S`) with inclusion, proved
   reflexive and transitive. Keep it distinct from `Instance/Ens.v`, whose homs
   are functions; a header note should say so, since the near-miss is easy to
   mistake for the real thing.
2. Give it products (intersection), a terminal object (the whole set),
   coproducts (union) and an initial object (the empty set), then obtain the
   symmetric monoidal structure through the generic cartesian bridge, and record
   Exercise 2.35's four clauses as named lemmas.
3. Exercise 2.36: the ℕ-indexed case. Either instantiate the powerset
   construction at `S := ℕ` and observe that predicates over ℕ *are* subsets of
   ℕ (with the book's identification of pointwise-equivalent statements as the
   quotient by mutual implication), or build the pointwise structure on an
   indexed family and supply the missing terminal object for functor categories.
   State which route is taken and prove the four clauses.
4. Exercise 2.94: show the powerset preorder has all joins (arbitrary unions) and
   is closed, with hom-element `A ⊸ B = (S \ A) ∪ B`, and conclude that it is a
   unital commutative quantale — or, if the intended answer is negative for a
   particular reading, say precisely which clause fails and prove that.

In-tree donors: `Instance/Proset.v:33`, `Instance/Props.v:39,53,61,69,80,94`,
`Structure/Monoidal/Internal/Product.v:54,314`, `Theory/Subobject.v:59,62,67`,
`Instance/Fun/Cartesian.v:111`, `Coq.Sets.Ensembles` (already imported by
`Instance/Ens.v` and `Instance/Rel.v`).

## Definition of Done

- [ ] `(P(S), ⊆)` exists as a thin category, distinct from `Instance/Ens.v`, and
      the distinction is documented in the file header.
- [ ] Intersection is proved to be the product and the whole set terminal;
      Exercise 2.35's clauses (a)–(d) are named lemmas (printed p. 54).
- [ ] Exercise 2.36 is discharged for predicates over ℕ, with the book's
      identification of pointwise-equivalent predicates handled explicitly
      (printed p. 54).
- [ ] Exercise 2.94 is answered with a proof: all joins, closedness, and the
      quantale packaging (printed p. 72).
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` in the new files.
- [ ] `Print Assumptions` on the powerset monoidal preorder and on the quantale
      instance reports "Closed under the global context" (or discloses exactly
      which stdlib axioms `Ensembles` pulls in, recorded in docs/AXIOMS.md).
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.

## Verification

```
coqc -R . Category Instance/Powerset.v
coqc -R . Category Instance/Powerset/Quantale.v
```
then
```
Require Import Category.Instance.Powerset.Quantale.
Print Assumptions Powerset_MonoidalPreorder.
Print Assumptions Powerset_Quantale.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: homs are
inclusions (a proposition), not functions; the unit is the whole set, not the
empty set; the quantale answer is proved rather than asserted.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: 7sketches:2.5.2:def90 (the quantale class).
Depends on: #382 (the powerset preorder and the direct-image/inverse-image
Depends on: #745 (Awodey 10.4/10.6 Ex 8 — the interior comonad and closure monad on the subsets of a space) — it targets the same new module `Instance/Powerset.v`; coordinate the module layout so the monoidal-preorder structure and the comonad/monad pair coexist rather than being built twice.
adjunction — the inclusion-ordered carrier).
Depends on: #389 (powerset lattices are cartesian closed — the residual whose
existence is half of Exercise 2.94's answer).
Depends on: #685 (powersets are complete Heyting algebras — the all-joins half of
Exercise 2.94's answer, which should be consumed rather than reproved).

<!-- catalog: {"ids": ["7sketches:2.2.4:ex35", "7sketches:2.2.4:ex36", "7sketches:2.5.2:ex94"], "deps": ["7sketches:2.2.1:def2", "7sketches:2.5.2:def90", "#382", "#389", "#685", "#745"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Cost, Lawvere's monoidal preorder of distances, and its opposite"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.4:example37, 7sketches:2.2.4:ex40]
deps_item_ids: [7sketches:2.2.1:def2, 7sketches:2.2.1:example4]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.4 — Example 2.37
(Cost, the extended non-negative reals under the reversed order, with unit 0 and
tensor `+`; printed pp. 54–55, PDF pp. 66–67) and Exercise 2.40 (describe the
opposite of Cost; printed p. 55, PDF p. 67). Items covered:
`7sketches:2.2.4:example37`, `7sketches:2.2.4:ex40`.

## Background

Cost is the monoidal preorder `([0, ∞], ≥, 0, +)`: distances ordered so that
smaller is higher, with addition as tensor extended by `x + ∞ = ∞`. It is
Lawvere's base of enrichment for generalized metric spaces and the running
example of the rest of the chapter
([nLab: monoidal preorder](https://ncatlab.org/nlab/show/monoidal+preorder),
[nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).

## Current state in the library

Nothing of this exists. The library imports no real or rational numbers
(`Reals`, `Rdefinitions`, `Rle`, `Rplus`, `R_scope`, `QArith`, `ZArith`: 0 hits
each) and has no `∞` of any kind (`infty`, `infinity`: 0 hits); the identifier
`Cost` occurs only as `Costrong`/`CostrongComonad` in `Comonad/Strong.v`, which
is unrelated. Cost is named in four background essays as a base the library does
*not* carry — `Construction/Enriched.v:74–79`, `Theory/Profunctor.v:100`,
`Instance/Poset.v:75–77`, `Instance/Two.v:71–73` (which says outright that only
the `V = 2` case is carried). The generic half of Exercise 2.40 *is* in-tree:
`Construction/Opposite/Monoidal.v:92` `Monoidal_op` and :175 `Symmetric_op` give
the opposite of a symmetric monoidal structure — so what is missing is the
carrier, not the duality.

## Work to be done

Suggested modules: `Instance/Cost.v` (the carrier and the monoidal preorder),
`Instance/Cost/Opposite.v` (or a section of the same file).

1. Introduce the extended non-negative reals `[0, ∞]` — an inductive
   `Rbar`-style carrier (`Finite : {r : R | 0 <= r} → ext` plus `Infinity`) is
   the least painful route and keeps decidability of the order questions
   separate — with addition extended by `x + ∞ = ∞` and the reversed order `≥`.
   Prove it is a preorder (in fact a total order) and that addition is monotone
   for it.
2. Feed the result into the ordered-commutative-monoid recipe to obtain Cost as a
   symmetric monoidal preorder, with clauses (a)–(d) of Definition 2.2 recorded
   as named lemmas and the unit `0` and tensor `+` visible in the statement.
   Document the order reversal prominently: `∞` is the *bottom*.
3. Exercise 2.40: identify `Cost^op` explicitly — the usual order on `[0, ∞]`,
   the same unit and the same tensor — by instantiating the existing
   `Symmetric_op`/`Monoidal_op` at Cost and proving the identification of the
   underlying order with `≤`.
4. Keep the axiom footprint disclosed: the file lives under `Instance/`, and
   docs/AXIOMS.md is extended with whatever the stdlib reals introduce.

In-tree donors: the ordered-commutative-monoid recipe from the Seven Sketches
§2.2.1 reals issue, `Instance/Proset.v:33`,
`Construction/Opposite/Monoidal.v:92,175`, `Instance/Omega.v:72` (style
precedent for a numeric order with a Type-valued relation).

## Definition of Done

- [ ] `[0, ∞]` exists with `+` extended by `x + ∞ = ∞`, and the reversed order
      is proved a (total) preorder.
- [ ] Cost is a symmetric monoidal preorder with unit 0 and tensor `+`, clauses
      (a)–(d) named, matching Example 2.37 (printed p. 54).
- [ ] `Cost^op` is identified explicitly in all three respects Exercise 2.40 asks
      for — order, unit, product — via the existing opposite-monoidal machinery
      (printed p. 55).
- [ ] The order-reversal convention is documented in the file header, with `∞`
      called out as the bottom element.
- [ ] Statements use `≈` on morphisms, never `=`.
- [ ] No `Admitted`, `admit` or `Axiom` written by hand in the new files.
- [ ] The file lives under `Instance/`; docs/AXIOMS.md is extended with the
      stdlib axioms the reals introduce, together with the `Print Assumptions`
      output for Cost; nothing under `Theory/`, `Structure/` or `Construction/`
      acquires a real-number dependency.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20
      build.
- [ ] `make todo` reports no new hits.
- [ ] CLAUDE.md "Key Files and Concepts" updated: Cost is the base the enrichment
      layer's own header essays promise and do not carry, so its arrival is
      flagship-level.

## Verification

```
coqc -R . Category Instance/Cost.v
```
then
```
Require Import Category.Instance.Cost.
Print Assumptions Cost_SymmetricMonoidalPreorder.
Print Assumptions Cost_op_identification.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the order
is reversed (`x ≤_Cost y` iff `x ≥ y`), `∞` is the bottom, `0` is the unit, and
the opposite is obtained from the generic construction rather than rebuilt.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the monoidal-preorder class).
Depends on: 7sketches:2.2.1:example4 (the ordered-commutative-monoid recipe and
the real carrier).

<!-- catalog: {"ids":["7sketches:2.2.4:example37","7sketches:2.2.4:ex40"],"deps":["7sketches:2.2.1:def2","7sketches:2.2.1:example4"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Monoidal monotones — a faithful lax level, the strong/strict trichotomy, and the oplax dual"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.5:def41, 7sketches:2.2.5:remark-oplax]
deps_item_ids: [7sketches:2.2.1:def2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.5 "Monoidal monotones"
— Definition 2.41 (monoidal monotone, with the strong and strict strengthenings)
and the unnumbered run-in remark that follows it (monoidal monotones as the
preorder-level case of monoidal functors, and the oplax dual). Printed pp. 55–56;
PDF pp. 67–68. Items covered: `7sketches:2.2.5:def41`,
`7sketches:2.2.5:remark-oplax`.

## Background

A monoidal monotone between monoidal preorders is a monotone map carrying two
one-directional comparisons — the unit of the target below the image of the unit,
and the tensor of two images below the image of the tensor — which is exactly a
lax monoidal functor between thin monoidal categories
([nLab: lax monoidal functor](https://ncatlab.org/nlab/show/lax+monoidal+functor),
[nLab: monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor)).
Strengthening the two comparisons to equivalences gives the strong notion and to
equalities the strict one; reversing both gives the oplax dual
([nLab: oplax monoidal functor](https://ncatlab.org/nlab/show/oplax+monoidal+functor)).

## Current state in the library

Two of the three levels are faithful, the primary one is not, and the dual is
missing.

- **Strong** — `Functor/Structure/Monoidal.v:77`, `Class MonoidalFunctor`, with
  `pure_iso : I ≅ F I` and `ap_iso {x y} : F x ⨂ F y ≅ F (x ⨂ y)`. Over a thin
  base an isomorphism is mutual `≤`, so these are precisely the book's clauses
  (a′) and (b′). `Functor/Structure/Monoidal.v:138`
  (`MonoidalFunctor_Is_Lax`) records strong ⇒ lax.
- **Strict** — `Functor/Structure/Monoidal/Strict.v:54`,
  `Class StrictMonoidalFunctor`, whose `strict_pure_obj : I = F I` and
  `strict_ap_obj : (F x ⨂ F y)%object = F (x ⨂ y)%object` are the book's (a″)
  and (b″) as Leibniz equalities of objects, plus the two fields identifying the
  comparisons with transported identities.
- **Lax** — `Functor/Structure/Monoidal.v:110`, `Class LaxMonoidalFunctor`, has
  `lax_pure : I ~> F I` and `lax_ap {x y} : F x ⨂ F y ~> F (x ⨂ y)` in exactly
  the book's direction, but **also requires three isomorphisms as data**:
  `pure_left {x} : I ⨂ F x ≅ F (I ⨂ x)`, `pure_right {x} : F x ⨂ I ≅ F (x ⨂ I)`
  and `ap_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z))` at `:119–123`.
  None carries a `:=` default, so all three are genuine obligations —
  `Functor/Structure/Monoidal/Id.v:83–85` must discharge them even for the
  identity functor (`ap_assoc` by `apply tensor_assoc`) — and none of them is
  mentioned by the class's three coherence laws at `:125–135`. Over a thin base
  `ap_assoc` forces `f(p₁) ⊗ f(p₂) ⊗ f(p₃)` to be *equivalent* to
  `f(p₁ ⊗ p₂ ⊗ p₃)`; taking `p₃` to be the unit of a unit-preserving map it
  forces `f(p₁ ⊗ p₂) ≃ f(p₁) ⊗ f(p₂)`. In other words the in-tree "lax" class
  collapses to the strong one on preorders, and the book's own paradigm
  lax-but-not-strong monoidal monotone (the floor map of Example 2.42) is not an
  instance of it.
- **Oplax** — entirely absent. `rg -iE 'oplax|opmonoidal|colax|comonoidal'`
  returns only the header comment at `Functor/Structure/Monoidal.v:34–36`, which
  says the variant "is not formalized here";
  `Theory/Bicategory/Lax.v:109`'s `OplaxTransformation`, which is the dual of a
  lax *transformation* between pseudofunctors and a different concept; and prose
  at `Construction/Grothendieck.v:120`. Nor is the dual reachable by the
  library's usual `op` trick, because no definition sets an oplax functor to be a
  lax functor between opposite monoidal categories.
- **No preorder-level packaging and no witness.** The phrase "monoidal monotone"
  has 0 hits; the only monotone-map API is
  `Construction/Enriched/Two.v:175` (`Record MonotoneMap`, used by
  `EnrichedFunctor_Two_monotone` at `:183`) and it carries no unit or product
  condition; and `LaxMonoidalFunctor`'s only inhabitants tree-wide are the closure
  instances `Functor/Structure/Monoidal/Id.v:73` and
  `Functor/Structure/Monoidal/Compose.v:291` plus hypotheses
  (`Construction/DecoratedCospan.v:114` takes one as a `Context` parameter);
  `Instance/Coq/Applicative.v:173–181` leaves the applicative-to-lax-monoidal
  instance commented out.

## Work to be done

Suggested modules: a repair of `Functor/Structure/Monoidal.v`, a new
`Functor/Structure/Monoidal/Oplax.v`, and
`Functor/Structure/Monoidal/Preorder.v` for the monoidal-monotone packaging.

1. **Repair the lax class.** Remove `pure_left`, `pure_right` and `ap_assoc` from
   `LaxMonoidalFunctor`, or replace them by the non-invertible composites built
   from `lax_pure`/`lax_ap` and the base's unitors and associator. They are used
   only to be propagated through `Functor/Structure/Monoidal/Compose.v:333–352`,
   so the closure instances must be re-derived; the identity instance
   (`Functor/Structure/Monoidal/Id.v:73`) and the composite instance are the two
   regression targets.
2. **Define the monoidal monotone** over the monoidal-preorder class: a monotone
   map `f` with `I_Q ≤ f(I_P)` and `f(p₁) ⊗ f(p₂) ≤ f(p₁ ⊗ p₂)`. Prove that,
   between thin bases, this is precisely a `LaxMonoidalFunctor` — a biconditional,
   both directions, so the repair of step 1 is certified by the book's own
   definition.
3. **Define strong and strict at the preorder level** using the induced
   equivalence and object equality respectively, and prove strict ⇒ strong ⇒ lax,
   matching `MonoidalFunctor_Is_Lax` and `StrictMonoidalFunctor`. State that the
   two strengthenings are proper: after step 1 the lax level must admit a map
   that is not strong (that separating witness is the floor map of the §2.2.5
   Example 2.42 issue; here it is enough to record the obligation).
4. **Introduce the oplax dual.** Prefer the library's duality architecture over a
   duplicated class: define an oplax monoidal functor as a lax monoidal functor
   between the opposite monoidal categories, using
   `Construction/Opposite/Monoidal.v:92` (`Monoidal_op`), in the style of
   `Comonad := @Monad (C^op) (M^op)`; then derive the covariant accessors
   `F (x ⨂ y) ~> F x ⨂ F y` and `F I ~> I` as definitional op-reads, and specialise
   to the preorder level as the oplax monoidal monotone of the remark. Update the
   `Functor/Structure/Monoidal.v:34–36` header, which currently disclaims the
   variant.
5. Exercise the trichotomy with at least one witness between thin bases, so the
   classes are not left uninhabited outside the `Id`/`Compose` closure.

In-tree donors: `Functor/Structure/Monoidal.v:77,110,138`,
`Functor/Structure/Monoidal/Strict.v:54`,
`Functor/Structure/Monoidal/Id.v:73,83`,
`Functor/Structure/Monoidal/Compose.v:291,333`,
`Construction/Opposite/Monoidal.v:92`, `Construction/Enriched/Two.v:175,183`,
`Instance/Two/Monoidal.v:105`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.41 (printed p. 55): the
      lax class demands the two one-directional comparisons and nothing that
      forces them to be invertible; `≈` on morphisms, never `=`
- [ ] **Library defect fixed** — `LaxMonoidalFunctor`
      (`Functor/Structure/Monoidal.v:110`) currently requires the isomorphism
      fields `pure_left`, `pure_right`, `ap_assoc` (`:119–123`, no defaults),
      which over a thin base collapse "lax" into "strong" and exclude the book's
      canonical lax-not-strong example; the class header at `:44–47` asserts the
      opposite. Either the fields go or they are replaced by non-invertible
      composites, and the header is corrected either way
- [ ] The biconditional "monoidal monotone between thin bases = lax monoidal
      functor" is proved in both directions
- [ ] strict ⇒ strong ⇒ lax proved at the preorder level
- [ ] The oplax dual exists, obtained through `Monoidal_op` rather than as a
      duplicated class where that is workable, and the disclaiming comment at
      `Functor/Structure/Monoidal.v:34–36` is updated
- [ ] At least one monoidal monotone between thin bases is constructed, so no
      level of the trichotomy is left without a witness
- [ ] No `Admitted`, `admit` or `Axiom` in the new or repaired files
- [ ] `Print Assumptions` reports "Closed under the global context" for the
      monoidal-monotone class, the biconditional, and the oplax dual
- [ ] The repair does not regress `Functor/Structure/Monoidal/Id.v`,
      `Functor/Structure/Monoidal/Compose.v` or
      `Construction/DecoratedCospan.v`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the lax/oplax layer is
      flagship-level and its current shape is described there

## Verification

```
coqc -R . Category Functor/Structure/Monoidal.v
coqc -R . Category Functor/Structure/Monoidal/Oplax.v
coqc -R . Category Functor/Structure/Monoidal/Preorder.v
rg -n 'pure_left|pure_right|ap_assoc' Functor/Structure/Monoidal.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions MonoidalMonotone.
Print Assumptions monoidal_monotone_iff_lax.
Print Assumptions OplaxMonoidalFunctor.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the lax
class no longer implies the strong one over a thin base (the reviewer should be
able to state the floor-map counterexample and see that nothing rules it out);
the oplax comparisons point the other way in both clauses; the trichotomy
statements are about the preorder-level notion, not only about functors.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the symmetric monoidal preorder class these
maps go between).

<!-- catalog: {"ids":["7sketches:2.2.5:def41","7sketches:2.2.5:remark-oplax"],"deps":["7sketches:2.2.1:def2"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: Inclusion and floor as monoidal monotones between ℕ and ℝ"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.2.5:example42]
deps_item_ids: [7sketches:2.2.5:def41, 7sketches:2.2.1:example4, 7sketches:2.2.4:example30]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.5 Example 2.42 — two
monoidal monotones in opposite directions between the naturals and the reals
under addition. Printed p. 56; PDF p. 68. Item covered:
`7sketches:2.2.5:example42`.

## Background

The inclusion of the naturals into the reals preserves the additive unit and sum
on the nose, so it is a strict monoidal monotone; the floor map back is monotone
and satisfies the lax comparison `⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋`, but the inequality can be
strict, so it is lax and not even strong
([Wikipedia: Floor and ceiling functions](https://en.wikipedia.org/wiki/Floor_and_ceiling_functions),
[nLab: lax monoidal functor](https://ncatlab.org/nlab/show/lax+monoidal+functor)).
This is the standard witness that the lax level of the definition is not vacuous.

## Current state in the library

Nothing of the example is available, and one of its two obstacles is a defect
rather than a gap.

- No reals. `rg -n 'Require.*Reals|Rdefinitions|QArith|R_scope|Rplus|Rle\b|Rabs'`
  over every `*.v` returns 0 hits; the only "real number" string is prose at
  `Instance/ZX.v:177–178`. Introducing `ℝ` (and `ℤ`) as a carrier and as a
  `Proset` is the obligation of #759.
- No floor or ceiling: `rg -n 'floor'` returns 0 hits.
- No additive monoidal structure on `(ℕ, ≤)`. The order exists twice —
  `Instance/Proset.v:47`
  (`LessThanEqualTo_Category := @Proset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder`)
  and `Instance/Omega.v:72` (`Omega`, over the Type-valued `le_t` at `:28`) — but
  there is no bifunctor with `fobj := Nat.add` on either, no unit `0`, and no
  `@Monoidal` instance; `rg -n 'add_le_mono|mul_le_mono|le_mono'` returns 0 hits,
  so even monotonicity of `+` with respect to `≤` is never stated. The near-miss
  to avoid citing: `(nat, +, 0)` *does* appear as a symmetric monoidal structure
  in-tree, at `Instance/FinSet.v:250` (`FinSet_Cocartesian`, `product_obj := m + n`,
  with `FinSet_Initial` at `:223`) and `Instance/Shapes.v:429` — but the homs
  there are functions between finite sets, not inequalities, so those are
  different categories and not this monoidal preorder.
- The lax half of the example is additionally blocked by the over-strengthened
  `LaxMonoidalFunctor` class recorded in the §2.2.5 Definition 2.41 issue: its
  `ap_assoc` field (`Functor/Structure/Monoidal.v:119–123`) fails for the floor
  map, since `(⌊0.5⌋ + ⌊0.5⌋) + ⌊0⌋ = 0` while `⌊0.5 + (0.5 + 0)⌋ = 1`.

## Work to be done

Suggested module: `Instance/Poset/Numeric/Monoidal.v`, alongside the numeric
carriers of #759.

1. Give `(ℕ, ≤, 0, +)` and `(ℝ, ≤, 0, +)` their monoidal-preorder structures
   through the smart constructor of the §2.2.1 Definition 2.2 issue; the
   monotonicity clause is `Nat.add_le_mono` and its real counterpart, neither of
   which is currently used anywhere in the tree.
2. Build the inclusion `ℕ → ℝ` and prove it a **strict** monoidal monotone: the
   unit and product conditions hold as equalities, and the monotonicity clause is
   the compatibility of the inclusion with both orders.
3. Build the floor map `ℝ → ℕ` (from `Coq.Reals`' `up`, or as a definition with
   its characteristic inequalities proved) and prove it a **lax** monoidal
   monotone: monotone, `0 ≤ ⌊0⌋`, and `⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋`.
4. Prove the separating half the example turns on: floor is **not** strong,
   by exhibiting `x = y = 1/2` with `⌊x⌋ + ⌊y⌋ = 0` and `⌊x + y⌋ = 1`, stated as
   a refutation in the style of `Instance/Two.v:122`'s `TwoHom_Y_X_absurd`. This
   makes the whole example the regression test for the `LaxMonoidalFunctor`
   repair: before the repair the lax half cannot even be stated.
5. Disclose in the header that `Coq.Reals` brings the standard library's
   classical axioms, so this file lives in the `Instance/` layer per the scoping
   in docs/AXIOMS.md, and record the expected `Print Assumptions` output there.

In-tree donors: `Instance/Proset.v:33,47`, `Instance/Omega.v:28,72`,
`Instance/Two.v:122` (the refutation idiom), the numeric carriers of #759, the
monoidal-monotone class of the §2.2.5 Definition 2.41 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 2.42 (printed p. 56); `≈` on
      morphisms, never `=`
- [ ] `(ℕ, ≤, 0, +)` and `(ℝ, ≤, 0, +)` are symmetric monoidal preorders in the
      sense of the §2.2.1 class, not ad-hoc records
- [ ] The inclusion is proved **strict**, with both conditions as equalities
- [ ] The floor map is proved **lax** — and this must be checked against the
      repaired lax class, not against a bespoke record
- [ ] Floor is proved **not strong**, by a genuine refutation at `x = y = 1/2`
- [ ] The axiom cost of `Coq.Reals` is disclosed in the header and recorded in
      docs/AXIOMS.md; `Print Assumptions` output for the real-side artifacts
      matches the disclosure
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` introduced by this
      development itself
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Poset/Numeric/Monoidal.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Nat_Add_MonoidalPreorder.
Print Assumptions R_Add_MonoidalPreorder.
Print Assumptions nat_into_R_strict_monotone.
Print Assumptions floor_lax_monotone.
Print Assumptions floor_not_strong.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
strictness verdicts match the book (inclusion strict, floor lax only); the
non-strongness statement is a refutation, not an omission; the file's axiom
disclosure matches what `Print Assumptions` actually prints.

## Dependencies

Depends on: #759 (the integers and the reals as ordered carriers).
Depends on: 7sketches:2.2.5:def41 (the monoidal-monotone class, including the
repair of the lax level without which the floor half cannot be stated).
Depends on: 7sketches:2.2.1:example4 (ℝ under addition as a symmetric monoidal
preorder).
Depends on: 7sketches:2.2.4:example30 (ℕ under addition as a symmetric monoidal
preorder).

<!-- catalog: {"ids":["7sketches:2.2.5:example42"],"deps":["#759","7sketches:2.2.5:def41","7sketches:2.2.1:example4","7sketches:2.2.4:example30"]} -->

---8<---

```yaml
title: "Seven Sketches 2.2: The monoidal monotones between Bool and Cost"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.2.5:construction-bool-to-cost, 7sketches:2.2.5:ex43, 7sketches:2.2.5:ex44]
deps_item_ids: [7sketches:2.2.5:def41, 7sketches:2.2.4:example37]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.2.5 — the unnumbered
construction of the map from the Booleans to the costs (printed p. 56, PDF p. 68),
Exercise 2.43 (verifying it is a monoidal monotone, and deciding strictness) and
Exercise 2.44 (the two candidate maps back, and the same three questions for
each). Items covered: `7sketches:2.2.5:construction-bool-to-cost`,
`7sketches:2.2.5:ex43`, `7sketches:2.2.5:ex44`.

## Background

Sending `false` to infinite cost and `true` to zero cost is a monoidal monotone
from the Boolean base to Lawvere's cost base, and it is the bridge between the
"can one get from a to b" and the "how expensive is it" readings of enrichment
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space),
[nLab: monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor)). Back
the other way there are two natural candidates — "is the cost zero?" and "is the
cost finite?" — and they behave differently, which is what makes change of base
along them interesting.

## Current state in the library

The source base exists, the target base does not, and the notion connecting them
has no instance between thin categories.

- `Bool` is in-tree and faithful: `Instance/Two.v:134` (`_2`), with
  `Instance/Two/Monoidal.v:80` (`Two_Cartesian`, `product_obj := two_meet`, i.e.
  conjunction), `:98` (`Two_Terminal`, `terminal_obj := TwoY`, i.e. `true`) and
  `:105` (`Two_Monoidal := @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal`).
- `Cost` is entirely absent: `rg -n '\bCost\b'` finds only the English word,
  `rg -in 'infty|Infinity'` returns 0 hits, and no numeric carrier is ever
  imported (`Require.*Reals|Rdefinitions|QArith`: 0 hits). Its construction is
  the obligation of the §2.2.4 Example 2.37 issue.
- No monoidal functor between thin categories exists anywhere:
  `LaxMonoidalFunctor` (`Functor/Structure/Monoidal.v:110`) is inhabited only by
  the closure instances `Functor/Structure/Monoidal/Id.v:73` and
  `Functor/Structure/Monoidal/Compose.v:291`, and the phrase "monoidal monotone"
  has 0 hits. The only map-of-preorders API,
  `Construction/Enriched/Two.v:175` (`Record MonotoneMap`), carries no unit or
  product condition, so none of the three checks the exercises ask for can be
  posed against it.

## Work to be done

Suggested module: `Instance/Cost/Bool.v` (the two bases already having their own
files).

1. Define `g : Bool → Cost` by `g(false) := ∞`, `g(true) := 0`, and prove it a
   monoidal monotone: monotone for the reversed order of `Cost`, the unit
   condition `0 ≥ g(true)`, and the product condition
   `g(p₁) + g(p₂) ≥ g(p₁ ∧ p₂)`. Settle Exercise 2.43's fourth question — whether
   `g` is strict — with a proof or a refutation, not a remark.
2. Define `d : Cost → Bool` (`true` exactly at zero cost) and `u : Cost → Bool`
   (`true` exactly at finite cost), and settle, for each, all three of Exercise
   2.44's questions: monotonicity, condition (a), condition (b), and strictness.
   Where a condition fails, the answer must be a refutation with an explicit
   witness.
3. Record the pair `d`, `u` as the two base-change maps the §2.4.1 issues use, so
   that "different monoidal monotones give different preorders" has its two
   inputs available from one place.

In-tree donors: `Instance/Two.v:38,122,134`, `Instance/Two/Monoidal.v:80,98,105`,
the `Cost` base of the §2.2.4 Example 2.37 issue, the monoidal-monotone class of
the §2.2.5 Definition 2.41 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches §2.2.5 (printed p. 56); `≈` on
      morphisms, never `=`
- [ ] `g` is constructed and proved a monoidal monotone, with all three clauses
      as named lemmas
- [ ] Every one of the six questions of Exercise 2.44 is answered by a proof or
      by an explicit refutation — none left as prose
- [ ] The strictness verdict for `g` (Exercise 2.43) is proved or refuted
- [ ] The maps are stated against the monoidal-monotone class, so they are
      genuine instances rather than bare functions with side lemmas
- [ ] No `Admitted`, `admit` or `Axiom` in the new file
- [ ] `Print Assumptions` reports the disclosed axiom set (inherited from the
      `Cost` carrier) and nothing more
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Cost/Bool.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions bool_to_cost.
Print Assumptions bool_to_cost_monotone.
Print Assumptions cost_to_bool_zero.
Print Assumptions cost_to_bool_finite.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
`Cost` order really is reversed (so `∞` is the bottom); the unit and product
conditions are stated in the lax direction of Definition 2.41; every negative
answer is a refutation.

## Dependencies

Depends on: 7sketches:2.2.5:def41 (the monoidal-monotone class).
Depends on: 7sketches:2.2.4:example37 (the `Cost` monoidal preorder).

<!-- catalog: {"ids":["7sketches:2.2.5:construction-bool-to-cost","7sketches:2.2.5:ex43","7sketches:2.2.5:ex44"],"deps":["7sketches:2.2.5:def41","7sketches:2.2.4:example37"]} -->

---8<---

```yaml
title: "Seven Sketches 2.3: Preorders are exactly Bool-categories — upgrading the two translations to a bijection"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.3.2:thm49, 7sketches:2.3.2:ex50]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.3.2 — Theorem 2.49 (the
one-to-one correspondence between preorders and Bool-categories; printed p. 58,
PDF p. 70) and Exercise 2.50 (both round trips are identities; printed p. 59,
PDF p. 71). Items covered: `7sketches:2.3.2:thm49`, `7sketches:2.3.2:ex50`. The
theorem and the exercise are one piece of work — the exercise supplies exactly
the content the theorem's word "one-to-one" asserts — and are therefore filed
together.

## Background

Enriching in the two-element order recovers ordinary order theory: a Bool-valued
hom assigns to each pair a truth value, the unit axiom forces the diagonal to be
true (reflexivity) and the composition axiom forces transitivity, so
Bool-categories and preorders are the same thing
([nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category),
[nLab: preorder](https://ncatlab.org/nlab/show/preorder)). This is the smallest
instance of Lawvere's programme and the template for the metric case.

## Current state in the library

Both translations exist and are the book's; the correspondence they are supposed
to constitute does not.

- `Construction/Enriched/Two.v:165` —
  `Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder`,
  where `↔` is `iffT` (`Lib/Foundation.v:72`), i.e. a bare pair of functions
  carrying no inverse laws. `iffT` is satisfied by translations that lose
  information, so "one-to-one" is not asserted anywhere.
- The two legs are faithful to the book's proof.
  `Construction/Enriched/Two.v:71` (`TwoPreorder_of_Enriched`) defines
  `tpre_le x y := @ehom _ _ E x y = TwoY`, takes reflexivity from `eid` through
  `Instance/Two.v:38` (`two_from_top : TwoHom TwoY z → z = TwoY`) and
  transitivity from `ecompose` under the meet; `:131`
  (`Enriched_of_TwoPreorder`) goes back.
- The round trips are missing. `Construction/Enriched/Two.v:104`
  (`ehom_of_le_complete : tpre_le P x y → ehom_of_le P x y = TwoY`) and `:113`
  (`ehom_of_le_sound`) are the only fragments, and they mention `ehom_of_le`
  alone; no lemma in the tree names both `TwoPreorder_of_Enriched` and
  `Enriched_of_TwoPreorder`, so neither round trip is stated, and the pair is
  never packaged as a bijection, isomorphism or equivalence.
- A disclosure the formalization must carry: the in-tree right-hand side is not
  "preorders" but *decidable* preorders — `TwoPreorder`
  (`Construction/Enriched/Two.v:60`) carries the field `tpre_dec`
  (`:65`). At the literal base `V = Bool` this is constructively unavoidable
  (producing an element of the two-element `TwoObj` from a Type-valued relation
  *is* a decision), and the file header says so, but the theorem statement must
  say so too.

## Work to be done

Suggested site: extend `Construction/Enriched/Two.v` (the material belongs beside
the two translations it completes).

1. Prove round trip (1): for a `TwoPreorder P`,
   `tpre_le (TwoPreorder_of_Enriched (Enriched_of_TwoPreorder P)) x y ↔ tpre_le P x y`,
   composing `ehom_of_le_complete` and `ehom_of_le_sound`, and additionally prove
   that the two decision procedures agree — without which the round trip is only
   at the level of the relation and not of the `TwoPreorder` record.
2. Prove round trip (2), which has no in-tree fragment at all:
   `ehom_of_le (TwoPreorder_of_Enriched E) x y = @ehom _ _ E x y` for every
   `E : @Enriched _2 Two_Monoidal`, by case analysis on `ehom`.
3. Package the correspondence: replace or supplement `Enriched_Two_preorder` with
   a statement carrying the inverse laws — an isomorphism of types, or a pair of
   maps with both composites proved to be the identity — so that the book's
   "one-to-one correspondence" is what the tree asserts.
4. State the decidability restriction in the theorem, and record in the header why
   it cannot be dropped at `V = Bool`.
5. Correct the section heading at `Construction/Enriched/Two.v:12`, which
   currently claims that categories enriched over the two-element order are
   "exactly" preorders — a claim the `iffT` does not support and which step 3 is
   what actually earns.

In-tree donors: `Construction/Enriched/Two.v:60,65,71,104,113,131,165`,
`Instance/Two.v:38`, `Instance/Two/Monoidal.v:105`, `Lib/Foundation.v:72`,
`Theory/Isomorphism.v:113` (the two-round-trips idiom).

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Theorem 2.49 (printed p. 58) and
      Exercise 2.50 (printed p. 59): the conclusion is a one-to-one
      correspondence, not a pair of translations; `≈` on morphisms, never `=`
- [ ] Both round trips proved, including agreement of the decision procedure in
      round trip (1)
- [ ] The correspondence packaged as a bijection/isomorphism, with
      `Enriched_Two_preorder` either upgraded or given a stronger sibling
- [ ] The decidability hypothesis appears in the statement and its
      unavoidability at `V = Bool` is recorded in the header
- [ ] **Library defect fixed** — the section heading at
      `Construction/Enriched/Two.v:12` asserts that enrichment over the
      two-element order is "exactly" a preorder, which no in-tree statement
      proves; after this issue it does, or the heading is qualified
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` reports "Closed under the global context" for both
      round trips and for the packaged correspondence
- [ ] No new file is required (the work extends `Construction/Enriched/Two.v`,
      already registered in `_CoqProject`); if the round trips are split into a
      sibling file, that file is registered
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated where it describes the
      `Construction/Enriched/Two.v` correspondence

## Verification

```
coqc -R . Category Construction/Enriched/Two.v
rg -n 'iffT|↔' Construction/Enriched/Two.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions preorder_enriched_roundtrip.
Print Assumptions enriched_preorder_roundtrip.
Print Assumptions Enriched_Two_preorder_bijection.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
packaged statement really carries inverse laws (an `iffT` alone does not count);
round trip (2) is proved, not assumed; the decidability restriction is visible in
the statement rather than only in a comment.

## Dependencies

Depends on: #223 (preorders as thin categories — the vocabulary the statement is
phrased in).

<!-- catalog: {"ids":["7sketches:2.3.2:thm49","7sketches:2.3.2:ex50"],"deps":["#223"]} -->

---8<---

```yaml
title: "Seven Sketches 2.4: The category of preorders, the category of Bool-categories, and the equivalence between them"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.4.2:remark71]
deps_item_ids: [7sketches:2.3.2:thm49]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.4.2 Remark 2.71 — the
observation that Theorem 2.49 together with Example 2.70 is an equivalence of
categories between preorders with monotone maps and Bool-categories with
Bool-functors. Printed p. 66; PDF p. 78. Item covered:
`7sketches:2.4.2:remark71`.

## Background

The object-level correspondence between preorders and Bool-categories extends to
morphisms — a Bool-functor is exactly a monotone map — and the two
correspondences together assemble into an equivalence of categories
([nLab: equivalence of categories](https://ncatlab.org/nlab/show/equivalence+of+categories),
[nLab: enriched functor](https://ncatlab.org/nlab/show/enriched+functor)). It is
the first place in the book where "the same thing" is upgraded from a bijection
of objects to a statement about categories.

## Current state in the library

Both legs of the would-be equivalence exist pointwise; neither category exists.

- Object leg: `Construction/Enriched/Two.v:165`
  (`Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder`).
- Morphism leg: `Construction/Enriched/Two.v:183`
  (`EnrichedFunctor_Two_monotone (P Q : TwoPreorder) : EnrichedFunctor _2 … ↔ MonotoneMap P Q`),
  with `Record MonotoneMap` at `:175`.
- **No category of preorders.** `Instance/Proset.v:33` (`Proset P`) and
  `Instance/Poset.v:116` (`Poset P`) build a *single* preorder *as* a category;
  nothing has preorders as objects and monotone maps as morphisms. Both files'
  headers point at an object they do not construct — `Instance/Proset.v:20`
  ("See also [Ord], for the category of preordered sets") and
  `Instance/Poset.v:21–22` ("See also [Pos] … whose objects are posets"). The
  poset case is the obligation of #641.
- **No category of Bool-categories.** `Construction/Enriched/Fun.v:270`
  (`Enriched_Fun`) has `obj := EnrichedFunctor K C D` at `:271`, i.e. its objects
  are V-*functors*; there is no category whose objects are V-categories, even
  though the identity and composite V-functors exist
  (`Construction/Enriched/Compose.v:25,49`). `rg 'VCat|ECat|EnrichedCat'` returns
  0 hits.
- Consequently no equivalence: no lemma anywhere mentions both a category of
  preorders and a category of enrichments.

## Work to be done

Suggested modules: `Instance/Preord.v` (the category of preorders and monotone
maps, sibling to the `Pos` of #641) and `Construction/Enriched/Cat.v` (the
category of V-categories and V-functors), with the comparison in
`Construction/Enriched/Two.v` or a new `Construction/Enriched/Two/Equivalence.v`.

1. Build `Preord`: objects are preorders (the `TwoPreorder` record already used
   by the §2.3.2 correspondence, or a decidability-free variant with the
   restriction disclosed), morphisms are `MonotoneMap`s, with the hom-setoid
   identifying two monotone maps when their underlying functions agree
   pointwise. Identity and composition are immediate.
2. Build `VCat K`, the category of `Enriched K` categories and `EnrichedFunctor`s
   over a fixed monoidal base, using `Construction/Enriched/Compose.v:25,49` for
   identity and composition and settling the hom-setoid (equality of object maps
   plus the hom-component condition). This is a reusable object: the base-change
   construction of §2.4.1 is a functor between two such categories.
3. Build the two functors `Preord ⟶ VCat _2` and back, on objects by the §2.3.2
   correspondence and on morphisms by `EnrichedFunctor_Two_monotone`, and prove
   functoriality (identities and composites are preserved — the content that the
   two pointwise `iffT`s do not supply).
4. Assemble the equivalence with `Theory/Equivalence.v:151`
   (`EquivalenceOfCategories`); the unit and counit isomorphisms are the round
   trips proved by the §2.3.2 issue, so this step should consume them rather than
   redo them.
5. Record the decidability restriction inherited from `V = Bool` in the header,
   and state precisely which category of preorders the equivalence is with.

In-tree donors: `Construction/Enriched/Two.v:165,175,183`,
`Construction/Enriched/Compose.v:25,49`, `Construction/Enriched/Fun.v:270`,
`Theory/Equivalence.v:151,163,172`, `Instance/Proset.v:33`,
`Instance/Poset.v:116`, the `Pos` of #641.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 2.71 (printed p. 66): the
      conclusion is an equivalence of categories, with both functors and both
      natural isomorphisms; `≈` on morphisms, never `=`
- [ ] A category of preorders and monotone maps exists in the library proper (not
      in `Test/`), and the dangling `[Ord]` reference at `Instance/Proset.v:20`
      is either resolved or corrected
- [ ] A category of V-categories and V-functors exists over an arbitrary monoidal
      base, usable by the §2.4.1 change-of-base issue
- [ ] Both comparison functors are proved functorial, not merely defined on
      objects and morphisms
- [ ] The equivalence is stated with `Theory/Equivalence.v`'s vocabulary and its
      round trips are inherited from the §2.3.2 issue
- [ ] The decidability restriction is stated, not only commented
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for both categories,
      both functors and the equivalence
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: a category of V-categories is
      flagship-level for the enriched development

## Verification

```
coqc -R . Category Instance/Preord.v
coqc -R . Category Construction/Enriched/Cat.v
coqc -R . Category Construction/Enriched/Two/Equivalence.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Preord.
Print Assumptions VCat.
Print Assumptions Preord_to_BoolCat.
Print Assumptions BoolCat_to_Preord.
Print Assumptions Preord_BoolCat_equivalence.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
objects of the second category are V-categories (not V-functors, which is what
`Construction/Enriched/Fun.v` already provides); the equivalence carries both
natural isomorphisms; the statement names which preorders are in scope.

## Dependencies

Depends on: 7sketches:2.3.2:thm49 (the object-level correspondence with its round
trips, which supplies the unit and counit).
Depends on: #641 (Pos, the category of posets and monotone maps — the sibling
construction and the natural home for the shared monotone-map API).

<!-- catalog: {"ids":["7sketches:2.4.2:remark71"],"deps":["7sketches:2.3.2:thm49","#641"]} -->

---8<---
```yaml
title: "Seven Sketches 2.3: Lawvere metric spaces as Cost-categories, and short maps as Cost-functors"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.3.3:def53, 7sketches:2.3.3:example54, 7sketches:2.3.3:ex55, 7sketches:2.4.2:example72]
deps_item_ids: [7sketches:2.2.4:example37]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.3.3 — Definition 2.53
(a Lawvere metric space is a Cost-category; printed p. 61, PDF p. 73),
Example 2.54 (the reals with the absolute-difference distance; printed p. 61,
PDF p. 73) and Exercise 2.55 (what changes when the point at infinity is removed
from the base; printed p. 61, PDF p. 73) — together with §2.4.2 Example 2.72
(Cost-functors are the distance-nonincreasing maps; printed p. 66, PDF p. 78),
which is the morphism half of the same identification. Items covered:
`7sketches:2.3.3:def53`, `7sketches:2.3.3:example54`, `7sketches:2.3.3:ex55`,
`7sketches:2.4.2:example72`.

## Background

Lawvere's observation is that a metric space is a category enriched in the
non-negative extended reals ordered by `≥` with addition as tensor: the unit
axiom becomes `d(x,x) = 0` and the composition axiom becomes the triangle
inequality, while symmetry and the separation axiom are simply not asked for
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space),
[nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category)). The
enriched functors between such spaces are exactly the 1-Lipschitz (short) maps
([Wikipedia: Lipschitz continuity](https://en.wikipedia.org/wiki/Lipschitz_continuity)).

## Current state in the library

The generic notion is present; the base it must be instantiated at is not, and
the two identifications are unstated.

- `Construction/Enriched.v:111` — `Class Enriched (K : Category) `{@Monoidal K}`
  with `eobj`, `ehom : eobj → eobj → K`, `eid {x} : I ~{K}~> (x ⟿ x)` and
  `ecompose {x y z} : (y ⟿ z) ⨂ (x ⟿ y) ~{K}~> (x ⟿ z)` — the V-category class,
  already credited against Definition 2.46, which is PRESENT.
- `Construction/Enriched.v:145` — `EnrichedFunctor`, likewise present and
  credited against Definition 2.69.
- The `Cost` base is absent in every layer. `rg -n '\bCost\b'` finds only the
  English word; `rg -in 'infty|Infinity'` returns 0 hits; no numeric carrier is
  imported anywhere (`Require.*Reals|Rdefinitions|QArith|Rle\b`: 0 hits). Its
  construction is the obligation of the §2.2.4 Example 2.37 issue.
- No metric of any kind is formalized: every occurrence of "metric" is background
  prose, at `Construction/Enriched.v:40,49,74–77`, `Instance/Poset.v:39,75–77`,
  `Theory/Profunctor.v:46,100` and `Construction/Karoubi.v:45,86` — several of
  which name Lawvere's base explicitly as something the library does *not* carry.
- No Lipschitz/short-map notion: `rg -in 'lipschitz|nonexpansive|short map'`
  returns nothing relevant, and `rg -n '\bMet\b|MetricSpaces'` returns 0 hits.
- Only one monoidal structure on a thin category exists at all
  (`Instance/Two/Monoidal.v:105`, `Two_Monoidal`), so even given a carrier the
  order-reversed base `([0,∞], ≥, 0, +)` would have to be built from scratch.

## Work to be done

Suggested modules: `Instance/Cost/Metric.v` (the definition and its instances),
with the base itself in the file the §2.2.4 Example 2.37 issue creates.

1. Define a Lawvere metric space as `@Enriched Cost Cost_Monoidal`, and prove the
   unpacking lemmas that make the definition usable: `d(x,x) = 0` (from `eid`
   under the reversed order) and `d(x,y) + d(y,z) ≥ d(x,z)` (from `ecompose`),
   each as a named lemma rather than as a field access. Provide the smart
   constructor in the other direction, taking a carrier and a distance with those
   two properties and returning the enrichment.
2. Prove Example 2.54: the reals with `d(x,y) := |y − x|` form a Lawvere metric
   space. The carrier comes from #759; the two axioms are reflexivity of
   subtraction and the triangle inequality for absolute value.
3. Prove Example 2.72, the morphism half: a `Cost`-functor between two Lawvere
   metric spaces is exactly a function `F` with `d_X(x₁,x₂) ≥ d_Y(F x₁, F x₂)` —
   a biconditional, both directions, so "Cost-functor" and "short map" are
   interchangeable in later files.
4. Discharge Exercise 2.55: build the sub-base `(ℝ≥0, ≥, 0, +)` without the point
   at infinity, and characterize the difference — an enrichment in the sub-base is
   a Lawvere metric space all of whose distances are finite. State it as a
   biconditional between the two enrichments over a common carrier, so the
   exercise's "what is ruled out" has a proof rather than an explanation.
5. Record in the header that symmetry and separation are deliberately absent, and
   point forward to the §2.4.2 Exercise 2.73 issue where they are restored as
   dagger and skeletality.

In-tree donors: `Construction/Enriched.v:111,145`,
`Construction/Enriched/Two.v` (the `V = Bool` development, the template to
imitate at `V = Cost`), `Instance/Two/Monoidal.v:105`, the `Cost` base of the
§2.2.4 Example 2.37 issue, the numeric carriers of #759.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.53 (printed p. 61),
      Example 2.54, Exercise 2.55 and Example 2.72 (printed p. 66); `≈` on
      morphisms, never `=`
- [ ] The two axioms are proved as standalone lemmas in the familiar metric form
      (`d(x,x) = 0`, triangle inequality), and a smart constructor goes back
- [ ] The reals are exhibited as a Lawvere metric space
- [ ] "Cost-functor = short map" is proved as a biconditional, both directions
- [ ] Exercise 2.55's comparison is a proved biconditional, not a remark
- [ ] The absence of symmetry and separation is disclosed in the header with a
      forward pointer to the dagger/skeletal issue
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` introduced by this
      development itself; the inherited `Coq.Reals` axioms are declared, and
      docs/AXIOMS.md is updated
- [ ] `Print Assumptions` recorded for every principal artifact
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: Lawvere metric spaces are
      flagship-level and the enriched section currently records their absence

## Verification

```
coqc -R . Category Instance/Cost/Metric.v
rg -n 'lipschitz|short' Instance/Cost/Metric.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions LawvereMetricSpace.
Print Assumptions lawvere_dist_refl.
Print Assumptions lawvere_triangle.
Print Assumptions R_LawvereMetricSpace.
Print Assumptions cost_functor_iff_short.
Print Assumptions finite_cost_enrichment_iff.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the base
order is genuinely reversed; the definition is an instance of the existing
`Enriched` class rather than a bespoke record; the short-map statement is a
biconditional.

## Dependencies

Depends on: 7sketches:2.2.4:example37 (the `Cost` monoidal preorder).
Depends on: #759 (the reals as an ordered carrier, needed for Example 2.54).

<!-- catalog: {"ids":["7sketches:2.3.3:def53","7sketches:2.3.3:example54","7sketches:2.3.3:ex55","7sketches:2.4.2:example72"],"deps":["7sketches:2.2.4:example37","#759"]} -->

---8<---

```yaml
title: "Seven Sketches 2.3: Cost-weighted graphs and their shortest-path Lawvere metric space"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.3.3:construction-weighted-graph-metric, 7sketches:2.3.3:ex58]
deps_item_ids: [7sketches:2.3.3:def53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.3.3 — the unnumbered
construction presenting a Lawvere metric space by a Cost-weighted graph, whose
distance is the total length of a shortest directed path (printed p. 62,
PDF p. 74), and Exercise 2.58, which fills out the distance table of the
four-vertex graph of display (2.56) (printed p. 62, PDF p. 74). Items covered:
`7sketches:2.3.3:construction-weighted-graph-metric`, `7sketches:2.3.3:ex58`.

## Background

A directed graph whose edges carry costs presents a Lawvere metric space: the
distance from one vertex to another is the least total weight of a directed path
between them, infinite when there is none
([Wikipedia: Shortest path problem](https://en.wikipedia.org/wiki/Shortest_path_problem),
[nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).
It is the metric analogue of presenting a preorder by a Hasse diagram, which is
the special case where the weights are Boolean
([nLab: free category](https://ncatlab.org/nlab/show/free+category)).

## Current state in the library

Only the Boolean case exists, and only as a relation rather than as a
presentation.

- `Instance/Lambda/Multi.v:46` — `Inductive multi (R : crelation X) : crelation X`
  with `multi_refl`/`multi_step`, `multi_trans` at `:61` and `multi_PreOrder` at
  `:74`: the reflexive-transitive closure of an edge relation, i.e. exactly the
  Boolean-weighted case of this construction (file registered in
  `_CoqProject:209`). Presenting a preorder by a graph in this way is the
  obligation of #768.
- `Construction/Enriched/Two.v:131` — `Enriched_of_TwoPreorder` completes the
  Boolean case to the enriched form, turning the generated preorder into a
  Bool-category.
- Everything specific to the Cost case is missing. (1) No `Cost` base and no
  `[0,∞]` (`rg -n '\bCost\b'`, `rg -in 'infty|infinity'`: no code hits), so edge
  labels and the value `∞` cannot be written. (2) No weighted graph:
  `Construction/Free/Quiver.v:54` (`Class Quiver`) carries only
  `edges : nodes → nodes → uedges` at `:57`, an unlabelled Set-valued edge
  family; `rg -inE 'weighted graph|shortest path|edge weight'` finds nothing but
  one unrelated comment. (3) No free *enriched* category on a graph:
  `Construction/Free/Quiver.v:431` (`FreeOnQuiver`, with
  `FreeForgetfulAdjunction` at `:550`) builds the free ordinary category, whose
  homs are lists of edges — the paths themselves, not a best value over paths.
  (4) No vertex-indexed distance table and no `shortest path|floyd|warshall|dijkstra`
  anywhere (0 hits).

## Work to be done

Suggested module: `Instance/Cost/Graph.v`.

1. Define a `V`-weighted graph over a monoidal preorder `V`: a node type together
   with an edge-weight family `nodes → nodes → V`, generalizing
   `Construction/Free/Quiver.v:54`'s unweighted `edges`. Keep it `V`-generic —
   the Boolean, powerset and bottleneck cases of §2.3.4 and the matrix
   development of §2.5.3 all consume it.
2. Define the presented distance at `V = Cost`: the infimum over directed paths
   of the sum of the edge weights, with the empty path contributing `0` and the
   infimum over the empty set of paths contributing `∞`. The path type can be
   `Construction/Free/Quiver.v`'s free-category homs or `Lib/TList.v:47`'s
   `tlist`, so paths need not be re-invented.
3. Prove the construction lands in a Lawvere metric space: `d(x,x) = 0` because
   the empty path is available, and the triangle inequality because path
   concatenation is a map from a pair of paths to a path whose weight is the sum.
   These are exactly the two axioms of the §2.3.3 Definition 2.53 issue.
4. Prove that the Boolean case of the construction agrees with the presented
   preorder of #768 — i.e. change of base along the Boolean-to-Cost monotone
   sends one presentation to the other — so the analogy the book draws is a
   theorem and not a remark. (If that comparison is easier once the §2.4.1 base
   change exists, state it there and leave a pointer here.)
5. Discharge Exercise 2.58: build the four-vertex weighted graph of display
   (2.56) and evaluate the complete distance table, as decidable computations or
   `eq_refl` Examples in the style of `Instance/FinSet/Topos.v`, including the
   entries that are `∞`.

In-tree donors: `Construction/Free/Quiver.v:54,57,431,550`, `Lib/TList.v:47`,
`Instance/Lambda/Multi.v:46,61,74`, `Construction/Enriched/Two.v:131`,
`Instance/FinSet/Topos.v` (the `eq_refl` Example style), the Lawvere metric space
of the §2.3.3 Definition 2.53 issue.

## Definition of Done

- [ ] Statement fidelity to the §2.3.3 construction (printed p. 62) and
      Exercise 2.58; `≈` on morphisms, never `=`
- [ ] The weighted-graph notion is stated over an arbitrary monoidal preorder, not
      only over `Cost`, so §2.3.4 and §2.5.3 can reuse it
- [ ] The presented distance is proved to satisfy both Lawvere-metric axioms
- [ ] The Boolean case is proved to agree with the presented preorder of #768
      (here or, with a pointer, in the base-change issue)
- [ ] The distance table of display (2.56) is computed, unreachable entries
      included
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` recorded for the construction and both axioms
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Cost/Graph.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions WeightedGraph.
Print Assumptions graph_metric.
Print Assumptions graph_metric_refl.
Print Assumptions graph_metric_triangle.
Print Assumptions graph_2_56_distance_table.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
distance is a genuine infimum over paths (not a fold along one chosen path); the
unreachable entries really are `∞`; the weighted-graph type is base-generic.

## Dependencies

Depends on: 7sketches:2.3.3:def53 (Lawvere metric spaces as Cost-categories).
Depends on: #768 (the preorder presented by a graph — the Boolean case this
construction generalizes, and the comparison target).

<!-- catalog: {"ids":["7sketches:2.3.3:construction-weighted-graph-metric","7sketches:2.3.3:ex58"],"deps":["7sketches:2.3.3:def53","#768"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: V-matrices over a quantale, and the category Mat(V)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.3:def100, 7sketches:2.5.3:equation101, 7sketches:2.5.3:def-identity-matrix, 7sketches:2.5.3:ex103, 7sketches:2.5.3:ex104]
deps_item_ids: [7sketches:2.5.2:def90, 7sketches:2.5.1:prop87]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.3 — Definition 2.100
(a V-matrix is a function from a product of two sets to the quantale), the
numbered display (2.101) defining the generalized matrix product, the unnumbered
display defining the identity V-matrix, Exercise 2.103 (the two-by-two identity
matrix in three quantales) and Exercise 2.104 (the unit and associativity laws,
which make sets and V-matrices a category). Printed pp. 73–74; PDF pp. 85–86.
Items covered: `7sketches:2.5.3:def100`, `7sketches:2.5.3:equation101`,
`7sketches:2.5.3:def-identity-matrix`, `7sketches:2.5.3:ex103`,
`7sketches:2.5.3:ex104`.

## Background

Replacing the summation of ordinary matrix multiplication by a join and the
product by the tensor of a quantale gives a matrix calculus over any quantale;
the Boolean case is composition of relations and the cost case is min-plus
(tropical) matrix multiplication
([nLab: quantale](https://ncatlab.org/nlab/show/quantale),
[Wikipedia: Min-plus matrix multiplication](https://en.wikipedia.org/wiki/Min-plus_matrix_multiplication)).
Sets and V-matrices form a category, which is where the graph-presentation
algorithm of the same section lives
([nLab: category of relations](https://ncatlab.org/nlab/show/category+of+relations)).

## Current state in the library

The definition exists only at two fixed bases, one of them up to isomorphism
only, and never parameterized by a quantale.

- `V = Bool`: `Instance/Rel.v:45` — `Program Definition Rel : Category` with
  `hom := fun A B => A ~> Ensemble B`, `homset` the entrywise `↔`,
  `id := Singleton` and
  `compose := fun x y z f g a b => (exists e : y, In y (g a) e ∧ In z (f e) b)%type`.
  This *is* display (2.101) at `V = Bool` — the existential is the join, the
  conjunction is the tensor — and `id := Singleton` is the identity V-matrix
  (unit on the diagonal, bottom off it). The category obligations at `:54–81`
  discharge exactly the two laws of Exercise 2.104: `id_left`/`id_right` at
  `:66`/`:73` and `comp_assoc`/`comp_assoc_sym` at `:80`/`:81`.
- `V = Sets`: `Construction/Profunctor/Compose.v:267` — `prof_compose`, the coend
  formula `∫^d P(c,d) × Q(d,e)`, with the unitors
  `Construction/Profunctor/Laws.v:236` (`prof_unit_left_iso`) and `:395`
  (`prof_unit_right_iso`) and associativity `:722` (`prof_assoc_iso`) — all three
  only up to natural isomorphism, and explicitly not assembled into a category
  ("no category of all profunctors is formed",
  `Construction/Profunctor/Compose.v:65`).
- Nothing is parameterized by a base. There is no `Quantale` class (`rg -i
  quantale` yields a single prose mention at `Construction/Enriched.v:78`), so
  `M : X × Y → V` for a quantale `V` cannot be written; there is no matrix
  datatype (every "matrix" hit is background prose or the biproduct matrix
  calculus on morphisms in `Structure/Semiadditive.v`, `Structure/Bicartesian.v`,
  `Structure/Abelian.v`); and the ℕ and `Cost` instances Exercise 2.103 asks for
  have no carriers at all (`Instance/Proset.v:47` and `Instance/Omega.v:72` give
  ℕ under `≤` as a bare category with no tensor or unit).

## Work to be done

Suggested module: `Structure/Quantale/Matrix.v`, with the concrete instances in
`Instance/Cost/Matrix.v`.

1. Define `VMatrix V X Y := X → Y → V` over the quantale class of the §2.5.2
   Definition 2.90 issue, with the entrywise equivalence (two matrices agree when
   every entry does, up to the base's induced equivalence) as its setoid.
2. Define the product of display (2.101),
   `(M ∗ N)(x,z) := ⋁_{y} M(x,y) ⊗ N(y,z)`, and prove it respects the entrywise
   equivalence in both arguments.
3. Define the identity V-matrix — the unit on the diagonal and `⋁∅` off it — and
   prove Exercise 2.104(1), both unit laws.
4. Prove Exercise 2.104(2), associativity. Both proofs are where the quantale
   axioms are actually consumed: the tensor must distribute over joins, which is
   Proposition 2.87(b), so this step should cite that result rather than re-derive
   it.
5. Assemble `Mat V`, the category with sets as objects and V-matrices as
   morphisms, and prove `Mat Bool ≅ Rel` (or at least that `Rel`'s composition and
   identity are the `V = Bool` instances of steps 2 and 3) — the check that the
   generalization is faithful to the case the library already has.
6. Discharge Exercise 2.103: the two-by-two identity matrix written out in
   `(ℕ, ≤, 1, ·)`, in `Bool` and in `Cost`, as `eq_refl`/decidable Examples.

In-tree donors: `Instance/Rel.v:45,54–81`,
`Construction/Profunctor/Compose.v:65,267`,
`Construction/Profunctor/Laws.v:236,395,722`, `Structure/Limit/Product.v:51`
(`iprod`, the indexed-family precedent), the quantale class of the §2.5.2
Definition 2.90 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.100, display (2.101), the
      identity-matrix display, Exercise 2.103 and Exercise 2.104 (printed
      pp. 73–74); `≈` on morphisms, never `=`
- [ ] The matrix type and its product are parameterized by an arbitrary quantale,
      not by a fixed base
- [ ] Both unit laws and associativity are proved, and `Mat V` is assembled as a
      `Category`
- [ ] The `V = Bool` instance is reconciled with `Instance/Rel.v`, so the
      generalization is certified against the existing case
- [ ] Exercise 2.103's three two-by-two identity matrices are computed
- [ ] The proofs of step 4 use the distributivity clause of Proposition 2.87(b)
      rather than an ad-hoc argument
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the matrix product,
      both unit laws, associativity and `Mat V`
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: `Mat V` is flagship-level and
      generalizes the existing `Instance/Rel.v`

## Verification

```
coqc -R . Category Structure/Quantale/Matrix.v
coqc -R . Category Instance/Cost/Matrix.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions VMatrix.
Print Assumptions vmatrix_mult.
Print Assumptions vmatrix_id.
Print Assumptions vmatrix_id_left.
Print Assumptions vmatrix_id_right.
Print Assumptions vmatrix_assoc.
Print Assumptions Mat.
Print Assumptions Mat_Bool_is_Rel.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
product is a join over the middle index (not a fold over a list); the identity
matrix uses `⋁∅` off the diagonal rather than a base-specific constant; the
laws hold on the nose in `Mat V`, unlike the profunctor case which is only up to
isomorphism.

## Dependencies

Depends on: 7sketches:2.5.2:def90 (the quantale class).
Depends on: 7sketches:2.5.1:prop87 (distributivity of the tensor over joins,
consumed by the unit and associativity proofs).
Depends on: #262 (Rel and converse relations — the `V = Bool` instance this
generalizes).

<!-- catalog: {"ids":["7sketches:2.5.3:def100","7sketches:2.5.3:equation101","7sketches:2.5.3:def-identity-matrix","7sketches:2.5.3:ex103","7sketches:2.5.3:ex104"],"deps":["7sketches:2.5.2:def90","7sketches:2.5.1:prop87","#262"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: The weight matrix of a V-weighted graph, and computing the presented V-category by matrix powers"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.3.3:construction-graph-matrix, 7sketches:2.3.3:ex60, 7sketches:2.5.3:construction-matrix-powers, 7sketches:2.5.3:ex105]
deps_item_ids: [7sketches:2.5.3:def100, 7sketches:2.3.3:construction-weighted-graph-metric, 7sketches:2.3.3:ex58]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* — §2.3.3, the unnumbered
construction of the matrix of a Cost-weighted graph (printed p. 62, PDF p. 74)
and Exercise 2.60, which fills it out for the graph of display (2.56) (printed
p. 63, PDF p. 75); and §2.5.3, the unnumbered construction computing the
presented V-category by iterated matrix multiplication (printed pp. 74–75,
PDF pp. 86–87) with Exercise 2.105, which runs it on that same graph and checks
the answer against the distance table (printed p. 75, PDF p. 87). Items covered:
`7sketches:2.3.3:construction-graph-matrix`, `7sketches:2.3.3:ex60`,
`7sketches:2.5.3:construction-matrix-powers`, `7sketches:2.5.3:ex105`.

## Background

A V-weighted graph has a weight matrix — the unit on the diagonal, the edge
weight where an edge exists, the bottom element elsewhere — whose `n`-th power
under the quantale matrix product records the best value over paths of at most
`n` edges; over a finite vertex set the powers stabilize, and the stable matrix
is the hom-matrix of the presented V-category
([Wikipedia: Adjacency matrix](https://en.wikipedia.org/wiki/Adjacency_matrix),
[Wikipedia: Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)).
At `V = Cost` this is the min-plus computation of all-pairs shortest paths
([Wikipedia: Tropical semiring](https://en.wikipedia.org/wiki/Tropical_semiring)).

## Current state in the library

Neither the matrix of a graph nor any iteration of a composition exists.

- No adjacency or weight matrix. The closest shape is
  `Construction/Free/Quiver.v:54–57`, `Class Quiver` with
  `edges : nodes → nodes → uedges` — an unlabelled, Set-valued edge family with no
  diagonal convention and no bottom element; `rg -inE 'adjacency|weighted
  graph|distance matrix'` finds nothing.
- No iteration. There is no `n`-fold composition operator for morphisms anywhere
  in the tree, so `M²`, `M³` cannot be formed even once a matrix product exists,
  and no stabilization statement of any kind is available.
- No algorithmic content: `rg -i 'shortest path|all-pairs|floyd|warshall|dijkstra'`
  returns 0 hits.
- The one honest relative is `Instance/Lambda/Multi.v:46`
  (`Inductive multi`, with `multi_PreOrder` at `:74`): at `V = Bool` the
  reflexive-transitive closure *is* the answer object `⋁ₙ Rⁿ` that the powers
  converge to — but it is defined inductively, not computed by iteration, so it
  supplies the target of the theorem and none of its method.
- The base and the matrix calculus themselves are missing, and are the
  obligations of the §2.2.4 Example 2.37 and §2.5.3 Definition 2.100 issues.

## Work to be done

Suggested module: `Instance/Cost/MatrixPowers.v` (with the base-generic part in
`Structure/Quantale/Matrix/Powers.v`).

1. Define the weight matrix `M_G` of a V-weighted graph: the unit `I` on the
   diagonal, the edge weight where there is an edge, `⋁∅` elsewhere. Keep it
   base-generic; the graph type is the one built by the §2.3.3 shortest-path
   issue.
2. Define the iterated product `M^n` in `Mat V`, and prove the path
   characterization: `M_G^n (x,y)` is the join over directed paths of length at
   most `n` of the tensor of their edge weights. This is the theorem the whole
   construction rests on and the book states it informally.
3. Prove stabilization for a finite vertex set: if `M^n = M^{n+1}` then
   `M^m = M^n` for all `m ≥ n`, and such an `n` exists (the `n = |X|` bound is
   the natural one). Conclude that the stable matrix is the hom-matrix of the
   presented V-category, i.e. that it agrees with the distance defined directly
   as a join over all paths in the §2.3.3 issue.
4. Discharge Exercise 2.60: write out `M_X` for the four-vertex graph of display
   (2.56), including the `⋁∅` entries.
5. Discharge Exercise 2.105: compute `M_X²`, `M_X³` and `M_X⁴` and prove `M_X⁴`
   equals the distance table of Exercise 2.58 — as `eq_refl`/decidable Examples,
   in the style of `Instance/FinSet/Topos.v`, so the algorithm is executed and
   not merely described.
6. Record the `V = Bool` reading: the same iteration computes reachability, and
   the stable matrix is `Instance/Lambda/Multi.v`'s `multi` of the edge relation
   — stated as a lemma, so the inductive closure and the iterative computation are
   proved to agree.

In-tree donors: `Construction/Free/Quiver.v:54,57`,
`Instance/Lambda/Multi.v:46,74`, `Instance/FinSet/Topos.v` (the `eq_refl`
Example style), `Instance/FinSet.v:116` (`Fin.t`-indexed finite carriers), the
`Mat V` of the §2.5.3 Definition 2.100 issue, the weighted graph of the §2.3.3
shortest-path issue.

## Definition of Done

- [ ] Statement fidelity to the §2.3.3 matrix construction (printed p. 62),
      Exercise 2.60, the §2.5.3 matrix-power construction (printed pp. 74–75) and
      Exercise 2.105; `≈` on morphisms, never `=`
- [ ] The weight matrix and the power operation are base-generic
- [ ] The path characterization of `M^n` is proved, not assumed
- [ ] Stabilization is proved for a finite vertex set, with an explicit bound,
      and the stable matrix is proved equal to the presented V-category's
      hom-matrix
- [ ] Exercises 2.60 and 2.105 are computed, and the agreement with the
      Exercise 2.58 distance table is a proof, not an inspection
- [ ] The `V = Bool` case is proved to agree with `Instance/Lambda/Multi.v`'s
      reflexive-transitive closure
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` recorded for the path characterization and the
      stabilization theorem
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Structure/Quantale/Matrix/Powers.v
coqc -R . Category Instance/Cost/MatrixPowers.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions weight_matrix.
Print Assumptions matrix_power_paths.
Print Assumptions matrix_power_stabilizes.
Print Assumptions presented_vcat_is_stable_power.
Print Assumptions matrix_power_bool_is_multi.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
powers are genuinely iterated in `Mat V` (not a bespoke recursion); the
stabilization bound is proved rather than assumed; Exercise 2.105's check against
Exercise 2.58 is a proved equality of tables.

## Dependencies

Depends on: 7sketches:2.5.3:def100 (V-matrices and their product).
Depends on: 7sketches:2.3.3:construction-weighted-graph-metric (the weighted
graph and the distance it presents, which the stable power must equal).
Depends on: 7sketches:2.3.3:ex58 (the distance table this computation is checked
against).

<!-- catalog: {"ids":["7sketches:2.3.3:construction-graph-matrix","7sketches:2.3.3:ex60","7sketches:2.5.3:construction-matrix-powers","7sketches:2.5.3:ex105"],"deps":["7sketches:2.5.3:def100","7sketches:2.3.3:construction-weighted-graph-metric","7sketches:2.3.3:ex58"]} -->

---8<---

```yaml
title: "Seven Sketches 2.3: Enrichment in the powerset and bottleneck quantales — V-weighted graphs beyond Bool and Cost"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.3.4:ex62, 7sketches:2.3.4:ex63]
deps_item_ids: [7sketches:2.2.4:ex35, 7sketches:2.5.3:def100, 7sketches:2.3.3:construction-weighted-graph-metric]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.3.4 — Exercise 2.62
(enrichment in the powerset of a set of transport modes, with the hom-object of a
graph the union over paths of the intersection of the edge labels; printed
pp. 63–64, PDF pp. 75–76) and Exercise 2.63 (enrichment in the bottleneck
preorder of the naturals with a point at infinity, ordered by `≤` with unit `∞`
and tensor `min`, whose matrix takes the maximum over paths of the minimum label;
printed p. 64, PDF p. 76). Items covered: `7sketches:2.3.4:ex62`,
`7sketches:2.3.4:ex63`.

## Background

Enrichment is parameterized by its base, and changing the base changes the
meaning of a hom-object: over the powerset of a set of modes of transport the
hom-object records which modes get one all the way from `a` to `b`, and over the
bottleneck order it records the capacity of the best route
([nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category),
[Wikipedia: Widest path problem](https://en.wikipedia.org/wiki/Widest_path_problem)).
Both are quantales, so both are covered by the same V-weighted-graph machinery
([nLab: quantale](https://ncatlab.org/nlab/show/quantale)).

## Current state in the library

Neither base exists, and no enrichment is ever computed from a labelled graph.

- No powerset preorder. `Instance/Ens.v:56` (`EnsT T`) has the right objects
  (`Ensemble T`) but its morphisms are carrier functions `f : T → T` with
  `∀ x, x ∈ A ↔ f x ∈ B`, i.e. preimage conditions rather than inclusions, and it
  carries no `Terminal`/`Cartesian` instance; `rg -in 'powerset|power set'`
  otherwise finds only `Structure/Topos.v:75,129` (`Pow a := Ω ^ a`, an internal
  exponential) and two prose lines in `Instance/Poset.v`. Building
  `(P(S), ⊆)` is the obligation of #382.
- No bottleneck base. `rg -i 'infty|infinity'` is empty tree-wide, so
  `ℕ ∪ {∞}` has no carrier; `Instance/Omega.v` is `le_t` (`:28`), three groupoid
  lemmas (`:51,:55,:63`), `Omega` (`:72`) and `omega_step` (`:85`) — no top
  element and no bifunctor, so neither the unit `∞` nor the tensor `min` exists.
  The only `min`-like operation in the tree is `two_meet`
  (`Instance/Two/Monoidal.v:37`) on the two-element order.
- No labelled graph and no hom computed from one. `Construction/Free/Quiver.v:54`
  (`Class Quiver`, `edges` at `:57`) and `:431` (`FreeOnQuiver`) exist, and
  `Lib/TList.v:47` (`tlist`) gives paths, but nothing labels edges by elements of
  a base or forms a best-value-over-paths hom-object.

## Work to be done

Suggested module: `Instance/Quantale/Examples.v` (the two bases) with the
enrichment computations in `Instance/Quantale/Examples/Graphs.v`.

1. Give `(P(M), ⊆, M, ∩)` its quantale structure — the monoidal preorder is the
   §2.2.4 Exercise 2.35 issue's obligation; here it needs the residual and
   arbitrary unions, which is the §2.5.2 Exercise 2.94 question.
2. Build the bottleneck base `W := (ℕ ∪ {∞}, ≤, ∞, min)`: the carrier as an
   option type or an inductive with a top element, the order, the `min` tensor
   with unit `∞`, monotonicity, and the quantale structure (arbitrary joins are
   suprema, which exist because the carrier is `ℕ` with a top).
3. Discharge Exercise 2.62: build the four-vertex graph labelled by subsets of a
   three-element mode set, compute its hom-matrix as the union over paths of the
   intersection of the edge labels — an instance of the V-weighted-graph
   construction, so it must be obtained from that machinery and not re-derived —
   and verify the two enrichment axioms. Then settle part (3): decide whether the
   stated reading ("which modes get you all the way from a to b") is correct, and
   record the verdict as a proof or a refutation, since a single mode must be
   usable on *every* edge of one path rather than on some path each.
4. Discharge Exercise 2.63: the analogous small graph over `W`, its
   maximum-over-paths-of-minimum-label matrix, the proof that it is a `W`-category,
   and the interpretation, stated as a lemma relating the hom-object to the
   capacity of the best route.
5. Record both bases in the same file as the running non-`Bool`, non-`Cost`
   examples, so the change-of-base issues have more than two bases to work with.

In-tree donors: `Instance/Ens.v:56`, `Instance/Two/Monoidal.v:37`,
`Instance/Omega.v:72`, `Construction/Free/Quiver.v:54,431`, `Lib/TList.v:47`,
`Construction/Enriched.v:111`, the V-weighted-graph machinery of the §2.3.3 and
§2.5.3 issues, the powerset preorder of #382.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Exercise 2.62 (printed pp. 63–64) and
      Exercise 2.63 (printed p. 64); `≈` on morphisms, never `=`
- [ ] Both bases are built as quantales, so they can serve as bases of enrichment
      and as matrix bases
- [ ] Both hom-matrices are obtained as instances of the general V-weighted-graph
      construction, not by bespoke definitions
- [ ] Both enrichment axioms are verified in each case
- [ ] Exercise 2.62(3)'s interpretation question is settled by a proof or a
      refutation
- [ ] Exercise 2.63(4)'s interpretation is stated as a lemma about the hom-object
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for both quantales and
      both enrichments
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Quantale/Examples.v
coqc -R . Category Instance/Quantale/Examples/Graphs.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Powerset_Quantale.
Print Assumptions Bottleneck_Quantale.
Print Assumptions transport_enrichment.
Print Assumptions bottleneck_enrichment.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
transport hom is a union over paths of an intersection along a path (not an
intersection of unions); the bottleneck unit is the top element `∞`, not `0`;
both examples reuse the general weighted-graph machinery.

## Dependencies

Depends on: 7sketches:2.2.4:ex35 (the powerset monoidal preorder).
Depends on: 7sketches:2.5.3:def100 (V-matrices, in which both hom-matrices are
computed).
Depends on: 7sketches:2.3.3:construction-weighted-graph-metric (the V-weighted
graph construction both exercises instantiate).
Depends on: #382 (the powerset preorder).

<!-- catalog: {"ids":["7sketches:2.3.4:ex62","7sketches:2.3.4:ex63"],"deps":["7sketches:2.2.4:ex35","7sketches:2.5.3:def100","7sketches:2.3.3:construction-weighted-graph-metric","#382"]} -->

---8<---

```yaml
title: "Seven Sketches 2.4: Change of base of enrichment along a monoidal monotone"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.4.1:construction64]
deps_item_ids: [7sketches:2.2.5:def41, 7sketches:2.4.2:remark71]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.4.1 Construction 2.64 —
a monoidal monotone `f : V → W` turns any V-category into a W-category by
applying `f` to every hom-object. Printed pp. 64–65; PDF pp. 76–77. Item covered:
`7sketches:2.4.1:construction64`.

## Background

A lax monoidal functor between bases induces a functor between the corresponding
categories of enriched categories, by post-composing the hom-assignment with it;
laxity is exactly what is needed for the unit and composition axioms to transport
([nLab: change of enriching category](https://ncatlab.org/nlab/show/change+of+enriching+category),
[nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category)).
It is the mechanism by which the metric and order readings of the same structure
are related.

## Current state in the library

The construction is absent, and so is any transport of an enrichment along
anything.

- `Construction/Enriched.v` provides `Enriched` (`:111`), `EnrichedFunctor`
  (`:145`), `Category_is_Enriched_over_Set` (`:163`) and
  `Functor_is_Enriched_over_Set` (`:215`); `Construction/Enriched/Compose.v`
  provides identity/composite enriched functors and both whiskerings
  (`:25,:49,:87,:118`); `Construction/Enriched/Fun.v:270` the category of
  V-functors; `Construction/Enriched/Natural.v` the V-natural transformations.
  Nothing in that list changes the base.
- `rg -l 'Construction.Enriched'` returns only `Instance/Two.v`,
  `Instance/Poset.v`, `Theory/Natural/Transformation.v`, `Structure/Closed.v`,
  `Structure/Monoidal.v` and the `Enriched/*` files — none of which transports an
  enrichment.
- Every "base change" hit in the tree is something else: pullback and cobase
  change of morphisms (`Theory/Morphisms/Stability.v`,
  `Construction/Slice/Pullback.v`) or colour re-indexing of coloured PROPs
  (`Construction/ColouredPROP/BaseChange.v`, whose functoriality laws hold only
  up to `hom_cast`). The phrase "monoidal monotone" has 0 hits.
- There is not even one monoidal functor between thin categories to change base
  along: `LaxMonoidalFunctor` (`Functor/Structure/Monoidal.v:110`) is inhabited
  only by `Functor/Structure/Monoidal/Id.v:73` and
  `Functor/Structure/Monoidal/Compose.v:291`.

## Work to be done

Suggested module: `Construction/Enriched/BaseChange.v`.

1. Define the transport: given a lax monoidal functor `f : V ⟶ W` and
   `C : Enriched V`, build `Enriched W` with the same `eobj` and
   `ehom x y := f (ehom x y)`. The unit axiom is `lax_pure` followed by `f` applied
   to `eid`; the composition axiom is `lax_ap` followed by `f` applied to
   `ecompose`. State it at the general (not merely thin) level: the book's proof
   is the general one, and the library's `Enriched` class is already general.
2. Prove functoriality on enriched functors: a V-functor transports to a
   W-functor, identities and composites are preserved, so change of base is a
   functor between the categories of enriched categories built by the §2.4.2
   Remark 2.71 issue.
3. Prove the two coherence facts that make "change of base" a well-behaved
   operation: transporting along the identity monoidal functor is the identity,
   and transporting along a composite is the composite of the transports (up to
   the appropriate equality/isomorphism — state which, and prove it).
4. Specialize to the preorder level, giving the statement in the book's form: a
   monoidal monotone between monoidal preorders converts V-categories into
   W-categories, with the two axioms in the inequality form of the text.
5. Record in the header that this is the construction that makes the base of
   enrichment a variable rather than a fixed choice, and list the instances that
   consume it (`Cost → Bool`, and the second monotone that distinguishes them).

In-tree donors: `Construction/Enriched.v:111,145`,
`Construction/Enriched/Compose.v:25,49,87,118`,
`Functor/Structure/Monoidal.v:110`, the monoidal-monotone class of the §2.2.5
Definition 2.41 issue, the category of V-categories of the §2.4.2 Remark 2.71
issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Construction 2.64 (printed pp. 64–65);
      `≈` on morphisms, never `=`
- [ ] The construction is stated for an arbitrary monoidal base, with the
      preorder-level form derived from it rather than proved separately
- [ ] Both enrichment axioms are proved, and their proofs visibly consume the
      laxity of `f` (the unit comparison for one, the product comparison for the
      other)
- [ ] Change of base is proved functorial on enriched functors
- [ ] Identity and composite base changes are related to the identity and
      composite transports
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the transport and
      for functoriality
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: change of base is flagship-level
      for the enriched development

## Verification

```
coqc -R . Category Construction/Enriched/BaseChange.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Enriched_BaseChange.
Print Assumptions EnrichedFunctor_BaseChange.
Print Assumptions BaseChange_id.
Print Assumptions BaseChange_compose.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the unit
axiom really is `lax_pure` composed with the image of `eid` (a strong monoidal
functor must not be needed); the construction keeps the object set fixed; the
preorder-level statement is a corollary and not a duplicate proof.

## Dependencies

Depends on: 7sketches:2.2.5:def41 (the monoidal-monotone / lax monoidal functor
class, including the repair of its lax level).
Depends on: 7sketches:2.4.2:remark71 (the category of V-categories, the target of
the functoriality statement).

<!-- catalog: {"ids":["7sketches:2.4.1:construction64"],"deps":["7sketches:2.2.5:def41","7sketches:2.4.2:remark71"]} -->

---8<---

```yaml
title: "Seven Sketches 2.4: Change of base along Cost → Bool — Lawvere metric spaces become preorders"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.4.1:example65, 7sketches:2.4.1:ex67, 7sketches:2.4.1:ex68]
deps_item_ids: [7sketches:2.4.1:construction64, 7sketches:2.3.3:def53, 7sketches:2.2.5:ex44, 7sketches:2.3.3:ex52]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.4.1 — Example 2.65 (the
zero-distance monotone from the cost base to the Boolean base, and the preorder
it induces on any Lawvere metric space; printed p. 65, PDF p. 77), Exercise 2.67
(applying it to the regions-of-the-world space and drawing the resulting Hasse
diagram; printed p. 65, PDF p. 77) and Exercise 2.68 (a second monoidal monotone
in the same direction, and a space on which the two base changes disagree;
printed p. 65, PDF p. 77). Items covered: `7sketches:2.4.1:example65`,
`7sketches:2.4.1:ex67`, `7sketches:2.4.1:ex68`.

## Background

Applying the "is the distance zero?" monotone to every hom-object of a Lawvere
metric space produces a preorder: one point is below another exactly when it can
be reached at no cost
([nLab: change of enriching category](https://ncatlab.org/nlab/show/change+of+enriching+category),
[nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).
Choosing a different monotone — for instance "is the distance finite?" — produces
a different preorder from the same space, which is what makes the base a genuine
parameter.

## Current state in the library

Nothing of it exists, and every ingredient is separately absent.

- No `Cost` base (`rg -n '\bCost\b'` finds only the English word; `infty|infinity`
  and `Reals|Rdefinitions|QArith` are all 0 hits), hence no Lawvere metric space
  to transport.
- No change of base of enrichment (see the §2.4.1 Construction 2.64 issue: the
  only "base change" hits in the tree are pullbacks of morphisms and coloured-PROP
  colour re-indexing).
- Not one monoidal monotone exists: `LaxMonoidalFunctor` is inhabited only by
  `Functor/Structure/Monoidal/Id.v:73` and
  `Functor/Structure/Monoidal/Compose.v:291`, so neither the map of Example 2.65
  nor a second one is available.
- The target base does exist: `Instance/Two/Monoidal.v:105`
  (`Two_Monoidal := @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal`), with
  `Two_Cartesian` at `:80` and `Two_Terminal` at `:98`.
- No three-element concrete preorder example and no Hasse diagram notion
  (`rg -in 'hasse'`: 0 hits); the only preorder instances in the tree are
  `Instance/Proset.v:47` and `Instance/Poset.v:120` on the naturals, plus
  `Test/Poset.v:54,139`.

## Work to be done

Suggested module: `Instance/Cost/BaseChange.v`.

1. Prove Example 2.65: the "distance zero" map is a monoidal monotone from `Cost`
   to `Bool` (monotone for the reversed cost order, unit and product conditions),
   and its base change sends a Lawvere metric space to the preorder
   `x ≤ y ⟺ d(x,y) = 0`. State the induced preorder as an explicit description,
   not merely as an instance of the general construction — the description is the
   content of the example.
2. Discharge Exercise 2.67: build the three-region Lawvere metric space of the
   §2.3.3 Exercise 2.52 issue, apply the base change, and exhibit the resulting
   preorder completely — every related pair proved and every unrelated pair
   refuted, in the style of `Instance/Roof.v`'s absurdity lemmas — together with
   a lemma reading the relation as containment/zero distance.
3. Discharge Exercise 2.68: give a second monoidal monotone `Cost → Bool` (the
   "distance finite" map of the §2.2.5 Exercise 2.44 issue is the intended one),
   prove it monoidal monotone, and then exhibit a Lawvere metric space on which
   the two base changes differ — a proof that the two induced preorders are not
   equal, which needs a witness pair related under one and refuted under the
   other.
4. Record the moral in the header: the preorder underlying a metric space depends
   on the chosen monotone, so "the underlying preorder" is not well defined
   without naming one.

In-tree donors: `Instance/Two/Monoidal.v:80,98,105`, `Instance/Two.v:122` (the
refutation idiom), `Instance/Roof.v` (concrete finite-shape absurdity lemmas),
the base change of the §2.4.1 Construction 2.64 issue, the two `Cost → Bool`
monotones of the §2.2.5 Exercise 2.44 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 2.65, Exercise 2.67 and
      Exercise 2.68 (printed p. 65); `≈` on morphisms, never `=`
- [ ] The induced preorder is described explicitly (`x ≤ y ⟺ d(x,y) = 0`), as a
      proved characterization
- [ ] The three-region example is worked out with every related pair proved and
      every unrelated pair refuted
- [ ] The two base changes are proved to differ, with an explicit separating
      space and pair — not merely asserted to be different
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` recorded for both monotones and for the separation
      result
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Cost/BaseChange.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions cost_to_bool_zero_monotone.
Print Assumptions basechange_zero_preorder.
Print Assumptions regions_preorder.
Print Assumptions basechange_zero_vs_finite_differ.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
induced preorder is obtained by the general base change and then characterized,
rather than defined directly; the separation result exhibits a concrete space and
pair; the regions example refutes the unrelated pairs.

## Dependencies

Depends on: 7sketches:2.4.1:construction64 (change of base).
Depends on: 7sketches:2.3.3:def53 (Lawvere metric spaces, the objects being
transported).
Depends on: 7sketches:2.2.5:ex44 (the two candidate monotones from the cost base
to the Boolean base).
Depends on: 7sketches:2.3.3:ex52 (the regions-of-the-world space Exercise 2.67
transports).

<!-- catalog: {"ids":["7sketches:2.4.1:example65","7sketches:2.4.1:ex67","7sketches:2.4.1:ex68"],"deps":["7sketches:2.4.1:construction64","7sketches:2.3.3:def53","7sketches:2.2.5:ex44","7sketches:2.3.3:ex52"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: Hausdorff distance between subsets of a V-category, and the failure of symmetry"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.2:remark97, 7sketches:2.3.3:ex52]
deps_item_ids: [7sketches:2.5.2:def90, 7sketches:2.3.3:def53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.2 Remark 2.97 — the
generalization of Hausdorff distance from the cost base to an arbitrary quantale,
as a meet of joins of hom-objects (printed p. 73, PDF p. 85) — together with
§2.3.3 Exercise 2.52 (printed p. 60, PDF p. 72), the motivating instance in which
the worst-case region-to-region distance is asymmetric and fails separation, and
which the remark generalizes. Items covered: `7sketches:2.5.2:remark97`,
`7sketches:2.3.3:ex52`.

## Background

For subsets `U`, `V` of a quantale-enriched category the value
`⋀_{u ∈ U} ⋁_{v ∈ V} X(u,v)` generalizes the classical one-sided Hausdorff
distance — "how far must one travel, in the worst case, to get from somewhere in
`U` into `V`" ([Wikipedia: Hausdorff distance](https://en.wikipedia.org/wiki/Hausdorff_distance)).
At the Boolean base it says every point of `U` is below some point of `V`; the
one-sided version is asymmetric, which is exactly why the book drops symmetry
from its notion of distance
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).

## Current state in the library

Absent in both directions, and structurally blocked at the class level.

- `rg -i 'hausdorff'` gives exactly two hits, `Theory/Equivalence.v:122` and
  `Theory/Monad.v:66`, both the phrase "compact Hausdorff spaces" in background
  essays — nothing about a distance between subsets.
- `Construction/Enriched.v:111`'s `Enriched` class supplies hom-objects between
  *objects* only, over a bare `Monoidal` base that provides neither `⋀` nor `⋁`,
  so the formula cannot be written until the base is a quantale.
- No order-theoretic meet or join vocabulary exists at all: `rg 'Definition
  (join|meet|sup|inf)'` finds only `two_meet` (`Instance/Two/Monoidal.v:37`) on
  the two-element order, and every other `join` in the tree is monad
  multiplication. The fact that a quantale has all meets as well as all joins is
  the obligation of #684.
- Exercise 2.52's instance is likewise absent: no numeric carrier, no
  set-to-set distance, and no quasi-metric notion against which to exhibit the
  failure of symmetry; `rg -ni 'worst case|supremum|infimum'` returns nothing
  relevant.

## Work to be done

Suggested module: `Structure/Quantale/Hausdorff.v` with the concrete instance in
`Instance/Cost/Regions.v`.

1. Define the one-sided Hausdorff value for two subsets of a V-category over a
   quantale, `X(U,V) := ⋀_{u ∈ U} ⋁_{v ∈ V} X(u,v)`, using the arbitrary meets
   supplied by #684 from the quantale's joins.
2. Prove the two structural facts that make the definition well behaved: it is
   antitone in `U` and monotone in `V`, and it extends the hom-object (singletons
   give `X({u},{v}) = X(u,v)`).
3. Prove the reflexivity and transitivity clauses, i.e. that the construction
   makes the subsets of a V-category into a V-category again — the natural
   statement the remark stops short of, and the one that makes it usable.
4. Prove the Boolean reading: at `V = Bool` the value is "for every `u ∈ U` there
   is `v ∈ V` with `u ≤ v`", as a biconditional.
5. Build the concrete instance of Exercise 2.52: a small Lawvere metric space of
   regions (a base space plus a chosen family of subsets), and prove that the
   one-sided value is asymmetric — an explicit pair `U`, `V` with
   `X(U,V) ≠ X(V,U)` — and that it fails separation, a pair of distinct subsets
   at distance zero. Both must be refutations with witnesses, since the point of
   the exercise is that two axioms of Definition 2.51 genuinely fail.

In-tree donors: `Construction/Enriched.v:111`, `Instance/Two/Monoidal.v:37`,
`Structure/Limit/Product.v:51` (`iprod`, the indexed-family precedent), the
quantale class of the §2.5.2 Definition 2.90 issue, the Lawvere metric spaces of
the §2.3.3 Definition 2.53 issue, the all-meets result of #684.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 2.97 (printed p. 73) and
      Exercise 2.52 (printed p. 60); `≈` on morphisms, never `=`
- [ ] The construction is defined over an arbitrary quantale, not only over `Cost`
- [ ] Monotonicity in each argument and agreement with the hom-object on
      singletons are proved
- [ ] The subsets of a V-category are proved to form a V-category under the
      construction
- [ ] The Boolean reading is proved as a biconditional
- [ ] Asymmetry and the failure of separation are proved by explicit witnesses
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` recorded for the construction, the V-category result and
      both failures
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Structure/Quantale/Hausdorff.v
coqc -R . Category Instance/Cost/Regions.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions hausdorff_hom.
Print Assumptions hausdorff_singleton.
Print Assumptions hausdorff_enriched.
Print Assumptions hausdorff_bool_reading.
Print Assumptions regions_hausdorff_asymmetric.
Print Assumptions regions_hausdorff_not_separated.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
formula is a meet of joins in that order (swapping them changes the meaning); the
meets come from the quantale's joins by the #684 result rather than being assumed;
the asymmetry claim is a refutation with a concrete pair.

## Dependencies

Depends on: 7sketches:2.5.2:def90 (the quantale class, which supplies the joins).
Depends on: 7sketches:2.3.3:def53 (Lawvere metric spaces, in which the concrete
instance lives).
Depends on: #684 (a complete lattice has all meets as well as all joins — the
meets this construction takes).

<!-- catalog: {"ids":["7sketches:2.5.2:remark97","7sketches:2.3.3:ex52"],"deps":["7sketches:2.5.2:def90","7sketches:2.3.3:def53","#684"]} -->

---8<---

```yaml
title: "Seven Sketches 2.4: Opposite, dagger and skeletal V-categories, and extended metric spaces"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.4.2:ex73]
deps_item_ids: [7sketches:2.3.3:def53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.4.2 Exercise 2.73 — the
opposite of a V-category, dagger V-categories, skeletal V-categories, the theorem
that a skeletal dagger Cost-category is exactly an extended metric space, and the
analogy that closes the section. Printed p. 66; PDF p. 78. Item covered:
`7sketches:2.4.2:ex73`.

## Background

Reversing the hom-objects of a V-category gives its opposite; requiring the
identity to be a V-functor into the opposite is symmetry, and requiring mutual
`I`-boundedness to force equality is skeletality
([nLab: dagger category](https://ncatlab.org/nlab/show/dagger+category),
[nLab: skeletal category](https://ncatlab.org/nlab/show/skeletal+category)).
Imposing both on a Cost-category restores exactly the two axioms Lawvere's
definition drops, recovering the classical (extended) metric space
([nLab: metric space](https://ncatlab.org/nlab/show/metric+space)).

## Current state in the library

All three notions are missing at the enriched level, and the one filed relative
is at the order level.

- No opposite of an enrichment: the enriched development's complete symbol list
  (`Construction/Enriched.v:111,145,163,215`, `Construction/Enriched/Compose.v`,
  `/Fun.v`, `/Natural.v`, `/Sets.v`, `/Two.v`) contains no `op`;
  `Construction/Opposite.v` gives `C^op` for an ordinary `Category` only.
- No dagger notion anywhere: `rg 'Class Dagger|Record Dagger'` returns 0 hits and
  every "dagger" occurrence is background prose.
- No skeletality: it is never a definition; the nearest are the per-instance
  regression lemmas `Test/Poset.v:102` (`poset_nat_skeletal`) and `:150`
  (`poset_two_skeletal`), both about ordinary categories in a test file.
- The order-level case — a dagger preorder is an equivalence relation and a
  skeletal one is discrete — is the obligation of #767, which is the template
  this exercise generalizes.
- The classical metric space, whose extended variant this exercise recovers, is
  the obligation of #308 (which builds the category of metric spaces); the
  `[0,∞]`-valued variant is not in that issue's scope and is added here.

## Work to be done

Suggested module: `Construction/Enriched/Dagger.v`.

1. Define the opposite of a V-category: the same objects with
   `X^op(x,y) := X(y,x)`, and prove it is a V-category. Note in the header that
   the composition axiom needs the symmetry of the base — the same use of
   Definition 2.2(d) that the V-product needs — and prove that dependence rather
   than leaving it implicit.
2. Define a dagger V-category as a V-category for which the identity function is
   a V-functor `X ⟶ X^op`, and prove the equivalent elementwise form
   `X(x,y) ≤ X(y,x)` (hence, by applying it twice, mutual `≤`).
3. Define skeletality: `I ≤ X(x,y)` and `I ≤ X(y,x)` together imply `x = y`.
   Prove the Boolean case agrees with #767's order-level notion, so the two
   layers are connected rather than parallel.
4. Prove the main statement: a skeletal dagger `Cost`-category is exactly an
   extended metric space in the sense of Definition 2.51 with codomain `[0,∞]` —
   both directions, so "exactly" is earned. The four classical axioms come out as
   `d(x,x) = 0` (the unit axiom), the triangle inequality (the composition
   axiom), symmetry (dagger) and separation (skeletality).
5. Formalize the analogy the exercise closes with, as far as it is formalizable:
   the Boolean instance of the same statement is "a skeletal dagger
   Bool-category is a set with equality", i.e. #767's discreteness result, so the
   two rows of the analogy are two instances of one theorem. State that
   specialization as a corollary.

In-tree donors: `Construction/Enriched.v:111,145`, `Construction/Opposite.v`,
`Construction/Enriched/Two.v` (the `V = Bool` template), `Test/Poset.v:102,150`
(the existing skeletality statements, to be promoted out of the test file), the
Lawvere metric spaces of the §2.3.3 Definition 2.53 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Exercise 2.73 (printed p. 66); `≈` on
      morphisms, never `=`
- [ ] The opposite of a V-category is constructed and its dependence on the
      symmetry of the base is proved, not merely remarked
- [ ] Dagger and skeletality are defined for an arbitrary base, with their
      elementwise characterizations proved
- [ ] "Skeletal dagger Cost-category = extended metric space" is proved in both
      directions, with all four classical axioms identified
- [ ] The Boolean specialization is derived as a corollary and matched against
      #767's order-level result
- [ ] Skeletality exists in the library proper, not only as the `Test/Poset.v`
      per-instance lemmas
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` recorded for the opposite, the two predicates and the
      characterization theorem
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Construction/Enriched/Dagger.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Enriched_op.
Print Assumptions DaggerEnriched.
Print Assumptions SkeletalEnriched.
Print Assumptions skeletal_dagger_cost_iff_extended_metric.
Print Assumptions skeletal_dagger_bool_is_discrete.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
opposite construction actually uses the base's symmetry; the main theorem is a
biconditional; the extended (`[0,∞]`-valued) codomain is used, not the
finite-valued one.

## Dependencies

Depends on: 7sketches:2.3.3:def53 (Lawvere metric spaces as Cost-categories).
Depends on: #767 (dagger preorders are equivalence relations and skeletal ones
are discrete — the order-level case this generalizes).
Depends on: #308 (the metric-space structure, whose extended variant this issue
adds).

<!-- catalog: {"ids":["7sketches:2.4.2:ex73"],"deps":["7sketches:2.3.3:def53","#767","#308"]} -->

---8<---

```yaml
title: "Seven Sketches 2.4: The V-product of V-categories, and where symmetry of the base is used"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.4.3:def74, 7sketches:2.4.3:ex75, 7sketches:2.4.3:example76, 7sketches:2.4.3:ex78]
deps_item_ids: [7sketches:2.3.3:def53, 7sketches:2.3.3:construction-weighted-graph-metric]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.4.3 — Definition 2.74
(the V-product of two V-categories; printed p. 67, PDF p. 79), Exercise 2.75
(that it is a V-category, and exactly where the symmetry of the base is used;
printed p. 67, PDF p. 79), Example 2.76 (the product of two Lawvere metric spaces
given by weighted graphs; printed pp. 67–68, PDF pp. 79–80) and Exercise 2.78
(a distance in the Cost-product of the reals with themselves; printed p. 68,
PDF p. 80). Items covered: `7sketches:2.4.3:def74`, `7sketches:2.4.3:ex75`,
`7sketches:2.4.3:example76`, `7sketches:2.4.3:ex78`.

## Background

The product of two V-categories has pairs as objects and the tensor of the two
component hom-objects as its hom-object; at the Boolean base this is the product
preorder and at the cost base it is the sum of coordinate distances, i.e. the
taxicab rather than the Euclidean metric
([nLab: tensor product of enriched categories](https://ncatlab.org/nlab/show/tensor+product+of+enriched+categories),
[Wikipedia: Taxicab geometry](https://en.wikipedia.org/wiki/Taxicab_geometry)).
Verifying the composition axiom shuffles four factors, which is where the
symmetry of the base is needed.

## Current state in the library

The ordinary product is present and the enriched one is absent, together with
every instance of it.

- `Construction/Product.v:95` — `Definition Product (C D : Category) : Category`
  with `obj := C * D` and
  `hom := fun x y => (fst x ~> fst y) * (snd x ~> snd y)`, `id := (id, id)`,
  componentwise composition: clauses (i) and (ii) of Definition 2.74 at
  `V = Sets`, since a pair type is the Sets-tensor.
- `Construction/Enriched.v:163` — `Category_is_Enriched_over_Set` bridges an
  ordinary category to an enrichment in `Sets`, so the `V = Sets` case can be
  read as the enriched product, though no file does so.
- There is **no** operation `Enriched K → Enriched K → Enriched K` anywhere: the
  entire enriched development (`Construction/Enriched.v` and
  `Enriched/{Compose,Fun,Natural,Sets,Two}.v`) provides identity and composite
  V-functors, both whiskerings, V-natural transformations, the category of
  V-functors, and the `V = Sets` and `V = Two` round trips, and nothing else. In
  particular there is no product of `TwoPreorder`s and no product of
  Cost-categories.
- The shuffle the exercise is about does exist in isolation:
  `Structure/Monoidal/Braided/Proofs.v:767` —
  `Definition swap_inner (a b c d : C) : (a ⨂ b) ⨂ (c ⨂ d) ~> (a ⨂ c) ⨂ (b ⨂ d)`,
  inside a `Context `{S : @SymmetricMonoidal C}` opening at `:632`, and it is used
  to build `Theory/Algebra/Comonoid/Tensor.v:214` (`Comonoid_Tensor`). No file
  connects it to `eid`/`ecompose`, so "the composition axiom of a product factors
  through `swap_inner`" is nowhere stated.
- Both instances are unavailable: no `Cost` base, hence no product of Lawvere
  metric spaces and no distance to compute in Exercise 2.78.

## Work to be done

Suggested module: `Construction/Enriched/Product.v`.

1. Define the V-product of `C D : Enriched K`: objects `eobj C * eobj D`,
   hom-object `ehom C x x' ⨂ ehom D y y'`.
2. Prove the unit axiom (Exercise 2.75(1)): `I ~> (I ⨂ I)` followed by the tensor
   of the two `eid`s — the inverse unitor of the base is what is needed here.
3. Prove the composition axiom (Exercise 2.75(2)) and, as the exercise demands,
   isolate the use of symmetry: the proof should go through
   `Structure/Monoidal/Braided/Proofs.v:767`'s `swap_inner`, and the file should
   state as a named lemma that the composition of the product factors as
   `(ecompose ⨂ ecompose) ∘ swap_inner`. That makes Exercise 2.75(3) — "where is
   Definition 2.2(d) used?" — a proof obligation rather than a comment.
4. Record the two readings as corollaries: at `V = Bool` the product is the
   product preorder (relate it to the product of `TwoPreorder`s once the §2.3.2
   correspondence is available), and at `V = Cost` the distance is the sum of the
   coordinate distances.
5. Discharge Example 2.76: build the two small Cost-weighted graphs, form their
   product, and prove the resulting distance is the coordinatewise sum on all
   thirty-six pairs (or on the displayed subset, as decidable computations).
6. Discharge Exercise 2.78: in the Cost-product of the reals with themselves,
   prove the distance from `(5,6)` to `(−1,4)` is `8` — with the header recording
   that the product metric is the taxicab and not the Euclidean one, which is the
   point of the exercise.

In-tree donors: `Construction/Product.v:95`, `Construction/Enriched.v:111,163`,
`Structure/Monoidal/Braided/Proofs.v:632,767`,
`Theory/Algebra/Comonoid/Tensor.v:214` (the existing consumer of `swap_inner`,
whose proof pattern transfers), the Lawvere metric spaces of the §2.3.3
Definition 2.53 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.74, Exercise 2.75,
      Example 2.76 and Exercise 2.78 (printed pp. 67–68); `≈` on morphisms, never
      `=`
- [ ] The V-product is defined for an arbitrary symmetric monoidal base and
      proved to be a V-category
- [ ] The use of the base's symmetry is isolated in a named lemma factoring the
      product's composition through `swap_inner` — Exercise 2.75(3) as an
      obligation, not a remark
- [ ] The Boolean and cost readings are proved as corollaries
- [ ] Example 2.76's product distances and Exercise 2.78's value `8` are computed
- [ ] The header records that the Cost-product gives the taxicab metric
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed
      carrier axioms
- [ ] `Print Assumptions` closed under the global context for the product, both
      axioms and the symmetry-factorization lemma
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated where the enriched development
      is described

## Verification

```
coqc -R . Category Construction/Enriched/Product.v
rg -n 'swap_inner' Construction/Enriched/Product.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Enriched_Product.
Print Assumptions enriched_product_eid.
Print Assumptions enriched_product_ecompose.
Print Assumptions enriched_product_uses_braid.
Print Assumptions cost_product_is_sum.
Print Assumptions ex78_distance.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
hom-object is the tensor of the components (not a pair type, except at
`V = Sets`); the symmetry lemma is genuinely load-bearing in the composition
proof; Exercise 2.78's answer is `8` and the header says why it is not the
Euclidean distance.

## Dependencies

Depends on: 7sketches:2.3.3:def53 (Lawvere metric spaces, in which Example 2.76
and Exercise 2.78 live).
Depends on: 7sketches:2.3.3:construction-weighted-graph-metric (the two weighted
graphs of Example 2.76).

<!-- catalog: {"ids":["7sketches:2.4.3:def74","7sketches:2.4.3:ex75","7sketches:2.4.3:example76","7sketches:2.4.3:ex78"],"deps":["7sketches:2.3.3:def53","7sketches:2.3.3:construction-weighted-graph-metric"]} -->

---8<---
```yaml
title: "Seven Sketches 2.5: Symmetric monoidal closed preorders — the hom-element and the tensoring Galois connection"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.1:def79, 7sketches:2.5.1:ex82]
deps_item_ids: [7sketches:2.2.1:def2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.1 — Definition 2.79
with its display (2.80) (a symmetric monoidal preorder is closed when every pair
of elements has a hom-element satisfying the residuation biconditional) and
Exercise 2.82 (that the biconditional says precisely that tensoring by a fixed
element has a right adjoint, in four steps). Printed pp. 69–70; PDF pp. 81–82.
Items covered: `7sketches:2.5.1:def79`, `7sketches:2.5.1:ex82`.

## Background

A monoidal preorder is closed when, for every element, tensoring by it has a
right adjoint — the residual or hom-element — so that `a ⊗ v ≤ w` holds exactly
when `a ≤ (v ⊸ w)`
([nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category),
[Wikipedia: Residuated lattice](https://en.wikipedia.org/wiki/Residuated_lattice)).
Read at the level of preorders this is a Galois connection
([nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection)), and
it is the axiom that makes the cost, Boolean and powerset bases computable.

## Current state in the library

The general class exists with no instance, the instantiated classes have the
wrong tensor, and the adjunction reading is unavailable.

- `Structure/Monoidal/StarAutonomous.v:109` — `Class SymMonClosed`, with
  `smc_is_symmetric : @SymmetricMonoidal C`, `exponent_obj : obj → obj → obj` and
  `exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z` at `:115`, plus `curry'`,
  `uncurry'`, `eval'` and the universal-property fields. `exp_iso` *is* display
  (2.80). The class has **no instance anywhere in the tree**.
- The two closed classes that do have instances — `Closed`
  (`Structure/Cartesian/Closed.v`) and `ClosedMonoidal` — require a *cartesian*
  tensor, so no non-cartesian closed base exists; `Structure/Closed.v`'s
  Eilenberg–Kelly `Class Closed` at `:166` sits inside a comment block spanning
  `:154–195` and asserts nothing (CLAUDE.md records it as an incomplete stub).
- The two thin bases in the tree sit on opposite sides of the requirement.
  `Instance/Props.v:94` (`Props_Closed`, `exponent_obj := Basics.impl`, with
  `Props_Cartesian` at `:69` and `Props_Terminal` at `:53`, over the thin `Props`
  at `:39`) supplies a hom-element but `Props` is never declared `Monoidal` or
  `SymmetricMonoidal`; `Instance/Two/Monoidal.v:105` (`Two_Monoidal`) is the
  Boolean base but has no `Closed` instance (`rg -i 'Two_Closed|Closed _2'`:
  0 hits).
- Steps (1)–(3) of Exercise 2.82 have general-form counterparts. Monotonicity of
  tensoring is `Structure/Premonoidal/Monoidal.v:92`
  (`Monoidal_Tensor_Left (w : C) : @AFunctor C C (fun x => (x ⨂ w)%object)`);
  the evaluation `((v ⊸ w) ⊗ v) ≤ w` is `Structure/Monoidal/Closed.v:83`
  (`Definition eval {x y} : (x ⇒ y) ⨂ x ~> y := uncurry id`), obtained the book's
  way by transposing the identity; monotonicity of the residual in its second
  argument follows from `Functor/Hom/Internal.v:40` (`InternalHomFunctor`) and
  `Structure/Cartesian/Closed.v:165` (`curry_comp_l`), both stated only for the
  cartesian tensor.
- Step (4), the biconditional, is missing in both directions. No `⊣` in the tree
  has a tensoring functor as its left adjoint (enumerating every declaration whose
  type mentions `⊣` gives only `Id ⊣ Id`, the Kleisli/Eilenberg–Moore and
  co-Kleisli/co-Eilenberg–Moore adjunctions, comma, lifting, composition and
  transport adjunctions), and no lemma turns "every `− ⨂ y` has a right adjoint"
  back into a closed structure. Mechanically what blocks the forward direction is
  that `exp_iso` is a pointwise isomorphism with no naturality field, so
  `Adjunction_Hom` cannot be instantiated from it without first proving naturality
  in all three variables at a non-cartesian base.

## Work to be done

Suggested module: `Structure/Monoidal/Preorder/Closed.v`.

1. Define the closed symmetric monoidal preorder: the §2.2.1 class plus a
   hom-element operation and display (2.80) as its single axiom, stated as a
   biconditional of inequalities. Prove it is the thin instance of
   `SymMonClosed` — i.e. build the `SymMonClosed` structure from it — so the
   library's general class finally acquires an instance and the two presentations
   are reconciled.
2. Prove Exercise 2.82(1): `− ⊗ v` is monotone, from clause (a) of the §2.2.1
   class (the specialization of `Monoidal_Tensor_Left`).
3. Prove Exercise 2.82(2): `(v ⊸ w) ⊗ v ≤ w`, by transposing the identity, in the
   preorder form. This is the counit of the adjunction and the preorder shadow of
   `Structure/Monoidal/Closed.v:83`'s `eval`.
4. Prove Exercise 2.82(3): `v ⊸ −` is monotone, using (2).
5. Prove Exercise 2.82(4), the biconditional: a symmetric monoidal preorder is
   closed **iff** `− ⊗ v` has a right adjoint for every `v`. The forward
   direction constructs an `Adjunction` between the two `Proset`s from display
   (2.80) — reusing the Galois-connection-as-adjunction dictionary of #380 rather
   than re-deriving it — and the converse reads the hom-element off the right
   adjoint.
6. Add the naturality that the general `exp_iso` lacks, or record precisely why
   it is not needed in the thin case (all parallel morphisms are equal, so any
   pointwise family is natural) — the header should say which, since it is the
   reason the preorder case is easier than the general one.

In-tree donors: `Structure/Monoidal/StarAutonomous.v:109,115`,
`Structure/Monoidal/Closed.v:83`, `Structure/Premonoidal/Monoidal.v:92`,
`Functor/Hom/Internal.v:40`, `Structure/Cartesian/Closed.v:165`,
`Instance/Props.v:39,53,69,94`, `Theory/Adjunction.v:130,195`, the monoidal
preorder class of the §2.2.1 Definition 2.2 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.79 with display (2.80)
      and Exercise 2.82 (printed pp. 69–70); `≈` on morphisms, never `=`
- [ ] The closed monoidal preorder is defined and shown to be an instance of the
      library's existing `SymMonClosed` class — which currently has none
- [ ] All four steps of Exercise 2.82 are proved, step (4) as a biconditional in
      both directions
- [ ] The forward direction produces a genuine `Adjunction`, routed through
      #380's Galois-connection dictionary
- [ ] The naturality question left open by `exp_iso` is either settled or
      explicitly discharged as vacuous in the thin case, in the header
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the class, the
      `SymMonClosed` instance and both directions of step (4)
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: `SymMonClosed` gaining its
      first instance is flagship-level and the current note records its absence

## Verification

```
coqc -R . Category Structure/Monoidal/Preorder/Closed.v
rg -n 'SymMonClosed' Structure/Monoidal/Preorder/Closed.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions ClosedMonoidalPreorder.
Print Assumptions closed_preorder_SymMonClosed.
Print Assumptions tensor_left_monotone.
Print Assumptions hom_element_eval.
Print Assumptions hom_element_monotone.
Print Assumptions closed_iff_tensor_has_right_adjoint.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
axiom is the biconditional of display (2.80) and not merely the existence of an
evaluation; the adjunction produced is between the two preorders read as
categories; the converse direction is proved, not assumed.

## Dependencies

Depends on: 7sketches:2.2.1:def2 (the symmetric monoidal preorder class).
Depends on: #380 (Galois connections are adjunctions between preorders — the
dictionary step (4) is stated through).

<!-- catalog: {"ids":["7sketches:2.5.1:def79","7sketches:2.5.1:ex82"],"deps":["7sketches:2.2.1:def2","#380"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: The calculus of a monoidal closed preorder, and its self-enrichment"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.1:prop87, 7sketches:2.5.1:remark89]
deps_item_ids: [7sketches:2.5.1:def79]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.1 — Proposition 2.87,
whose five clauses (a)–(e) collect the basic consequences of closure, including
the distributivity display (2.88) (printed p. 70, PDF p. 82), and Remark 2.89,
the corollary that a closed preorder is enriched in itself (printed p. 71,
PDF p. 83). Items covered: `7sketches:2.5.1:prop87`, `7sketches:2.5.1:remark89`.
The remark is the corollary of clause (e) and is filed with it.

## Background

In a closed monoidal preorder tensoring is a left adjoint, hence preserves all
joins; the residual satisfies an evaluation law, is trivial at the unit, and
composes — and that last composition law is precisely what makes the preorder a
category enriched in itself
([nLab: closed monoidal category](https://ncatlab.org/nlab/show/closed+monoidal+category),
[nLab: internal hom](https://ncatlab.org/nlab/show/internal+hom),
[nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category)).

## Current state in the library

Clause by clause, the picture is uneven, and the one clause the self-enrichment
needs is entirely absent.

- Clause (a), tensoring is a left adjoint: not stated. `exp_iso`
  (`Structure/Monoidal/StarAutonomous.v:115`) is a pointwise isomorphism with no
  naturality field, no `Adjunction_Hom` is built from it, and no `⊣` in the tree
  has a tensoring functor on the left. This is the obligation of the §2.5.1
  Definition 2.79 issue and is consumed here.
- Clause (b), tensoring preserves joins: only the binary and empty cases, only
  for a cartesian tensor — `Structure/BiCCC.v:90` (`prod_coprod_r`) and `:221`
  (`prod_zero_r`), both inside the section whose context is
  `` `{@Cartesian C} `{@Cocartesian C} `{@Closed C _} `` and packaged as
  `BiCCC_Distributive` at `:257`. The general principle is available —
  `Adjunction/Continuity.v:223`
  (`left_adjoint_preserves_colimits (A : F ⊣ U) : PreservesAllColimits F`) — but
  cannot be applied without clause (a).
- Clause (c), evaluation: present in general form,
  `Structure/Monoidal/Closed.v:83` (`Definition eval {x y} : (x ⇒ y) ⨂ x ~> y :=
  uncurry id`), obtained exactly the book's way by transposing the identity.
- Clause (d), `v ≅ (I ⊸ v)`: only for the cartesian tensor with the terminal
  unit, `Structure/Cartesian/Closed.v:389` (`exp_one : x^1 ≅ x`).
- Clause (e), `(u ⊸ v) ⊗ (v ⊸ w) ≤ (u ⊸ w)`: **no in-tree witness at all**. The
  only internal composition in the tree is `hom_compose {x y z} : [y, z] ~>
  [[x, y], [x, z]]` at `Structure/Closed.v:175`, which sits inside the comment
  block spanning `:154–195` (`Class Closed` at `:166` is likewise commented out,
  as is `hom_id` at `:174`), so it asserts nothing. The cartesian instance of the
  same morphism is the obligation of #391.
- Remark 2.89: no general self-enrichment exists. There is no construction
  `SymMonClosed C → Enriched C`, and both ingredients are missing at that
  generality — the unit axiom needs a transpose `I ~> (x ⇒ x)` (nothing of that
  type is defined; the Eilenberg–Kelly `hom_id` is in the disabled block) and the
  composition axiom needs clause (e). The one in-tree enrichment of a category in
  something is `Construction/Enriched.v:163`
  (`Category_is_Enriched_over_Set : Enriched Sets ↔ Category`), a statement about
  *arbitrary* categories rather than about closure; reading it as
  self-enrichment of `Sets` needs two steps no file performs — instantiating the
  backward leg at `Sets`, and identifying the resulting hom-object with
  `Instance/Sets/Cartesian/Closed.v:38`'s `exponent_obj`.

## Work to be done

Suggested module: `Structure/Monoidal/Preorder/Closed/Calculus.v`, with the
self-enrichment in `Construction/Enriched/Self.v`.

1. Prove clause (a) by consuming the adjunction produced by the §2.5.1
   Definition 2.79 issue; state it as `(− ⊗ v) ⊣ (v ⊸ −)` in the library's
   `Theory/Adjunction.v` vocabulary rather than as a bare biconditional.
2. Prove clause (b), display (2.88): if the join of a family exists then so does
   the join of its image under `v ⊗ −`, and the two agree up to the induced
   equivalence. Route it through `Adjunction/Continuity.v:223` rather than by a
   direct argument — the point of clause (a) is to make that possible — and state
   it for an *arbitrary* family, not only binary and empty.
3. Prove clauses (c) and (d) at the preorder level: evaluation by transposing the
   identity, and `v ≃ (I ⊸ v)` for a general (non-cartesian) unit, which
   `exp_one` does not cover.
4. Prove clause (e), the composition of residuals — the missing morphism. Prove it
   at the preorder level here, and state the general monoidal-closed form
   `(u ⇒ v) ⨂ (v ⇒ w) ~> (u ⇒ w)` if it comes out of the same transposition,
   since the tree has no internal composition in force at any base.
5. Prove Remark 2.89: a symmetric monoidal closed preorder is enriched in itself,
   with `ehom v w := (v ⊸ w)`. The unit axiom is `I ≤ (x ⊸ x)` from `I ⊗ x ≤ x`;
   the composition axiom is clause (e). Give the construction as
   `ClosedMonoidalPreorder → Enriched` so it is reusable, and record in the
   header what would be needed to lift it to an arbitrary `SymMonClosed` base
   (namely a naturality condition the thin case makes free).
6. As a consistency check, relate the construction to the two existing
   self-enrichment fragments: the `Sets` reading of
   `Construction/Enriched.v:163` and the cartesian internal composition of #391,
   so the tree ends up with one story rather than three.

In-tree donors: `Structure/Monoidal/StarAutonomous.v:109,115`,
`Structure/Monoidal/Closed.v:83`, `Structure/Cartesian/Closed.v:389`,
`Structure/BiCCC.v:90,221,257`, `Adjunction/Continuity.v:223`,
`Construction/Enriched.v:111,163`, `Instance/Sets/Cartesian/Closed.v:38`,
`Structure/Closed.v:154–195` (the disabled Eilenberg–Kelly sketch, for reference
only — it must not be cited as existing API).

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Proposition 2.87 (all five clauses,
      printed p. 70) and Remark 2.89 (printed p. 71); `≈` on morphisms, never `=`
- [ ] Clause (a) is an `Adjunction`, not a restatement of display (2.80)
- [ ] Clause (b) is proved for an arbitrary family and derived from clause (a)
      through the library's left-adjoint preservation result
- [ ] Clause (d) is proved for a general monoidal unit, not only the terminal
      object
- [ ] Clause (e) is proved — the tree's first internal composition of residuals
      that is actually in force
- [ ] Self-enrichment is delivered as a reusable construction from the closed
      preorder class, with both enrichment axioms proved
- [ ] The header records what is missing for the general `SymMonClosed` case
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for all five clauses
      and the self-enrichment
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: self-enrichment is
      flagship-level and the enriched section currently records its absence

## Verification

```
coqc -R . Category Structure/Monoidal/Preorder/Closed/Calculus.v
coqc -R . Category Construction/Enriched/Self.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions tensor_left_adjoint.
Print Assumptions tensor_preserves_joins.
Print Assumptions residual_eval.
Print Assumptions unit_residual_iso.
Print Assumptions residual_compose.
Print Assumptions closed_preorder_self_enriched.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: clause
(b) quantifies over an arbitrary family; clause (e) is a theorem and not a
citation of the commented-out `Structure/Closed.v` block; the self-enrichment's
composition axiom is clause (e) rather than a fresh argument.

## Dependencies

Depends on: 7sketches:2.5.1:def79 (the closed monoidal preorder and its
adjunction characterization).
Depends on: #391 (internal composition in a cartesian closed category — the
cartesian case of clause (e) and of the self-enrichment).

<!-- catalog: {"ids":["7sketches:2.5.1:prop87","7sketches:2.5.1:remark89"],"deps":["7sketches:2.5.1:def79","#391"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: Unital commutative quantales — the class and its join vocabulary"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.2:def90]
deps_item_ids: [7sketches:2.5.1:def79]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.2 Definition 2.90 — a
unital commutative quantale is a symmetric monoidal closed preorder with all
joins, the empty join being the bottom element. Printed p. 71; PDF p. 83. Item
covered: `7sketches:2.5.2:def90`.

## Background

A quantale is a complete lattice carrying a monoid structure whose multiplication
distributes over arbitrary joins; in the unital commutative case it is exactly a
closed symmetric monoidal preorder with all joins, and it is the setting in which
the book's matrix calculus and graph-presentation algorithm live
([nLab: quantale](https://ncatlab.org/nlab/show/quantale),
[nLab: suplattice](https://ncatlab.org/nlab/show/suplattice)). The Boolean and
cost quantales are the two running examples
([nLab: complete lattice](https://ncatlab.org/nlab/show/complete+lattice)).

## Current state in the library

Both conjuncts exist as notions; nothing joins them, and the order-theoretic
vocabulary the definition uses is missing.

- Closure: `Structure/Monoidal/StarAutonomous.v:109` — `Class SymMonClosed`, with
  `exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z` at `:115` — the correct general
  class, currently without a single instance.
- All joins: `Structure/Complete.v:119` —
  `Definition Cocomplete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Colimit F`
  — over a thin base a colimit is the join of the diagram's image, so this is
  "all joins exist"; it has no instance in the library, and no lemma identifies a
  colimit in a thin category with a join.
- Nothing conjoins them: `rg -i quantale` yields a single prose mention
  (`Construction/Enriched.v:78`), and there is no `Quantale`, `CompleteLattice` or
  `SupLattice` class anywhere.
- No order-theoretic join vocabulary. `rg 'Definition (join|meet|sup|inf)'` finds
  only `two_meet` (`Instance/Two/Monoidal.v:37`); every other `join` in the tree
  is monad multiplication. So `⋁A` is expressible only through `Colimit`, and the
  bottom element `0 = ⋁∅` only as an `Initial` object with no in-tree link to the
  empty colimit in this setting. Order-theoretic completeness is the obligation of
  #684.
- Finitary fragments exist at one thin base only: `Instance/Props.v:80`
  (`Props_Cocartesian`, `product_obj := or`) and `:61` (`Props_Initial`,
  `terminal_obj := False`) give binary and empty joins in the entailment
  preorder, and there is no indexed-coproduct construction dual to
  `Structure/Limit/Product.v`'s `iprod`.

## Work to be done

Suggested module: `Structure/Quantale.v`.

1. Define arbitrary joins order-theoretically for a preorder: an operation taking
   an arbitrary indexed family to an upper bound together with the least-upper-bound
   clause, as *data* rather than as an existence statement, so no choice principle
   is introduced. This is the join half of #684's completeness vocabulary; if that
   issue has landed, consume its definition instead of adding a second one.
2. Prove the bridge to the categorical reading: in a thin category a colimit of a
   diagram is a join of its image, and the initial object is the empty join. This
   is the dual of the dictionary #422 establishes for products and meets, and it
   is what lets `Structure/Complete.v:119`'s `Cocomplete` be used as "all joins".
3. Define `Class Quantale` as the §2.5.1 closed monoidal preorder together with
   all joins, with the bottom `0 := ⋁∅` as a derived notion and its
   characterization (below everything) as a lemma.
4. Prove the small facts the later sections use without comment: the tensor is
   monotone in the join order, `0 ⊗ v ≃ 0` (a corollary of Proposition 2.87(b) at
   the empty family), and joins are computed pointwise in a product of quantales.
5. Record in the header the scoping decision — the book's "quantale" always means
   the unital commutative one — and leave a pointer for the noncommutative
   variant that §2.6 mentions.

In-tree donors: `Structure/Monoidal/StarAutonomous.v:109,115`,
`Structure/Complete.v:115,119`, `Structure/Limit/Product.v:51,93,105` (`iprod`,
the indexed-family precedent), `Instance/Props.v:61,80`,
`Instance/Two/Monoidal.v:37`, the closed monoidal preorder of the §2.5.1
Definition 2.79 issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 2.90 (printed p. 71); `≈`
      on morphisms, never `=`
- [ ] Arbitrary joins are data, so no choice principle is introduced
- [ ] The thin-category dictionary "colimit = join of the image, initial = empty
      join" is proved, dual to #422's product/meet dictionary
- [ ] `Class Quantale` conjoins the closed monoidal preorder with all joins, and
      the bottom element is derived rather than posited
- [ ] The corollaries of step 4 are proved
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the class, the
      dictionary and the corollaries
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the first quantale class in the
      tree, and the base of the §2.5.3 matrix calculus

## Verification

```
coqc -R . Category Structure/Quantale.v
rg -n 'Quantale' Structure/ Instance/ | head -40
```
then, in `coqtop -R . Category`:
```
Print Assumptions Quantale.
Print Assumptions thin_colimit_is_join.
Print Assumptions quantale_bottom_least.
Print Assumptions quantale_tensor_bottom.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: "all
joins" quantifies over arbitrary index types, not finite ones; the joins are
data; the class really is the conjunction of closure and completeness rather than
a fresh axiomatization.

## Dependencies

Depends on: 7sketches:2.5.1:def79 (the symmetric monoidal closed preorder).
Depends on: #684 (complete lattices and the order-theoretic completeness
vocabulary this class is stated over).
Depends on: #422 (products in a preorder are greatest lower bounds — the
dictionary this issue dualizes).

<!-- catalog: {"ids":["7sketches:2.5.2:def90"],"deps":["7sketches:2.5.1:def79","#684","#422"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: Cost is monoidal closed by truncated subtraction, and is a quantale"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:2.5.1:example83, 7sketches:2.5.2:example91, 7sketches:2.5.2:ex92]
deps_item_ids: [7sketches:2.2.4:example37, 7sketches:2.5.1:def79, 7sketches:2.5.2:def90]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* — §2.5.1 Example 2.83 (the
cost base is monoidal closed, with truncated subtraction as its hom-element;
printed p. 69, PDF pp. 81–82) and §2.5.2 Example 2.91 (the cost base is a unital
commutative quantale, its joins being infima in the usual order and its empty
join infinity; printed p. 71, PDF pp. 83–84). Exercise 2.92 (printed p. 72,
PDF p. 84) is a two-base exercise: its cost clauses (1b) and (2b) — the empty and
binary joins in the cost base — are covered here, while its Boolean clauses (1a)
and (2a) are covered by the `Bool` issue of §2.2.4/§2.5. Items covered:
`7sketches:2.5.1:example83`, `7sketches:2.5.2:example91`,
`7sketches:2.5.2:ex92` (cost clauses).

## Background

In the cost base the residual of `x` and `y` is `max(0, y − x)`, so monoidal
closure *defines* truncated subtraction from the order and the addition alone —
subtraction was never part of the data
([nLab: quantale](https://ncatlab.org/nlab/show/quantale)). Because the order is
reversed, joins in the cost base are infima in the usual order and the empty join
is infinity, which together with closure makes it a quantale — the base in which
shortest-path computations live
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space),
[Wikipedia: Tropical semiring](https://en.wikipedia.org/wiki/Tropical_semiring)).

## Current state in the library

Neither statement has any counterpart, and neither does the shape of either.

- The cost base itself is absent — `rg -n '\bCost\b'` finds only the English
  word, `rg -in 'infty|Infinity'` returns 0 hits, and no numeric carrier is ever
  imported. Its construction is the obligation of the §2.2.4 Example 2.37 issue.
- Truncated subtraction has no counterpart: `rg -in 'truncated subtraction|monus'`
  returns 0 hits.
- No non-cartesian closed instance exists anywhere. An enumeration of every
  `exponent_obj` in the tree (`AST`, `Lambda`, `Rel`, `Algs`, `Coq`, `Props`,
  `Cat`, `FinSet`, `Sets`, `Product_Closed`, plus `CCC_ClosedMonoidal` and
  `Coq_ClosedMonoidal`) contains no numeric carrier and no non-cartesian tensor,
  so even the *shape* of Example 2.83 — residuation of a non-cartesian tensor over
  a thin base — has no in-tree witness.
- No arbitrary joins and no infima: `rg 'Definition (join|meet|sup|inf)'` finds
  only `two_meet` (`Instance/Two/Monoidal.v:37`), and there is no infimum of an
  arbitrary subset anywhere. `Instance/Omega.v` is the naturals under a
  Type-valued `le_t` (`:28`, `Omega` at `:72`) and carries no monoidal or join
  structure.
- `rg -i quantale` yields one prose mention (`Construction/Enriched.v:78`).

## Work to be done

Suggested module: `Instance/Cost/Quantale.v`, beside the base built by the
§2.2.4 Example 2.37 issue.

1. Define truncated subtraction on the extended non-negative reals,
   `x ⊸ y := max(0, y − x)` with the conventions at infinity spelled out
   (`∞ ⊸ y = 0`, `x ⊸ ∞ = ∞`), and prove display (2.80) for it: `a + x ≥ y` iff
   `a ≥ (x ⊸ y)`, in the reversed order of the base. Assemble the closed monoidal
   preorder instance of the §2.5.1 Definition 2.79 issue.
2. Record the observation the example turns on, as a header note and, where it
   can be stated, as a lemma: the residual is *derived* from the order and the
   tensor, so subtraction is not extra data.
3. Prove the cost clauses of Exercise 2.92: the empty join is `∞` (because it
   must be below every element in the reversed order) and the binary join is
   `min`. State each as a lemma about the join operation, not as a definition.
4. Prove Example 2.91: the cost base has *all* joins — the join of a family is
   its infimum in the usual order, so the proof needs the greatest-lower-bound
   property of the reals for an arbitrary bounded-below family, including the
   infinite case the book illustrates. Together with step 1 this gives the
   `Quantale` instance.
5. Sanity-check the instance by computing a small example: the join of a
   two-element family and of an explicitly given decreasing family, so the
   instance is exercised and not merely declared.

In-tree donors: `Instance/Two/Monoidal.v:37`, `Instance/Omega.v:28,72`, the cost
base of the §2.2.4 Example 2.37 issue, the closed monoidal preorder of the §2.5.1
Definition 2.79 issue, the quantale class of the §2.5.2 Definition 2.90 issue,
the numeric carriers of #759.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 2.83 (printed p. 69),
      Example 2.91 (printed p. 71) and the cost clauses of Exercise 2.92 (printed
      p. 72); `≈` on morphisms, never `=`
- [ ] The residuation biconditional is proved for truncated subtraction, with the
      conventions at infinity explicit
- [ ] The cost base is registered as an instance of the closed monoidal preorder
      class and of the quantale class
- [ ] The empty join is proved to be `∞` and the binary join `min`
- [ ] All joins are proved to exist, the infinite case included
- [ ] The axiom cost of the real carrier is disclosed in the header and recorded
      in docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` introduced by this
      development itself
- [ ] `Print Assumptions` recorded for the closed instance and the quantale
      instance
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Cost/Quantale.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions cost_residual.
Print Assumptions cost_residuation.
Print Assumptions Cost_ClosedMonoidalPreorder.
Print Assumptions cost_empty_join.
Print Assumptions cost_binary_join.
Print Assumptions Cost_Quantale.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
biconditional is stated in the base's reversed order; the empty join is `∞` and
not `0`; the "all joins" proof covers infinite families, since the finite case
would not make the base a quantale.

## Dependencies

Depends on: 7sketches:2.2.4:example37 (the cost monoidal preorder).
Depends on: 7sketches:2.5.1:def79 (the closed monoidal preorder class).
Depends on: 7sketches:2.5.2:def90 (the quantale class).
Depends on: #759 (the reals as an ordered carrier).

<!-- catalog: {"ids":["7sketches:2.5.1:example83","7sketches:2.5.2:example91","7sketches:2.5.2:ex92"],"deps":["7sketches:2.2.4:example37","7sketches:2.5.1:def79","7sketches:2.5.2:def90","#759"]} -->

---8<---

```yaml
title: "Seven Sketches 2.5: Closedness of a monoidal preorder equals distributivity of the tensor over joins"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:2.5.2:prop98]
deps_item_ids: [7sketches:2.5.1:prop87, 7sketches:2.5.2:def90]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §2.5.2 Proposition 2.98 — a
symmetric monoidal preorder with all joins is closed if and only if its tensor
distributes over joins, the residual in the converse direction being the join of
everything whose tensor with the argument stays below the target. Printed p. 73;
PDF p. 85. Item covered: `7sketches:2.5.2:prop98`.

## Background

Distributivity over arbitrary joins is the recognition criterion for closure in a
join-complete monoidal preorder: one direction is that left adjoints preserve
joins, the other is the order-theoretic adjoint functor theorem, which manufactures
the right adjoint as a join over a comprehension
([nLab: quantale](https://ncatlab.org/nlab/show/quantale),
[nLab: adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem)).
For the cartesian tensor this is the frame condition that distinguishes complete
Heyting algebras among complete lattices
([nLab: frame](https://ncatlab.org/nlab/show/frame)).

## Current state in the library

Only the easy direction exists, only for a cartesian tensor, and only finitely.

- Forward, in general categorical form: `Adjunction/Continuity.v:223` —
  `left_adjoint_preserves_colimits {C D} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesAllColimits F` — but it cannot be applied here, because no adjunction
  with a tensoring functor on the left exists (the obligation of the §2.5.1
  Definition 2.79 issue).
- Forward, concretely: only binary and empty distributivity, and only for the
  cartesian tensor — `Structure/BiCCC.v:90` (`prod_coprod_r : x × (y + z) ≅
  x × y + x × z`) and `:221` (`prod_zero_r : x × 0 ≅ 0`), inside the section whose
  context is `` `{@Cartesian C} `{@Cocartesian C} `{@Closed C _} ``, packaged as
  `BiCCC_Distributive` at `:257`. Nothing states preservation of an arbitrary
  join by a general monoidal tensor.
- Converse: entirely missing, and the tool it needs is not applicable as it
  stands. The only adjoint functor theorem in the tree, `Adjunction/GAFT.v:241`,
  carries hypotheses this setting does not supply (`Complete C`, cone-level
  preservation, a solution set at every object) and is oriented to produce a
  *left* adjoint; it is never instantiated at a tensoring functor. The
  order-theoretic form — a join-preserving monotone map between complete posets
  has a right adjoint — is the obligation of #737.
- The setting itself is unavailable: there is no symmetric monoidal preorder with
  all joins (no `Quantale`, no `Cocomplete` instance), and the residual
  `v ⊸ w := ⋁{a : a ⊗ v ≤ w}` has no counterpart because there is no
  order-theoretic join over a comprehension.

## Work to be done

Suggested module: `Structure/Quantale/Closed.v`.

1. State the setting: a symmetric monoidal preorder with all joins, i.e. the
   quantale class of the §2.5.2 Definition 2.90 issue *without* its closure
   conjunct — so the class should be factored to make that intermediate notion
   nameable, or the proposition stated over the two ingredients directly.
2. Prove the forward direction by consuming Proposition 2.87(b) rather than
   re-deriving it: closure gives the adjunction, the adjunction gives preservation
   of all joins through `Adjunction/Continuity.v:223`.
3. Prove the converse: given distributivity, define `v ⊸ w := ⋁{a : a ⊗ v ≤ w}`
   as a join over the comprehension, and prove display (2.80) for it. The
   `≤`-direction uses distributivity to push the tensor inside the join; the
   `≥`-direction is the defining property of the join. Route the argument through
   #737's order-theoretic adjoint functor theorem if that has landed, and
   otherwise prove it directly and note the overlap.
4. Assemble the biconditional as a single statement, and derive the corollary the
   book draws: a symmetric monoidal preorder with all joins is a quantale exactly
   when its tensor distributes over joins.
5. Relate the result to its cartesian special case — the frame/complete-Heyting
   criterion of #684 — as a corollary or, if the shapes differ, as a header note
   saying precisely how the two statements are related. The Seven Sketches
   statement is strictly more general: an arbitrary monoidal tensor rather than
   the meet.

In-tree donors: `Adjunction/Continuity.v:223`, `Structure/BiCCC.v:90,221,257`,
`Structure/Complete.v:119`, `Adjunction/GAFT.v:241` (for comparison only — its
hypotheses do not apply here), the quantale class of the §2.5.2 Definition 2.90
issue, Proposition 2.87(b) from the §2.5.1 calculus issue.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Proposition 2.98 (printed p. 73): a
      biconditional over a symmetric monoidal preorder with all joins, with an
      arbitrary (non-cartesian) tensor and arbitrary joins; `≈` on morphisms,
      never `=`
- [ ] The forward direction is derived from the adjunction, not proved by hand
- [ ] The converse *constructs* the residual as the join over the comprehension
      and proves display (2.80) for it
- [ ] The corollary "join-complete + distributive = quantale" is stated
- [ ] The relation to the cartesian/frame criterion of #684 is stated, with the
      generalization made explicit
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for both directions and
      the corollary
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Structure/Quantale/Closed.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions closed_implies_distributive.
Print Assumptions distributive_implies_closed.
Print Assumptions closed_iff_distributive.
Print Assumptions distributive_join_complete_is_quantale.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
distributive law quantifies over an arbitrary family, not a finite fold; the
converse defines the residual by the stated join rather than assuming it; the
tensor is not required to be cartesian anywhere in the proof.

## Dependencies

Depends on: 7sketches:2.5.1:prop87 (clause (b), the forward direction).
Depends on: 7sketches:2.5.2:def90 (the quantale class and its join vocabulary).
Depends on: #684 (the cartesian/frame special case).
Depends on: #737 (the adjoint functor theorem for complete posets — the tool the
converse direction uses).

<!-- catalog: {"ids":["7sketches:2.5.2:prop98"],"deps":["7sketches:2.5.1:prop87","7sketches:2.5.2:def90","#684","#737"]} -->

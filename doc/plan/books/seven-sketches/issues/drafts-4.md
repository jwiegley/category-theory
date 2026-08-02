```yaml
title: "Seven Sketches 4.1: Co-design diagrams — a typed box-and-wire syntax denoting feasibility relations"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.1:def-codesign-diagram]
deps_item_ids: [7sketches:4.3.2:def4.24, 7sketches:4.5.2:thm4.63, 7sketches:4.4.3:ex4.50]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.1 — the unnumbered prose
definition of a co-design diagram (printed p. 118, PDF p. 130; the robot picture
itself is the numbered display (4.1)), together with the semantics the chapter
supplies for it in §4.2.3 (printed pp. 124–125, PDF pp. 136–137) and §4.5–4.5.2
(printed pp. 140–145, PDF pp. 152–157). Item covered:
`7sketches:4.1:def-codesign-diagram`.

## Background

A co-design diagram is a string diagram whose wires are typed by preorders of
resources and whose boxes are design components: the left ports of a box carry
what it produces, the right ports what it requires, and each connecting wire
asserts that a requirement sits below a production
([nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram)). Its
denotation is a morphism in a compact closed category whose morphisms are
feasibility relations, which is what makes such a diagram compose
([nLab: compact closed category](https://ncatlab.org/nlab/show/compact+closed+category)).

## Current state in the library

The generic box-and-wire *syntax* is in tree; nothing of the co-design reading
is.

- `Construction/ColouredPROP/Signature.v:139` —
  `Inductive CTerm : list Colour -> list Colour -> Type` with constructors
  `CT_id`, `CT_braid`, `CT_comp`, `CT_tens`, `CT_gen`: terms with an ordered list
  of coloured input wires and output wires, built from identity wires, braids,
  sequential and parallel composition, and signature generators.
- `Construction/ColouredPROP/Free.v:97` — `Program Definition CFreeCat : Category`
  with `obj := list Colour` and `hom := @CTerm Colour S`, so those terms already
  form a category.
- `Construction/ColouredPROP/Universal.v:648` — `Theorem cinterp_unique`, the
  universal property: any strict symmetric monoidal functor out of `CFreeCat`
  agreeing with a valuation on generators is the canonical interpretation, up to
  `hom_cast`.
- `Structure/Monoidal/CompactClosed.v:139` — `Class CompactClosed` with `dual`,
  `cc_unit`, `cc_counit`, `snake_left`, `snake_right`: the ambient structure in
  which a diagram with bent wires would be interpreted.

The gap is the whole co-design specialisation. Colours are elements of an
arbitrary `Type`, never preorders of resources; generators come from an arbitrary
signature, never feasibility relations; ports carry no produces/requires
polarity; no `≤` is attached to a connecting wire; and the intended semantic
target does not exist — a whole-tree search finds no occurrence of *co-design*,
*design problem* or *feasibility* in any `.v` file, and the category of preorders
and feasibility relations is itself an open obligation (the §4.3.2 Definition
4.24 issue).

## Work to be done

Suggested module: `Instance/Codesign.v`, over
`Construction/ColouredPROP/{Signature,Free,Universal}.v`.

1. Fix the colour type to be preorders (or, cheaply, an index type equipped with
   a preorder-valued interpretation), so a wire carries a resource ordering
   rather than a bare label.
2. Define the signature of a co-design problem: a generator with left boundary
   `ℓ` and right boundary `r` is interpreted as a feasibility relation from the
   product of the right-port preorders to the product of the left-port preorders,
   in the sense of the §4.2.1 Definition 4.2 issue. Record the polarity
   convention explicitly in the header, since it is the one place readers of the
   book get lost.
3. Give the valuation and instantiate the existing universal property: the
   denotation of a co-design diagram is the unique strict symmetric monoidal
   functor from the free coloured PROP into the category of preorders and
   feasibility relations, which requires that category to be symmetric monoidal —
   supplied by the §4.5.2 Theorem 4.63 issue.
4. Prove the two facts that make the picture legitimate: (a) the composite of a
   diagram is again a feasibility relation between the product preorders of its
   outer boundary (immediate from functoriality, but state it); (b) a wire that
   connects a requirement to a production imposes exactly the `≤` constraint, so
   that the denotation of a two-box series composite is the profunctor composite
   of the two denotations.
5. Discharge the running example: build the robot problem of §4.1 (chassis, motor
   and battery with two summing boxes) over small finite resource preorders and
   compute its denotation, in the decidable-`Example` style of
   `Instance/FinSet/Topos.v`, so the diagram is *evaluated* and not merely typed.
6. Where the chapter draws feedback wires and caps/cups (printed pp. 140–141),
   record which diagrams are expressible with the compact closed structure of the
   §4.5.2 issue and which need only the symmetric monoidal fragment.

In-tree donors: `Construction/ColouredPROP/Signature.v:139`,
`Construction/ColouredPROP/Free.v:97`,
`Construction/ColouredPROP/Universal.v:648`,
`Structure/Monoidal/CompactClosed.v:139`, `Instance/FinSet/Topos.v` (the
`eq_refl` example style), and the feasibility-relation and `Feas` issues below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches §4.1 (printed p. 118) and the
      semantics of §4.2.3 and §4.5.2; `≈` on morphisms, never `=`
- [ ] Wires are typed by preorders and the produces/requires polarity is part of
      the definition, not a comment
- [ ] The denotation is obtained by instantiating `cinterp_unique`, not by a
      bespoke recursion
- [ ] The composite of a co-design diagram is proved to be a feasibility relation
      between the boundary product preorders
- [ ] Series composition of boxes is proved to denote the profunctor composite
- [ ] The robot example is computed, not merely stated
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the denotation
      functor and the two soundness lemmas
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: this is the first in-tree
      diagram language with a non-syntactic semantic target

## Verification

```
coqc -R . Category Instance/Codesign.v
rg -n 'cinterp_unique' Instance/Codesign.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Codesign_denotation.
Print Assumptions codesign_denotation_is_feasibility.
Print Assumptions codesign_series_is_profunctor_composite.
Print Assumptions robot_example.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
denotation lands in the category of preorders and feasibility relations (not in a
PROP); the polarity convention matches the book's left-produces/right-requires
reading; the robot example computes.

## Dependencies

Depends on: 7sketches:4.3.2:def4.24 (the category of preorders and feasibility
relations, which is the semantic target).
Depends on: 7sketches:4.5.2:thm4.63 (its symmetric monoidal and compact closed
structure, without which the diagram cannot be interpreted).
Depends on: 7sketches:4.4.3:ex4.50 (interpretation of a wiring diagram in an
arbitrary symmetric monoidal category).

<!-- catalog: {"ids":["7sketches:4.1:def-codesign-diagram"],"deps":["7sketches:4.3.2:def4.24","7sketches:4.5.2:thm4.63","7sketches:4.4.3:ex4.50"]} -->

---8<---

```yaml
title: "Seven Sketches 4.2: V-profunctors over a quantale, and feasibility relations as the Boolean case"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.2.2:def4.8, 7sketches:4.2.1:def4.2, 7sketches:4.2.2:ex4.9, 7sketches:4.2.2:ex4.10, 7sketches:4.2.3:ex4.18]
deps_item_ids: [7sketches:4.4.4:remark4.53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* — §4.2.1 Definition 4.2, the
feasibility relation between two preorders (printed p. 120, PDF p. 132); §4.2.2
Definition 4.8, the V-profunctor between two V-categories over a unital
commutative quantale, with Exercise 4.9 (the elementwise characterisation) and
Exercise 4.10 (that the Boolean case is exactly a feasibility relation), printed
p. 121, PDF p. 133; and §4.2.3 Exercise 4.18, on a feasibility relation with an
empty row (printed p. 125, PDF p. 137). Items covered:
`7sketches:4.2.2:def4.8`, `7sketches:4.2.1:def4.2`, `7sketches:4.2.2:ex4.9`,
`7sketches:4.2.2:ex4.10`, `7sketches:4.2.3:ex4.18`.

## Background

A profunctor between V-categories is a V-functor out of the tensor of the
opposite of one with the other into the base, regarded as enriched in itself;
equivalently it is a family of hom-objects acted on by both categories, which is
why it is also called a bimodule or distributor
([nLab: profunctor](https://ncatlab.org/nlab/show/profunctor),
[nLab: bimodule](https://ncatlab.org/nlab/show/bimodule)). Over the two-element
quantale this is a relation between preorders that is down-closed in its first
argument and up-closed in its second — the book's feasibility relations
([nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category)).

## Current state in the library

Only the `V = Sets` instance of this schema exists, and even that is built from
ordinary rather than enriched ingredients.

- `Theory/Profunctor.v:122` —
  `Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.` with notation
  `C ⇸ D`. The variance schema is right, but the codomain is `Sets` and the
  opposite and product are the ordinary ones on categories, not their enriched
  analogues.
- `Construction/Enriched.v:111` — `Class Enriched (K : Category) `{@Monoidal K}`
  with `eobj`, `ehom : eobj → eobj → K`, `eid {x} : I ~{K}~> (x ⟿ x)`,
  `ecompose {x y z} : (y ⟿ z) ⨂ (x ⟿ y) ~{K}~> (x ⟿ z)` and the three laws;
  `:145` — `Class EnrichedFunctor` with `efobj`, `efmap`, `efmap_id`,
  `efmap_comp`. So V-categories and V-functors exist over any monoidal base.
- `Construction/Enriched/Two.v:165` —
  `Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder` and
  `:183` — `Theorem EnrichedFunctor_Two_monotone … ↔ MonotoneMap P Q`: the
  Boolean dictionary is proved for categories and functors and stops exactly one
  level below profunctors.
- The three ingredients Definition 4.8 names are each missing: there is no
  opposite of a V-category, no tensor of two V-categories, and no self-enrichment
  of the base — the enriched development consists only of
  `Construction/Enriched.v` and `Construction/Enriched/{Compose,Fun,Natural,Sets,Two}.v`
  — and there is no quantale class at all (`quantale` occurs once in the tree, as
  prose at `Construction/Enriched.v:78`). `Construction/Enriched/Fun.v:30–35`
  already records the same obstruction for hom-objects (ledger 11).
- The elementwise condition of Exercise 4.9 is nowhere stated: the two actions
  are subsumed definitionally by functoriality in the `Sets` case, which is an
  equality of morphisms rather than the single inequality the exercise asks for,
  and `Theory/Dinatural.v` is the ordinary mixed-variance dinaturality condition,
  not an enriched action inequality.
- Nothing in the tree mentions feasibility relations, so neither side of
  Exercise 4.10's identification is available; `Instance/Rel.v:45` and
  `Instance/Props.v:39` were checked and neither carries an order on objects or a
  monotonicity requirement.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor.v`.

1. Define `VProfunctor` over a quantale base: given V-categories `X` and `Y`, a
   V-functor from the tensor of the opposite of `X` with `Y` into the
   self-enriched base. Use the enriched opposite and enriched product supplied by
   the §2.4 issues rather than re-deriving them, and use the base's
   self-enrichment for the codomain.
2. Prove Exercise 4.9 as a biconditional: such a V-functor is the same thing as a
   family of base elements indexed by pairs of objects satisfying the single
   two-sided action inequality (hom of `X` tensor the family tensor hom of `Y`
   below the family). Over a thin base this is where the collapse of the §4.4.4
   Remark 4.53 issue is consumed — cite it, do not re-prove it. Introduce the
   elementwise form as the *working* definition (a smart constructor plus its
   inverse), since every later section computes with it.
3. Specialise to `V = Bool`: define feasibility relations between preorders as
   Definition 4.2 does (a monotone map out of the product of the opposite of one
   preorder with the other into the truth values), and prove Exercise 4.10 as a
   biconditional against the general definition instantiated at the Boolean
   quantale, routed through the existing preorder/Bool-category dictionary. State
   the two unfolded monotonicity clauses as named lemmas, since they are what the
   later sections actually apply.
4. Introduce the notation for a profunctor between V-categories, keeping it
   distinct from the existing `⇸` of `Theory/Profunctor.v` (or generalise that
   notation and prove the `Sets` case agrees).
5. Discharge Exercise 4.18: exhibit a feasibility relation between two small
   finite preorders having an object of the source unrelated to every object of
   the target, and prove it satisfies the definition — i.e. that left-totality is
   *not* required. Add the reading as a header note.

In-tree donors: `Construction/Enriched.v:111,145`,
`Construction/Enriched/Two.v:165,183`, `Theory/Profunctor.v:122` (the `V = Sets`
instance to be reconciled), `Instance/Two/Monoidal.v:80,105`, and the quantale,
enriched-opposite and enriched-product issues cited below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 4.2 (printed p. 120),
      Definition 4.8, Exercises 4.9, 4.10 (printed p. 121) and Exercise 4.18
      (printed p. 125); `≈` on morphisms, never `=`
- [ ] The definition is parameterised by an arbitrary quantale, not by a fixed
      base, and uses the enriched opposite and enriched product rather than the
      ordinary ones
- [ ] Exercise 4.9 is proved as a biconditional, and the elementwise form is the
      one exported for downstream use
- [ ] Feasibility relations are defined and Exercise 4.10 is proved as a
      biconditional against the Boolean instance, with the two monotonicity
      clauses stated as named lemmas
- [ ] The relationship to `Theory/Profunctor.v:122`'s `Sets`-valued profunctor is
      recorded — either as a proved instance or as an explicit header note saying
      why it is not one
- [ ] Exercise 4.18's witness is constructed and its defining property proved
- [ ] The false claim at `Construction/Enriched.v:79–81` — that any closed
      monoidal base is enriched in itself "as `Structure/Closed.v` records" — is
      corrected while this file is being written: `Structure/Closed.v` contains
      only `Curry`, `Flip` and its own `Class Closed` and registers no `Enriched`
      instance, and CLAUDE.md itself describes that file as an incomplete stub
      whose class is not in force. Either the self-enrichment supplied by #798 is
      cited there instead, or the sentence is withdrawn — this codomain is exactly
      what the present definition needs, so the header must not claim it already
      exists
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the definition, the
      elementwise characterisation and the Boolean identification
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: this opens the enriched
      profunctor spine that the rest of Seven Sketches Chapter 4 hangs off

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor.v
rg -n 'VProfunctor|Feasibility' Construction/Enriched/Profunctor.v | head -30
```
then, in `coqtop -R . Category`:
```
Print Assumptions VProfunctor.
Print Assumptions vprofunctor_elementwise.
Print Assumptions Feasibility.
Print Assumptions feasibility_is_bool_profunctor.
Print Assumptions feasibility_not_left_total.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
codomain is the self-enriched base and not `Sets`; the elementwise condition is a
single inequality, not two functoriality equations; the Boolean statement is a
biconditional, not a construction in one direction only.

## Dependencies

Depends on: #799 (the unital commutative quantale class, which is the base).
Depends on: #795 (the opposite of a V-category).
Depends on: #796 (the tensor of two V-categories).
Depends on: #798 (the self-enrichment of the base, which is the codomain).
Depends on: #785 (preorders are exactly Bool-categories, the dictionary the
Boolean case is routed through).
Depends on: 7sketches:4.4.4:remark4.53 (over a thin base the enrichment data are
determined by properties, which is what makes the elementwise form equivalent).

<!-- catalog: {"ids":["7sketches:4.2.2:def4.8","7sketches:4.2.1:def4.2","7sketches:4.2.2:ex4.9","7sketches:4.2.2:ex4.10","7sketches:4.2.3:ex4.18"],"deps":["#799","#795","#796","#798","#785","7sketches:4.4.4:remark4.53"]} -->

---8<---

```yaml
title: "Seven Sketches 4.2: The bridge presentation of a Bool-profunctor, and its feasibility matrix"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.2.2:example4.11, 7sketches:4.2.2:ex4.12]
deps_item_ids: [7sketches:4.2.2:def4.8, 7sketches:4.3.1:def4.21]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.2.2 — Example 4.11, the
reading of a Bool-profunctor as a set of one-way bridges between two preorders,
whose value at a pair is the existence of a route running inside the source,
across one bridge, and on inside the target; and Exercise 4.12, which tabulates
that profunctor as a matrix of truth values indexed by the two object sets and
names it the feasibility matrix. Printed p. 122; PDF p. 134. Items covered:
`7sketches:4.2.2:example4.11`, `7sketches:4.2.2:ex4.12`.

## Background

A Boolean profunctor between two preorders is generated by an arbitrary relation
between their carriers: closing that relation under the two orders gives the
least profunctor containing it, and its value is precisely reachability through
one crossing
([nLab: profunctor](https://ncatlab.org/nlab/show/profunctor),
[nLab: category of relations](https://ncatlab.org/nlab/show/category+of+relations)).
Tabulating the result is the Boolean case of the quantale matrix calculus
([nLab: quantale](https://ncatlab.org/nlab/show/quantale)).

## Current state in the library

Neither the generation statement nor the tabulation exists, and the object being
tabulated is itself missing.

- Bridges: nothing in the tree relates two preorders by a raw relation and closes
  it under their orders. `Instance/Rel.v:45` —
  `Program Definition Rel : Category` with `hom := fun A B => A ~> Ensemble B` and
  `compose := fun x y z f g a b => (exists e : y, In y (g a) e ∧ In z (f e) b)%type`
  — has the right composition formula but its objects are bare Coq types with no
  order, so nothing is closed under anything.
- Matrices: there is no matrix datatype anywhere. Every `matrix` hit is either
  prose (`Theory/Profunctor.v:54,64,69` describes a profunctor as a matrix of
  sets) or the biproduct matrix calculus of `Structure/Semiadditive.v` and
  `Structure/Preadditive.v`, which is morphism-valued in a semiadditive category
  and unrelated.
- Reachability: `Instance/Lambda/Multi.v:46` (`Inductive multi`, with
  `multi_PreOrder` at `:74`) is the only reflexive-transitive closure in the tree
  and is about lambda-term reduction; it is not connected to preorders presented
  by graphs.
- The Boolean profunctor itself does not exist (see the §4.2.2 Definition 4.8
  issue), so neither Example 4.11's claim nor Exercise 4.12's table can currently
  be stated.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor/Bool.v`.

1. Define the profunctor generated by a raw relation between the carriers of two
   preorders, as the composite of the source's unit profunctor, the relation and
   the target's unit profunctor, using the composition of the §4.3.1 Definition
   4.21 issue.
2. Prove Example 4.11's claim in two parts: (a) the generated family really is a
   feasibility relation (the two monotonicity clauses), and (b) its value at a
   pair holds exactly when there is a chain running inside the source order, one
   step of the raw relation, and a chain inside the target order — a reachability
   statement, so it should be proved against the graph-presented preorder of the
   §1.2 reachability issue rather than a bespoke inductive relation.
3. Prove the universal property that justifies the word *generated*: the result
   is the least feasibility relation containing the raw relation, so any
   feasibility relation containing it contains the closure.
4. Define the feasibility matrix of a Boolean profunctor as the Boolean instance
   of the quantale matrix type, and prove the tabulation is a bijection: a
   feasibility relation is exactly a Boolean matrix satisfying the two-sided
   action inequality. This is where the general elementwise characterisation is
   consumed at `V = Bool`.
5. Discharge Exercise 4.12: build the four-element and five-element preorders of
   the example, the three bridges, and compute the full table of truth values as
   decidable `Example`s in the style of `Instance/FinSet/Topos.v`, checking the
   three entries the book supplies.

In-tree donors: `Instance/Rel.v:45`, `Instance/Lambda/Multi.v:46,74`,
`Construction/Enriched/Two.v:165`, `Instance/FinSet/Topos.v` (the `eq_refl`
example style), the V-matrix calculus of #789 and the profunctor issues below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 4.11 and Exercise 4.12
      (printed p. 122); `≈` on morphisms, never `=`
- [ ] The generated profunctor is defined by composition with the two unit
      profunctors, not by an ad-hoc closure
- [ ] The reachability reading is proved, and stated against the graph-presented
      preorder rather than a new inductive relation
- [ ] Leastness (the universal property of the generated profunctor) is proved
- [ ] The feasibility matrix is the Boolean instance of the V-matrix type of
      #789, and the tabulation bijection is proved in both directions
- [ ] Exercise 4.12's table is computed, and the book's three supplied entries
      are checked as proofs, not by inspection
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the generated
      profunctor, the reachability theorem and the tabulation bijection
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor/Bool.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions bridges_profunctor.
Print Assumptions bridges_profunctor_reachability.
Print Assumptions bridges_profunctor_least.
Print Assumptions feasibility_matrix_iso.
Print Assumptions ex4_12_table.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
generated profunctor is a composite of three profunctors, not a hand-rolled
inductive; the reachability statement quantifies over chains in both preorders;
the table is computed rather than asserted.

## Dependencies

Depends on: 7sketches:4.2.2:def4.8 (V-profunctors and feasibility relations).
Depends on: 7sketches:4.3.1:def4.21 (composition of profunctors, out of which the
generated profunctor is built).
Depends on: #789 (V-matrices over a quantale, of which the feasibility matrix is
the Boolean instance).
Depends on: #768 (the preorder presented by a graph and its reachability closure,
against which the route reading is stated).

<!-- catalog: {"ids":["7sketches:4.2.2:example4.11","7sketches:4.2.2:ex4.12"],"deps":["7sketches:4.2.2:def4.8","7sketches:4.3.1:def4.21","#789","#768"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: Composition of V-profunctors, the unit profunctor, and the category Prof_V"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.1:def4.21, 7sketches:4.3.2:def4.25, 7sketches:4.3.2:lem4.27, 7sketches:4.3.2:ex4.30, 7sketches:4.3.2:lem4.31, 7sketches:4.3.2:ex4.32, 7sketches:4.3.2:thm4.23]
deps_item_ids: [7sketches:4.2.2:def4.8]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* — §4.3.1 Definition 4.21, the
composite of two V-profunctors as the join over the middle object of the tensor
of the two values (printed p. 127, PDF p. 139); §4.3.2 Theorem 4.23, that over a
skeletal quantale the V-categories and V-profunctors form a category (printed
p. 127, PDF p. 139); the numbered display (4.25) defining the unit profunctor as
the hom-object assignment of the category itself (printed p. 128, PDF p. 140);
Lemma 4.27 with Exercise 4.30, two-sided unitality and the justification of its
two inequality chains including their collapse to equalities at the Boolean base
(printed pp. 128–129, PDF pp. 140–141); and Lemma 4.31 with Exercise 4.32,
associativity (printed p. 129, PDF p. 141). Items covered:
`7sketches:4.3.1:def4.21`, `7sketches:4.3.2:def4.25`, `7sketches:4.3.2:lem4.27`,
`7sketches:4.3.2:ex4.30`, `7sketches:4.3.2:lem4.31`, `7sketches:4.3.2:ex4.32`,
`7sketches:4.3.2:thm4.23`.

## Background

Profunctors compose by a coend over the middle category; when the base is a
quantale that coend is a join of tensors, i.e. matrix multiplication over the
base, and the hom-object assignment is the unit
([nLab: profunctor](https://ncatlab.org/nlab/show/profunctor),
[nLab: Prof](https://ncatlab.org/nlab/show/Prof)). Composition is unital and
associative only up to isomorphism in general; over a skeletal (antisymmetric)
quantale the two mutual inequalities collapse to equalities and one gets an
honest category
([nLab: quantale](https://ncatlab.org/nlab/show/quantale)).

## Current state in the library

The composition formula exists at two fixed bases, never over a quantale, and the
`Sets` case is deliberately not assembled into a category.

- `V = Sets`: `Construction/Profunctor/Compose.v:267` —
  `Program Definition prof_compose : C ⇸ E` whose object part is
  `coend_obj (SetsCoend (prof_integrand …))`, the coend over the middle category;
  its unit is `prof_id {C} : C ⇸ C := Hom C` (`Compose.v:342`), which is exactly
  the book's unit profunctor read at `V = Sets`.
- The laws are proved, but only up to natural isomorphism:
  `Construction/Profunctor/Laws.v:236` — `prof_unit_left_iso : prof_compose
  prof_id P ≅[Fun] P`; `:395` — `prof_unit_right_iso`; `:722` —
  `prof_assoc_iso : prof_compose (prof_compose P Q) R ≅[Fun] prof_compose P
  (prof_compose Q R)`, resting on `Theory/Coend/Fubini.v:449`'s `coend_fubini`.
  The two mutually inverse maps of the unit law (`Laws.v:129,138,146,213`)
  correspond one-for-one to the book's two inequality chains: `lu_from` inserts
  the identity at the join, `lu_to` applies the profunctor's own reindexing.
- No category is formed: `Theory/Profunctor.v:31–38` states that no single
  category of all profunctors between all categories is assembled, on a
  universe-size ground, and `Construction/Profunctor/Laws.v:43–44` records that
  the bicategory packaging is deferred.
- `V = Bool`, discrete objects only: `Instance/Rel.v:45` — `Program Definition
  Rel : Category` with `id := Singleton` and the existential-of-conjunction
  composition — realises the Boolean instance of the formula *strictly*, with
  `id_left`/`id_right` at `:66`/`:73` and `comp_assoc` at `:79–80`. But its
  objects are bare Coq types, so it is the theorem restricted to discrete
  preorders and the profunctor side condition is vacuous on it.
- Nothing is parameterised by a base: there is no quantale class, hence no join
  of tensors, no skeletality hypothesis, and no statement in which the collapse
  of two inequalities to an equality could be made. The Boolean half of
  Exercise 4.30 — that every step of the chain is an equality at the Boolean
  base — has no counterpart at all.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor/Compose.v`, with the category
in `Construction/Enriched/Profunctor/Cat.v`.

1. Define the composite of two V-profunctors by the join-over-the-middle-object
   formula, and prove it respects the elementwise equivalence in both arguments.
   State and use the fact that this is the V-matrix product of #789 restricted to
   profunctors — do not re-derive the matrix algebra.
2. Define the unit profunctor as the hom-object assignment of a V-category, and
   prove it *is* a profunctor (the action inequality is the enriched composition
   law).
3. Prove Lemma 4.27 (two-sided unitality) by the book's route: each direction as
   an inequality — one from the unit law of the base together with the identity
   element of the V-category and the join being an upper bound, the other from
   the universal property of the join together with the profunctor action
   inequality — then combined by skeletality. Keep the two inequalities as named
   lemmas, since Exercise 4.30 is precisely the request to justify their steps.
4. Discharge Exercise 4.30 as three obligations: the two chains become the two
   named lemmas of step 3 with each step a cited law rather than a `cat` call,
   and the Boolean claim becomes a proved statement that at the Boolean base both
   inequalities are equalities (the base is idempotent and its tensor is the
   meet).
5. Prove Lemma 4.31 (associativity), which is Exercise 4.32's request: both
   inequalities, using distributivity of the tensor over joins, then skeletality.
6. Assemble `ProfV`: objects the V-categories, morphisms the V-profunctors,
   identities the unit profunctors, composition as above — a genuine `Category`
   with the laws holding on the nose. Record in the header why this is possible
   here while `Theory/Profunctor.v:31–38` declines it at `V = Sets` (the
   hom-collection of a quantale-enriched profunctor does not raise the universe
   level, and skeletality makes the laws strict).
7. Reconcile with what exists: prove that the Boolean instance restricted to
   discrete preorders is `Instance/Rel.v`'s composition and identity, so the
   generalisation is certified against the case already in tree.

In-tree donors: `Construction/Profunctor/Compose.v:267,342`,
`Construction/Profunctor/Laws.v:98,110,129,138,146,213,236,395,516,620,722`
(the `V = Sets` proof skeleton, which transfers step by step),
`Theory/Coend/Fubini.v:449`, `Instance/Rel.v:45,66,73,79`, and #789's `Mat V`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 4.21, Theorem 4.23, display
      (4.25), Lemma 4.27, Exercise 4.30, Lemma 4.31 and Exercise 4.32 (printed
      pp. 127–129); `≈` on morphisms, never `=`
- [ ] Composition is the join-over-the-middle-object formula over an arbitrary
      quantale and is proved to be the #789 matrix product restricted to
      profunctors
- [ ] The unit profunctor is proved to be a profunctor, not merely defined
- [ ] Both unit inequalities and both associativity inequalities are separate
      named lemmas, so Exercise 4.30's justification is a proof obligation
- [ ] The Boolean collapse of Exercise 4.30(2) is proved, not remarked
- [ ] Skeletality of the base is what upgrades the inequalities to equalities,
      and this use is isolated rather than diffused through the proofs
- [ ] `ProfV` is assembled as a `Category` with strict unit and associativity
      laws, and the header records why the universe obstruction of
      `Theory/Profunctor.v:31–38` does not apply
- [ ] The Boolean-on-discrete-objects case is proved to agree with
      `Instance/Rel.v`
- [ ] `Theory/Profunctor.v:132`'s `Id_Profunctor` — a duplicate of
      `Construction/Profunctor/Compose.v:342`'s `prof_id` with no use site
      anywhere in the tree — is either given a use site or removed while this
      file is being written, so the tree does not acquire a third unit profunctor
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the composite, the
      unit, both laws and the category
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: this is flagship-level — the
      first category of profunctors in the tree

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor/Compose.v
coqc -R . Category Construction/Enriched/Profunctor/Cat.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions vprof_compose.
Print Assumptions vprof_unit.
Print Assumptions vprof_unit_left.
Print Assumptions vprof_unit_right.
Print Assumptions vprof_unit_bool_equalities.
Print Assumptions vprof_assoc.
Print Assumptions ProfV.
Print Assumptions ProfV_Bool_discrete_is_Rel.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the laws
are strict equalities in `ProfV` (not natural isomorphisms as in the `Sets`
development); skeletality is genuinely load-bearing and cited where used; the
`Instance/Rel.v` reconciliation is a proof.

## Dependencies

Depends on: 7sketches:4.2.2:def4.8 (V-profunctors, the morphisms being composed).
Depends on: #799 (the quantale class, and its skeletality predicate).
Depends on: #789 (V-matrices and their product, of which this composition is the
restriction to profunctors).
Depends on: #801 (closedness equals distributivity of the tensor over joins — the
step the associativity proof consumes).

<!-- catalog: {"ids":["7sketches:4.3.1:def4.21","7sketches:4.3.2:def4.25","7sketches:4.3.2:lem4.27","7sketches:4.3.2:ex4.30","7sketches:4.3.2:lem4.31","7sketches:4.3.2:ex4.32","7sketches:4.3.2:thm4.23"],"deps":["7sketches:4.2.2:def4.8","#799","#789","#801"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: Feas — preorders and feasibility relations as the Boolean instance of Prof_V"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.2:def4.24]
deps_item_ids: [7sketches:4.3.2:thm4.23, 7sketches:4.2.1:def4.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.3.2 Definition 4.24 — the
category whose objects are preorders and whose morphisms are feasibility
relations, obtained as the Boolean instance of the category of V-categories and
V-profunctors, with composition the join-of-meets formula and identities the
order relations themselves. Printed p. 127; PDF p. 139. Item covered:
`7sketches:4.3.2:def4.24`.

## Background

Preorders and order-compatible relations between them form a category in which
composition is relational composition and the identity at a preorder is its own
order relation rather than equality; it is the Boolean case of the bicategory of
profunctors and the ambient in which the book's design problems compose
([nLab: profunctor](https://ncatlab.org/nlab/show/profunctor),
[nLab: category of relations](https://ncatlab.org/nlab/show/category+of+relations)).

## Current state in the library

The two halves of the definition exist separately, in different files, and
neither covers the other.

- Objects: `Construction/Enriched/Two.v:165` —
  `Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder`, with
  the morphism leg `EnrichedFunctor_Two_monotone` at `:183`. This supplies
  exactly the objects of the intended category, in both directions.
- Composition and identities: `Instance/Rel.v:45` — `Program Definition Rel :
  Category` with `hom := fun A B => A ~> Ensemble B`, `id := Singleton` and
  composition by the existential of a conjunction, whose category obligations are
  discharged at `:54–81`. But its objects are bare Coq types, its hom-sets carry
  no order-compatibility requirement, and its identity is the equality relation
  rather than an order relation — so it is the intended category restricted to
  discrete preorders.
- Nothing assembles preorders as objects with feasibility relations as morphisms:
  there is no category of preorders in the tree at all
  (`Instance/Poset.v:116`'s `Poset` builds a single poset *as* a category, not
  the category of them), and no hom-type of order-compatible relations.

## Work to be done

Suggested module: `Instance/Feas.v`.

1. Define the category by instantiating the category of V-categories and
   V-profunctors of the §4.3.2 Theorem 4.23 issue at the Boolean quantale, rather
   than by rebuilding it: objects the Bool-categories, morphisms the Boolean
   profunctors.
2. Transport it along the existing preorder dictionary so the objects are
   literally preorders and the morphisms literally feasibility relations in the
   sense of the §4.2.1 Definition 4.2 issue — an isomorphism (or at least an
   equivalence) of categories, proved rather than asserted, since the whole point
   of the definition is that the two readings coincide.
3. Prove the two facts a reader needs about the transported form: the identity at
   a preorder is its order relation, and composition is the join-of-meets formula
   over intermediate objects.
4. Relate it to `Instance/Rel.v`: the assignment sending a bare type to its
   discrete preorder is a functor into this category which is fully faithful, so
   `Rel` embeds as the full subcategory on discrete objects. This is the check
   that the generalisation is faithful to the case already in tree.
5. Record in the header the two consumers this category exists for: the co-design
   semantics of §4.1 and the compact closed structure of §4.5.2.

In-tree donors: `Construction/Enriched/Two.v:165,183`, `Instance/Rel.v:45,54–81`,
`Instance/Proset.v:33`, `Instance/Two/Monoidal.v:80,105`, and the two profunctor
issues below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 4.24 (printed p. 127); `≈`
      on morphisms, never `=`
- [ ] The category is obtained by instantiating the general one at the Boolean
      base, not rebuilt from scratch
- [ ] The transport to literal preorders and literal feasibility relations is
      proved, not asserted
- [ ] The identity is proved to be the order relation and composition the
      join-of-meets formula
- [ ] `Rel` is exhibited as the full subcategory on discrete preorders, with full
      faithfulness proved
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed under the global context for the category, the
      transport and the `Rel` embedding
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the category of preorders and
      feasibility relations is the semantic home of the co-design development

## Verification

```
coqc -R . Category Instance/Feas.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Feas.
Print Assumptions Feas_objects_are_preorders.
Print Assumptions Feas_id_is_order.
Print Assumptions Feas_compose_formula.
Print Assumptions Rel_into_Feas_fully_faithful.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
identity really is the order relation and not the diagonal; the objects are
arbitrary preorders, not discrete ones; the `Rel` comparison is a proved full
faithfulness, not a remark.

## Dependencies

Depends on: 7sketches:4.3.2:thm4.23 (the category of V-categories and
V-profunctors, of which this is the Boolean instance).
Depends on: 7sketches:4.2.1:def4.2 (feasibility relations, which are its
morphisms).
Depends on: #785 (preorders are exactly Bool-categories — the object-level
dictionary this transport uses).
Depends on: #262 (`Rel` and converse relations — the discrete case this embeds).

<!-- catalog: {"ids":["7sketches:4.3.2:def4.24"],"deps":["7sketches:4.3.2:thm4.23","7sketches:4.2.1:def4.2","#785","#262"]} -->

---8<---

```yaml
title: "Seven Sketches 4.2/4.3: Cost-profunctors — distance matrices, composition, and computation by matrix powers"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:4.2.2:example4.13, 7sketches:4.2.2:ex4.15, 7sketches:4.2.2:remark4.16, 7sketches:4.2.2:ex4.17, 7sketches:4.3.1:ex4.22, 7sketches:4.3.2:ex4.26]
deps_item_ids: [7sketches:4.2.2:def4.8, 7sketches:4.3.1:def4.21]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality* — §4.2.2 Example 4.13, the
cost reading of a profunctor as bridges of given length between two weighted
graphs whose value is the shortest route across one bridge (printed pp. 122–123,
PDF pp. 134–135); Exercise 4.15, the resulting distance table (printed p. 123,
PDF p. 135); Remark 4.16, the algorithm computing that table as a product of the
two stabilised distance matrices with the bridge matrix (printed p. 123, PDF
p. 135); Exercise 4.17, running that product and checking it against the table
(printed pp. 123–124, PDF pp. 135–136); §4.3.1 Exercise 4.22, the composite of
two cost profunctors (printed p. 127, PDF p. 139); and §4.3.2 Exercise 4.26, the
unit profunctor of a cost category, whose bridge lengths are its own distances
(printed p. 128, PDF p. 140). Items covered: `7sketches:4.2.2:example4.13`,
`7sketches:4.2.2:ex4.15`, `7sketches:4.2.2:remark4.16`, `7sketches:4.2.2:ex4.17`,
`7sketches:4.3.1:ex4.22`, `7sketches:4.3.2:ex4.26`.

## Background

Enriching in the non-negative extended reals ordered by reverse magnitude with
addition as tensor turns categories into Lawvere metric spaces and profunctors
into families of distances between two such spaces
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).
Their composition is min-plus matrix multiplication, and a profunctor presented
by finitely many bridges is computed by multiplying the two spaces' stabilised
distance matrices with the bridge matrix
([Wikipedia: Min-plus matrix multiplication](https://en.wikipedia.org/wiki/Min-plus_matrix_multiplication),
[Wikipedia: Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)).

## Current state in the library

Neither the base nor any of the computations exists.

- No cost quantale: the non-negative extended reals are not in the tree at all —
  the library never imports Coq's reals, and every occurrence of *metric* is
  prose in a header (`Construction/Enriched.v:74–77`, `Instance/Poset.v:75–77`,
  `Instance/Two.v:71`, the last of which states outright that only the
  truth-value base is carried in full). Providing that base is the obligation of
  #781 and #787.
- No matrices and no matrix powers: there is no matrix datatype, no iterated
  composition operator for morphisms anywhere in the tree, and no shortest-path
  or transitive-closure computation over a numeric base — those are the
  obligations of #789 and #790.
- The general composition formula that Exercise 4.22 instantiates exists only at
  `V = Sets` (`Construction/Profunctor/Compose.v:267`, as a coend) and at the
  discrete Boolean base (`Instance/Rel.v:45`), and the unit profunctor that
  Exercise 4.26 draws exists only as `prof_id := Hom C`
  (`Construction/Profunctor/Compose.v:342`) at `V = Sets`; neither is available
  over a numeric base.
- Consequently no distance table, no bridge, and no product of the shape the
  remark describes can currently be written down.

## Work to be done

Suggested module: `Instance/Cost/Profunctor.v`.

1. Instantiate the general V-profunctor at the cost quantale and prove the
   elementwise reading: a cost profunctor between two Lawvere metric spaces is a
   family of extended-real values satisfying one two-sided triangle inequality,
   which is the numeric form of the general action inequality.
2. Prove Example 4.13's characterisation: for a profunctor presented by finitely
   many bridges of given lengths, the value at a pair is the minimum over routes
   of the sum of the source distance, one bridge length and the target distance.
   State it against the generated profunctor of the §4.2.2 Example 4.11 issue at
   the cost base, so the Boolean and cost readings are two instances of one
   theorem rather than two ad-hoc statements.
3. Prove Remark 4.16's algorithm: the matrix of the profunctor is the matrix
   product of the source's stabilised distance matrix, the raw bridge matrix and
   the target's stabilised distance matrix. The stabilised matrices are #790's
   matrix powers, so this issue supplies only the new step — that pre- and
   post-multiplying a bridge matrix by the two closures yields exactly the
   generated profunctor — and cites #790 for the rest.
4. Discharge the four computations as decidable `Example`s in the style of
   `Instance/FinSet/Topos.v`, each checked against the entries the book supplies:
   Exercise 4.15's four-by-three table; Exercise 4.17's product of the three
   matrices, proved equal to that table; Exercise 4.22's four-by-four composite of
   two cost profunctors; and Exercise 4.26's unit profunctor of a cost category,
   proved to have the space's own distances as its values.
5. Record in the header that the bound on the number of matrix powers needed is
   the vertex count of the corresponding space, citing #790's stabilisation
   theorem rather than re-deriving it.

In-tree donors: `Construction/Profunctor/Compose.v:267,342`,
`Instance/FinSet/Topos.v` (the `eq_refl` example style),
`Instance/FinSet.v:116` (finite carriers), and the cost-base, matrix and
matrix-power issues below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 4.13, Exercises 4.15 and 4.17,
      Remark 4.16 (printed pp. 122–124), Exercise 4.22 (printed p. 127) and
      Exercise 4.26 (printed p. 128); `≈` on morphisms, never `=`
- [ ] The elementwise (triangle-inequality) reading of a cost profunctor is
      proved from the general definition, not posited
- [ ] The shortest-route characterisation is an instance of the general generated
      profunctor, not a separate construction
- [ ] Remark 4.16's identity — closure times bridge matrix times closure equals
      the generated profunctor — is proved, and cites #790 for stabilisation
- [ ] Exercises 4.15, 4.17, 4.22 and 4.26 are computed, with the book's supplied
      entries checked as proofs
- [ ] Exercise 4.17's agreement with Exercise 4.15 is a proved equality of tables,
      not an inspection
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the carrier
      axioms disclosed by the cost base, which are declared and recorded in
      docs/AXIOMS.md
- [ ] `Print Assumptions` recorded for the elementwise reading, the shortest-route
      characterisation and the matrix identity
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Instance/Cost/Profunctor.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions cost_profunctor_elementwise.
Print Assumptions cost_profunctor_shortest_route.
Print Assumptions cost_profunctor_matrix_product.
Print Assumptions ex4_15_table.
Print Assumptions ex4_17_agrees.
Print Assumptions ex4_22_composite.
Print Assumptions ex4_26_unit_is_distance.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
matrix identity is proved for an arbitrary finite presentation, not only for the
book's example; every table is computed rather than asserted; the stabilisation
bound is cited, not re-proved.

## Dependencies

Depends on: 7sketches:4.2.2:def4.8 (V-profunctors, instantiated here at the cost
base).
Depends on: 7sketches:4.3.1:def4.21 (composition of profunctors, which
Exercise 4.22 computes).
Depends on: #781 (the cost monoidal preorder).
Depends on: #787 (Lawvere metric spaces as cost categories).
Depends on: #789 (V-matrices and their product).
Depends on: #790 (matrix powers and their stabilisation, on which Remark 4.16's
algorithm rests).

<!-- catalog: {"ids":["7sketches:4.2.2:example4.13","7sketches:4.2.2:ex4.15","7sketches:4.2.2:remark4.16","7sketches:4.2.2:ex4.17","7sketches:4.3.1:ex4.22","7sketches:4.3.2:ex4.26"],"deps":["7sketches:4.2.2:def4.8","7sketches:4.3.1:def4.21","#781","#787","#789","#790"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: Companions and conjoints of a V-functor, and the adjointness criterion"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.3:def4.34, 7sketches:4.3.3:example4.35, 7sketches:4.3.3:ex4.36, 7sketches:4.3.3:ex4.41, 7sketches:4.3.3:example4.37, 7sketches:4.3.3:ex4.38]
deps_item_ids: [7sketches:4.2.2:def4.8, 7sketches:4.3.3:remark4.39]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.3.3 — Definition 4.34,
the companion and the conjoint of a V-functor as the two profunctors obtained by
applying it inside the target's hom-object (printed p. 130, PDF p. 142);
Example 4.35 and Exercise 4.36, that the companion and conjoint of an identity
functor agree and are the unit profunctor (printed pp. 130–131, PDF pp. 142–143);
Example 4.37 and Exercise 4.38, the companion and conjoint of the monotone
addition map on triples of reals, read as feasibility relations (printed p. 131,
PDF p. 143); and Exercise 4.41, that two V-functors are adjoint exactly when the
companion of one equals the conjoint of the other, with the identity case as a
corollary (printed p. 131, PDF p. 143). Items covered:
`7sketches:4.3.3:def4.34`, `7sketches:4.3.3:example4.35`,
`7sketches:4.3.3:ex4.36`, `7sketches:4.3.3:ex4.41`,
`7sketches:4.3.3:example4.37`, `7sketches:4.3.3:ex4.38`.

## Background

Every functor induces two profunctors — its companion, representable on one side,
and its conjoint, representable on the other — and the two are exchanged by
passing to an adjoint; in a proarrow equipment this is the standard companion and
conjoint of a vertical arrow
([nLab: proarrow equipment](https://ncatlab.org/nlab/show/proarrow+equipment),
[nLab: companion pair](https://ncatlab.org/nlab/show/companion+pair)). The
identity functor has companion and conjoint both equal to the unit profunctor
([nLab: profunctor](https://ncatlab.org/nlab/show/profunctor)).

## Current state in the library

The two constructions exist verbatim at `V = Sets` and the criterion is proved
there at full biconditional strength; the enriched form and the corollaries are
missing.

- `Theory/Profunctor.v:155` —
  `Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D := Hom D ◯ (F^op ∏⟶ (@Id D))`,
  which on a pair is the target hom out of the image: the companion. `:158` —
  `Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D := Hom C ◯ ((@Id C)^op ∏⟶ U)`,
  which is the conjoint, including the source/target reversal.
- `Theory/Profunctor/Adjunction.v:70` —
  `Definition representable_adjunction : (F ⊣ U) ↔ (Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U)`,
  with both legs constructed (`:57`, `:64`). This *is* Exercise 4.41(1) at
  `V = Sets`, with a natural isomorphism where the book has an equality.
- Neither corollary is recorded. `Instance/Adjoints.v:42` gives
  `adj_id : Id ⊣ Id`, so the identity case is one application away, but no
  statement in the tree draws it; and the identification of the companion of an
  identity with the unit profunctor `prof_id := Hom C`
  (`Construction/Profunctor/Compose.v:342`) is unstated — at functor level it
  needs an identity law for the componentwise functor product, which the library
  does not have.
- The abstract double-category form exists but is instantiated in the wrong
  place: `Theory/DoubleCategory/Companion.v:142` (`Record Companion`), `:308`
  (`Record Conjoint`) and `:252` (`companion_unique`) are at full strength, but
  the only model is `Construction/Sq.v`, where every morphism is its own
  companion (`:118`) while conjoints exist *only* for isomorphisms (`:146`,
  `:161`) — the opposite of the situation here, where every V-functor has both.
- The concrete instance of Example 4.37 is unavailable: the reals are not in the
  tree, no monotonicity of addition is stated even for the naturals, and
  `Repr_right` is never instantiated at any concrete functor.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor/Companion.v`, with the
concrete instance in `Instance/Cost/Codesign.v` or alongside the reals.

1. Define the companion and the conjoint of a V-functor by the book's two
   formulas, and prove each satisfies the action inequality, so both really are
   V-profunctors.
2. Prove Exercise 4.41(1) as a biconditional over a skeletal quantale: two
   V-functors are V-adjoint, in the sense of the §4.3.3 Remark 4.39 issue,
   exactly when the companion of one equals the conjoint of the other. Follow the
   `Sets` proof, which routes an adjunction through the hom-bifunctor
   isomorphism, but conclude an equality rather than an isomorphism, using
   skeletality.
3. Prove Exercise 4.36 and Example 4.35 as corollaries: the companion of an
   identity is the unit profunctor (a computation on hom-objects), and the
   companion and the conjoint of an identity agree — the latter obtained from
   step 2 applied to the identity adjunction, so the exercise's intended route is
   the one taken.
4. Record the `V = Sets` reconciliation: state and prove that the general
   companion and conjoint instantiate to `Repr_left` and `Repr_right`, and that
   the general criterion instantiates to `representable_adjunction`. This is the
   check that the enriched development generalises what is already in tree rather
   than duplicating it. While doing so, add the missing identity law for the
   componentwise functor product, which is what currently blocks stating
   `Repr_left Id ≅ prof_id` at functor level.
5. Discharge Example 4.37 and Exercise 4.38 over the reals: prove that addition
   on triples is monotone for the product order, hence a Boolean functor, and
   compute its companion (a triple is feasible for a target value when its sum is
   below that value) and its conjoint (the reverse inequality), each proved to be
   a feasibility relation.
6. Add a header note relating the two presentations: the companion and conjoint
   defined here are the horizontal cells that
   `Theory/DoubleCategory/Companion.v` axiomatises, and the double category of
   V-categories, V-functors and V-profunctors — in which every vertical arrow has
   both — is not built here.

In-tree donors: `Theory/Profunctor.v:155,158`,
`Theory/Profunctor/Adjunction.v:57,64,70`, `Instance/Adjoints.v:42`,
`Construction/Profunctor/Compose.v:342`,
`Theory/DoubleCategory/Companion.v:142,252,308`, `Construction/Sq.v:118,146,161`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 4.34, Examples 4.35 and
      4.37, Exercises 4.36, 4.38 and 4.41 (printed pp. 130–131); `≈` on
      morphisms, never `=`
- [ ] Both constructions are proved to be V-profunctors, not merely defined
- [ ] The adjointness criterion is a biconditional over a skeletal quantale, with
      an equality of profunctors as its conclusion
- [ ] Both corollaries are recorded as in-tree statements: companion of an
      identity equals the unit profunctor, and companion equals conjoint there
- [ ] The `V = Sets` instantiation to `Repr_left`/`Repr_right` and to
      `representable_adjunction` is proved
- [ ] The identity law for the componentwise functor product is added, so
      `Repr_left Id` is identified with `prof_id` at functor level
- [ ] Monotonicity of addition is proved and the two feasibility relations of
      Example 4.37 and Exercise 4.38 are constructed and verified
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the carrier axioms
      disclosed by the real-number base
- [ ] `Print Assumptions` closed for the two constructions, the criterion and both
      corollaries
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor/Companion.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions vprof_companion.
Print Assumptions vprof_conjoint.
Print Assumptions adjoint_iff_companion_eq_conjoint.
Print Assumptions companion_id_is_unit.
Print Assumptions companion_id_eq_conjoint_id.
Print Assumptions companion_Sets_is_Repr_left.
Print Assumptions addition_companion.
Print Assumptions addition_conjoint.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
conjoint runs in the reverse direction; the criterion is proved in both
directions; the identity corollary is derived from the criterion rather than
recomputed.

## Dependencies

Depends on: 7sketches:4.2.2:def4.8 (V-profunctors).
Depends on: 7sketches:4.3.3:remark4.39 (V-adjunctions, the left-hand side of the
criterion).
Depends on: #799 (the quantale class and its skeletality predicate, which turns
the criterion's isomorphism into an equality).
Depends on: #759 (the reals as an ordered carrier, in which Example 4.37 and
Exercise 4.38 live).
Depends on: #774 (the reals under addition as a symmetric monoidal preorder,
supplying the monotonicity of addition).

<!-- catalog: {"ids":["7sketches:4.3.3:def4.34","7sketches:4.3.3:example4.35","7sketches:4.3.3:ex4.36","7sketches:4.3.3:ex4.41","7sketches:4.3.3:example4.37","7sketches:4.3.3:ex4.38"],"deps":["7sketches:4.2.2:def4.8","7sketches:4.3.3:remark4.39","#799","#759","#774"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: V-adjunctions between V-categories"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.3:remark4.39]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.3.3 Remark 4.39 with its
numbered display (4.40) — a V-adjunction is a pair of V-functors for which the
hom-object of the source at an object and the image of the other is isomorphic to
the hom-object of the target at the image and the object, for all pairs; over a
skeletal base the isomorphism is an equality. Printed p. 131; PDF p. 143. Item
covered: `7sketches:4.3.3:remark4.39`.

## Background

An enriched adjunction is a pair of enriched functors whose hom-objects
correspond, which at the base of truth values is a Galois connection between
preorders and at the base of sets is an ordinary adjunction
([nLab: enriched functor](https://ncatlab.org/nlab/show/enriched+functor),
[nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection)). This
hom-object form is the one the companion/conjoint criterion of the same section
is stated against
([nLab: adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor)).

## Current state in the library

The hom-object form exists only for ordinary categories, and no enriched
adjunction of any kind is defined.

- `Theory/Adjunction.v:130` — `Class Adjunction` whose field `adj {x y}` is an
  isomorphism in `Sets` between the hom-setoid of the target at the image and the
  hom-setoid of the source, with naturality in both variables recorded as four
  further fields.
- `Adjunction/Hom.v:72` — `Class Adjunction_Hom :=
  { hom_adj : Hom C ◯ F^op ∏⟶ Id ≅[[D^op ∏ C, Sets]] Hom D ◯ Id^op ∏⟶ U }`,
  which is the same statement packaged as a natural isomorphism of hom-bifunctors
  — display (4.40) read at the base of sets.
- The Boolean case is available only indirectly: `Instance/Proset.v:33` makes a
  preorder a thin category, so an adjunction between two of them is a Galois
  connection, as `Theory/Adjunction.v:78` and `Instance/Poset.v:47` both note in
  prose. No Galois-connection definition or theorem exists in the tree; that is
  the obligation of #380.
- Nothing enriched: `Construction/Enriched.v` and all five of its satellites
  contain no occurrence of *adjunction* whatsoever, and no statement anywhere
  relates two enriched functors by an isomorphism of hom-objects. There is no
  quantale base either, so the skeletal upgrade of the isomorphism to an equality
  cannot presently be phrased.

## Work to be done

Suggested module: `Construction/Enriched/Adjunction.v`.

1. Define a V-adjunction over a monoidal base: two V-functors together with an
   isomorphism of hom-objects, natural in both arguments. State the naturality
   explicitly even though it is automatic over a thin base, so the definition is
   the correct one for a general base and specialises without change.
2. Prove that over a thin (preorder) base the naturality requirement is vacuous,
   so the definition collapses to the book's two-inequality form — consuming the
   §4.4.4 Remark 4.53 collapse rather than restating it.
3. Prove the skeletal upgrade: over a skeletal base the isomorphism of hom-objects
   is an equality, which is what the companion/conjoint criterion of the same
   section needs.
4. Reconcile with the two cases already in tree: at the base of sets a
   V-adjunction is exactly `Adjunction_Hom` (hence, through the existing
   conversions, an `Adjunction`), and at the base of truth values it is exactly a
   Galois connection between the corresponding preorders. Both as biconditionals.
5. Record the consequences the chapter uses without comment: composition of
   V-adjunctions, and that a V-adjunction between skeletal V-categories determines
   each functor from the other up to equality.

In-tree donors: `Theory/Adjunction.v:130`, `Adjunction/Hom.v:72`,
`Construction/Enriched.v:111,145`, `Construction/Enriched/Two.v:165,183`,
`Instance/Proset.v:33`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 4.39 and display (4.40)
      (printed p. 131); `≈` on morphisms, never `=`
- [ ] The definition is over an arbitrary monoidal base with naturality stated,
      not assumed away
- [ ] The thin-base collapse to the two-inequality form is proved
- [ ] The skeletal upgrade to an equality of hom-objects is proved
- [ ] Both reconciliations — with `Adjunction_Hom` at the base of sets, and with
      Galois connections at the base of truth values — are biconditionals
- [ ] Composition of V-adjunctions is proved
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the class, the two collapses and both
      reconciliations
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated where the enriched development is
      described

## Verification

```
coqc -R . Category Construction/Enriched/Adjunction.v
rg -n 'adjunc' Construction/Enriched/ | head -20
```
then, in `coqtop -R . Category`:
```
Print Assumptions EnrichedAdjunction.
Print Assumptions enriched_adjunction_thin.
Print Assumptions enriched_adjunction_skeletal_eq.
Print Assumptions enriched_adjunction_Sets_is_Adjunction_Hom.
Print Assumptions enriched_adjunction_Bool_is_galois.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist:
naturality is a field, not a derived convenience; both reconciliations are proved
in both directions; the skeletal statement really concludes an equality.

## Dependencies

Depends on: #799 (the quantale class and its skeletality predicate).
Depends on: #380 (Galois connections are adjunctions between preorders — the
base-of-truth-values case this generalises).
Depends on: #771 (symmetric monoidal preorders, the general thin base).

<!-- catalog: {"ids":["7sketches:4.3.3:remark4.39"],"deps":["#799","#380","#771"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: The collage of a V-profunctor, and the collage inclusions"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.3:def4.42, 7sketches:4.3.3:example4.43, 7sketches:4.3.3:ex4.44]
deps_item_ids: [7sketches:4.2.2:def4.8]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.3.3 — Definition 4.42,
the collage of a V-profunctor: the V-category whose objects are the disjoint
union of the two object collections and whose hom-object is the source's hom on
one block, the target's on the other, the profunctor's value on one off-diagonal
block and the empty join on the other, together with the two collage inclusions
(printed pp. 131–132, PDF pp. 143–144); Example 4.43, the collage of a small cost
profunctor drawn as a weighted graph and tabulated (printed p. 132, PDF p. 144);
and Exercise 4.44, the collage of the cost profunctor of the earlier display
(printed p. 132, PDF p. 144). Items covered: `7sketches:4.3.3:def4.42`,
`7sketches:4.3.3:example4.43`, `7sketches:4.3.3:ex4.44`.

## Background

The collage (also called the cograph or cylinder) of a profunctor glues the two
categories into one, with the profunctor supplying the arrows that run from the
first to the second and nothing running back
([nLab: collage](https://ncatlab.org/nlab/show/collage),
[nLab: cograph of a functor](https://ncatlab.org/nlab/show/cograph+of+a+functor)).
Over the truth-value base this turns a bridge picture into a single preorder;
over the cost base, two metric spaces joined by one-way bridges into a single
Lawvere metric space
([nLab: Lawvere metric space](https://ncatlab.org/nlab/show/Lawvere+metric+space)).

## Current state in the library

The construction is absent, and the one occurrence of its name is a disclaimer.

- `Construction/Comma.v:248–254` defines `Cocomma` as the pointwise opposite of a
  comma category, and its own comment at `:253` says explicitly that this is not
  the colimit-side dual — the collage — which it describes as a genuinely
  different construction that the file does not build. Searches for *cograph* and
  *cylinder* return nothing.
- The degenerate case exists: `Construction/Coproduct.v:35` builds the coproduct
  category with objects the sum of the two object types and cross-summand
  hom-types empty, which is exactly the collage of the bottom profunctor. It has
  no profunctor parameter and no inclusions with a non-trivial cross block.
- The one-sided case at the base of sets is a filed obligation elsewhere: #587
  builds the category obtained by adjoining a single object whose incoming
  hom-sets are the values of a set-valued functor, i.e. the collage of a
  profunctor out of the terminal category.
- No V-profunctor exists to take the collage of (see the §4.2.2 Definition 4.8
  issue), and the empty join that the definition puts in the reverse block has no
  in-tree home, since there is no quantale.
- The concrete instances are unavailable: there is no cost base, so neither
  Example 4.43's tabulation nor Exercise 4.44's graph can be written down.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor/Collage.v`.

1. Define the collage of a V-profunctor: objects the sum of the two object types;
   hom-object by the four-way case split of the definition, with the empty join in
   the reverse block. Prove it is a V-category — the identity element on each
   block comes from that block's own identity, and each of the composition cases
   is either a composition of one of the two categories, an action of the
   profunctor, or absorbed by the empty join.
2. Define the two collage inclusions and prove each is a fully faithful V-functor
   (hom-objects are preserved on the nose).
3. Prove the two structural facts a reader expects and the chapter uses
   implicitly: the collage of the bottom profunctor is the coproduct V-category
   (which reconciles the construction with `Construction/Coproduct.v`), and the
   hom-object from the second block to the first is the bottom element, so no
   arrow runs backwards.
4. Prove the universal property, so that *collage* is more than a formula: a
   V-functor out of the collage is exactly a pair of V-functors out of the two
   blocks together with a compatible family of morphisms out of the profunctor's
   values. Record the relationship with #587's one-sided construction — that
   issue's category is this one applied to a profunctor out of the unit
   V-category.
5. Discharge Example 4.43 and Exercise 4.44 over the cost base as decidable
   `Example`s: build the two small spaces and the bridges, compute the collage
   distance table, and prove the reverse block is infinite. Record in the header
   that the printed table of Example 4.43 shows finite entries in that block,
   which contradicts the definition's own clause, and that the formalisation
   follows the definition.

In-tree donors: `Construction/Coproduct.v:35`, `Construction/Comma.v:248–254`
(the disclaimer that motivates a new file), `Construction/Enriched.v:111`,
`Instance/FinSet/Topos.v` (the `eq_refl` example style), and #587's one-sided
collage.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Definition 4.42, Example 4.43 and
      Exercise 4.44 (printed pp. 131–132); `≈` on morphisms, never `=`
- [ ] The collage is a V-category over an arbitrary quantale, with the empty join
      in the reverse block
- [ ] Both inclusions are constructed and proved fully faithful
- [ ] The degenerate case is proved to be the coproduct V-category
- [ ] The universal property is proved, and its relationship to #587's one-sided
      construction is recorded
- [ ] Example 4.43 and Exercise 4.44 are computed, and the header records the
      discrepancy in the book's printed table for the reverse block
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the carrier
      axioms disclosed by the cost base
- [ ] `Print Assumptions` closed for the collage, the inclusions and the universal
      property
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the collage is the construction
      `Construction/Comma.v:253` explicitly declines to build

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor/Collage.v
rg -n 'collage' Construction/ Theory/ | head -20
```
then, in `coqtop -R . Category`:
```
Print Assumptions Collage.
Print Assumptions collage_incl_left.
Print Assumptions collage_incl_right.
Print Assumptions collage_reverse_block_bottom.
Print Assumptions collage_of_bottom_is_coproduct.
Print Assumptions collage_ump.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
reverse block is the empty join and not a copy of anything; the inclusions
preserve hom-objects on the nose; the universal property is proved, not asserted.

## Dependencies

Depends on: 7sketches:4.2.2:def4.8 (V-profunctors, whose collage this is).
Depends on: #799 (the quantale class, supplying the empty join).
Depends on: #587 (the one-sided collage at the base of sets, which this
generalises).
Depends on: #787 (Lawvere metric spaces, in which the two instances live).

<!-- catalog: {"ids":["7sketches:4.3.3:def4.42","7sketches:4.3.3:example4.43","7sketches:4.3.3:ex4.44"],"deps":["7sketches:4.2.2:def4.8","#799","#587","#787"]} -->

---8<---

```yaml
title: "Seven Sketches 4.3: Profunctors as a bicategory — the non-skeletal base by iso-classes or weak composition"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.3.2:remark4.33]
deps_item_ids: [7sketches:4.3.2:thm4.23]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.3.2 Remark 4.33 — the two
standard ways to accommodate a base whose underlying preorder is not skeletal:
take isomorphism classes of profunctors as the morphisms, as the book later does
for cospans, or relax the notion of category so that composition is unital and
associative only up to isomorphism, i.e. pass to bicategories. Printed pp. 129–130;
PDF pp. 141–142. Item covered: `7sketches:4.3.2:remark4.33`.

## Background

Profunctor composition is unital and associative only up to coherent isomorphism,
so profunctors naturally form a bicategory rather than a category; quotienting the
hom-collections by isomorphism recovers a strict one
([nLab: Prof](https://ncatlab.org/nlab/show/Prof),
[nLab: bicategory](https://ncatlab.org/nlab/show/bicategory),
[Wikipedia: Bicategory](https://en.wikipedia.org/wiki/Bicategory)).

## Current state in the library

Both devices exist in general form, and neither is applied to profunctors.

- The laws are already available in the weak form the remark describes:
  `Construction/Profunctor/Laws.v:236` (`prof_unit_left_iso`), `:395`
  (`prof_unit_right_iso`) and `:722` (`prof_assoc_iso`) give unitality and
  associativity of profunctor composition as natural isomorphisms — but they are
  deliberately left unpackaged: `Construction/Profunctor/Laws.v:43–44` states that
  assembling them into a bicategory instance is deferred, and
  `Theory/Profunctor.v:31–38` explains that no single category of all profunctors
  is formed, on a universe-size ground.
- The target class exists: `Theory/Bicategory.v:204` — `Class Bicategory` with
  `hcompose`, `hunit_left`, `hunit_right`, `hassoc` as invertible 2-cells,
  constrained by triangle and pentagon. It carries more coherence data than the
  remark asks for. Existing instances are `Theory/Bicategory/OneObject.v`,
  `Theory/Bicategory/Lax.v` and `Instance/Cat/Bicategory.v`; none concerns
  profunctors.
- The iso-class device exists at the remark's own comparison point:
  `Construction/Cospan/Category.v:560` — `Program Definition CospanCat : Category`
  whose hom-setoid identifies cospans up to isomorphism of apexes, with the file
  header at `:35–44` describing exactly this manoeuvre. The generic hom-congruence
  quotient `Construction/Quotient.v:254` is likewise never applied to profunctors.
- Nothing about a base of any kind: with no quantale in the tree, "skeletal versus
  non-skeletal base" has no formal content at all.

## Work to be done

Suggested module: `Construction/Profunctor/Bicategory.v`, with the enriched case
in `Construction/Enriched/Profunctor/Bicategory.v`.

1. Discharge the deferral recorded at `Construction/Profunctor/Laws.v:43–44`:
   assemble the existing composition, unitors and associator into a `Bicategory`
   instance whose hom-categories are the functor categories of profunctors between
   a fixed pair. This requires the naturality of the three isomorphisms in the
   profunctor arguments and the triangle and pentagon coherence laws, which the
   current development does not state.
2. Prove the coherence obligations rather than assuming them; the pentagon is the
   one real piece of work and should go through the double-coend interchange
   `Theory/Coend/Fubini.v:449` that `prof_assoc_iso` already rests on.
3. State the remark's first device generically: given a bicategory whose 2-cells
   are all invertible, the quotient of each hom-category by isomorphism is a
   category. Instantiate it at the bicategory of step 1, obtaining the strict
   category of profunctors-up-to-isomorphism, and relate it to
   `Construction/Quotient.v:254`.
4. Apply both devices to the enriched case: over a non-skeletal quantale the
   V-profunctors of the §4.3.2 Theorem 4.23 issue form a bicategory, and taking
   isomorphism classes recovers a category; over a skeletal one, prove that the
   quotient is trivial, so the strict category of that issue and the quotient
   agree. This is what makes the remark a theorem rather than an aside.
5. Record in the header how the universe obstruction of
   `Theory/Profunctor.v:31–38` is handled — the bicategory is over a fixed pair of
   universe levels, or the construction is stated for a chosen small collection of
   categories — since that obstruction is the stated reason the packaging was
   avoided.

In-tree donors: `Construction/Profunctor/Laws.v:43,236,395,722`,
`Theory/Coend/Fubini.v:449`, `Theory/Bicategory.v:204`,
`Instance/Cat/Bicategory.v`, `Construction/Cospan/Category.v:35–44,560`,
`Construction/Quotient.v:254`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 4.33 (printed pp. 129–130); `≈`
      on morphisms, never `=`
- [ ] The bicategory instance for profunctors is assembled, discharging the
      deferral recorded at `Construction/Profunctor/Laws.v:43–44`
- [ ] Naturality of the unitors and associator in the profunctor arguments, and
      the triangle and pentagon laws, are proved
- [ ] The iso-class quotient is stated generically and instantiated at that
      bicategory
- [ ] Both devices are applied over a non-skeletal quantale, and the quotient is
      proved trivial over a skeletal one
- [ ] The universe treatment is disclosed in the header, answering
      `Theory/Profunctor.v:31–38`
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the bicategory instance, the coherence laws
      and the quotient
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the profunctor entry currently
      records the bicategory packaging as deferred

## Verification

```
coqc -R . Category Construction/Profunctor/Bicategory.v
rg -n 'deferred' Construction/Profunctor/Laws.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions Prof_Bicategory.
Print Assumptions prof_pentagon.
Print Assumptions prof_triangle.
Print Assumptions iso_class_quotient.
Print Assumptions ProfV_quotient_skeletal_trivial.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
pentagon is proved and not assumed; the quotient construction is generic rather
than bespoke to profunctors; the skeletal triviality statement is what connects
this issue to the strict category.

## Dependencies

Depends on: 7sketches:4.3.2:thm4.23 (the strict category over a skeletal base,
which the quotient must be shown to agree with).
Depends on: #799 (the quantale class, whose skeletality is the hypothesis being
removed).

<!-- catalog: {"ids":["7sketches:4.3.2:remark4.33"],"deps":["7sketches:4.3.2:thm4.23","#799"]} -->

---8<---

```yaml
title: "Seven Sketches 4.4: Transporting braiding and symmetry along an equivalence, and symmetric monoidal categories as those equivalent to strict ones"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.4.3:remark4.47]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.4.3 Remark 4.47 — the
promised complete replacement for the chapter's deliberately informal definition:
a symmetric monoidal category is a category equipped with an equivalence to the
underlying category of a symmetric strict monoidal one. Printed p. 137; PDF
p. 149. Item covered: `7sketches:4.4.3:remark4.47`.

## Background

Monoidal structure transports along an equivalence of categories, so being
equivalent to a strict monoidal category endows a category with a genuine
monoidal structure; combined with strictification this makes the
definition-by-equivalence agree with the axiomatic one
([nLab: monoidal category](https://ncatlab.org/nlab/show/monoidal+category),
[nLab: symmetric monoidal category](https://ncatlab.org/nlab/show/symmetric+monoidal+category)).

## Current state in the library

The monoidal half of the transport is proved; the symmetric half and the
comparison of the two definitions are missing.

- `Theory/Equivalence/Monoidal.v:928` —
  `Definition Transported_Monoidal : @Monoidal D`, built from the transported data
  plus the two coherence lemmas, in a section fixing an equivalence and a monoidal
  structure on the source; the tensor is the image of the tensor of the
  quasi-inverses and the unit is the image of the unit. The coherence obligations
  are genuinely discharged, e.g. `:870` — `Lemma Transported_triangle_identity`.
- No braiding or symmetry is transported: the file provides only
  `Transported_Monoidal`, and `Theory/Equivalence/` contains
  `Adjoint.v`, `Adjunction.v`, `Bundled.v`, `FullFaithful.v`, `Limit.v` and
  `Monoidal.v` — no braided or symmetric transport file.
- No converse: nothing states that a monoidal category admits an equivalence to a
  strict one. That is the obligation of #609, which builds the strict source as
  the free monoid on the objects; the *symmetric* version of that statement is
  filed nowhere.
- The library defines its structures axiomatically (`Structure/Monoidal.v:125`,
  `Structure/Monoidal/Braided.v:128`, `Structure/Monoidal/Symmetric.v:103`), so
  the definition-by-equivalence is never stated, let alone compared with them.

## Work to be done

Suggested module: `Theory/Equivalence/Braided.v` (or extend
`Theory/Equivalence/Monoidal.v`).

1. Transport a braiding along an equivalence: given an equivalence and a braided
   monoidal structure on the source, construct one on the target, with naturality
   and both hexagons proved. Follow the proof pattern of the existing monoidal
   transport, including its rectification of the counit so the zig-zag holds.
2. Transport symmetry: the involutivity condition, giving a symmetric monoidal
   structure on the target.
3. Define the book's alternative notion — a category equipped with an equivalence
   to a symmetric strict monoidal category — as a record, and prove it yields a
   `SymmetricMonoidal` structure by steps 1 and 2.
4. Prove the converse and conclude the comparison: every symmetric monoidal
   category admits such an equivalence, so the two definitions agree. The
   monoidal case of the converse is #609's theorem; this issue must supply the
   symmetric upgrade — the strict source of that construction carries a braiding,
   and the comparison functors respect it.
5. Record in the header that the library keeps the axiomatic definition as
   primary and this equivalence as a theorem about it, which is the opposite of
   the book's presentational choice.

In-tree donors: `Theory/Equivalence/Monoidal.v:870,928`,
`Structure/Monoidal/Braided.v:128`, `Structure/Monoidal/Symmetric.v:103`,
`Structure/Monoidal/Strict.v:52`, `Theory/Equivalence.v`, and #609's
strictification.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 4.47 (printed p. 137); `≈` on
      morphisms, never `=`
- [ ] The braiding transports along an equivalence, with naturality and both
      hexagons proved
- [ ] The symmetry transports, giving a `SymmetricMonoidal` structure on the
      target
- [ ] The definition-by-equivalence is stated as a record and proved to yield the
      axiomatic structure
- [ ] The converse is proved, so the two definitions are shown to agree rather
      than merely coexist
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the two transports and the comparison
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated where the equivalence-transport
      development is described

## Verification

```
coqc -R . Category Theory/Equivalence/Braided.v
rg -n 'Transported_(Braided|Symmetric)' Theory/Equivalence/
```
then, in `coqtop -R . Category`:
```
Print Assumptions Transported_Braided.
Print Assumptions Transported_Symmetric.
Print Assumptions symmetric_monoidal_iff_equivalent_to_strict.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: both
hexagons are proved for the transported braiding; the comparison is a
biconditional; the strict source used in the converse is symmetric strict, not
merely strict.

## Dependencies

Depends on: #609 (strictification — every monoidal category is monoidally
equivalent to a strict one, the monoidal case of the converse).
Depends on: #520 (coherence for symmetric monoidal categories, and the
free-standing symmetric strict class recorded on it).

<!-- catalog: {"ids":["7sketches:4.4.3:remark4.47"],"deps":["#609","#520"]} -->

---8<---

```yaml
title: "Seven Sketches 4.4: Enrichment over a thin base — identity and composition data determined by properties"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.4.4:remark4.53]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.4.4 Remark 4.53 — the
reconciliation of the chapter's categorified definition of an enriched category
with the earlier order-level one: when the base is a monoidal preorder, the
identity elements and composition morphisms need not be chosen, since between two
objects of a preorder there is at most one morphism, so it suffices that they
exist — which is exactly the two conditions the earlier definition imposes.
Printed p. 139; PDF p. 151. Item covered: `7sketches:4.4.4:remark4.53`.

## Background

Enrichment in a thin monoidal category turns the structure of an enriched category
into a property: the identity element becomes the assertion that the unit is below
each self-hom, and the composition morphism becomes the assertion that the tensor
of two consecutive homs is below the composite hom
([nLab: enriched category](https://ncatlab.org/nlab/show/enriched+category),
[nLab: thin category](https://ncatlab.org/nlab/show/thin+category)). This is the
standard illustration of categorification turning properties into structure.

## Current state in the library

The collapse is proved for exactly one base and never in general.

- `Construction/Enriched/Two.v:165` —
  `Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder`, with
  the mechanism visible at `:71` — `TwoPreorder_of_Enriched`, whose reflexivity
  field is obtained from the enriched identity element: the chosen identity
  morphism forces the self-hom to be the top element, i.e. degenerates into the
  property of reflexivity, and the enriched composition likewise degenerates into
  transitivity. The three enrichment laws hold automatically because the
  two-object base is thin (`Instance/Two/Monoidal.v:26`, `two_thin`).
- Nothing general: there is no notion of a monoidal preorder in the tree (that is
  the obligation of #771), and no lemma anywhere says that a thin base makes the
  enrichment data determined. `Construction/Enriched/` contains only `Compose.v`,
  `Fun.v`, `Natural.v`, `Sets.v` and `Two.v`.
- Consequently the general remark has no counterpart, and each further base — the
  cost base, the powerset base — would need its own bespoke round trip rather than
  inheriting one theorem.

## Work to be done

Suggested module: `Construction/Enriched/Thin.v`.

1. Define what it is for a monoidal base to be thin, reusing the thin-category
   vocabulary of #771 rather than introducing a second notion, and prove the two
   consequences the remark relies on: any two parallel morphisms of the base agree,
   so every diagram in it commutes.
2. Prove that over a thin base an enriched category is uniquely determined by its
   objects and hom-objects together with two *properties*: the unit is below each
   self-hom, and the tensor of two consecutive hom-objects is below the composite
   hom-object. State it as a biconditional between the enrichment class and the
   order-level data, with both round trips.
3. Derive the existing two-object case as a corollary, so that
   `Construction/Enriched/Two.v`'s round trip becomes an instance rather than a
   parallel development; keep its statement, but re-prove it through the general
   theorem so the tree does not carry two independent arguments.
4. Prove the same collapse one level up for enriched functors: over a thin base an
   enriched functor is an object assignment satisfying an inequality, recovering
   `EnrichedFunctor_Two_monotone` as an instance.
5. Record in the header the reading the remark supplies — that this is where
   properties become structure — and note which downstream developments consume
   it (the profunctor definition of §4.2.2 and the V-adjunctions of §4.3.3).

In-tree donors: `Construction/Enriched.v:111,145`,
`Construction/Enriched/Two.v:71,104,131,165,183`, `Instance/Two/Monoidal.v:26`,
`Instance/Proset.v:33`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Remark 4.53 (printed p. 139); `≈` on
      morphisms, never `=`
- [ ] Thinness is taken from the #771 vocabulary rather than redefined
- [ ] The collapse theorem is a biconditional with both round trips, for an
      arbitrary thin monoidal base
- [ ] The two-object case is re-derived as a corollary, and the existing bespoke
      round trip is not left as a second independent proof
- [ ] The functor-level collapse is proved and the existing monotone-map theorem
      recovered from it
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the collapse theorem, its functor-level
      analogue and the two corollaries
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated where the enriched development is
      described

## Verification

```
coqc -R . Category Construction/Enriched/Thin.v
coqc -R . Category Construction/Enriched/Two.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions thin_enrichment_iff.
Print Assumptions thin_enriched_functor_iff.
Print Assumptions Enriched_Two_preorder.
Print Assumptions EnrichedFunctor_Two_monotone.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
theorem quantifies over an arbitrary thin monoidal base, not over the two-object
one; both round trips are present; the existing two-object statements still hold
and are now corollaries.

## Dependencies

Depends on: #771 (symmetric monoidal preorders and the thin-category vocabulary).
Depends on: #785 (preorders are exactly Bool-categories — the instance this
theorem must reproduce).

<!-- catalog: {"ids":["7sketches:4.4.4:remark4.53"],"deps":["#771","#785"]} -->

---8<---

```yaml
title: "Seven Sketches 4.4: Interpreting a wiring diagram in an arbitrary symmetric monoidal category, with a worked set-valued example"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:4.4.3:ex4.50]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.4.3 Exercise 4.50 — a
three-box wiring diagram whose wires are typed by the integers and the booleans
and whose boxes are given functions; the diagram denotes a function out of the
product of its two input types, and the exercise evaluates that function at
several arguments. Printed p. 138; PDF p. 150. Item covered:
`7sketches:4.4.3:ex4.50`.

## Background

A symmetric monoidal category interprets string diagrams: boxes are morphisms,
side-by-side placement is the tensor, and wires crossing are the symmetry, so a
diagram denotes a morphism determined up to the coherence isomorphisms
([nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram),
[Wikipedia: String diagram](https://en.wikipedia.org/wiki/String_diagram)). At
the cartesian monoidal category of sets this is ordinary dataflow
([nLab: monoidal category](https://ncatlab.org/nlab/show/monoidal+category)).

## Current state in the library

Diagram semantics exists, but only into a target with strict, natural-number
indexed objects; the ambient structure the exercise needs exists but is not a
possible target.

- `Construction/PROP/Interp.v:1030` —
  `Theorem interp_sound {m n : nat} {s t : Term S m n} : TermEq S s t → interp s ≈ interp t`,
  where `interp` sends a free string-diagram term to a morphism of the target,
  taking sequential composition to composition and parallel composition to the
  tensor. But the section fixes the target to a PROP (`Interp.v:165–167`), and
  `Construction/PROP/Universal.v:145–149` likewise fixes a PROP together with a
  strict monoidal functor into it. The coloured interpreter has the same
  restriction.
- `Instance/Sets.v:283` — `Program Instance Sets_Product_Monoidal : @Monoidal Sets`
  with the singleton as unit and the product of setoids as tensor, acting
  pointwise on morphisms; and `Structure/Monoidal/Internal/Product.v:314` —
  `Definition CC_SymmetricMonoidal` upgrades any cartesian category with a
  terminal object to a symmetric monoidal one, so the ambient the exercise works
  in is available. But setoids are not natural numbers, so this category is not a
  PROP and the existing interpreter cannot be instantiated at it.
- No worked example: nothing in `Instance/` or `Test/` builds a multi-box
  composite in a concrete category and evaluates it.

## Work to be done

Suggested module: `Construction/PROP/Interp/Symmetric.v`, with the example in
`Test/WiringDiagramSets.v`.

1. Generalise the interpreter's target from a PROP to an arbitrary symmetric
   monoidal category together with an object assignment for wire labels: a free
   diagram term is sent to a morphism between the folded tensors of its two
   boundaries, with the folds supplied by the existing list-tensor machinery
   rather than a new recursion.
2. Prove soundness in that generality — equal terms denote equal morphisms — which
   is where the non-strict unitors and associator have to be threaded, and which
   is exactly what the current PROP restriction avoids. Record in the header that
   the strict case is recovered by taking the coherence isomorphisms to be
   identities, so the existing theorem becomes an instance rather than a rival.
3. Prove the universal property in the same generality: the interpretation is the
   unique strong symmetric monoidal functor out of the free PROP extending the
   valuation, generalising the existing strict statement.
4. Discharge Exercise 4.50 in the cartesian monoidal category of setoids: define
   the three boxes as concrete morphisms over the integers and the booleans, build
   the diagram term, and prove each of the exercise's seven requested values by
   computation, so the diagram is executed rather than described.
5. Record in the header the relationship to the order-level wiring diagrams of
   #776: there a diagram is a proof of an inequality, here it is a morphism, and
   the former is the thin case of the latter.

In-tree donors: `Construction/PROP/Interp.v:165,1030`,
`Construction/PROP/Universal.v:145`, `Construction/ColouredPROP/Universal.v:648`,
`Instance/Sets.v:283`, `Instance/Sets/Cartesian.v:32`,
`Structure/Monoidal/Internal/Product.v:314`,
`Theory/Multicategory/Representable.v` (the list-tensor folds).

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Exercise 4.50 (printed p. 138); `≈` on
      morphisms, never `=`
- [ ] The interpreter's target is an arbitrary symmetric monoidal category, and
      the existing PROP interpreter is recovered as the strict instance
- [ ] Soundness and the universal property are proved in that generality
- [ ] All seven values requested by the exercise are computed and proved
- [ ] The relationship to #776's order-level diagrams is recorded in the header
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the generalised interpreter, its soundness
      theorem and its universal property
- [ ] New files registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the PROP entry currently
      describes interpretation into a PROP only

## Verification

```
coqc -R . Category Construction/PROP/Interp/Symmetric.v
coqc -R . Category Test/WiringDiagramSets.v
rg -n '^Context' Construction/PROP/Interp/Symmetric.v
```
then, in `coqtop -R . Category`:
```
Print Assumptions sinterp.
Print Assumptions sinterp_sound.
Print Assumptions sinterp_unique.
Print Assumptions ex4_50_values.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
target really is an arbitrary symmetric monoidal category (the context line shows
no PROP); the coherence isomorphisms appear in the soundness proof; the seven
values are proved, not asserted.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:4.4.3:ex4.50"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 4.5: Consequences of compact closure — monoidal closedness, uniqueness of duals, and the double dual"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.5.1:prop4.60]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.5.1 Proposition 4.60 —
three consequences of compact closure: the category is monoidal closed, with the
internal hom given by the tensor of the dual with the target; any two duals of an
object are isomorphic; and every object is isomorphic to its double dual. Printed
p. 142; PDF p. 154. Item covered: `7sketches:4.5.1:prop4.60`.

## Background

In a compact closed category the dual object supplies an internal hom, so
compactness implies closedness, and duals are unique up to canonical isomorphism
because a dual is an adjoint in the delooping of the monoidal structure
([nLab: compact closed category](https://ncatlab.org/nlab/show/compact+closed+category),
[nLab: dual object](https://ncatlab.org/nlab/show/dual+object),
[nLab: monoidal closed category](https://ncatlab.org/nlab/show/monoidal+closed+category)).

## Current state in the library

The class exists and nothing whatsoever is derived from it; the pieces needed for
one of the three clauses are present but never connected.

- `Structure/Monoidal/CompactClosed.v:139` — `Class CompactClosed` over a
  symmetric monoidal base, with `dual : C -> C`, `cc_unit`, `cc_counit` and both
  snake laws written exactly as the book's two composites. Its only downstream
  use in the whole tree is `Structure/Monoidal/Collapse.v:192` (the no-cloning
  collapse): searching for `cc_unit`, `cc_counit`, `snake_left` or `snake_right`
  outside `Structure/Monoidal/CompactClosed.v` returns nothing else, so no
  consequence of compact closure is currently derived.
- For the uniqueness clause the ingredients are in place but never joined:
  `Theory/Bicategory/Adjunction.v:708` —
  `Theorem adjoint_unique {a b : bicat y x} (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) : a ≅[bicat y x] b`,
  proved through the mates correspondence; and
  `Theory/Bicategory/OneObject.v:56` — `Monoidal_OneObject_Bicategory`, the
  delooping in which the hom-category is the monoidal category itself
  definitionally, horizontal composition is the tensor and the associator is the
  monoidal one, so a dual of an object is precisely a right adjoint of it and the
  two adjunction triangles unfold to the two snake laws. No corollary performs
  that instantiation, and nothing mentions the `dual` field of the compact closed
  class.
- For closedness: `Structure/Monoidal/StarAutonomous.v:109` (`Class SymMonClosed`,
  with its transposition isomorphism at `:115`) and
  `Structure/Monoidal/Closed.v:46` (`Class ClosedMonoidal`) both *postulate* the
  internal hom as data. Nothing derives closedness from duals.
- For the double dual: the only occurrence is
  `Structure/Monoidal/StarAutonomous.v:269`, `star_double_dual`, which is a field
  of the star-autonomous class over the dualizing-object notion of dual —
  assumed, and about a different construction.

## Work to be done

Suggested module: `Structure/Monoidal/CompactClosed/Properties.v`.

1. Prove clause (1): define the internal hom of a compact closed category as the
   tensor of the dual of the source with the target, construct the transposition
   from the unit and counit by the book's route (pre-composing with the unit in
   one direction, post-composing with the counit in the other), prove the two
   round trips using the snake laws, and prove naturality in the remaining
   argument. Conclude a `SymMonClosed` instance, thereby giving that class its
   first instance in the tree.
2. Prove clause (2): instantiate `adjoint_unique` at the delooping to obtain that
   any two duals of an object are isomorphic. This requires a bridge lemma stating
   that a dual in the sense of the compact closed class is a bicategorical
   adjunction in the delooping and conversely; state that bridge as a named
   biconditional, since it is what makes the whole bicategorical development
   usable in the monoidal setting.
3. Prove clause (3): the double dual is isomorphic to the object, by exhibiting
   the object as a dual of the dual (swapping the roles of the unit and counit,
   which is where the symmetry of the base is used) and applying clause (2).
4. Record the corollary the chapter uses in passing: the dual assignment extends
   to a contravariant functor, with the action on morphisms defined by bending
   wires, and the double dual isomorphism is natural.
5. Note in the header the two notions of dual now in the tree — the compact closed
   one and the dualizing-object one of `Structure/Monoidal/StarAutonomous.v` — and
   state precisely how they differ, so a reader does not conflate
   `star_double_dual` with clause (3).

In-tree donors: `Structure/Monoidal/CompactClosed.v:139,303`,
`Theory/Bicategory/Adjunction.v:270–291,708`,
`Theory/Bicategory/OneObject.v:41–56`,
`Structure/Monoidal/StarAutonomous.v:109,115,269`,
`Structure/Monoidal/Closed.v:46`, `Structure/Monoidal/Collapse.v:192`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Proposition 4.60 (printed p. 142); `≈`
      on morphisms, never `=`
- [ ] Clause (1) is proved: a compact closed category is symmetric monoidal
      closed, with the internal hom built from the dual and the transposition
      proved natural — giving `SymMonClosed` its first in-tree instance
- [ ] The bridge lemma "a dual is a bicategorical adjunction in the delooping" is
      stated and proved in both directions
- [ ] Clause (2) is derived from `adjoint_unique` through that bridge, not
      re-proved
- [ ] Clause (3) is proved, and the use of the base's symmetry is isolated
- [ ] The dual is extended to a contravariant functor and the double-dual
      isomorphism proved natural
- [ ] The header distinguishes this notion of dual from the star-autonomous one
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for all three clauses and the bridge lemma
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the compact closed entry
      currently records no consequences at all

## Verification

```
coqc -R . Category Structure/Monoidal/CompactClosed/Properties.v
rg -n 'cc_unit|cc_counit|snake_left|snake_right' --glob '*.v' | grep -v 'CompactClosed.v'
```
then, in `coqtop -R . Category`:
```
Print Assumptions compact_closed_SymMonClosed.
Print Assumptions dual_iff_bicat_adjunction.
Print Assumptions dual_unique.
Print Assumptions double_dual_iso.
Print Assumptions dual_functor.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
internal hom is derived and not postulated; uniqueness of duals goes through the
existing bicategorical theorem rather than a fresh argument; the double dual is
about the compact closed notion of dual, not the star-autonomous one.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:4.5.1:prop4.60"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 4.5: Corel — corelations as a compact closed category, and the snake check at a three-element set"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.5.1:example4.61, 7sketches:4.5.1:ex4.62]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.5.1 — Example 4.61, the
category whose objects are finite sets and whose morphisms are equivalence
relations on the disjoint union of source and target, composed by transitive
closure and restriction, with its symmetric monoidal structure given by the empty
set and disjoint union and its compact closed structure making every object its
own dual (printed pp. 142–143, PDF pp. 154–155); and Exercise 4.62, which draws
the unit and counit at a three-element set and checks the snake equations,
observing that self-duality makes one check suffice (printed p. 143, PDF p. 155).
Items covered: `7sketches:4.5.1:example4.61`, `7sketches:4.5.1:ex4.62`.

## Background

A corelation between two finite sets is an equivalence relation on their disjoint
union — equivalently a jointly epic cospan — and such relations compose by
gluing; the resulting category is the canonical example of a hypergraph category,
in which every object carries a special commutative Frobenius structure and is
therefore its own dual
([nLab: corelation](https://ncatlab.org/nlab/show/corelation),
[nLab: hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category),
[nLab: compact closed category](https://ncatlab.org/nlab/show/compact+closed+category)).

## Current state in the library

The general theory is in tree in a stronger form than the book states, but it is
carried by cospans rather than by corelations, and the corelation category has no
instance at all.

- `Structure/Monoidal/CompactClosed.v:303` — `Program Instance
  Hypergraph_CompactClosed : @CompactClosed C S` with `dual := fun X => X`, the
  unit and counit built from the special commutative Frobenius structure, and both
  snake laws discharged by `hypergraph_snake_left` (`:241`) and
  `hypergraph_snake_right` (`:273`). So every hypergraph category is compact
  closed and self-dual — exactly the cup and cap the exercise draws — for every
  object, not merely a three-element one.
- `Construction/Cospan/HypergraphInstance.v:703` — `Cospan_Hypergraph` makes the
  cospan category a hypergraph category, over `Construction/Cospan/Hypergraph.v:1973`
  (`Cospan_Monoidal`, with the initial object as unit and the coproduct as tensor)
  and `Construction/Cospan/Symmetric.v:398` (`Cospan_SymmetricMonoidal`).
  `Instance/FinSet/Pushout.v:513` — `FinSet_HasPushouts` — makes that available
  over finite sets.
- The subject is the gap. `Construction/Cospan/Corelation.v:259` — `Program
  Definition CorelCat : Category` with morphisms the jointly-epic cospans — carries
  no monoidal, hypergraph or compact closed instance; searching for `CorelCat`
  outside its own file finds only prose.
- Worse, `CorelCat` is uninhabited in tree: it is parameterised by a
  `CorelComposable` instance and no such instance exists for any concrete
  category, as the file's own closing note (`Construction/Cospan/Corelation.v:306–324`)
  and `Instance/Sets/Pushout.v:41,221` both record as outstanding work. So the
  book's concrete category of corelations of finite sets is not a category in tree
  at all.
- The two presentations are never related: nothing identifies a corelation in the
  book's sense — an equivalence relation on the disjoint union — with a jointly
  epic cospan, even though `Instance/FinSet/Pushout.v` already computes connected
  components.
- The exercise's own observation is also missing: `snake_left` and `snake_right`
  are two independent fields of the compact closed class, proved by two separate
  calculations, and no lemma derives either from the other when the dual is the
  object itself. `Structure/Monoidal/Collapse.v:331,409,421` consume `snake_left`
  only.

## Work to be done

Suggested module: `Instance/FinSet/Corelation.v`, with the general lemma in
`Structure/Monoidal/CompactClosed.v`.

1. Supply the missing `CorelComposable` instance for finite sets, so that the
   corelation category exists concretely; this is the load-bearing step and is the
   reason the whole example is currently unavailable.
2. Prove the presentation lemma: a corelation between two finite sets in the
   book's sense is the same thing as a jointly epic cospan out of their coproduct,
   as a bijection of hom-setoids, with composition on one side matching
   transitive-closure-then-restrict on the other. Use the connected-components
   computation already present for pushouts of finite sets.
3. Transport the monoidal structure to the corelation category: the empty set as
   unit and disjoint union as tensor, symmetric, obtained from the cospan
   structure by the jointly-epic quotient rather than rebuilt.
4. Give the corelation category a hypergraph structure and hence, through
   `Hypergraph_CompactClosed`, a compact closed one with every object its own
   dual, the unit and counit being the relation whose classes are the two copies
   of each element.
5. Prove the general form of the exercise's observation: if the dual of an object
   is the object itself and the unit and counit are related by the symmetry, then
   one snake law implies the other. Site it next to the two existing lemmas, so
   the redundancy the exercise points out is recorded in the library rather than
   only in the book.
6. Discharge Exercise 4.62 concretely at a three-element set: exhibit the unit and
   the counit, and check the snake law by computation, citing step 5 for the other
   one.

In-tree donors: `Structure/Monoidal/CompactClosed.v:241,273,303`,
`Construction/Cospan/Corelation.v:259,306–324`,
`Construction/Cospan/HypergraphInstance.v:703`,
`Construction/Cospan/Hypergraph.v:1973`, `Construction/Cospan/Symmetric.v:398`,
`Construction/Cospan/Category.v:560`, `Instance/FinSet/Pushout.v:513`,
`Instance/Sets/Pushout.v:41,221`.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Example 4.61 and Exercise 4.62
      (printed pp. 142–143); `≈` on morphisms, never `=`
- [ ] A concrete `CorelComposable` instance exists, so `CorelCat` is inhabited in
      tree — closing the outstanding obligation recorded at
      `Construction/Cospan/Corelation.v:306–324` and `Instance/Sets/Pushout.v:41,221`
- [ ] The equivalence-relation and jointly-epic-cospan presentations are proved to
      agree, composition included
- [ ] The corelation category is symmetric monoidal with the empty set as unit and
      disjoint union as tensor, obtained by transport rather than rebuilt
- [ ] It is compact closed with every object self-dual, through the existing
      hypergraph instance
- [ ] The general "self-duality makes one snake law imply the other" lemma is
      proved and sited with the existing snake lemmas
- [ ] Exercise 4.62 is discharged at a three-element set by computation
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the composability instance, the presentation
      bijection, the compact closed instance and the snake-redundancy lemma
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: the cospan/corelation entry
      currently describes `CorelCat` without a witness

## Verification

```
coqc -R . Category Instance/FinSet/Corelation.v
rg -n 'CorelComposable' --glob '*.v'
```
then, in `coqtop -R . Category`:
```
Print Assumptions FinSet_CorelComposable.
Print Assumptions corelation_is_equivalence_relation.
Print Assumptions Corel_SymmetricMonoidal.
Print Assumptions Corel_CompactClosed.
Print Assumptions self_dual_snake_left_implies_right.
Print Assumptions ex4_62_snake.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
composability instance is concrete, not another parameter; the presentation
lemma covers composition and not merely the hom-sets; the snake redundancy is a
lemma, not a comment.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:4.5.1:example4.61","7sketches:4.5.1:ex4.62"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 4.5: Prof_V is compact closed — the product of V-categories as tensor, and the opposite as dual"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:4.5.2:thm4.63, 7sketches:4.5.2:ex4.64, 7sketches:4.5.2:ex4.65, 7sketches:4.5.2:ex4.66]
deps_item_ids: [7sketches:4.3.2:thm4.23]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §4.5.2 — Theorem 4.63, that
over a skeletal quantale the category of V-categories and V-profunctors is
compact closed, with the tensor given by the product of V-categories on objects
and by the tensor of values on morphisms, the unit given by the one-object
V-category whose hom-object is the base's unit, and the dual of a V-category
given by its opposite, with unit and counit both given by the hom-object
assignment (printed p. 144, PDF p. 156; the proof is only sketched, in unnumbered
run-in paragraphs continuing to printed p. 145, PDF p. 157); Exercise 4.64, the
reading of that tensor at the Boolean base as a combination of resources
(printed p. 144, PDF p. 156); Exercise 4.65, the two unitor profunctors (printed
p. 144, PDF p. 156); and Exercise 4.66, the check that the proposed unit and
counit satisfy the snake equations, which is what completes the theorem (printed
p. 145, PDF p. 157). Items covered: `7sketches:4.5.2:thm4.63`,
`7sketches:4.5.2:ex4.64`, `7sketches:4.5.2:ex4.65`, `7sketches:4.5.2:ex4.66`.

## Background

The bicategory of profunctors is compact closed with the opposite category as
dual and the hom-profunctor as unit and counit, which is the abstract reason
design diagrams may be bent and fed back
([nLab: Prof](https://ncatlab.org/nlab/show/Prof),
[nLab: compact closed category](https://ncatlab.org/nlab/show/compact+closed+category),
[nLab: tensor product of enriched categories](https://ncatlab.org/nlab/show/tensor+product+of+enriched+categories)).

## Current state in the library

Nothing of the theorem exists, and its subject does not either.

- There is no category of V-profunctors to equip (the §4.3.2 Theorem 4.23 issue),
  and no V-profunctor at all: `Theory/Profunctor.v:122` fixes the base to `Sets`,
  and `Theory/Profunctor.v:164` records that even there the collection of
  profunctors is only a setoid handle rather than a registered category.
- Profunctors carry no monoidal product of any kind: searching for a tensor on
  profunctors returns nothing. `Construction/Profunctor/Laws.v:236,395` are a
  near-miss to be avoided — those are the unitors of profunctor *composition*, the
  content of the §4.3.2 Theorem 4.23 issue, not the unitors of a monoidal product,
  which is what Exercise 4.65 asks for.
- The proposed dual does not exist: there is no opposite of a V-category
  (`Construction/Opposite.v` is for ordinary categories), and no product or unit
  V-category — those are the obligations of #795 and #796.
- The proposed unit and counit have the shape of the hom-object assignment, which
  in the `Sets` case is `Theory/Profunctor.v:132`'s `Id_Profunctor := Hom C`, but
  nothing anywhere states a snake identity for it against any dual.
- The only compact closed instance in the whole tree is
  `Structure/Monoidal/CompactClosed.v:303` (`Hypergraph_CompactClosed`), which is
  about cospan-like categories and has no bearing here. The class itself
  (`:139`) is the target to instantiate.

## Work to be done

Suggested module: `Construction/Enriched/Profunctor/CompactClosed.v`.

1. Define the tensor on the category of V-profunctors: on objects the product of
   V-categories of #796; on morphisms the profunctor whose value at a pair of
   pairs is the tensor of the two values. Prove it is a profunctor and that the
   assignment is a bifunctor on that category — the interchange law is where the
   symmetry of the base is used.
2. Define the monoidal unit as the one-object V-category whose hom-object is the
   base's unit, and discharge Exercise 4.65 by constructing the two unitor
   profunctors and proving them mutually inverse in that category. Keep them
   clearly distinct in naming from the unitors of profunctor composition, which
   already exist for the `Sets` case and are a different structure.
3. Prove the associator and the symmetry, and the triangle and pentagon coherence
   laws, so the result is a `SymmetricMonoidal` instance rather than a bare
   tensor.
4. Define the dual as the opposite V-category of #795, with unit and counit both
   given by the hom-object assignment as the book proposes, and discharge
   Exercise 4.66: prove both snake laws, concluding a `CompactClosed` instance —
   the first in the tree that is not the hypergraph one.
5. Discharge Exercise 4.64 as a statement rather than a paraphrase: at the Boolean
   base, the tensor is the product preorder and the tensor of two feasibility
   relations is the relation that holds exactly when both components do, proved as
   two lemmas about the specialised structure.
6. Record the payoff in the header: this instance is what licenses the co-design
   diagrams of §4.1 to be interpreted with feedback and bent wires, and it is the
   semantic target of the co-design issue.

In-tree donors: `Structure/Monoidal/CompactClosed.v:139`,
`Structure/Monoidal/Symmetric.v:103`, `Construction/Product.v:95`,
`Instance/One.v:25,54`, `Instance/Cat/Cartesian.v:39`,
`Construction/Profunctor/Laws.v:236,395,722` (the composition-side laws, to be
kept distinct), and the enriched product, enriched opposite and profunctor-category
issues below.

## Definition of Done

- [ ] Statement fidelity to Seven Sketches Theorem 4.63 and Exercises 4.64, 4.65
      and 4.66 (printed pp. 144–145); `≈` on morphisms, never `=`
- [ ] The tensor is a bifunctor on the category of V-profunctors, with the
      interchange law proved and the use of the base's symmetry isolated
- [ ] The unit V-category is defined and both unitors are constructed and proved
      invertible (Exercise 4.65)
- [ ] The result is a `SymmetricMonoidal` instance with triangle and pentagon
      proved, not a bare tensor
- [ ] Both snake laws are proved for the opposite-as-dual (Exercise 4.66), giving
      a `CompactClosed` instance
- [ ] The naming keeps the monoidal unitors distinct from the composition unitors
      of `Construction/Profunctor/Laws.v`
- [ ] Exercise 4.64's Boolean reading is stated as two proved lemmas
- [ ] No `Admitted`, `admit` or `Axiom`
- [ ] `Print Assumptions` closed for the bifunctor, the symmetric monoidal
      instance and the compact closed instance
- [ ] New file registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1; the nix targets for Coq 8.19 and 8.20 build
- [ ] `make todo` reports no new hits
- [ ] CLAUDE.md "Key Files and Concepts" updated: this is flagship-level — the
      second compact closed instance in the tree and the semantics of the
      co-design development

## Verification

```
coqc -R . Category Construction/Enriched/Profunctor/CompactClosed.v
rg -n 'CompactClosed' --glob '*.v' | grep -v Hypergraph | head -20
```
then, in `coqtop -R . Category`:
```
Print Assumptions ProfV_tensor.
Print Assumptions ProfV_unit.
Print Assumptions ProfV_unitors.
Print Assumptions ProfV_SymmetricMonoidal.
Print Assumptions ProfV_CompactClosed.
Print Assumptions ProfV_Bool_tensor_is_product_preorder.
```
plus `make` and `nix build .#category-theory_8_20`. Reviewer checklist: the
monoidal product is the product of V-categories and not profunctor composition;
both snake laws are proved rather than assumed; the Boolean specialisation is
stated as lemmas, not prose.

## Dependencies

Depends on: 7sketches:4.3.2:thm4.23 (the category of V-categories and
V-profunctors being equipped here).
Depends on: #795 (the opposite of a V-category, which is the proposed dual).
Depends on: #796 (the tensor of two V-categories, which is the monoidal product).
Depends on: #799 (the quantale class and its skeletality predicate).

<!-- catalog: {"ids":["7sketches:4.5.2:thm4.63","7sketches:4.5.2:ex4.64","7sketches:4.5.2:ex4.65","7sketches:4.5.2:ex4.66"],"deps":["7sketches:4.3.2:thm4.23","#795","#796","#799"]} -->

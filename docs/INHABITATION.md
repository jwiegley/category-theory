# Flagship inhabitation

This document records, for the library's headline results, whether the
distinctive hypothesis of each result is satisfied by a concrete object
constructed inside the library, or whether the result stands as an
axiom-free *conditional* whose hypothesis no in-tree object yet meets.

Read this scope precisely.  Every result named below is proven, and (per
`docs/AXIOMS.md`) the audited ones are free of axioms.  The question here is
a different and complementary one: is the theorem *about* something the
library actually builds?  A theorem quantified over `Complete C` is a real
theorem whether or not any `Complete` category is exhibited; but a reader
calibrating how much the library demonstrates should know which results come
with a model and which do not.  Proving a theorem parametrically and
instantiating it in-tree are distinct achievements, and this table keeps
them apart.

Two cautions apply throughout.  First, "no in-tree witness" is not
"unsatisfiable": in most cases a model exists in ordinary mathematics and
simply has not been formalised here.  Second, a witness is not always
merely absent for want of effort — the library's universe discipline can
make a particular concrete instantiation impossible, as the cospan row
below shows, so the fact that a premise is inhabited in mathematics does not
guarantee it can be inhabited in this development.

## Witnessed results

Each result here is instantiated by a concrete object constructed in the
library, so the "Closed under the global context" report on it certifies a
result about something the library actually contains.

| Result | Distinctive premise | In-tree witness |
|--------|---------------------|-----------------|
| `classifier_classifies`, `relations_iso` | an `ElementaryTopos` | `FinSet_Topos` (`Instance/FinSet/Topos.v`) |
| `lambek`, `lambek_final` | an initial `F`-algebra / final `F`-coalgebra | `list A` (`Instance/Coq/Lists.v`), `nat` (`Instance/Coq/Nat.v`), streams (`Instance/Sets/Streams.v`) |
| `monadic_creates` | a `Monad` with its Eilenberg–Moore adjunction | `Id_Monad` (`Monad/Strong.v`) |
| `mate_iso` | a `Bicategory` | `Cat` as a bicategory (`Instance/Cat/Bicategory.v`) |
| `markov_all_deterministic_iff_cartesian` | a `Markov` category | `Markov_of_Cartesian` on any cartesian category (`Structure/Monoidal/Markov.v`) |
| `GAFT_from_initials` | a family of comma-initial objects | `InternalProductFunctor` (`Adjunction/GAFT/Examples.v`) |
| `Cospan_Hypergraph`, `spider_collapse`, `spider_frobenius` | `HasPushouts` on a base whose objects fit its homs | `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v`) over `FinSet`; see the cospan note below |
| `ZX_Cat` | the three `Phase` parameters | supplied by a user; see `docs/AXIOMS.md` |
| `LawvereTheory`, `CopyDiscard` supplies | — | `FinSet_Lawvere`, the Kleisli comonoid supplies |
| `skeleton_inclusion_is_equivalence`, `skeletons_are_isomorphic`, `skeletons_isomorphic_iff_equivalent` | a `Skeleton C` — a full subcategory with one chosen representative per isomorphism class, and its uniqueness | `Indiscrete_bool_Skeleton` (`Theory/Skeleton/Separation.v`), a category that is NOT skeletal whose skeleton is exhibited on the nose as `1` (`Indiscrete_bool_skeleton_is_One`); plus `Skeleton_of_Skeletal`, applied in tree at `FinSet` (`FinSet_Skeletal`, `FinSet_Skeleton`) and at any `Poset` (`Proset_Skeleton`), and available at `1`, `2` and `DiscreteCat A` from `One_Skeletal`, `Two_Skeletal` and `DiscreteCat_Skeletal` |

## Conditional results (no in-tree witness of the distinctive premise)

Each result here is proven, but its distinctive hypothesis has no inhabitant
anywhere in the library, so no concrete object exercises it.  These are
honest conditionals — "given such-and-such structure, the following holds" —
and nothing proven elsewhere secretly depends on their being inhabited.

| Result | Distinctive premise | Status of the premise |
|--------|---------------------|-----------------------|
| `GAFT` (solution-set form) | `Complete C` | no `Complete`/`Cocomplete` instance exists in-tree |
| `SAFT` | `SolutionSet` + `Cogenerator` + `SubobjectIndex` | none of the three is inhabited; `SAFT` is never applied |
| `RoundTrip_Equivalence` | a `SplitCleaving` of the required shape | never inhabited in that shape |
| `beck_monadicity` | `CreatesUSplitCoequalizers` composed from the engine | never assembled; `Id` is shown monadic by a direct proof (`Monad/Monadicity/Examples.v`), bypassing the coequalizer machinery |
| `image_mediator_epic` | an `Abelian` category | no `Abelian` instance; `CMon` cannot serve, since `Additive` requires additive inverses |
| the `Sheaf` development | a `Site` | no `Site` instance; the development is abstract throughout |
| `StarAutonomous` | a `SymMonClosed` category | doubly uninhabited — even the base `SymMonClosed` has no instance |
| `Regular`, `Distributive`, `Additive`, `localization_universal` | the corresponding class | abstract-by-design; no in-tree instance |
| `Category_SpanMonoid`, `Category_monoid_iso` (`Theory/Category/Monoid.v`) | `HomRigid C` | no in-tree category is given a `HomRigid` witness; `HomRigid_of_ObjUIP` + Hedberg would supply one for any category with decidable object equality, but the application is never made — and the necessity theorem `arrow_mul_respects_forces_UIP` shows the premise cannot be discharged uniformly |

### The cospan universe note

`Cospan_Hypergraph` and the spider results are witnessed exactly when a
`HasPushouts` instance exists on a base category whose object universe sits
at or below its hom universe.  The only `HasPushouts` instance in the tree
is `Sets_HasPushouts` (`Instance/Sets/Pushout.v`), and it cannot serve: a
cospan's hom carries an apex *object*, so `CospanCat` requires
objects ≤ homs, whereas `Sets` places its objects one universe *above* its
homs.  The failure is structural, not an annotation defect —
`CospanCat Sets HP` reports a universe inconsistency for any `HP`.

The category that does fit is skeletal `FinSet`, whose objects are natural
numbers and therefore sit below its homs.  `FinSet_HasPushouts`
(`Instance/FinSet/Pushout.v`) supplies the instance, and
`Cospan_Hypergraph` together with both spider results now instantiate over
`FinSet` — each reported "Closed under the global context" — which is why
they appear in the witnessed table above.

### The skeleton choice note

The `Skeleton` record is inhabited in-tree, but it is not dischargeable
uniformly: "every category has a skeleton" is equivalent to the axiom of
choice, a caveat `Theory/Equivalence.v` has recorded since long before this
development, and `Theory/Skeleton.v` accordingly never produces a
`Skeleton C` for an arbitrary `C`.  Two things keep the packaging honest.
The uniqueness clause is stated at the level of `Sub`'s objects rather than
their carriers, and that strengthening is necessary rather than convenient:
`skeleton0_skeletal_forces_UIP` shows the carrier-level weakening cannot
yield skeletality of the subcategory without entailing UIP for every type,
by a free-loop-space countermodel over `DiscreteCat`, while
`skeleton0_is_skeletal_carrier` shows the carrier statement itself still
holds.  And every witness supplied is a category whose representatives can
be named explicitly — `Indiscrete bool` chooses `true`, a skeletal category
chooses itself — so no witness in the table smuggles a choice principle.

## Maintaining this table

When a new headline result is added, record here whether its distinctive
premise is witnessed in-tree, and by what.  When a previously conditional
premise gains an instance, move its row up.  The intent is that a reader can
tell at a glance which results are demonstrated over a concrete model and
which are proven parametrically and await one.

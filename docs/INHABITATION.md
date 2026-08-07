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
| `lambek`, `lambek_final` | an initial `F`-algebra / final `F`-coalgebra | `list A` (`Instance/Coq/Lists.v`), streams (`Instance/Sets/Streams.v`) |
| `monadic_creates` | a `Monad` with its Eilenberg–Moore adjunction | `Id_Monad` (`Monad/Strong.v`) |
| `mate_iso` | a `Bicategory` | `Cat` as a bicategory (`Instance/Cat/Bicategory.v`) |
| `markov_all_deterministic_iff_cartesian` | a `Markov` category | `Markov_of_Cartesian` on any cartesian category (`Structure/Monoidal/Markov.v`) |
| `GAFT_from_initials` | a family of comma-initial objects | `InternalProductFunctor` (`Adjunction/GAFT/Examples.v`) |
| `GAFT` (solution-set form) | `Complete C` + `PreservesImageLimit U` + `SolutionSet U d` | all three at `U := Id : Sets ⟶ Sets` (`Adjunction/GAFT/Sets.v`); see the GAFT note below |
| `Cospan_Hypergraph`, `spider_collapse`, `spider_frobenius` | `HasPushouts` on a base whose objects fit its homs | `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v`) over `FinSet`; see the cospan note below |
| `ZX_Cat` | the three `Phase` parameters | supplied by a user; see `docs/AXIOMS.md` |
| `LawvereTheory`, `CopyDiscard` supplies | — | `FinSet_Lawvere`, the Kleisli comonoid supplies |

## Conditional results (no in-tree witness of the distinctive premise)

Each result here is proven, but the premise package named below is not met
as a whole by anything the library builds: at least one component has no
in-tree inhabitant, so no concrete object exercises the result.  (Where a
row's package names several premises, some may be witnessed individually;
what is missing is a simultaneous witness.)  These are honest conditionals —
"given such-and-such structure, the following holds" — and nothing proven
elsewhere secretly depends on their being inhabited.

| Result | Distinctive premise | Status of the premise |
|--------|---------------------|-----------------------|
| `SAFT` | `Complete C` + `PreservesImageLimit U` + `Cogenerator C` + `SubobjectIndex` + `SubobjectCover` | the first two are witnessed (`Sets_Complete`; `right_adjoint_PreservesImageLimit`), but no `Cogenerator`, `SubobjectIndex` or `SubobjectCover` exists in-tree, so `SAFT` is never applied.  `SAFT` takes no `SolutionSet` — it builds one itself, by `SAFT_solution_set` (`Adjunction/SAFT.v:252`) |
| `RoundTrip_Equivalence` | a `SplitCleaving` of the required shape | never inhabited in that shape |
| `beck_monadicity` | `CreatesUSplitCoequalizers` composed from the engine | never assembled; `Id` is shown monadic by a direct proof (`Monad/Monadicity/Examples.v`), bypassing the coequalizer machinery |
| `image_mediator_epic` | an `Abelian` category | no `Abelian` instance; `CMon` cannot serve, since `Additive` requires additive inverses |
| the `Sheaf` development | a `Site` | no `Site` instance; the development is abstract throughout |
| `StarAutonomous` | a `SymMonClosed` category | doubly uninhabited — even the base `SymMonClosed` has no instance |
| `Regular`, `Distributive`, `Additive`, `localization_universal` | the corresponding class | abstract-by-design; no in-tree instance |

### The GAFT note

`GAFT` (`Adjunction/GAFT.v:241`) takes three premises, and each now has an
in-tree supply:

* `Complete C` — `Sets_Complete` (`Instance/Sets/Complete.v`), the library's
  first `Complete` instance.
* `PreservesImageLimit U` — `right_adjoint_PreservesImageLimit`
  (`Construction/Comma/Limit.v:264`), which discharges it for *every* right
  adjoint; `adj_id` (`Instance/Adjoints.v:42`) and `Diagonal_Product C ⊣ ×(C)`
  (`Adjunction/Diagonal/Product.v`) are concrete adjunctions to feed it.  This
  bridge predates the `Complete` instance.
* `SolutionSet U d` — constructible, and constructed at `Id` as
  `Sets_Id_SolutionSet` (`Adjunction/GAFT/Sets.v`).

`GAFT_at_Sets_Id` (`Adjunction/GAFT/Sets.v`) assembles the three and runs the
theorem, so `GAFT` is applied in-tree and its row belongs above.  Read the
row with two qualifications, both disclosed in that file's header.  The
functor is `Id`, so the adjoint produced is `Id` again — proved, as
`GAFT_at_Sets_Id_is_Id` — and the demonstration is that the premises are
simultaneously satisfiable, not that a new adjunction was found.  And `GAFT`
is a `Qed`-opaque theorem whose frozen universe context pins both categories'
hom *and* proof universes to `Set`, so the application lands at `Sets@{Set _}`
— one instantiation of the polymorphic `Sets` at which `Sets_Complete` itself
is stated, and the smallest.

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

## Maintaining this table

When a new headline result is added, record here whether its distinctive
premise is witnessed in-tree, and by what.  When a previously conditional
premise gains an instance, move its row up.  The intent is that a reader can
tell at a glance which results are demonstrated over a concrete model and
which are proven parametrically and await one.

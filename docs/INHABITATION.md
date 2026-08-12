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
| `connected_deloop_equiv` | a connected groupoid (`IsGroupoid C` + `Connected C`); `connected_iff_deloop_equiv` needs only `IsGroupoid C`, since it CONCLUDES connectedness in one direction | `Bool_Wide := WideDeloop Bool_Xor_Grp bool` (`Structure/Groupoid/Connected.v`): two objects, eight arrows, vertex group Z/2, with the equivalence instantiated at both objects (`Bool_Wide_structure`, `Bool_Wide_structure_false`). The hypothesis is also shown necessary: `Two_Discrete_no_deloop_equivalence` refutes the conclusion for the disconnected two-object discrete groupoid |
| `conjugation_iso` (conjugation is a group isomorphism of vertex groups) | a groupoid with a NONABELIAN vertex group, without which the automorphism is the identity | `Deloop S3_Grp` (`Structure/Groupoid.v`) — the tree's first nonabelian group, added with this work; `S3_conjugation_not_identity` exhibits conjugation moving an element |
| `Inversion_iso` (a groupoid is isomorphic to its opposite, in `StrictCat`) | `IsGroupoid C` | `core_is_groupoid C` for every `C`; `Deloop Z3_Grp` for a case where the morphism map is not the identity (`Z3_inversion_not_identity`) |
| `Curry_Adjunction`, `Curry_Representable` | a cartesian closed category | `Sets` via `Sets_Closed` (`Instance/Sets/Cartesian/Closed.v`), instantiated with computing counit and a concrete transposed arrow in `Instance/Sets/Cartesian/Closed/Adjunction.v` |
| `pointed_monic_split`, `pointed_epic_split` | decidable image membership / decidable equality + an enumeration | `PointedBool`, `PointedThree` (`Instance/Sets/Pointed/Finite.v`), with the retraction and section computed by `reflexivity` |
| `Grp_injectivity_is_monic`, `Grp_Cartesian`, `Grp_Op` | a nontrivial group | `Z2` on `bool` (`Instance/Grp.v`), with `Monic_in_Grp_is_not_vacuous` and the kernel shown non-degenerate |
| `fixed_product_functor`, `fixed_product_transform` | a `Cartesian` category, and an `f : H ~> K` that is not invertible | `Grp` via `Grp_Cartesian`, instantiated as `Grp_fixed_product`/`Grp_fixed_product_transform` (`Functor/Product/Fixed.v`); the zero endomorphism `Grp_Z2_zero` of `Z/2` witnesses non-degeneracy — `Grp_Z2_zero_not_iso` and `Grp_fixed_product_transform_not_id` |
| `grp_not_epic_of_witness`, `grp_epic_iff_surjective` | a homomorphism together with an element proved outside its image. For the biconditional, `GrpImageStable` on top — but under `Epic f` that premise is EQUIVALENT to its own conclusion (`stability_is_the_conclusion`), so it is not an independent hypothesis | Two witnesses, deliberately not interchangeable. `grp_two_incl`, the inclusion of Z/2 as a factor of Z/2 x Z/2 (`Instance/Grp/Epi.v`), exhibits the missing element, the decidability of image membership, and the non-identity of both the action and the twist — but its image is NORMAL, so the equivariance step degenerates there and the whole image acts as the identity (`grp_two_incl_image_acts_trivially`). `grp_two_sym3`, Z/2 into the symmetric group of a three-letter setoid, supplies the NON-NORMAL image at which that step has content (`grp_two_sym3_image_acts_nontrivially`) |
| `Hausdorff_Subcategory`, `CompactHausdorff_Subcategory` | a Hausdorff / compact space | `Bool_Discrete_Hausdorff` (two points, with `TwoPoint_Indiscrete_not_Hausdorff` refuting the indiscrete twin) and `Point_Compact` (`Instance/Top.v`) |

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
| `pointed_part_equivalence` | the GLOBAL basepoint decidability `∀ Z, DecidablePt Z` | uninhabited: finiteness discharges only the per-object form (`PointedBool`, `PointedThree`); the global form is classically automatic but follows from no finite witness. The functor's full-and-faithfulness (`Part_to_Pointed_Full`/`_Faithful`) is unconditional |
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

## Maintaining this table

When a new headline result is added, record here whether its distinctive
premise is witnessed in-tree, and by what.  When a previously conditional
premise gains an instance, move its row up.  The intent is that a reader can
tell at a glance which results are demonstrated over a concrete model and
which are proven parametrically and await one.

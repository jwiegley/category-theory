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
| `Cospan_Hypergraph`, `spider_collapse`, `spider_frobenius` | `HasPushouts` on a base whose objects fit its homs | `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v`) over `FinSet`; see the cospan note below |
| `ZX_Cat` | the three `Phase` parameters | supplied by a user; see `docs/AXIOMS.md` |
| `LawvereTheory`, `CopyDiscard` supplies | — | `FinSet_Lawvere`, the Kleisli comonoid supplies |
| `connected_deloop_equiv`, `connected_vertex_moniso` | a connected groupoid (`IsGroupoid C` + `Connected C`); `connected_iff_deloop_equiv` needs only `IsGroupoid C`, since it CONCLUDES connectedness in one direction | `Bool_Wide := WideDeloop Bool_Xor_Grp bool` (`Structure/Groupoid/Connected.v`): two objects, eight arrows, vertex group Z/2, with the equivalence instantiated at both objects (`Bool_Wide_structure`, `Bool_Wide_structure_false`) and the vertex-group isomorphism at `Bool_Wide_vertex_moniso` (`Structure/Groupoid/Basepoint.v`). A second witness: `FundamentalGroupoid TwoPoint_Indiscrete` is connected, and `TwoPoint_Indiscrete_inclusion_equivalence` instantiates the structure theorem there. The hypothesis is also shown necessary: `Two_Discrete_no_deloop_equivalence` refutes the conclusion for the disconnected two-object discrete groupoid. For `connected_vertex_moniso` read the fundamental-groupoid note below: the premise is witnessed, the conclusion is not yet exercised |
| `FundamentalGroupoid`, `fundamental_groupoid_is_groupoid`, `fundamental_group_basepoint_independent`, `fundamental_group_inclusion_equivalence` | `PathConnected X` for the last two (the first two need only a `TopSpace`) | `TwoPoint_Indiscrete_pathconnected` (`Instance/Top/FundamentalGroupoid.v`), the indiscrete topology on two points, with the base-point isomorphism instantiated at `TwoPoint_Indiscrete_basepoint_iso`. The premise is shown to be a real restriction rather than a formality: `Bool_Discrete_pi_not_connected` refutes connectedness of π for the DISCRETE topology on the same setoid of points (`bool_carriers_agree` holds by `eq_refl`), so π is reading the topology and not the underlying set. See the fundamental-groupoid note below for what is still missing |
| `conjugation_iso` (conjugation is a group isomorphism of vertex groups) | a groupoid with a NONABELIAN vertex group, without which the automorphism is the identity | `Deloop S3_Grp` (`Structure/Groupoid.v`) — the tree's first nonabelian group, added with this work; `S3_conjugation_not_identity` exhibits conjugation moving an element |
| `Inversion_iso` (a groupoid is isomorphic to its opposite, in `StrictCat`) | `IsGroupoid C` | `core_is_groupoid C` for every `C`; `Deloop Z3_Grp` for a case where the morphism map is not the identity (`Z3_inversion_not_identity`) |
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
| `Regular`, `Distributive`, `Additive`, `localization_universal` | the corresponding class | abstract-by-design; no in-tree instance |

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

### The fundamental-groupoid note

Two limits of the π₁ development belong here rather than only in the file
headers, because the gap between them is exactly what this document exists to
keep visible.

**No space with a nontrivial fundamental group is exhibited.**  Both witnesses
above have trivial vertex groups at *every* base point, and both facts are
proved rather than assumed (`Bool_Discrete_loops_trivial`,
`TwoPoint_Indiscrete_loops_trivial`).  So
`fundamental_group_basepoint_independent` is witnessed in the strict sense
this document uses — its premise is met by an object the library builds, and
that premise is shown to be a genuine restriction — while the isomorphism it
produces happens to run between two trivial groups.  Reaching a nontrivial one
means building S¹ and computing π₁(S¹) ≅ ℤ, which needs covering-space theory;
nothing in the tree attempts it.  The witnessed pair is a contrast in
*connectedness* and in nothing else.

**A witnessed premise is not an exercised conclusion.**
`connected_vertex_moniso` is instantiated at `Bool_Wide`
(`Bool_Wide_vertex_moniso`), which satisfies both hypotheses; but `WideDeloop`
fixes the hom type uniformly, so the two vertex groups being compared are the
*same* monoid, and the resulting type is already inhabited by the identity
maps — `Bool_Wide_vertex_moniso_trivial` records exactly that, with no appeal
to connectedness or to the structure theorem.  The fundamental-groupoid
witness improves on this in one respect (the two vertex groups then have
different carriers, so the identity does not typecheck) and not in the other
(both groups are trivial).  A witness that made the conclusion informative
would need a connected groupoid whose vertex group both depends on the object
and is nonabelian; `S3_Grp` supplies such a group but nothing in the tree
spreads it over objects non-uniformly.

## Maintaining this table

When a new headline result is added, record here whether its distinctive
premise is witnessed in-tree, and by what.  When a previously conditional
premise gains an instance, move its row up.  The intent is that a reader can
tell at a glance which results are demonstrated over a concrete model and
which are proven parametrically and await one.

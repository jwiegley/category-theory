Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Elements.Kan.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Every set-valued functor is canonically a colimit of representables. *)

(* nLab: https://ncatlab.org/nlab/show/density+theorem
   nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma
   nLab: https://ncatlab.org/nlab/show/category+of+elements
   Wikipedia: https://en.wikipedia.org/wiki/Dense_functor

   BOOK LOCATIONS.  Recorded from the statement of issue #346: Mac Lane,
   "Categories for the Working Mathematician" (2nd ed.), III.7, Theorem 1
   and the dual remark, book pp. 76-77; Awodey, "Category Theory", 8.6,
   Proposition 8.10, for the presheaf orientation.  Those texts were not
   consulted while writing this file.  The locations are given so a
   reader can look the theorem up; nothing beyond the locations is
   reproduced here, and no claim is made about the wording or numbering
   at those places.

   THE STATEMENT.  For K : D -> Sets, index a diagram by the OPPOSITE of
   the category of elements of K, send the element (d, x) to the
   covariant representable [Hom d,-], and send an element-carrying
   morphism to the corresponding precomposition.  The Yoneda family
   whose value at (d, x) is the transformation g |-> fmap[K] g x is then
   a cocone with apex K, and it is COLIMITING in [D, Sets].

   THE VARIANCE IS FORCED, AND IT IS PINNED AS A TYPING NEGATIVE.  The
   assignment d |-> [Hom d,-] is CONTRAVARIANT (that is what
   [Curried_Hom D : D^op -> [D, Sets]] says), so the index category is
   [(Elements K)^op] and not [Elements K].  Probe negative 3 below shows
   that the covariant reading does not even typecheck: [Curried_Hom D]
   composed with [Elements_proj K] is rejected because [Elements_proj K]
   lands in D and not in D^op.

   A CORRECTION TO THE ISSUE'S "CURRENT STATE"
   -------------------------------------------

   The issue says no category-of-elements index exists in the tree.
   That is STALE.  [Construction/Elements.v] declares [Elements],
   [Elements_proj], [Elements_lift], [PElements] and [PElements_proj],
   and [Construction/Elements/Kan.v] builds cone machinery over
   [Elements_proj].  Both were landed by issue #345, and this file
   consumes them rather than rebuilding anything.

   Three absence measurements in the issue DO still hold, re-run here.
   [rg Colimit] over [Structure/Coend.v], [Structure/End.v] and
   [Instance/Sets/Coend.v] returns 0 in each, so there is still no
   in-tree lemma identifying a coend with a colimit.  No categorical
   density statement existed: the five files matching [densit|dense] are
   [Theory/Kan/Extension.v], [Instance/Top.v], [Instance/Field.v],
   [Instance/Grp/Epi.v] and [Instance/Met/Completion.v], all of them
   topological, metric or image density -- with one refinement an audit
   supplied: Theory/Kan/Extension.v's hits are all "codensity"/"codense",
   a CATEGORICAL notion, but they lie entirely in header prose and
   formalise nothing, which strengthens rather than weakens the absence
   claim.

   A THIRD absence claim of the issue is FALSE and is corrected here
   rather than repeated.  It says the [IsColimitCocone]/[IsAColimit] hits
   are exhausted by [Functor/Hom/Limit.v]'s hom-functor preservation
   results and prose in [Structure/Limit/Initial.v].  Fourteen files
   mention the two predicates.  Most are generic ([Adjunction/
   Continuity.v], [Structure/Limit/{Initial,Unique,Preservation}.v],
   [Structure/Coequalizer/Wide.v], [Theory/{Adamek,Equivalence/Limit}.v],
   [Functor/Hom/Limit.v]), and [Structure/Limit/Initial.v] carries a real
   [terminal_IsColimitCocone] rather than prose -- conditional on the
   INDEX category having a terminal object.  Concrete instantiations do
   exist: [Instance/Top/Forgetful.v]'s [bool_cocone_colimit], in [Sets],
   and [Instance/Ab/DirectedColimit.v]'s [ab_fg_colimit], in [Ab], with
   [Instance/Proset/{Limit,Order}.v] carrying the apex-only form in
   [Proset].  What is genuinely new is the AMBIENT: over that survey no
   [IsColimitCocone] in the tree has a FUNCTOR CATEGORY as its ambient
   category.  That is a statement about those fourteen files, not a
   survey of the tree.

   RELATION TO Construction/Elements/Kan.v, WHICH THE ISSUE DOES NOT NAME
   ---------------------------------------------------------------------

   That file is a genuine donor and is [Require]d here, but it is NOT the
   same theorem in the other variance, and the reason is worth stating
   because it looks as though it should be.

     - Kan.v relates [K ==> [Hom a,-]] -- maps INTO a representable --
       to cones over [Elements_proj K : Elements K -> D], a diagram in D.
     - This file is about [[Hom d,-] ==> K] -- maps OUT of a
       representable -- and a cocone over a diagram in [D, Sets].

   The two diagrams land in different categories (D versus [D, Sets]),
   so neither statement is the formal dual of the other and nothing of
   Kan.v's headline transfers.  [KanNat], [KanCone], [KanDelta] and
   [kan_coyoneda] are used NOWHERE below.

   What DID transfer, literally: [elements_same] (the morphism
   (d, x) ~> (d, y) whose underlying D-morphism is the identity,
   existing because [fmap[K] id x] is `≈` to x, hence to y).  It is
   consumed once, in [den_med_respects], for exactly the reason Kan.v
   records for [kan_leg_respects]: objects of [Elements K] are compared
   by LEIBNIZ equality, so two `≈`-equal elements over one object of D
   are two DIFFERENT objects, and a cocone assigns them two a priori
   unrelated legs -- whereas the transformation built out of them must
   have a component that RESPECTS `≈`.  That respectfulness is DERIVED
   from cocone coherence, not assumed.  From [Construction/Elements.v]
   itself this file consumes [elements_id_cond], [elements_comp_cond],
   [elements_respects_cond] and [Elements_lift]; the last is what turns
   cocone coherence into the naturality square of the mediator.

   THE ROUTE DECISION, AND WHY IT IS NOT A MATTER OF TASTE
   ------------------------------------------------------

   The issue asks for an explicit choice between proving the colimit
   form DIRECTLY and building a coend-is-a-colimit bridge and
   transporting [coyoneda_reduction] along it.  The direct route is
   taken, and the second route is BLOCKED rather than merely dearer.

     (1) The bridge does not exist and is not a lookup.  The 0-hit
         measurement above is a measurement of names; the shape argument
         is stronger.  A coend in this tree is a cowedge over an
         integrand [C^op * C -> Sets] ([Structure/Coend.v]), whose index
         is the product category, while a colimit is a cocone over a
         diagram indexed by [(Elements K)^op].  Relating them is a
         construction in its own right, not a repackaging.

     (2) Even with the bridge, the transport runs the wrong way round.
         [Theory/Coend/Yoneda.v] opens [Section Yoneda] with
         [Context (c : C)], so [YoI] and [coyoneda_reduction] both
         DEPEND on c and the reduction is a pointwise isomorphism of
         setoids at a fixed c.  Turning it into a statement in
         [D, Sets] needs naturality in c FIRST -- that is, the issue's
         own work item 3 would have to precede work item 1.

     (3) And that naturality has to be BUILT.  It needs
         [c |-> coend_obj (SetsCoend (YoI c))] to be a functor, hence an
         action of the coend on a map of integrands.  [Structure/Coend.v]
         declares no such action -- it mentions [Functor] only in its
         [Require] lines -- and [SetsCoend F : Coend F] is built at one
         fixed integrand ([Instance/Sets/Coend.v]).

         AN EARLIER DRAFT CONCLUDED FROM THOSE TWO FACTS THAT "the tree
         supplies no such action", AND THAT IS FALSE.  An audit found the
         action already built, for a different integrand family, in
         [Construction/Day.v]: [Day_map] (:292) with
         [Day : C ⟶ Sets] (:315) whose [fobj] is literally
         [fun c => coend_obj (SetsCoend (DayI F G c))] -- that IS
         "[c |-> coend_obj (SetsCoend (I c))] is a functor" -- together
         with [DFG_c] (:833), the action of the coend on a map of
         integrands induced by a pair of transformations, and the
         integrand-AGNOSTIC [day_theta_leg_cowedge] (:861), which takes
         ANY transform of integrands and whose proof uses only
         [coend_cowedge] and [naturality_sym].  Transcribing that pattern
         to [YoI] is perhaps sixty lines, not a lookup.

         So the honest word is DEARER, not BLOCKED, and the bad evidence
         is named as bad: the measurement offered was a name grep on the
         abstract class file rather than a survey of its CONSUMERS -- the
         very failure mode this tree records elsewhere.  Steps (1) and
         (2) are unaffected and do stand, and the direct route remains
         the right choice on cost; what changes is only the strength of
         the word.

   The direct route by contrast needs NO new index and NO new diagram:
   [DensityDiagram] is [Curried_Hom D] composed with
   [(Elements_proj K)^op], a plain [Definition] with no obligation, so
   all three functor laws are inherited.  The whole file contains no
   [Program] and therefore no obligations at all, which is what the
   [eq_refl] measurements below rest on.

   [Theory/Coend/Yoneda.v] IS nevertheless imported, for work item 3
   alone and not as a route; the measured cost of that import is SIX
   modules ([Structure/Wedge.v], [Structure/End.v], [Structure/Coend.v],
   [Instance/Sets/End.v], [Instance/Sets/Coend.v] and the file itself)
   on top of a 30-module base closure.

   WHAT IS DELIVERED, IN ORDER
   ---------------------------

   (1) [ElementsOp], [DensityDiagram] and the cocone: [yo_inj] (the
       Yoneda transformation at an element), [density_inj],
       [density_cocone_coherence] and [DensityCocone], whose apex is K
       and whose injections are the [yo_inj]s, both by [eq_refl].

   (2) The mediator, built from a competing cocone by EVALUATION AT THE
       IDENTITY: [den_med_component e] sends z : K e to the value at
       [id[e]] of the competing injection at the object (e, z).  Its
       respectfulness ([den_med_respects]) and its naturality
       ([den_med_naturality]) are both derived from cocone coherence --
       at [elements_same] and at [Elements_lift] respectively -- and
       nothing else.

   (3) [density : IsColimitCocone DensityCocone], Mac Lane's Theorem 1
       at CONE level, together with the derived apex-only
       [density_IsAColimit], the bundled [DensityColimit], the mediator
       accessors, the elementary covering statement
       [density_elements_covered] and the corollary
       [density_jointly_epic].

   (4) The presheaf dual as named artifacts: [PDensityDiagram],
       [PDensityCocone], [presheaf_density].

   (5) The connection to the coend form, four [eq_refl] identifications
       and one naturality theorem; see below.

   (6) A non-vacuity witness over the terminal category, in which the
       mediator COMPUTES.

   (7) A probe section: four negatives of THREE KINDS, each against
       positive controls, plus an instrument check.

   THE PRESHEAF DUAL IS A ZERO-CONTENT SPECIALIZATION, AND THAT IS
   MEASURED RATHER THAN ASSERTED
   ---------------------------------------------------------------

   The issue calls the dual a zero-content specialization.  Here it
   genuinely is, and the reason is a coincidence of definitions that had
   to be checked: [PElements P] is DEFINED in
   [Construction/Elements.v] as [(Elements P)^op], which is exactly this
   file's [ElementsOp P].  [presheaf_index] records the identity by
   [eq_refl].  Consequently [PDensityDiagram], [PDensityCocone] and
   [presheaf_density] are the general constants at [D := C^op] with no
   tactic, no transport and no coercion, and
   [pdensity_diagram_obj] records by [eq_refl] that the diagram's value
   at (c, x) is the contravariant representable [Hom -,c] -- because
   [Curried_CoHom C] is by definition [Curried_Hom C^op].

   In particular the gap [Construction/Elements.v:140] discloses --
   [PElements P ≅[Cat] (=(1) ↓ P)^op] is not proved, for want of a
   transport of a Cat-isomorphism along opposites -- DOES NOT BITE.  The
   dual never touches the comma presentation.

   What is NOT definitional is the other evident description of the
   diagram: [Curried_CoHom C ◯ PElements_proj P] agrees with
   [PDensityDiagram] on objects AND on arrows, both by [eq_refl]
   ([pdd_via_proj_obj], [pdd_via_proj_fmap]), but the two FUNCTOR RECORDS
   are not convertible, and the cause is located -- [PElements_proj] is a
   [Program Definition] whose functor-law fields are opaque obligations,
   where [(Elements_proj P)^op] rebuilds them from [Elements_proj]'s.
   That is probe negative 1.

   THE COEND CONNECTION, AT THE STRENGTH IT ACTUALLY REACHES
   ---------------------------------------------------------

   Work item 3 asks for a connection to [coyoneda_reduction] with a
   naturality-in-c upgrade.  What is delivered is the upgrade of the
   LEGS, which is what is stateable without coend functoriality, and it
   is delivered at [eq_refl]:

     - [coy_leg_is_density_inj]: the coend's cowedge leg
       [coy_leg F c x] at the pair (g, a) IS the density cocone's
       injection at (x, a), evaluated at c and applied to g.  The two
       constructions share their legs -- but read that precisely, since
       an earlier draft over-read it as "the SAME legs, on the nose":
       the Example is a VALUE equation at a fixed [a], and the two
       morphisms have DIFFERENT domains ([coy_leg F c x] is a
       [SetoidMorphism] out of [(x ~> c) * F x], while
       [transform[density_inj F (x;a)] c] is one out of [x ~> c]).  The
       coend leg is the UNCURRIED family of injections, not the same
       morphism.
     - [coy_leg_natural_in_apex]: for fixed x and a, the family
       c |-> coy_leg F c x (-, a) EXTENDS to a natural transformation
       [Hom x,-] ==> F, whose value at every c and g is the coend leg by
       [reflexivity].  [coy_leg_natural_witness] identifies the witness
       as [yo_inj F a], by [eq_refl].  This is the naturality in c that
       [Theory/Coend/Yoneda.v] cannot state, and the density cocone's
       injections are exactly it.
     - [coy_from_at] and [coy_to_from_is_covering]: the coend's inverse
       map is "insert at the identity", [b |-> ci c (id, b)], and
       composing it with [coy_to] gives the density injection at (c, b)
       applied to [id] -- which is [density_elements_covered]'s left-hand
       side.  So the coend's inverse and this file's mediator formula are
       the same move, and the identification is [eq_refl].

   NOT delivered here, and disclosed rather than approximated: the
   isomorphism [coyoneda_reduction] is NOT upgraded to an isomorphism in
   [C, Sets], because per (3) above that needs an action of the coend on
   its parameter which the tree does not have; and the coend apex is NOT
   identified with the colimit apex, so nothing below says that a coend
   IS a colimit.

   STRENGTHS, MEASURED STRICT-FIRST
   --------------------------------

   Everything was tried at [eq_refl] first.  What HOLDS strictly, each
   pinned as an [Example]: the diagram's object action
   ([density_diagram_obj]); the injections' values
   ([density_inj_at], [pdensity_inj]); the cocone's apex and its
   injections ([density_cocone_apex], [density_cocone_inj]); the
   extracted mediator against the named one
   ([density_med_is_den_med]); the presheaf index and the presheaf
   diagram's object action; the two [pdd_via_proj_*] actions; all four
   coend identifications; and both witness computations.

   What is only `≈`, with the diagnosis: [den_med_commutes] (equivalently
   [density_med_commutes]).  It is refuted at [eq_refl] as probe negative
   2, and the cause is structural rather than a packaging accident -- the
   mediator evaluates the competing cocone at the object
   (e, fmap[K] g x) of the index, while the right-hand side evaluates it
   at the DIFFERENT object j, and the two are brought together by cocone
   coherence at [Elements_lift], which is a `≈` fact.  So no rearrangement
   of the definitions makes this one strict.

   NON-VACUITY
   -----------

   Over the terminal category 1 with K the constant functor at the
   two-element setoid on [bool]:

     - the index is genuinely non-trivial -- the two objects (ttt, true)
       and (ttt, false) are distinct ([kbool_objects_differ]) and their
       injections are distinct morphisms of [1, Sets]
       ([kbool_injections_differ]), so the cocone is not a one-object
       degeneracy;
     - the diagram is CONSTANT at one representable
       ([kbool_diagram_constant], [eq_refl]) and there are no morphisms
       between the two elements, so the theorem here says exactly that
       the two-element set is the coproduct of two copies of the
       singleton -- a recognizable instance rather than a vacuous one;
     - the apex is NOT itself a representable
       ([kbool_not_representable]): [Hom ttt,-] is singleton-valued over
       1, and a natural isomorphism would collapse [true] onto [false].
       So the theorem is not the trivial "a representable is a colimit of
       one representable";
     - and the mediator COMPUTES.  [NegCocone] is a competing cocone,
       with the same apex but with the injections twisted by [negb], and
       [neg_med_true]/[neg_med_false] evaluate the produced mediator to
       [false] and [true] by [eq_refl], with [neg_med_not_id] proving it
       is not the identity transformation.  Nothing here is [Qed]-blocked
       on the value side; the competing cocone's coherence proof is
       opaque but the mediator's value does not pass through it.

   UNIVERSES (measured in the constraint blocks with [Set Printing
   Universes], and separately pinned by a formability negative -- not
   read off the binders)
   ---------------------------------------------------------------------

   Every constant below displays [D : Category@{u u0 u0}], hom and proof
   IDENTIFIED.  That is the donors' doing, not this file's: [Instance/
   Fun.v]'s [Fun] demands hom = proof in both its arguments, and
   [Sets@{u0 u1}] is a [Category@{u1 u0 u0}].  Nothing here adds to it.

   The interesting constraint is [u <= u0] -- D's OBJECT universe at or
   below its HOM universe -- and the block shows exactly where it enters:

     - [ElementsOp@{u u0 u1 u2 u3}] does NOT carry it.  Its block bounds
       both u and u0 below u2, the object universe of the elements
       category, and nothing forces u below u0.
     - [yo_inj@{u u0 u1 u2 u3}] does NOT carry it either.
     - [DensityDiagram@{u u0 u1 u2}] DOES.  So the pin enters at the
       DIAGRAM, not at the index and not at the Yoneda transformation.
     - [density_inj], [DensityCocone], [density], [density_IsAColimit],
       [DensityColimit], [density_med], [density_jointly_epic] and
       [presheaf_density] each carry [u <= u0] and [u <= u1].
       [PDensityDiagram] carries [u <= u0] but not [u <= u1].
       [den_med@{u u0 u1 u2 u3}] carries [u1 = u2] in addition.
     - [coy_leg_natural_in_apex@{u u0 u1 u2 u3 u4}] carries NEITHER;
       the coend-connection theorem is free of the pin.

   Probe negative 4 pins this at one universe setting: inside a section
   declaring [Constraint uh < uo], [ElementsOp] and [yo_inj] are both
   formable and [DensityDiagram] is REJECTED, with the error naming the
   declared levels.  The same restriction is what
   [Construction/Elements/Kan.v] records for [KanNat] and [KanCone] --
   there too a set of transformations, or of cones, is a family indexed
   by objects, so the objects must fit where hom-sets live.  It is stated
   rather than worked around and is NOT claimed unavoidable.

   The witness section does NOT pin [Set], which is the opposite of what
   a concrete [bool]-carrying witness usually costs and was checked
   rather than assumed: printing the universes of all FIFTEEN witness
   constants turns up no occurrence of [Set] at all (an earlier draft
   said fourteen; an audit recounted).  [bool : Set] only
   ever contributes [Set <= u], which is a bound and not an
   identification, and the carrier setoid is built with
   [Lib/Setoid.v]'s polymorphic [eq_Setoid] rather than left to instance
   resolution -- the idiom [Instance/Sets/Pullback.v] records, whose
   point is exactly that resolving [eq_equivalence] at an unannotated
   binder is what pins the level.

   TWO ENGINEERING FINDINGS, RECORDED BECAUSE THEY COST TIME
   ---------------------------------------------------------

   [Category.Functor.Opposite] opens [functor_scope], in which [_ ^op] is
   the OPPOSITE FUNCTOR.  Argument and ascription positions that bind
   [category_scope] are safe -- every [C^op] below sits in one -- but a
   bare type ascription is not: [(ttt : _1^op)] is read as an opposite
   FUNCTOR and fails with a message naming neither culprit.  The
   representable in [kbool_not_representable] is therefore spelled
   [@Curried_Hom _1 ttt].  This is the same family as the notation guard
   [Instance/Rng/Mod.v] records.

   Second: a [Transform] is [hom] of a functor category only by
   unfolding, so writing [f ∘ g] with f built by [Build_Transform] leaves
   [∘]'s category as an unresolved metavariable.  Every such definition
   below is given the type [_ ~{[D, Sets]}~> _] explicitly rather than
   [_ ⟹ _], which is the whole fix.

   PROBE ACCOUNTING
   ----------------

   FOUR negatives of THREE KINDS, kept lexically apart, each stripped
   once and its failure kind read off the message tail:

     1  CONVERSION   the two presheaf-diagram records
     2  CONVERSION   the mediator triangle at [eq_refl]
     3  TYPING       the covariant composite (the variance)
     4  FORMABILITY  the universe pin, at [Constraint uh < uo]

   against EIGHT positive commands ([ctrl_pdd_obj], [ctrl_pdd_fmap],
   [ctrl_diag_def], [ctrl_med_commutes] and FOUR [Check]s -- an earlier
   draft said seven and three, which an audit recounted), plus an
   instrument check ([Fail Fail Check density]) confirming that [Fail]
   reports an error when its command SUCCEEDS.

   RENAME SIMULATION, WITH ITS LIMIT STATED.  Of the ELEVEN constants the
   four negatives name, SIX are donors -- [Curried_CoHom],
   [PElements_proj], [Cocone], [cocone_inj], [Curried_Hom],
   [Elements_proj] -- and renaming any one of them breaks a control, 6/6.
   The other FIVE ([PDensityDiagram], [DensityDiagram], [ElementsOp],
   [density_med], [density_inj]) are declared in this file,
   and there a rename that touched the definitions but NOT the [Fail]
   bodies would leave the negative vacuously green: the controls are
   renamed in lockstep, so no in-file control can catch it.  That is a
   limit of keeping the probe in the target file, which this work's
   single-file scope imposes.  (An earlier draft counted TWELVE and put
   [density] among the file-local five; an audit corrected both --
   [density] is named by NO negative, only by the instrument check
   [Fail Fail Check density].  Test/ProbeDensity346.v guards it anyway,
   so the coverage claim is unaffected and the count was the error.)
   The tree's usual remedy is a separate
   [Test/Probe*.v], where the target's names are not renamed alongside.
   It is recorded rather than papered over.

   AXIOMS.  All 62 constants of this module report "Closed under the
   global context".  The count is exact rather than a floor: the file
   contains no [Program], no [Record]/[Class]/[Inductive] and no
   [Instance], so there are no obligations and no constructors for a name
   sweep to miss, and [Print Module] lists exactly these 62.  (The
   [.glob] shows 64, because two of the five [Fail] commands are NAMING
   commands and a [Fail Example] still records a [def] entry, while a
   [Fail Check] records none.)

   NOT DELIVERED
   -------------

     - no identification of the coend with the colimit, hence no
       upgrade of [coyoneda_reduction] itself to a natural isomorphism,
       for the reason given in the route discussion;
     - no pointwise-colimit lemma for functor categories, so nothing here
       says that this colimit is computed pointwise in [D, Sets] -- which
       is the step that would make the density theorem AT c literally the
       co-Yoneda reduction;
     - no density of the Yoneda embedding as a PROPERTY: no [Dense]
       predicate is declared, and no left Kan extension along
       [Curried_Hom] is formed, so no connection is made with
       [Theory/Kan/Extension.v] or [Structure/Limit/Kan/Pointwise.v];
     - no functoriality or naturality of the construction in K, and no
       uniqueness of the diagram or the cocone up to isomorphism;
     - no statement that [Elements_proj] is a discrete opfibration, and
       no comparison with [Construction/Grothendieck.v];
     - no [Cocomplete] hypothesis and no consequence of the form "a
       functor out of [D, Sets] preserving colimits is determined by its
       values on representables";
     - the presheaf dual is delivered as named artifacts, not as a
       separate development; nothing is stated in [StrictCat], and the
       colimit is a cocone-level fact plus its apex-only reading, with no
       separation between the two proved. *)

Section Density.

Context {D : Category}.
Context (K : D ⟶ Sets).

(** ** The index category and the diagram of representables *)

(* The index is the OPPOSITE of the category of elements: the assignment
   d |-> [Hom d,-] is contravariant, so a morphism (d, x) ~> (d', x') of
   [Elements K] must give a transformation running backwards. *)

Definition ElementsOp : Category := (Elements K)^op.

(* A pure assembly: the covariant Yoneda embedding of D composed with
   the opposite of the elements projection.  No obligation, so all three
   functor laws are inherited. *)

Definition DensityDiagram : ElementsOp ⟶ [D, Sets] :=
  Curried_Hom D ◯ (Elements_proj K)^op.

Example density_diagram_obj (d : D) (x : K d) :
  DensityDiagram ((d; x) : ElementsOp) = [Hom d,─] := eq_refl.

(** ** The Yoneda transformation at an element *)

(* For x an element of K d, the transformation [Hom d,-] ==> K whose
   component at e carries g : d ~> e to [fmap[K] g x].  Respectfulness is
   [elements_respects_cond] and both naturality orientations are
   [fmap_comp] read at an element. *)

Definition yo_component {d : D} (x : K d) (e : D) :
  @hom Sets ([Hom d,─] e) (K e) :=
  @Build_SetoidMorphism (d ~{D}~> e) _ (K e) _
    (fun g => fmap[K] g x)
    (fun u v H => elements_respects_cond K u v H).

Lemma yo_naturality {d : D} (x : K d) {e e' : D} (f : e ~> e') :
  fmap[K] f ∘ yo_component x e ≈ yo_component x e' ∘ fmap[[Hom d,─]] f.
Proof. intro g; symmetry; exact (@fmap_comp _ _ K _ _ _ f g x). Qed.

Lemma yo_naturality_sym {d : D} (x : K d) {e e' : D} (f : e ~> e') :
  yo_component x e' ∘ fmap[[Hom d,─]] f ≈ fmap[K] f ∘ yo_component x e.
Proof. intro g; exact (@fmap_comp _ _ K _ _ _ f g x). Qed.

Definition yo_inj {d : D} (x : K d) : [Hom d,─] ⟹ K :=
  @Build_Transform D Sets ([Hom d,─]) K
    (fun e => yo_component x e)
    (fun e e' f => yo_naturality x f)
    (fun e e' f => yo_naturality_sym x f).

(** ** The canonical cocone *)

Definition density_inj (j : ElementsOp) :
  @hom ([D, Sets]) (DensityDiagram j) K := yo_inj (`2 j).

Example density_inj_at (d : D) (x : K d) (e : D) (g : d ~> e) :
  transform[density_inj ((d; x) : ElementsOp)] e g = fmap[K] g x := eq_refl.

(* Cocone coherence.  For f : x ~> y in [Elements K] the diagram sends f
   to precomposition with its underlying D-morphism, so the condition
   reads [fmap[K] (g ∘ `1 f) (`2 x) ≈ fmap[K] g (`2 y)] at every e and
   g -- which is [elements_comp_cond] fed the carried witness `2 f. *)

Lemma density_cocone_coherence {x y : Elements K}
      (f : x ~{Elements K}~> y) :
  density_inj x ∘ @fmap _ _ DensityDiagram y x f ≈ density_inj y.
Proof.
  intros e g.
  exact (elements_comp_cond K g (`1 f) (`2 f) (reflexivity _)).
Qed.

Definition DensityCocone : Cocone DensityDiagram.
Proof.
  unshelve eapply Build_Cone.
  - exact K.
  - unshelve eapply Build_ACone.
    + exact (fun j => density_inj j).
    + intros x y f; exact (density_cocone_coherence f).
Defined.

Example density_cocone_apex : vertex_obj[DensityCocone] = K := eq_refl.

Example density_cocone_inj (j : ElementsOp) :
  cocone_inj DensityCocone j = density_inj j := eq_refl.

(** ** The mediating transformation out of K *)

Section Mediator.

Context (M : Cocone DensityDiagram).

(* Respectfulness in the ELEMENT argument, derived from cocone coherence
   at [elements_same] and not assumed.  Two `≈`-equal elements over one
   object of D are DIFFERENT objects of [Elements K] -- objects are
   compared by Leibniz equality -- so their injections are a priori
   unrelated; [elements_same] is the morphism between them whose
   underlying D-morphism is the identity. *)

Lemma den_med_respects {e : D} (z w : K e) (H : z ≈ w) :
  transform[cocone_inj M ((e; z) : ElementsOp)] e id
    ≈ transform[cocone_inj M ((e; w) : ElementsOp)] e id.
Proof.
  pose proof (cocone_inj_coherence M (elements_same K z w H) e id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  now rewrite id_left.
Qed.

(* Evaluation at the identity: z : K e goes to the value at [id[e]] of
   the competing injection at the object (e, z). *)

Definition den_med_component (e : D) :
  @hom Sets (K e) (vertex_obj[M] e) :=
  @Build_SetoidMorphism (K e) _ (vertex_obj[M] e) _
    (fun z => transform[cocone_inj M ((e; z) : ElementsOp)] e id)
    (fun z w H => den_med_respects z w H).

(* Naturality: one step of the competing injection's own naturality, then
   cocone coherence at the chosen lift [Elements_lift K z f], whose image
   under the projection is f itself definitionally. *)

Lemma den_med_naturality {e e' : D} (f : e ~> e') :
  fmap[vertex_obj[M]] f ∘ den_med_component e
    ≈ den_med_component e' ∘ fmap[K] f.
Proof.
  intro z; simpl.
  pose proof (naturality[cocone_inj M ((e; z) : ElementsOp)] e e' f id) as Hn.
  simpl in Hn.
  rewrite Hn.
  pose proof (cocone_inj_coherence M (Elements_lift K z f) e' id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  now rewrite id_left, id_right.
Qed.

Lemma den_med_naturality_sym {e e' : D} (f : e ~> e') :
  den_med_component e' ∘ fmap[K] f
    ≈ fmap[vertex_obj[M]] f ∘ den_med_component e.
Proof. symmetry; apply den_med_naturality. Qed.

Definition den_med : K ~{[D, Sets]}~> vertex_obj[M] :=
  @Build_Transform D Sets K (vertex_obj[M])
    (fun e => den_med_component e)
    (fun e e' f => den_med_naturality f)
    (fun e e' f => den_med_naturality_sym f).

Lemma den_med_commutes (j : ElementsOp) :
  den_med ∘ density_inj j ≈ cocone_inj M j.
Proof.
  destruct j as [d x].
  intros e g; simpl.
  pose proof (cocone_inj_coherence M (Elements_lift K x g) e id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  unfold op; now rewrite id_left.
Qed.

Lemma den_med_unique (v : K ~{[D, Sets]}~> vertex_obj[M]) :
  (∀ j : ElementsOp, v ∘ density_inj j ≈ cocone_inj M j) → den_med ≈ v.
Proof.
  intros Hv e z; simpl.
  rewrite <- (Hv ((e; z) : ElementsOp) e id).
  simpl.
  apply proper_morphism.
  apply elements_id_cond.
Qed.

End Mediator.

(** ** Mac Lane III.7 Theorem 1 *)

Definition density : IsColimitCocone DensityCocone.
Proof.
  intro M.
  unshelve refine {| unique_obj := den_med M |}.
  - exact (den_med_commutes M).
  - exact (den_med_unique M).
Defined.

(** ** Derived packagings and corollaries *)

Definition density_IsAColimit : IsAColimit DensityDiagram K :=
  colimitcocone_isacolimit density.

Definition DensityColimit : Colimit DensityDiagram :=
  limitcone_limit DensityCocone density.

Definition density_med (M : Cocone DensityDiagram) :
  K ~{[D, Sets]}~> vertex_obj[M] := unique_obj (density M).

Example density_med_is_den_med (M : Cocone DensityDiagram) :
  density_med M = den_med M := eq_refl.

Lemma density_med_commutes (M : Cocone DensityDiagram) (j : ElementsOp) :
  density_med M ∘ density_inj j ≈ cocone_inj M j.
Proof. exact (den_med_commutes M j). Qed.

Lemma density_med_uniq (M : Cocone DensityDiagram)
      (v : K ~{[D, Sets]}~> vertex_obj[M]) :
  (∀ j : ElementsOp, v ∘ density_inj j ≈ cocone_inj M j) →
  density_med M ≈ v.
Proof. exact (den_med_unique M v). Qed.

(* The elementary content: every element of K e is the value at [id[e]]
   of the injection at its own object of the index. *)

Lemma density_elements_covered {e : D} (z : K e) :
  transform[density_inj ((e; z) : ElementsOp)] e id ≈ z.
Proof. apply elements_id_cond. Qed.

(* The injections are jointly epic: K is generated by representables. *)

Lemma density_jointly_epic {G : [D, Sets]}
      (u v : K ~{[D, Sets]}~> G) :
  (∀ j : ElementsOp, u ∘ density_inj j ≈ v ∘ density_inj j) → u ≈ v.
Proof.
  intros H e z.
  transitivity (transform[u] e (fmap[K] id z)).
  - apply proper_morphism; symmetry; apply elements_id_cond.
  - rewrite (H ((e; z) : ElementsOp) e id).
    simpl; apply proper_morphism; apply elements_id_cond.
Qed.

End Density.

(** ** The presheaf dual (Mac Lane III.7, the dual remark; Awodey 8.6) *)

Section PresheafDensity.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* The index needs no construction: [PElements P] is DEFINED as
   [(Elements P)^op], which is [ElementsOp P] on the nose. *)

Example presheaf_index : ElementsOp P = PElements P := eq_refl.

Definition PDensityDiagram : PElements P ⟶ [C^op, Sets] := DensityDiagram P.

(* The value at (c, x) is the CONTRAVARIANT representable, because
   [Curried_CoHom C] is by definition [Curried_Hom C^op]. *)

Example pdensity_diagram_obj (c : C) (x : P c) :
  PDensityDiagram ((c; x) : PElements P) = [Hom ─,c] := eq_refl.

Definition PDensityCocone : Cocone PDensityDiagram := DensityCocone P.

Definition presheaf_density : IsColimitCocone PDensityCocone := density P.

Example pdensity_inj (c : C) (x : P c) (e : C) (g : e ~{C}~> c) :
  transform[cocone_inj PDensityCocone ((c; x) : PElements P)] e g
    = fmap[P] g x := eq_refl.

(* The other evident description of the diagram agrees on objects AND on
   arrows, both by [eq_refl]; the two functor RECORDS do not (probe
   negative 1), because [PElements_proj] is a [Program Definition] whose
   law fields are opaque obligations. *)

Example pdd_via_proj_obj (c : C) (x : P c) :
  PDensityDiagram ((c; x) : PElements P)
    = (Curried_CoHom C ◯ PElements_proj P) ((c; x) : PElements P) := eq_refl.

Example pdd_via_proj_fmap (x y : PElements P) (f : x ~{PElements P}~> y) :
  @fmap _ _ PDensityDiagram x y f
    = @fmap _ _ (Curried_CoHom C ◯ PElements_proj P) x y f := eq_refl.

End PresheafDensity.

(** ** The connection to the coend form of co-Yoneda *)

(* These two [Require]s are for this section alone.  They are NOT the
   route by which the theorem above is proved; see the header. *)

Require Import Category.Instance.Sets.Coend.
Require Import Category.Theory.Coend.Yoneda.

Section CoendConnection.

Context {C : Category}.
Context (F : C ⟶ Sets).

(* The coend's cowedge leg IS the density cocone's injection, on the
   nose: both send (g, a) to [fmap[F] g a]. *)

Example coy_leg_is_density_inj (c x : C) (g : x ~{C}~> c) (a : F x) :
  coy_leg F c x (g, a)
    = transform[density_inj F ((x; a) : ElementsOp F)] c g := eq_refl.

(* The naturality-in-c upgrade of the LEGS.  [Theory/Coend/Yoneda.v]
   fixes c as a section variable; an audit sharpened the attribution,
   since that variable IS generalised at [End Yoneda] and so does not by
   itself prevent the statement -- what does is that Yoneda.v imports
   neither [Category.Instance.Fun] nor
   [Category.Theory.Natural.Transformation], so it has no vocabulary for
   [[Hom x,-] ==> F].  The conclusion stands.  The family of
   coend legs at fixed (x, a) extends to a natural transformation out of
   the representable, and that transformation is the density cocone's
   injection. *)

Theorem coy_leg_natural_in_apex (x : C) (a : F x) :
  { tau : [Hom x,─] ~{[C, Sets]}~> F
  & ∀ (c : C) (g : x ~{C}~> c), transform[tau] c g = coy_leg F c x (g, a) }.
Proof. exists (yo_inj F a); intros c g; reflexivity. Defined.

Example coy_leg_natural_witness (x : C) (a : F x) :
  `1 (coy_leg_natural_in_apex x a) = yo_inj F a := eq_refl.

(* The coend's inverse map is "insert at the identity", and running it
   back through the mediator gives the density injection at (c, b)
   applied to [id] -- the left-hand side of [density_elements_covered].
   So the two constructions share their inverse formula as well. *)

Example coy_from_at (c : C) (b : F c) :
  coy_from F c b = ci (YoI F c) c (id, b) := eq_refl.

Example coy_to_from_is_covering (c : C) (b : F c) :
  coy_to F c (coy_from F c b)
    = transform[density_inj F ((c; b) : ElementsOp F)] c id := eq_refl.

End CoendConnection.

(** ** Non-vacuity *)

Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.

Section Witness.

(* The two-element setoid, and the constant functor at it over the
   terminal category.  Over 1 the representables are singleton-valued,
   so this K is provably not one of them. *)

Definition DensityBool : Sets :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Definition KBool : 1 ⟶ Sets := Diagonal _1 DensityBool.

Example kbool_obj : KBool ttt = DensityBool := eq_refl.

Definition et : ElementsOp KBool := (ttt; true).
Definition ef : ElementsOp KBool := (ttt; false).

(* The diagram is CONSTANT at the one representable, and there are no
   morphisms between the two elements, so the theorem here says that the
   two-element set is the coproduct of two copies of the singleton. *)

Example kbool_diagram_constant :
  DensityDiagram KBool et = DensityDiagram KBool ef := eq_refl.

Lemma kbool_injections_differ :
  density_inj KBool et ≈ density_inj KBool ef → False.
Proof. intro H; pose proof (H ttt ttt) as Hb; discriminate. Qed.

Lemma kbool_objects_differ : et = ef → False.
Proof.
  intro H.
  pose proof (f_equal (fun j : ElementsOp KBool => (`2 j : bool)) H) as Hb.
  discriminate.
Qed.

(* The two elements are not merely DISTINCT objects of the index: there
   is no morphism between them either, in the covariant [Elements]
   reading.  This is what makes the "2 = 1 + 1" description above honest
   rather than decorative, and an audit found it asserted in prose and
   pinned nowhere, so it is a lemma now.  A morphism (ttt;true) ~> (ttt;
   false) carries a D-morphism (necessarily [id], D being [_1]) together
   with a proof that it transports [true] to [false]. *)
Lemma kbool_no_hom_et_ef :
  ((ttt; true) ~{Elements KBool}~> (ttt; false)) → False.
Proof. intros [f Hf]; simpl in Hf; discriminate. Qed.

(* The apex is not a representable: [Hom ttt,-] is singleton-valued over
   1, so an isomorphism would collapse [true] onto [false]. *)

Lemma kbool_not_representable :
  KBool ≅[[1, Sets]] @Curried_Hom _1 ttt → False.
Proof.
  intro i.
  assert (Ht := iso_from_to i ttt true).
  assert (Hf := iso_from_to i ttt false).
  simpl in Ht, Hf.
  destruct (transform[to i] ttt true).
  destruct (transform[to i] ttt false).
  rewrite Ht in Hf.
  discriminate.
Qed.

(* A competing cocone with the same apex but injections twisted by
   [negb].  The mediator it produces computes. *)

Definition neg_inj (j : ElementsOp KBool) :
  @hom ([1, Sets]) (DensityDiagram KBool j) KBool :=
  yo_inj KBool (negb (`2 j)).

Lemma neg_cocone_coherence {x y : Elements KBool}
      (f : x ~{Elements KBool}~> y) :
  neg_inj x ∘ @fmap _ _ (DensityDiagram KBool) y x f ≈ neg_inj y.
Proof.
  destruct f as [f0 Hf].
  intros e g; simpl in *.
  now rewrite Hf.
Qed.

Definition NegCocone : Cocone (DensityDiagram KBool).
Proof.
  unshelve eapply Build_Cone.
  - exact KBool.
  - unshelve eapply Build_ACone.
    + exact (fun j => neg_inj j).
    + intros x y f; exact (neg_cocone_coherence f).
Defined.

Example neg_med_true :
  transform[density_med KBool NegCocone] ttt true = false := eq_refl.

Example neg_med_false :
  transform[density_med KBool NegCocone] ttt false = true := eq_refl.

Lemma neg_med_not_id :
  density_med KBool NegCocone ≈ nat_id → False.
Proof. intro H; pose proof (H ttt true) as Hb; discriminate. Qed.

End Witness.

(** ** Probe: negatives of three kinds, with positive controls *)

(* Each [Fail] below was stripped once and its error read off, so its
   KIND is known and it is not vacuously green.  Every constant named in
   a negative is also named in a control in the same section, so a rename
   breaks the file loudly instead of turning a negative into a
   "reference not found" false pass. *)

Section ProbeConversion.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* Controls: the two functors agree on objects and on arrows. *)

Definition ctrl_pdd_obj (c : C) (x : P c) :
  PDensityDiagram P ((c; x) : PElements P)
    = (Curried_CoHom C ◯ PElements_proj P) ((c; x) : PElements P)
  := pdd_via_proj_obj P c x.

Definition ctrl_pdd_fmap (x y : PElements P) (f : x ~{PElements P}~> y) :
  @fmap _ _ (PDensityDiagram P) x y f
    = @fmap _ _ (Curried_CoHom C ◯ PElements_proj P) x y f
  := pdd_via_proj_fmap P x y f.

(* NEGATIVE 1 (CONVERSION).  Stripped, this reports
   [cannot unify "PDensityDiagram P" and
   "Curried_CoHom C ◯ PElements_proj P"].  The two records differ only
   in their functor-law fields, which [PElements_proj] supplies as
   opaque [Program] obligations. *)

Fail Example neg_pdd_records :
  PDensityDiagram P = Curried_CoHom C ◯ PElements_proj P := eq_refl.

End ProbeConversion.

Section ProbeMediator.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* Controls. *)

Example ctrl_diag_def :
  DensityDiagram K = Curried_Hom D ◯ (Elements_proj K)^op := eq_refl.

Definition ctrl_med_commutes (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j ≈ cocone_inj M j
  := density_med_commutes K M j.

(* NEGATIVE 2 (CONVERSION).  Stripped, this reports
   [cannot unify "density_med K M ∘ density_inj K j" and
   "cocone_inj M j"].  The mediator evaluates the competing cocone at the
   object (e, fmap[K] g x) of the index while the right-hand side
   evaluates it at j, and the two are reconciled only by cocone coherence
   at [Elements_lift], which is a `≈` fact. *)

Fail Example neg_med_commutes_strict (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j = cocone_inj M j := eq_refl.

(* Control for negative 3: the composite is formable with the OPPOSITE of
   the projection. *)

Check (Curried_Hom D ◯ (Elements_proj K)^op).

(* NEGATIVE 3 (TYPING).  Stripped, this reports
   ["Elements_proj K" has type "Elements K ⟶ D" while it is expected to
   have type "Elements K ⟶ D^op" (cannot unify "D" and "(D^op)")].
   This is the variance: the diagram of representables cannot be indexed
   by [Elements K] covariantly. *)

Fail Check (Curried_Hom D ◯ Elements_proj K).

End ProbeMediator.

Section ProbeUniverse.

Universe uo uh us.
Constraint uh < uo.
Constraint uh < us.

(* Controls: at a category whose OBJECTS sit strictly ABOVE its homs,
   both the index category and the Yoneda transformation are formable,
   and [DensityDiagram] itself is nameable. *)

Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => ElementsOp K).
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => @yo_inj D K).
Check @DensityDiagram.

(* NEGATIVE 4 (FORMABILITY).  Stripped, this reports a universe
   inconsistency naming the declared levels: [Cannot enforce uh = _
   because uh < uo <= _].  So the constraint [u <= u0] read off
   [DensityDiagram]'s block is real, and it enters at the DIAGRAM rather
   than at the index or at [yo_inj]. *)

Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              DensityDiagram K).

End ProbeUniverse.

(* Instrument check: [Fail] does report an error when its command
   SUCCEEDS, so the four negatives above are genuine failures and not an
   inert tactic. *)

Fail Fail Check density.

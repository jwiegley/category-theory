Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Reflection of limits, colimits and coequalizers *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           Springer GTM 5, 1998, §VI.7 "Beck's Theorem": the Definition
           of reflecting colimits, printed p. 154 (PDF p. 163) —
           maclane:VI.7:def2; Exercise 1, p. 154 (PDF p. 163) —
           maclane:VI.7:ex1; Exercise 3, p. 155 (PDF p. 164) —
           maclane:VI.7:ex3
   Book:   Riehl, "Category Theory in Context", 2nd ed., §3.4:
           Definition 3.4.1 (ii), printed p. 104 (PDF p. 124) —
           riehl:3.4:def1; Lemma 3.4.5, p. 105 (PDF p. 125) —
           riehl:3.4:lem5; Exercise 3.4.iii, p. 108 (PDF p. 128) —
           riehl:3.4:exiii
   nLab:   https://ncatlab.org/nlab/show/reflected+limit
   nLab:   https://ncatlab.org/nlab/show/conservative+functor

   WHAT THE BOOKS SAY, read from the page images.  Mac Lane, p. 154:
   "Definition.  A functor G : A → X reflects colimits of T : J → A when
   every cone λ : T →· a from T to a ∈ A for which Gλ : GT →· Ga is a
   colimiting cone in X is already a colimiting cone in A.  In
   particular, G reflects coequalizers when every fork in A which becomes
   a coequalizer in X is already a coequalizer in A.  Similarly, G
   reflects isomorphisms when, for all arrows t of A, Gt an isomorphism
   implies t an isomorphism."  The exercises open "(Throughout,
   "coequalizers" means "coequalizers of parallel pairs".)"; "1. If G
   creates coequalizers, prove that it also reflects coequalizers."; and
   p. 155, "3. (Alternative hypothesis for Exercise 2.)  If A has all
   coequalizers, G preserves all coequalizers, and G reflects
   isomorphisms, prove that G reflects all coequalizers."  Riehl, p. 104:
   F "reflects limits of K if every cone over K, whose image under F is a
   limit cone for the diagram FK, is a limit cone over K", and "More
   commonly, we speak of a functor that preserves, reflects, or creates
   limits of a class of diagrams, for instance of a particular shape or
   size.  Definition 3.4.1 dualizes ..."; p. 105, Lemma 3.4.5: "Any full
   and faithful functor reflects any limits and colimits that are present
   in its codomain."; p. 108, Exercise 3.4.iii: "Prove that F : C → D
   creates limits for a particular class of diagrams if both of the
   following hold: (i) C has those limits and F preserves them.  (ii)
   F : C → D reflects isomorphisms."

   ALREADY IN THE TREE.  Mac Lane's definition, per diagram and at cone
   level, is Structure/Limit/Preservation.v's [ReflectsColimitCocone K F]
   (PR #1087, merged 2026-08-14, for #427): a cocone N over K whose image
   cocone [FCocone F N], the injections of N under F, is colimiting is
   itself colimiting (the probe reads it off, C1).  Riehl's 3.4.1 (ii) is
   [ReflectsLimitCone K F] beside it (PR #1083, merged 2026-08-13, for
   #406; moved there by #1087), and reflection of isomorphisms is the
   class [ReflectsIsos].  On the limit side creation gives reflection by
   Structure/Limit/Creation.v's [creates_reflects_limits] (#1083).  The
   transports [Full_op] and [Faithful_op] that the colimit half of
   Riehl's 3.4.5 needs are Functor/Opposite.v's (PR #1108, merged
   2026-08-15, for #266).  The name [ReflectsLimit], which Creation.v
   left unused for this issue, stays unused: [ReflectsLimitCone] is that
   predicate, and a second name would be a duplicate.

   WHAT IS HERE.
     - Reflection over a shape, over a class of shapes, over a class of
       diagrams and over every diagram, shaped like Preservation.v's
       [PreservesLimitConesOfShape] and [PreservesLimitConesOver] and
       Creation.v's [CreatesAllLimits]: [ReflectsLimitConesOfShape],
       [ReflectsLimitConesOver], [ReflectsLimitConesOfClass],
       [ReflectsAllLimits], and the colimit twins
       [ReflectsColimitCoconesOfShape], [ReflectsColimitCoconesOver],
       [ReflectsColimitCoconesOfClass], [ReflectsAllColimits].  The
       issue's [ReflectsLimits] and [ReflectsColimits] are the [All]
       forms, named like [CreatesAllLimits].  [ReflectsAllLimits_Over]
       and its twin descend from every diagram to any class of shapes.
       A class of shapes is a predicate on categories, so
       Structure/Limit/Finite.v's [FiniteCategory] is Riehl's "all
       finite shapes" (the probe, C11 and C12).  A class of diagrams,
       Riehl's own quantifier, is a predicate on the diagrams K : J ⟶ C
       of every shape J, and a class of shapes S is the class of all
       diagrams of those shapes, [fun J _ => S J]:
       [ReflectsLimitConesOver_OfClass] and
       [ReflectsLimitConesOfClass_Over] take the form over S to the form
       over [fun J _ => S J] and back, each the other's inverse at
       [eq_refl] (C23, C24), and so do their colimit twins (C25, C26).
     - [ReflectsIsos_op]: the opposite of a conservative functor is
       conservative, an isomorphism of C^op being one of C with its two
       laws exchanged (Theory/Morphisms/CokernelPair.v's
       [IsIsomorphism_of_op] and [op_IsIsomorphism_of]).
     - Creation gives reflection on the colimit side:
       [creates_reflects_colimits] is the reflection field of
       [CreatesColimit K F], which is [CreatesLimit] of [K^op] along
       [F^op], with the image cocone over (F ◯ K)^op read over
       F^op ◯ K^op by Preservation.v's [islimitcone_op_comp] (C2, at
       [eq_refl]); [creates_reflects_all_limits] and
       [creates_reflects_all_colimits] quantify.
     - Mac Lane's creation, read literally (§V.1, p. 112):
       [MacLaneCreatesLimit K F] lifts every limiting cone N over F ◯ K
       to a strict lift (Creation.v's [StrictLift]: the image apex equal
       to N's, the image legs N's up to ≈ along that equality) that is
       limiting and equal to every other strict lift of N, the apex by
       [=] and the legs by ≈ along it.  It gives reflection by Mac Lane's
       own argument ([maclane_creates_reflects]): a cone upstairs whose
       image is limiting is a strict lift of that image (Creation.v's
       [self_lift]), so it is the lift, which is limiting.  So it maps
       into the tree's creation ([maclane_CreatesLimit], its reflection
       field that theorem), it holds of the identity
       ([id_maclane_creates]), and [MacLaneCreatesColimit] is its colimit
       side, by the opposite.  In the iso-invariant reading of the same
       clauses, a lift that is limiting and unique up to cone
       isomorphism gives reflection in one line
       ([iso_unique_lift_reflects]); Creation.v's [creates_limiting] and
       [creates_lift_unique] derive those two clauses back from the
       reflection field and the lift's comparison, so for a lift with its
       comparison the field and the two clauses are interderivable.
     - A conservative functor reflects the limits it preserves:
       [conservative_reflects_limit] takes a limiting cone L over K
       whose image is limiting.  For a cone M whose image is limiting,
       the mediator u from M into L has F u commuting with the image
       legs, so F u is the comparison of two limiting image cones and
       invertible ([limitcone_iso]); F reflects that, and M is limiting
       by transport along the cone isomorphism u
       ([limitcone_transport]).  [preserves_conservative_reflects_limit]
       is the book's form (a limit of K, and F preserving it), with its
       forms over a shape, over a class of shapes and over a class of
       diagrams ([preserves_conservative_reflects_limits_of_class]; the
       form over a class of shapes S is the one over [fun J _ => S J],
       through [ReflectsLimitConesOfClass_Over], at [eq_refl], C27), and
       the colimit side goes by the opposite
       ([conservative_reflects_colimit] and its four forms; C28).  This
       is the reflection half of Riehl's 3.4.iii and, at the walking
       parallel pair, Mac Lane's Exercise 3.
     - Riehl's Exercise 3.4.iii: [preserves_conservative_creates_limit]
       is a [CreatesLimit K F] whose lift of every limiting cone
       downstairs is the given limit upstairs ([eq_refl], C4), whose
       comparison is [limitcone_iso] of two limiting cones over F ◯ K,
       and whose reflection is the theorem above.  For a class of
       diagrams, as the exercise states it,
       [preserves_conservative_creates_limits_of_class]: if C has the
       limits of the diagrams of the class, F preserves them and F
       reflects isomorphisms, F creates them.  For a class of shapes S,
       [preserves_conservative_creates_limits_over], consuming
       Preservation.v's [PreservesLimitConesOver]; it is the form over
       [fun J _ => S J], pointwise at [eq_refl] (C29).  On the
       colimit side, [preserves_conservative_creates_colimit] per
       diagram and [preserves_conservative_creates_colimits_of_class]
       for a class of diagrams.
     - Coequalizers.  [ReflectsCoequalizers F] is Mac Lane's "in
       particular" over the tree's elementary [IsCoequalizer]
       (Structure/Coequalizer.v): a fork e ∘ f ≈ e ∘ g in C whose image
       is a coequalizer in D is a coequalizer in C.
       [PreservesCoequalizers F] is the dual of Structure/Limit/
       FromProducts.v's [PreservesEqualizers]; [CreatesCoequalizers F]
       is Creation.v's [CreatesColimit] at every diagram of
       parallel-pair shape, a cocone-level predicate and not an
       elementary one.  The elementary and cone-level readings
       agree both ways ([ReflectsCoequalizers_ReflectsColimitCocones]
       and its converse, [PreservesCoequalizers_PreservesColimitCocones]
       and its converse), through Structure/Coequalizer.v's conversions
       at a diagram of parallel-pair shape (#477) and the converse for a
       given cocone added there by this issue
       ([parallel_cocone_coequalizer_colimit]): an image cocone is a
       cocone over F ◯ K, whose pair and whose injection over ParY are
       the images of K's, by conversion.  The two converses use their
       hypothesis only at the diagrams [APair f g], so they are stated
       per parallel pair
       ([ReflectsColimitCocones_ReflectsCoequalizers_of_pairs],
       [PreservesColimitCocones_PreservesCoequalizers_of_pairs]), the
       forms over every diagram of parallel-pair shape being their
       restrictions.
     - Exercise 1, per parallel pair as the book states it (its
       "coequalizers" are "coequalizers of parallel pairs"):
       [creates_reflects_coequalizers_of_pairs], from the tree's creation
       at every [APair f g], and [maclane_creates_reflects_coequalizers],
       from Mac Lane's, by his argument; [creates_reflects_coequalizers],
       from [CreatesCoequalizers], is the first at the restriction of its
       hypothesis (C17, at [eq_refl]).  Exercise 3:
       [conservative_reflects_coequalizers], from [HasCoequalizers C],
       [PreservesCoequalizers F] and [ReflectsIsos F]; it IS the
       cone-level theorem at the walking parallel pair, read back
       through the bridges (C5, at [eq_refl]), its colimits chosen by
       Coequalizer.v's [HasCoequalizers_HasColimitsOfShape].
     - Riehl's Lemma 3.4.5 is in Theory/Equivalence/Limit.v, beside the
       limit half [ff_reflects_limit] that it completes:
       [ff_reflects_colimit] in that apex-pinned form, and
       [ff_ReflectsLimitCone] and [ff_ReflectsColimitCocone] at cone
       level, which give [ReflectsAllLimits] and [ReflectsAllColimits]
       of every full and faithful functor (C8, C9).

   EXERCISE 1, UNDER BOTH READINGS OF CREATION.  Mac Lane's creation
   (the unnumbered Definition of §V.1, p. 112) asks for exactly one lift
   of each limiting cone, and with it Exercise 1 is immediate: a cone
   upstairs whose image is limiting is a lift of that image, hence the
   unique lift, which is limiting.  Creation.v's [CreatesLimit] does not
   carry that uniqueness as a field (its UNIQUENESS OF THE LIFT; the
   on-the-nose clause is refuted for [EM_Forget] at the identity monad
   on [Sets], #467) and carries reflection instead, so under the tree's
   creation Exercise 1 is that field read through the bridge
   ([creates_reflects_coequalizers_of_pairs]).  A field must hold of
   every creation the tree builds; a hypothesis need not, so
   [MacLaneCreatesLimit] states the book's clauses as a predicate on a
   functor, and [maclane_creates_reflects_coequalizers] is Exercise 1
   under it, by the book's argument through Creation.v's [self_lift].
   Both are per parallel pair.  The constants of Mac Lane's reading sit
   here and not in Creation.v: they consume only names Creation.v
   exports, their one consumer is this file's Exercise 1, and Creation.v
   stays as it was.

   EXERCISE 3'S CONSERVATIVITY IS NEEDED.  Instance/One.v's [Erase Sets],
   the functor from [Sets] to the point, preserves coequalizers, every
   fork in the point being a coequalizer, and [Sets] has them
   (Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers]).  It does not
   reflect them: on the two-element setoid the fork of the identity,
   twice, with the map ! onto the singleton becomes a coequalizer in the
   point and is none in [Sets].  So by Exercise 3 it is not conservative
   (the probe, C13 to C16).  The three hypotheses do hold together, at
   the identity on [Sets], which Exercise 3 then shows reflects
   coequalizers (C22).

   THE OPPOSITE.  [ReflectsLimitCone (K^op) (F^op)] is not
   [ReflectsColimitCocone K F]: the probe's R1 is refused at conversion,
   under its import list with "(cannot unify "Cone (F^op ◯ K^op)" and
   "Cone (F ◯ K)^op")", the two functors being distinct records
   (Preservation.v); so every colimit statement here reads its image
   cocone through [islimitcone_op_comp], and C3 converts in one line.

   STRENGTHS.  At [eq_refl], restated in the probe: Mac Lane's
   definition as [ReflectsColimitCocone] (C1), Exercise 1 at cone level
   as the creation's field (C2), the lift of 3.4.iii (C4), Exercise 3 as
   the cone-level theorem (C5), [ff_ReflectsLimitCone] as
   [ff_reflect_ump] (C10), Exercise 1 over every diagram of
   parallel-pair shape as the per-pair theorem at the restriction of its
   hypothesis (C17), the maps between the forms over a class of shapes
   and over a class of diagrams as each other's inverses (C23 to C26),
   and the conservative reflection and Riehl's 3.4.iii over a class of
   shapes as their forms over a class of diagrams (C27 to C29).  The
   universal properties hold at the categories' own ≈.  Every new
   constant is transparent, a term or closed [Defined]; the one [Qed] of
   this issue is the probe's C15.

   UNIVERSES, read off [About] for every name on Rocq 9.1.1.  No block
   carries an equation, and none mentions [Set].  The cone-level names
   bind J, C and D at one hom level, as the in-tree predicates they
   state already do ([ReflectsLimitCone], [ReflectsColimitCocone] and
   [CreatesLimit] each bind all three at one hom level), and so does
   [MacLaneCreatesLimit], stated over [Cone] and [StrictLift];
   [ReflectsIsos_op] binds C and D at the one hom level of [ReflectsIsos],
   and the full and faithful names at the one hom level of [Full].
   [ReflectsCoequalizers] and [PreservesCoequalizers] are
   [@{co ch do dh u}] with ch <= dh, [Functor]'s own bound (h1 <= h2):
   their binders are written out, and the probe accepts both with ch < dh
   strict (C6, C7), while [ReflectsIsos] is refused there (R2,
   "Cannot enforce dh = ch because ch < dh").  So Exercises 1 and 3 hold
   at C's hom level, and the tie is a minimization artifact, twice over.
   First, the classes of their hypotheses leave their binders to Rocq,
   which identifies the two hom levels: [ReflectsIsos] with its binders
   written out is accepted with ch < dh (C18, C19) and is the class at
   one level (C20), and [Full] and [Faithful], each refused there, are
   each accepted with their binders written out (measured in a scratch
   file, not pinned).  Second, and independently, the route through the
   cone level ties them: [ReflectsColimitCocone], [CreatesColimit] and
   [MacLaneCreatesColimit] at a pair, and [PreservesColimitCoconesOfShape]
   at [Parallel], are each refused with ch < dh, with R2's message, and
   with the annotated [ReflectsIsos] Exercise 3 by this route is refused
   there at its first cone-level step (measured in a scratch file, not
   pinned).  The cone vocabulary is on #1363's list of such carriers.
   Lifting Exercise 3 above C's hom level would take [ReflectsIsos]
   annotated together with #1363's carriers, or a direct elementary
   proof over the annotated class; lifting Exercise 1 would take #1363's
   carriers, creation being cone-level.  Caps: [Projections] on the
   twenty-seven names whose terms reach Preservation.v's
   [limitcone_transport], whose own block carries them, as do the blocks
   of the cone-isomorphism lemmas before it ([coneiso_from],
   [ConeIso_sym]); and [False_rect] on the eight whose terms reach
   Instance/Parallel.v's [APair], whose own block carries it.  Two first
   drafts were rejected by measurement:
   [conservative_reflects_limit] stated in a Section carried four
   equations from the Section's [Context] (u0 = u2, u0 = u4, u2 = u4,
   u6 = u8), none at top level; and a converse bridge through
   Coequalizer.v's [is_coequalizer_cocone_ump], read as an
   [IsColimitCocone] of the cofork cocone, bounded the walking pair's
   object level by C's hom level (po <= ch, carried by that ascription
   alone, measured), where [parallel_coequalizer_colimit] leaves it
   free.  On Coq 8.19.2 and 8.20.1 ([About] in source overlays of the
   dependency closure of this issue's changed files, with the probe and
   a scratch file, 105 files each) every name binds as many levels, at
   the same type, under the same constraints apart from standard-library
   caps; the two versions agree with each other; and the caps differ
   from 9.1.1's on 56 of the 59 names ([eq], [sigT], [Specif] and
   [Logic] universes there), none of it an equation.  Only the printing
   of 8.19.2 differs: in five names it shows the implicit binders that
   follow an arrow in parentheses.  No explicit universe instance of a
   new constant is written.

   CLOSURE.  The [Require]s load 35 [Category] modules, this one
   included ([Print Libraries]); Theory/Morphisms/CokernelPair.v, which
   only [ReflectsIsos_op] uses, accounts for 7 of them.  The shared route
   is taken at that cost.

   STALE PREMISES, dated from gh.  Issue #481 (filed 2026-07-23; the
   three Riehl sections appended 2026-07-31) says that only the
   isomorphism case of reflection is first-class, "reflects colimits"
   existing only as the unfolded conclusion of theorems about full and
   faithful functors and equivalences; that creation implies reflection
   only for isomorphisms, from U-split creation; that a search for
   "CreatesLimit|ReflectsLimit" returns nothing; and that
   Functor/Opposite.v mentions neither [Full] nor [Faithful].  Each was
   accurate when written and is stale since PR #1083 (merged 2026-08-13:
   [CreatesLimit], [ReflectsLimitCone] and [creates_reflects_limits],
   which also gives the reflection of colimits read in the opposite
   category), PR #1087 (merged 2026-08-14: [ReflectsColimitCocone]) or
   PR #1108 (merged 2026-08-15: [Full_op], [Faithful_op] and their
   converses).  Its line citations are replaced by names here.  The
   quantified predicates, Exercise 3, Riehl's 3.4.iii, the elementary
   coequalizer predicates and [ff_reflects_colimit] were absent until
   this change: a sweep of the tree's .v and .glob files for the 59
   names (instrumented: [IsLimitCone] found, a made-up name not) finds
   them only in this file, the probe, the declarations and prose this
   change adds to Structure/Coequalizer.v and Theory/Equivalence/Limit.v,
   the three proof bodies it routes through [ff_ReflectsLimitCone] with
   their CORRECTION notes, and Adjunction/Continuity/Equalizer.v, whose
   sentence that no [PreservesCoequalizers] exists carries a CORRECTION
   (#481) in place, which names the bridge
   [PreservesColimitCocones_PreservesCoequalizers].

   DUPLICATES, UNIFIED AND KEPT.  Three constants of the tree wrote out
   [ff_ReflectsLimitCone]'s term at their own functors, and each reads
   back as it at [eq_refl] (measured): Theory/Equivalence/Creation.v's
   [equivalence_ReflectsLimitCone], Construction/Subcategory/Creation.v's
   [sub_ReflectsLimitCone] and Construction/Reflective/Limit.v's
   [reflective_ReflectsLimitCone].  Each body now calls it, eta-expanded,
   with a CORRECTION (#481) in place, and the [About] blocks of all 38
   constants of the three files are unchanged (compared by script).  Two
   others state special cases of new constants and are not convertible
   with them, their readbacks at [eq_refl] being refused ("cannot
   unify", measured): Structure/Coequalizer/Absolute.v's
   [image_coequalizer_colimit], against
   [parallel_cocone_coequalizer_colimit] at [T ◯ APair f g], and
   Theory/Equivalence/Limit.v's [equivalence_reflects_colimits], against
   [ff_reflects_colimit], its fullness and faithfulness of F^op being
   those of the opposite equivalence and not [Full_op] and [Faithful_op]
   of F's.  Re-routing either would change its term, so both are kept as
   they are, for the maintainer to decide.

   NOT DELIVERED.  A functor other than the identity that creates in
   Mac Lane's literal sense: the on-the-nose uniqueness is refuted for
   [EM_Forget] at the identity monad on [Sets] (#467), and
   [id_maclane_creates] at the opposite diagram is a creation along
   [Id[C^op]], which Rocq does not accept where one along [Id[C]^op] is
   expected, so it gives no instance of
   [maclane_creates_reflects_coequalizers] (measured).  Creation
   transported along an isomorphism of diagrams, which would give the
   hypothesis of [creates_reflects_coequalizers] from that of its
   per-pair form.  Reflection relative to a class of pairs in the
   elementary form (at cocone level it is [ReflectsColimitCoconesOfClass]
   at a class of diagrams of parallel-pair shape), which the section's
   Exercises 5 and 6 use, Beck's U-split pairs among them
   (Monad/Monadicity/Beck.v's [CreatesUSplitCoequalizers] yields
   [creates_split_reflects_isos] and not the reflection of the
   coequalizers of U-split pairs).  A [PreservesColimitCoconesOver]
   beside Preservation.v's limit-side [PreservesLimitConesOver]: the
   colimit form of reflection over a class of shapes takes its
   preservation shape by shape, and 3.4.iii on the colimit side has no
   form over a class of shapes of its own, being stated per diagram and
   over a class of diagrams.  A witness of Exercise 3's conclusion at a
   functor that is neither an equivalence nor full and faithful; the
   probe shows its conservativity hypothesis is needed (C13 to C16), not
   the other two.  The elementary Exercises at a target hom level above
   C's (UNIVERSES). *)

(** ** Reflection over a shape, a class of shapes or diagrams, and all *)

Definition ReflectsLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsLimitCone K F.

Definition ReflectsLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsLimitCone K F.

(* Over a class of diagrams, Riehl's own quantifier: a predicate on the
   diagrams K of every shape J.  A class of shapes S is the class of all
   diagrams of those shapes, [fun J _ => S J], and the two forms agree up
   to the order of their arguments, by the two maps below, each the
   other's inverse at [eq_refl] (the probe, C23 and C24). *)

Definition ReflectsLimitConesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsLimitCone K F.

Definition ReflectsLimitConesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsLimitConesOver S F) :
  ReflectsLimitConesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsLimitConesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsLimitConesOfClass (fun J _ => S J) F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsLimitCone K F.

Definition ReflectsAllLimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllLimits F) : ReflectsLimitConesOver S F :=
  fun J _ K => H J K.

Definition ReflectsColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver {C D : Category}
  (S : Category → Type) (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsColimitCoconesOver S F) :
  ReflectsColimitCoconesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsColimitCoconesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsColimitCoconesOfClass (fun J _ => S J) F) :
  ReflectsColimitCoconesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsColimitCocone K F.

Definition ReflectsAllColimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllColimits F) : ReflectsColimitCoconesOver S F :=
  fun J _ K => H J K.

(** ** A conservative functor's opposite is conservative *)

(* An isomorphism of C^op is one of C with its two laws exchanged;
   Theory/Morphisms/CokernelPair.v's [IsIsomorphism_of_op] and
   [op_IsIsomorphism_of] read it across, in D and in C. *)

Definition ReflectsIsos_op {C D : Category} {F : C ⟶ D}
  (R : ReflectsIsos F) : ReflectsIsos (F^op) :=
  @Build_ReflectsIsos (C^op) (D^op) (F^op)
    (fun x y f I =>
       @op_IsIsomorphism_of C x y f
         (@reflects_iso C D F R y x f (IsIsomorphism_of_op (fmap[F] f) I))).

(** ** Creation gives reflection: the colimit side *)

(* The colimit twin of Structure/Limit/Creation.v's
   [creates_reflects_limits].  [CreatesColimit K F] is [CreatesLimit] of
   [K^op] along [F^op], whose reflection field asks for the image cone over
   [F^op ◯ K^op]; Structure/Limit/Preservation.v's [islimitcone_op_comp]
   reaches it from the image cocone over [(F ◯ K)^op]. *)

Definition creates_reflects_colimits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesColimit K F) :
  ReflectsColimitCocone K F :=
  fun N H =>
    @creates_reflect (J^op) (C^op) (D^op) (K^op) (F^op) CR N
      (islimitcone_op_comp H).

Definition creates_reflects_all_limits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : ReflectsAllLimits F :=
  fun J K => creates_reflects_limits (CR J K).

Definition creates_reflects_all_colimits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllColimits F) : ReflectsAllColimits F :=
  fun J K => creates_reflects_colimits (CR J K).

(** ** Mac Lane's creation, read literally *)

(* Mac Lane §V.1, the unnumbered Definition on p. 112: F creates the
   limit of K when every limiting cone N over F ◯ K has exactly one lift,
   an apex a with F a equal to N's apex and legs whose images are N's, and
   that lift is limiting.  The lift is Creation.v's [StrictLift] (the
   apex by [=], the legs by ≈ along it), and "exactly one" is equality
   with every other strict lift of N, the apex by [=] and the legs by ≈
   along it.  Creation.v declines that uniqueness as a FIELD of
   [CreatesLimit] (its UNIQUENESS OF THE LIFT); as a hypothesis it is
   what Mac Lane's Exercise 1 assumes. *)

Record MacLaneCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  mlc_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  mlc_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (mlc_lift N HN));
  mlc_unique (N : Cone (F ◯ K)) (HN : IsLimitCone N) (L : StrictLift K F N) :
    { p : vertex_obj[slift_cone L] = vertex_obj[slift_cone (mlc_lift N HN)]
    & ∀ x : J, cone_leg (slift_cone (mlc_lift N HN)) x ∘ to (obj_eq_iso p)
                 ≈ cone_leg (slift_cone L) x }
}.

Arguments mlc_lift {J C D K F} _ _ _.
Arguments mlc_limiting {J C D K F} _ _ _.
Arguments mlc_unique {J C D K F} _ _ _ _.

(* Reflection by Mac Lane's argument: a cone M upstairs whose image is
   limiting is a strict lift of that image (Creation.v's [self_lift]), so
   it is the lift, which is limiting.  The cone isomorphism is built with
   [exact], not as a pair term, which Coq 8.19 and 8.20 check by
   unification. *)

Definition maclane_creates_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : ReflectsLimitCone K F.
Proof.
  intros M HM.
  refine (limitcone_transport (ConeIso_sym _)
            (mlc_limiting CR (FCone F M) HM)).
  unshelve eexists.
  - exact (obj_eq_iso (`1 (mlc_unique CR (FCone F M) HM (self_lift M)))).
  - exact (`2 (mlc_unique CR (FCone F M) HM (self_lift M))).
Defined.

(* So Mac Lane's creation is one of the tree's, whose reflection field is
   the theorem above. *)

Definition maclane_CreatesLimit {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : CreatesLimit K F.
Proof.
  unshelve refine
    {| creates_lift := fun N HN => slift_cone (mlc_lift CR N HN);
       creates_reflect := maclane_creates_reflects CR |}.
  intros N HN.
  exists (slift_iso (mlc_lift CR N HN)).
  intro x.
  exact (slift_iso_legs (mlc_lift CR N HN) x).
Defined.

(* The same two clauses in the iso-invariant reading, a lift that is
   limiting and unique up to cone isomorphism, give reflection in one
   line; Creation.v's [creates_limiting] and [creates_lift_unique] derive
   them back from the reflection field and the lift's comparison. *)

Definition iso_unique_lift_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D}
  (lift : ∀ N : Cone (F ◯ K), IsLimitCone N → Cone K)
  (lift_limiting : ∀ N HN, IsLimitCone (lift N HN))
  (lift_unique : ∀ N HN (M : Cone K), ConeIso (FCone F M) N →
                   ConeIso M (lift N HN)) :
  ReflectsLimitCone K F :=
  fun M HM =>
    limitcone_transport (ConeIso_sym (lift_unique _ HM M (ConeIso_id _)))
      (lift_limiting _ HM).

(* The identity creates every limit in Mac Lane's sense: the lift of N is
   N itself, read over K, and a strict lift of N has N's apex. *)

Definition id_maclane_creates {J C : Category} (K : J ⟶ C) :
  MacLaneCreatesLimit K Id[C].
Proof.
  unshelve econstructor.
  - intros N HN.
    unshelve econstructor.
    + exact (@Build_Cone J C K vertex_obj[N]
               (@Build_ACone J C vertex_obj[N] K (fun x => cone_leg N x)
                  (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N)
                                  x y f))).
    + reflexivity.
    + intro x; reflexivity.
  - intros N HN; simpl.
    intro M.
    exact (HN (@Build_Cone J C (Id ◯ K) vertex_obj[M]
                 (@Build_ACone J C vertex_obj[M] (Id ◯ K)
                    (fun x => cone_leg M x)
                    (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M)
                                    x y f)))).
  - intros N HN L; simpl.
    exists (slift_eq L).
    intro x.
    pose proof (slift_legs L x) as HL.
    destruct L as [L p HLs]; simpl in *.
    destruct N as [n acN]; simpl in *.
    destruct p; simpl in *.
    rewrite id_right.
    symmetry; exact HL.
Defined.

(* The colimit side, by the opposite, as Creation.v's [CreatesColimit]. *)

Definition MacLaneCreatesColimit {J C D : Category} (K : J ⟶ C)
  (F : C ⟶ D) : Type := MacLaneCreatesLimit (K^op) (F^op).

(** ** A conservative functor reflects the limits it preserves *)

(* Let M be a cone over K whose image is limiting, and u its mediator
   into L.  F u commutes with the image legs, so it is the comparison
   between the two limiting image cones, an isomorphism; F reflects it,
   so u is a cone isomorphism from M to L, and M is limiting. *)

Definition conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cone K) (HL : IsLimitCone L) (HFL : IsLimitCone (FCone F L)) :
  ReflectsLimitCone K F.
Proof.
  intros M HFM.
  pose (u := unique_obj (HL M)).
  assert (Hu : ∀ x : J, cone_leg L x ∘ u ≈ cone_leg M x)
    by exact (unique_property (HL M)).
  pose (i := limitcone_iso HFM HFL).
  assert (HFu : fmap[F] u ≈ to `1 i).
  { symmetry.
    apply (uniqueness (HFL (FCone F M))).
    intro x.
    change (fmap[F] (cone_leg L x) ∘ fmap[F] u ≈ fmap[F] (cone_leg M x)).
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact (Hu x). }
  assert (IFu : IsIsomorphism (fmap[F] u)).
  { unshelve refine {| two_sided_inverse := from `1 i |}.
    - rewrite HFu.
      exact (iso_to_from `1 i).
    - rewrite HFu.
      exact (iso_from_to `1 i). }
  assert (ci : ConeIso M L).
  { exists (IsIsoToIso u (@reflects_iso C D F R _ _ u IFu)).
    exact Hu. }
  exact (limitcone_transport (ConeIso_sym ci) HL).
Defined.

Definition preserves_conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitCone K F :=
  conservative_reflects_limit R (@limit_cone _ _ _ L) (limit_limitcone L)
    (P (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition preserves_conservative_reflects_limits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOfShape J F) (R : ReflectsIsos F) :
  ReflectsLimitConesOfShape J F :=
  fun K => preserves_conservative_reflects_limit (HL K) (P K) R.

Definition preserves_conservative_reflects_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_limit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitConesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_limit (HL J K HS) (P J K HS) R.

(* The colimit side, by op: [F^op] is conservative ([ReflectsIsos_op]),
   and both image cocones are read as image cones over [F^op ◯ K^op]. *)

Definition conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cocone K) (HL : IsColimitCocone L)
  (HFL : IsColimitCocone (FCocone F L)) : ReflectsColimitCocone K F :=
  fun N HFN =>
    @conservative_reflects_limit (J^op) (C^op) (D^op) (K^op) (F^op)
      (ReflectsIsos_op R) L HL (islimitcone_op_comp HFL) N
      (islimitcone_op_comp HFN).

Definition preserves_conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCocone K F :=
  conservative_reflects_colimit R (@limit_cone _ _ _ L)
    (colimit_colimitcocone L)
    (P (@limit_cone _ _ _ L) (colimit_colimitcocone L)).

Definition preserves_conservative_reflects_colimits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Colimit K)
  (P : PreservesColimitCoconesOfShape J F) (R : ReflectsIsos F) :
  ReflectsColimitCoconesOfShape J F :=
  fun K => preserves_conservative_reflects_colimit (HL K) (P K) R.

Definition preserves_conservative_reflects_colimits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Colimit K)
  (P : ∀ J : Category, S J → PreservesColimitCoconesOfShape J F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_colimit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_colimit (HL J K HS) (P J K HS) R.

(** ** Riehl Exercise 3.4.iii: preservation and conservativity create *)

(* The lift of every limiting cone downstairs is the given limit upstairs,
   whose image is limiting by preservation and so isomorphic, as a cone,
   to any limiting cone downstairs; reflection is the theorem above. *)

Definition preserves_conservative_creates_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : CreatesLimit K F :=
  @Build_CreatesLimit J C D K F
    (fun N HN => @limit_cone _ _ _ L)
    (fun N HN =>
       limitcone_iso (P (@limit_cone _ _ _ L) (limit_limitcone L)) HN)
    (preserves_conservative_reflects_limit L P R).

Definition preserves_conservative_creates_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ∀ J : Category, S J → CreatesLimitsOfShape J F :=
  fun J HJ K =>
    preserves_conservative_creates_limit (HL J HJ K) (P J HJ K) R.

(* For a class of diagrams, as the exercise states it; the form over a
   class of shapes S above is this one at [fun J _ => S J], pointwise at
   [eq_refl] (the probe, C29). *)

Definition preserves_conservative_creates_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesLimit K F :=
  fun J K HS =>
    preserves_conservative_creates_limit (HL J K HS) (P J K HS) R.

Definition preserves_conservative_creates_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : CreatesColimit K F :=
  @preserves_conservative_creates_limit (J^op) (C^op) (D^op) (K^op) (F^op)
    L (fun N HN => islimitcone_op_comp (P N HN)) (ReflectsIsos_op R).

Definition preserves_conservative_creates_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesColimit K F :=
  fun J K HS =>
    preserves_conservative_creates_colimit (HL J K HS) (P J K HS) R.

(** ** Coequalizers: Mac Lane's "in particular" and Exercises 1 and 3 *)

(* Mac Lane's reflection of coequalizers, over the tree's elementary
   [IsCoequalizer]: a fork in C (e ∘ f ≈ e ∘ g) whose image is a
   coequalizer in D is a coequalizer in C. *)

Definition ReflectsCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    e ∘ f ≈ e ∘ g →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e) →
    IsCoequalizer f g q e.

(* Preservation in the same form: the dual of Structure/Limit/
   FromProducts.v's [PreservesEqualizers], and Monad/Monadicity/Crude.v's
   [PreservesReflexiveCoequalizers] without its reflexivity hypothesis.
   The binders of both predicates are written out: left to Rocq,
   minimization identified D's hom level with C's (measured), and the
   probe accepts both with D's strictly above (C6, C7). *)

Definition PreservesCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    IsCoequalizer f g q e →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e).

(* Creation of coequalizers: Structure/Limit/Creation.v's creation of the
   colimit of every diagram of parallel-pair shape. *)

Definition CreatesCoequalizers {C D : Category} (F : C ⟶ D) : Type :=
  ∀ K : Parallel ⟶ C, CreatesColimit K F.

(* The elementary and the cocone-level readings agree, both ways, through
   Structure/Coequalizer.v's conversions at a diagram of parallel-pair
   shape: an image cocone is a cocone over [F ◯ K], whose pair is the
   image pair and whose injection over [ParY] is the image injection, by
   conversion. *)

Definition ReflectsCoequalizers_ReflectsColimitCocones {C D : Category}
  {F : C ⟶ D} (R : ReflectsCoequalizers F) :
  ReflectsColimitCoconesOfShape Parallel F.
Proof.
  intros K N H.
  apply (parallel_cocone_coequalizer_colimit K N).
  apply R.
  - (* N coforks the pair: both composites are its injection over ParX *)
    transitivity (cocone_inj N ParX).
    + exact (cocone_inj_coherence N
               ((true; ParOne) : ParX ~{Parallel}~> ParY)).
    + symmetry.
      exact (cocone_inj_coherence N
               ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
  - exact (parallel_colimit_coequalizer (F ◯ K) (FCocone F N) H).
Defined.

(* The two bridges from the cocone level to the elementary predicates use
   their hypothesis only at the diagrams [APair f g], so they are stated
   per parallel pair, and their forms over every diagram of parallel-pair
   shape are the restrictions. *)

Definition ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (R : ∀ (x y : C) (f g : x ~> y), ReflectsColimitCocone (APair f g) F) :
  ReflectsCoequalizers F :=
  fun x y f g q e H E =>
    parallel_colimit_coequalizer (APair f g) (cofork_cocone f g e H)
      (R x y f g (cofork_cocone f g e H)
         (parallel_cocone_coequalizer_colimit (F ◯ APair f g)
            (FCocone F (cofork_cocone f g e H)) E)).

Definition ReflectsColimitCocones_ReflectsCoequalizers {C D : Category}
  {F : C ⟶ D} (R : ReflectsColimitCoconesOfShape Parallel F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => R (APair f g)).

Definition PreservesCoequalizers_PreservesColimitCocones {C D : Category}
  {F : C ⟶ D} (P : PreservesCoequalizers F) :
  PreservesColimitCoconesOfShape Parallel F :=
  fun K N HN =>
    parallel_cocone_coequalizer_colimit (F ◯ K) (FCocone F N)
      (P _ _ _ _ _ _ (parallel_colimit_coequalizer K N HN)).

Definition PreservesColimitCocones_PreservesCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (P : ∀ (x y : C) (f g : x ~> y), PreservesColimitCocone (APair f g) F) :
  PreservesCoequalizers F :=
  fun x y f g q e E =>
    parallel_colimit_coequalizer (F ◯ APair f g)
      (FCocone F (parallel_cofork_cocone (APair f g) e (cofork E)))
      (P x y f g (parallel_cofork_cocone (APair f g) e (cofork E))
         (parallel_coequalizer_colimit (APair f g) E)).

Definition PreservesColimitCocones_PreservesCoequalizers {C D : Category}
  {F : C ⟶ D} (P : PreservesColimitCoconesOfShape Parallel F) :
  PreservesCoequalizers F :=
  PreservesColimitCocones_PreservesCoequalizers_of_pairs
    (fun x y f g => P (APair f g)).

(* Mac Lane §VI.7 Exercise 1, per parallel pair, as the book states it:
   under the tree's creation, where reflection is a field ... *)

Definition creates_reflects_coequalizers_of_pairs {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), CreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => creates_reflects_colimits (CR x y f g)).

(* ... and under Mac Lane's own, by his argument. *)

Definition maclane_creates_reflects_coequalizers {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), MacLaneCreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g N H =>
       maclane_creates_reflects (CR x y f g) N (islimitcone_op_comp H)).

(* Over every diagram of parallel-pair shape, by restriction (C17). *)

Definition creates_reflects_coequalizers {C D : Category} {F : C ⟶ D}
  (CR : CreatesCoequalizers F) : ReflectsCoequalizers F :=
  creates_reflects_coequalizers_of_pairs (fun x y f g => CR (APair f g)).

(* Mac Lane §VI.7 Exercise 3. *)

Definition conservative_reflects_coequalizers {C D : Category}
  {F : C ⟶ D} (HC : HasCoequalizers C) (P : PreservesCoequalizers F)
  (R : ReflectsIsos F) : ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers
    (preserves_conservative_reflects_colimits_of_shape Parallel
       (HasCoequalizers_HasColimitsOfShape HC)
       (PreservesCoequalizers_PreservesColimitCocones P) R).

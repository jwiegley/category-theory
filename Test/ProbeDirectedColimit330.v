(** * Boundary probes for Instance/Ab/DirectedColimit.v (issue #330)

    Mac Lane CWM 2nd ed. §III.3 Exercise 7, book p. 68.

    This file pins the two measurements the target's header states, so that
    a later edit which quietly makes either one FALSE breaks the build
    instead of silently invalidating the prose.

    The two negatives are of DIFFERENT KINDS and are kept lexically apart:

      * CONVERSION -- [fg_med_commutes] is stated at [≈] and NOT at Leibniz
        equality of whole morphisms.  The cause is the mediator's design:
        it evaluates the competing cocone at the CYCLIC object [cyc a],
        while the triangle's right-hand side evaluates it at [X].  Those
        are different objects of the index, so no amount of reduction
        identifies the two morphisms.

      * FORMABILITY (universe) -- [Instance/Proset.v]'s [Proset] cannot
        host THIS index.  [Proset] takes a stdlib [relation A], which is
        [A -> A -> Prop], while [FGHom] is [Type]-valued because
        [absub_mem] is.  Squashing the hom to [Prop] is formable (the
        positive control below) and is exactly what would break [fmap],
        which must APPLY an inclusion to transport a membership witness.

        READ THAT SCOPE EXACTLY.  It does NOT show the index cannot be
        hosted by [Proset] at all, and an earlier revision of this header
        said so ("[Proset] cannot host this index", full stop), which was
        wrong: with membership itself made [Prop]-valued, [FGHom] is
        natively a [relation], nothing is squashed, and [fmap] only applies
        a [Prop -> Prop] function -- a variant that compiles and yields the
        same colimit.  What this negative measures is a consequence of the
        target's [Type]-valued membership CONVENTION, not an impossibility.
        [Structure/Thin.v:57] records the [relation]-is-Prop-valued fact
        independently.

    PROBE HYGIENE.  This file carries the target's import list in the
    target's order, plus the target itself and [Relation_Definitions] (for
    [relation], named in Negative 2), and minus [Coq.micromega.Lia], which
    is a tactic library the probe has no use for.  It is therefore NOT
    literally "the target's full list" -- an earlier revision of this
    header said that, and it was wrong in both directions.  The point of
    the discipline stands: a short prefix leaves names like [cocone_inj]
    unresolved, and a [Fail] that succeeds because a reference is missing
    measures NOTHING.  Exactly that false pass was hit and discarded while
    these measurements were being made.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES -- re-run after each control was
    added.  The measured score is recorded at the end of this file. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Relations.Relation_Definitions.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous.
    This one must fail for a reason that has nothing to do with the
    development. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the factorization triangle is not Leibniz *)

Section TriangleNegative.

Context (A : AbObject) (N : Cocone (FGDiagram A)) (X : FGSub A).

Fail Definition probe_triangle_strict :
  fg_med N ∘ cocone_inj (FGCocone A) X = cocone_inj N X := eq_refl.

(* Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here. *)
Check (fg_med_commutes N X).
Check (fg_med N).
Check (cocone_inj (FGCocone A) X).
Check (FGCocone A).
Check (FGDiagram A).
Check (FGSub A).

End TriangleNegative.

(** ** Negative 2 (FORMABILITY): Proset cannot host THIS index

    [FGHom] is [Type]-valued -- because [absub_mem] is -- and so cannot be
    read as a stdlib [relation], which is [Prop]-valued.  This is a universe
    inconsistency, not a conversion failure: a different KIND from Negative
    1.  It measures the consequence of a CONVENTION, not an impossibility;
    see the scope paragraph in this file's header. *)

Fail Check (FGHom ab_Z : relation (FGObj ab_Z)).

(* Positive controls.  The squashed variant IS formable, which is what
   makes the negative a statement about [Prop] rather than about a
   malformed application; and every constant named in the negative is
   independently well-formed. *)
Check (fun X Y : FGObj ab_Z => inhabited (FGHom ab_Z X Y) : Prop).
Check FGHom.
Check FGObj.
Check ab_Z.
Check (relation (FGObj ab_Z)).

(** ** Controls for the delivered results

    These name the principal artifacts, so a rename anywhere in the target
    breaks this file loudly. *)

Check ab_fg_colimit.
Check ab_fg_isacolimit.
Check ab_fg_Colimit.
Check FGSub_directed.
Check FGSub_Thin.
Check AbSubgroup.
Check AbSubgroupAb.
Check absub_incl.
Check gen_sub.
Check gen_least.
Check InGen.
Check FinGen.
Check fg_join.
Check fg_of_list.
Check cyc.

(** ** Non-vacuity controls *)

Check Ztwo.
Check Zthree.
Check Ztwo_proper.
Check Zthree_proper.
Check Zsub_incomparable.
Check Zjoin_strictly_larger.
Check Ztwo_dup_iso.

(** ** MEASURED RENAME-SIMULATION SCORE

    The two negatives name these constants:

      Negative 1: [fg_med], [cocone_inj], [FGCocone]
      Negative 2: [FGHom], [FGObj], [ab_Z], [relation]

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning its negative vacuously
    green.  Score: 7/7, counted rather than recalled. *)

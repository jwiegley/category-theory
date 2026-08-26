(** * Boundary probes for Construction/Free/Quiver/Limit.v (issue #332)

    Mac Lane CWM 2nd ed. §III.4, book p. 71 (def 8, remark 6).

    This file pins two measurements the target's header rests on, so that a
    later edit which quietly makes either FALSE breaks the build rather
    than silently invalidating the prose.

    The two negatives are of DIFFERENT KINDS and are kept lexically apart:

      * CONVERSION -- [dpath D p] and [fmap[FunctorOfDiagram D] p] are NOT
        convertible at a VARIABLE path.  [dpath] is a [Fixpoint] over the
        path while [InducedFunctor]'s arrow action elaborates as a
        [tlist'_rect], so neither reduces against the other until the path
        is a literal.  At a ONE-EDGE path they DO agree, and that is the
        positive control [dpath_singleton_is_fmap] shipped in the target.

      * FORMABILITY (universe) -- [Diagram G C] identifies C's hom and
        proof universes.  This is why [AGraphCone] displays
        [C : Category@{u u0 u0}] where the [ACone] it mirrors displays them
        apart, and it is INHERITED from the donor, not introduced by the
        target.  The controls below localize that: under
        [Constraint uh < up], [QuiverOfCat C] and [ACone c F] are BOTH
        formable and only [Diagram G C] is rejected, with
          "universe inconsistency: Cannot enforce up = uh because uh < up".
        The target's header declined to measure this and said so; the
        measurement is recorded here and the attribution is to
        Theory/Diagram.v's [Diagram], NOT to anything this issue added.
        SHARPER, AND IT CHANGES WHAT THE PIN MEANS: [Diagram] opens its
        section with an unannotated [Context {C : Category}]
        (Theory/Diagram.v:143-151), so the identification is a universe
        MINIMIZATION artifact -- the family
        Construction/Free/Quiver/Examples.v's header records -- and is
        repairable upstream with explicit binders.  It is not inherent
        content, and nothing here claims it is unavoidable.

    NOT PINNED HERE, and said plainly: the target also measures that the
    three WHOLE-RECORD round trips are refuted at [eq_refl] (the records
    have primitive projections with eta, so record equality is field
    equality, and the coherence fields are rebuilt proofs).  Those are
    stated in its header and are guarded nowhere -- they are not pinned
    below either, so a later edit could make them silently true.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES.  The measured score is at the
    end of this file. *)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Coq.
Require Import Category.Construction.Free.Quiver.Limit.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): dpath is not fmap at a variable path *)

Section PathNegative.

Context (G : Quiver) (C : Category) (D : Diagram G C) (x y : G)
        (p : @hom (FreeOnQuiver G) x y).

Fail Definition probe_dpath_is_fmap :
  dpath D p = fmap[FunctorOfDiagram D] p := eq_refl.

(* Positive controls naming the negative's own constants.  At a ONE-EDGE
   path the two DO agree -- that is the target's own Example. *)
Check dpath_singleton_is_fmap.
Check (dpath D p).
Check (fmap[FunctorOfDiagram D] p).
Check (FunctorOfDiagram D).
Check (@FreeOnQuiver G).

End PathNegative.

(** ** Negative 2 (FORMABILITY, universe): Diagram identifies hom and proof

    Different KIND from Negative 1. *)

Section HomProofApart.

Universe uo uh up.
Constraint uh < up.

Context (G : Quiver) (C : Category@{uo uh up}) (c : obj[C])
        (J : Category) (F : J ⟶ C).

(* Control (a): the underlying quiver of C is formable with hom and proof
   DECLARED APART, so the identification is not the quiver's doing. *)
Check (QuiverOfCat C).

(* Control (b): the ordinary cone -- the thing [AGraphCone] mirrors -- is
   likewise formable here. *)
Check (ACone c F).

(* Control (c): THE ONE THAT ACTUALLY LOCALIZES.  [Diagram] is BY
   DEFINITION [QuiverHomomorphism G (QuiverOfCat C)], so ruling out the
   quiver and the cone does not rule out the homomorphism -- the obvious
   alternative culprit.  It IS formable here, so the identification is
   [Diagram]'s own.  An earlier revision of this file claimed the two
   controls above "localize" the cause; they do not, and this one does. *)
Check (QuiverHomomorphism G (QuiverOfCat C)).

(* The negative. *)
Fail Check (Diagram G C).

End HomProofApart.

(** ** Controls for the delivered results *)

Check AGraphCone.
Check GraphCone.
Check gcone_leg.
Check gcone_dpath.
Check ACone_of_AGraphCone.
Check AGraphCone_of_ACone.
Check Cone_of_GraphCone.
Check GraphCone_of_Cone.
Check Cone_of_GraphCone_round.
Check IsLimitGraphCone.
Check graph_limitcone.
Check limitcone_graph_limit.
Check graph_limit_iff_limitcone.
Check graph_limit_IsALimit.
Check GraphLimit.
Check graph_limit_med.
Check gcone_leg_fwd.
Check gcone_leg_bwd.

(** ** Non-vacuity controls *)

Check TriangleGraphCone.
Check triangle_graph_limit.
Check tri_gcone_of_arrow.
Check loop_gcone.
Check loop_paths_distinct.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants at risk are the ones the NEGATIVES name:

      Negative 1: [dpath], [fmap], [FunctorOfDiagram], [FreeOnQuiver]
      Negative 2: [Diagram]

    That is FIVE, and all five are named by a positive control above, so
    renaming any one breaks this file rather than turning its negative
    vacuously green.  An earlier revision counted SEVEN by folding in
    [QuiverOfCat] and [ACone]; those occur only in the controls, so their
    guarding is vacuously satisfied and they padded the denominator.  The
    simulation was run over all seven anyway and all seven are caught --
    the score is reproducible, but 5/5 is the honest accounting of what
    the negatives put at risk. *)

(** * Boundary probes for Structure/Limit/Initial.v (issue #334)

    Mac Lane CWM 2nd ed. §III.4 Exercise 3, book p. 72; Fong-Spivak
    *Seven Sketches* §3.5.3 Ex 3.98; Riehl *CTiC* 2nd ed. §3.1.

    This file pins the three measurements the target's header records and
    states are pinned nowhere.  The target is right that they are
    measurements; this file is where they stop being unguarded.

    THREE NEGATIVES OF TWO KINDS, kept lexically apart:

      * CONVERSION -- [initial_leg I F initial_obj] is not [id] on the
        nose.  It is [fmap[F] zero] at the initial object, and [zero]
        there is only [≈]-equal to [id] (by [zero_unique]), not
        convertible to it; [F] then has no reason to send it to [id]
        definitionally.  The target proves the [≈] form
        ([initial_leg_id]) and says plainly that the strict form fails.

      * CONVERSION (different cause; and an earlier draft of this file
        wrote the statement with [initial_Cones_Terminal] applied to no
        arguments, so its [Fail] fired on a MISSING ARGUMENT rather than
        on the refutation -- a false guard, caught by strip-verifying the
        failure KIND) -- the WHOLE-RECORD identity
        [Limit_Cones … = initial_Limit] is refuted, although the CONE
        components agree by [eq_refl] (that is the target's shipped
        [initial_Cones_strict]).  What differs is the rebuilt universal
        property, not the data.

      * FORMABILITY (universe), THREE of them -- the index category's
        hom-and-proof universes get identified with the ambient
        category's, and an earlier draft of this file blamed [IsALimit]
        ALONE on the strength of an [ACone] control.  That inference was
        invalid.  With J's levels declared apart, [ACone c F] and [Cone F]
        are formable, but [cone_leg N x]
        (Structure/Limit/Preservation.v:108), [IsLimitCone N] (:166) AND
        [IsALimit F c] (Structure/Limit.v:129) are all rejected with the
        same message.  Two of the three donors ARE cone vocabulary, so the
        control rules out [ACone]/[Cone] and nothing further; all three
        rejections are pinned below.  None of the three carries universe
        annotations, so this stays a repairable annotation defect of the
        family this repo has met before, NOT inherent content, and not
        claimed unavoidable here.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Structure.Limit.Initial.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the leg at the initial object is not [id] *)

Section LegAtInitial.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_initial_leg_is_id :
  initial_leg I F (@initial_obj J I) = id := eq_refl.

(* Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here. *)
Check (initial_leg_id I F).
Check (initial_leg I F).
Check (@initial_obj J I).

End LegAtInitial.

(** ** Negative 2 (CONVERSION, different cause): the whole-record identity *)

Section WholeRecord.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_limit_cones_record :
  @Limit_Cones J C F (initial_Cones_Terminal I F)
    = initial_Limit I F := eq_refl.

(* Positive controls.  The CONE components DO agree by [eq_refl] -- that is
   the target's own Example -- so what fails is the rebuilt universal
   property, not the data. *)
Check initial_Cones_strict.
Check (@Limit_Cones J C F).
Check (initial_Limit I F).
Check (initial_Cones_Terminal I F).

End WholeRecord.

(** ** Negative 3 (FORMABILITY, universe): IsALimit identifies J's levels

    A DIFFERENT KIND from 1 and 2. *)

Section UniverseIdentification.

Universe jo jh jp co ch cp.
Constraint jh < jp.

Context (J : Category@{jo jh jp}) (C : Category@{co ch cp})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

(* Controls: these two pieces of cone vocabulary ARE formable with J's hom
   and proof levels declared APART.  They rule out [ACone] and [Cone] as
   the donor -- and nothing more, which is exactly the correction this
   file records. *)
Check (ACone c F).
Check (Cone F).

(** ** Negative 4 (FORMABILITY, universe): cone_leg identifies them too

    Same KIND as negatives 3 and 5, different CONSTANT.  This is the one
    that refutes the earlier draft's attribution: [cone_leg] is cone
    vocabulary and is rejected at the same levels.  It is also the donor
    this development meets FIRST -- [initial_med]'s body is
    `cone_leg N initial_obj`, and [initial_med] already displays
    `u0 = u2` while its type mentions no [IsALimit] at all. *)

Fail Check (cone_leg N x).

(** ** Negative 5 (FORMABILITY, universe): IsLimitCone likewise *)

Fail Check (IsLimitCone N).

End UniverseIdentification.

(* Controls naming the two constants of negatives 4 and 5. *)
Check @cone_leg.
Check @IsLimitCone.

(* Control naming [IsALimit] itself.  The rename simulation over the
   constants in the NEGATIVES found it named by no control -- it occurred
   only inside the Fail above -- so that negative would have gone
   vacuously green on a rename.  Recorded rather than quietly added. *)
Check @IsALimit.

Section UniverseIdentification2.

Universe jo2 jh2 jp2 co2 ch2 cp2.
Constraint jh2 < jp2.

Context (J : Category@{jo2 jh2 jp2}) (C : Category@{co2 ch2 cp2})
        (F : J ⟶ C) (c : C).

Fail Check (IsALimit F c).

End UniverseIdentification2.

(** ** Applied controls for negatives 3-5

    [Check @IsALimit] above is name resolution ONLY; it cannot show that
    the three negatives fire on the CONSTRAINT rather than on some
    unrelated defect in how they are written.  These do: the SAME three
    applications, at levels DECLARED but deliberately NOT constrained
    apart, all elaborate. *)

Section UniverseControl.

Universe jo3 jh3 jp3 co3 ch3 cp3.

Context (J : Category@{jo3 jh3 jp3}) (C : Category@{co3 ch3 cp3})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

Check (IsALimit F c).
Check (cone_leg N x).
Check (IsLimitCone N).

End UniverseControl.

(** ** Controls for the delivered results *)

Check initial_leg.
Check initial_cone.
Check initial_med.
Check initial_med_commutes.
Check initial_med_unique.
Check initial_IsLimitCone.
Check initial_IsALimit.
Check limiting_iff_initial_leg_iso.
Check terminal_inj.
Check terminal_cocone.
Check terminal_IsColimitCocone.
Check terminal_IsAColimit.
Check colimiting_iff_terminal_inj_iso.
Check One_Initial.
Check point_IsALimit.
Check point_Cones_strict.
Check Ordinal_Succ_Terminal.
Check ordinal_succ_IsAColimit.
Check Omega_Initial.
Check Omega_no_Terminal.

(** ** Non-vacuity controls *)

Check point_Sets_med.
Check point_Sets_separates.
Check ordinal_omega_nonconstant.
Check ord_top_neq_bot.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [initial_leg], [initial_obj]
      Negative 2: [Limit_Cones], [initial_Cones_Terminal], [initial_Limit]
      Negative 3: [IsALimit]
      Negative 4: [cone_leg]
      Negative 5: [IsLimitCone]

    That is EIGHT.  An earlier draft of this file scored 7/7 by listing
    [ACone] under negative 3 -- but [ACone] occurs in NO [Fail] here; it
    is a control, and including it inflated the denominator in the very
    sentence that denied padding.  It is dropped.  All eight are named by
    a positive control above, so renaming any one breaks this file rather
    than turning its negative vacuously green.  Score: 8/8, counted
    rather than recalled. *)

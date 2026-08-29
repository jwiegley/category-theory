Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Discrete.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.
Require Import Category.Instance.Grp.Completion.
Require Import Category.Instance.CMon.Grothendieck.
Require Import Category.Instance.Sets.Pointed.Free.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(** * Boundary probe for issue #312 (maclane:III.1:ex3)

    Each delivered file carries its own [Fail] probes.  Those guard their
    measurements from INSIDE, which is exactly what a whole-file rename
    cannot test: rename a definition and its in-file [Fail] renames with
    it, so the guard goes vacuously green.  This file restates the
    cross-file boundaries from OUTSIDE, each against a positive control
    that NAMES the same constants, so renaming any of them breaks this
    file loudly.

    Negatives are grouped BY KIND and kept lexically apart.  Each was
    stripped of its [Fail] once and the resulting error read; the kind
    recorded is the kind that actually fired. *)

(** ** Positive controls

    Every constant named in a negative below is also named here outside
    any [Fail], so a rename cannot silently vacate a guard. *)

Check @Top_Discrete.
Check @Top_Forget.
Check @discrete_universal.
Check @disc_unit.
Check @abelianize_left.
Check @Abelianization_Functor.
Check @abelianize_adjunction.
Check @abelianize_adjunction_via_transform.
Check @completion_adjunction.
Check @grothendieck_adjunction.
Check @free_pointed_adjunction.
Check @free_rng_ab_universal_arrow.

(** ** Positive controls: the four rows of Mac Lane §III.1 Exercise 3

    Row (b) is discharged by #400's Instance/Rng/Free.v and is CITED
    here rather than rebuilt, which is what that issue's dependency note
    on #312 requires. *)

Example row_a_abelianization : Grp ⟶ Ab := abelianize_left.
Example row_b_free_ring (A : Ab) : UniversalArrow A Rng_Forget_Ab :=
  free_rng_ab_universal_arrow A.
Example row_d_basepoint : Sets ⟶ PointedSets := FreePointed.

(** ** FORMABILITY negative: the discrete adjunction cannot be packaged

    This is #312's one genuinely obstructed row, and the obstruction is
    PRE-EXISTING, not introduced here: Instance/Top/Forgetful.v:70-83
    records that a functor out of [Top] lands in a lifted [Sets] while a
    functor into [Top] must come from the unlifted one, so an
    [Adjunction] record "would need both functors to share ONE Sets, at
    levels o and h simultaneously, with o < h: the packaged triple is
    unformable at every universe assignment."

    The controls above show BOTH functors exist and are nameable, so the
    negative is about the packaging and not about a missing constant.
    Stripped, it reports a [Functor] universe mismatch between the two
    instantiations of [Sets] — a FORMABILITY failure, not a conversion
    one.  Instance/Top/Discrete.v therefore delivers the universal
    property written out ([discrete_universal]) and the unit
    ([disc_unit]) rather than a packaged record, and claims nothing more. *)

Fail Check (Top_Discrete ⊣ Top_Forget).

(** ** CONVERSION negative: the produced left adjoint is not the
       pre-existing functor on the nose

    [LeftAdjointFunctorFromUniversalArrows] PRODUCES a left functor, so
    [abelianize_adjunction] is stated against [abelianize_left] rather
    than against the pre-existing [Abelianization_Functor].  The two
    agree on objects definitionally and on arrows up to [≈]
    (Instance/Grp/Abelianize.v's [abelianize_left_obj] and
    [abelianize_left_iso]), but they are NOT the same functor record —
    the law fields are rebuilt.  Pinned so that a later edit cannot
    quietly assert the stronger identification. *)

Fail Example probe_left_is_pre_existing :
  abelianize_left = Abelianization_Functor := eq_refl.

(** ** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #312,
    so a broken [Fail] mechanism would be visible here rather than
    silently passing every negative above.  Deliberately scope-free: a
    numeral would risk failing on a missing scope delimiter instead of on
    the proposition. *)

Fail Example probe_312_instrument : (true = false) := eq_refl.

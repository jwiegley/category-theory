Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Boundary probes for the quotient module and the quotient ring

    Companion to Instance/Mod/Quotient.v,
    Instance/Mod/Quotient/Isomorphism.v and Instance/Rng/Quotient.v
    (issue #314, Mac Lane §III.1 Exercises 5 and 6).  Those files make
    four strength claims whose negative side is a CONVERSION boundary;
    a measurement recorded only in prose would not be noticed by a
    refactor, so it is pinned here.  **If the [Fail] commands below stop
    being rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  Every negative is a [Fail Definition ... := eq_refl] and not a
    [Fail Example ... : T.]; the latter guards only that the STATEMENT
    elaborates and reports "The command has not failed!" when the
    statement is fine and only the proof would have been rejected.

    The instrument itself was checked (wrapping [Fail] around a
    succeeding command aborts compilation with "The command has not
    failed!"), and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended conversion failure
    and not a syntax, scope or resolution error.  The observed errors
    are recorded beside each probe.

    THE IMPORT LIST IS THE UNION OF THE TARGETS', IN THEIR ORDER, and
    that is deliberate rather than tidy: a short prefix is exactly what
    makes a probe pass vacuously, by turning a conversion rejection into
    an elaboration error that [Fail] swallows just as happily. *)

(** ** (1) The two quotient relations are not convertible

    Instance/Mod/Quotient.v reconciles Instance/Mod.v's [RModQuotient]
    with [QuotientMod (ImageSubmod f)] by the BICONDITIONAL
    [rmod_quotient_relations_agree] and by an isomorphism whose legs are
    the identity on elements.  The header says the two relations are not
    convertible -- [{ a & x ≈ y + f a }] against [{ a & x + (-y) ≈ f a }]
    -- and this is that measurement.

    Stripped, the first probe reports
      "(cannot unify "ab_coset_eq f x y" and
        "mquot_rel (ImageSubmod f) x y")"
    -- a genuine conversion failure between the two [sigT] types.  (The
    printed form drops [rm_hom], which is a coercion.) *)

Section RelationBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).
Context (x y : carrier (cmon_setoid N)).

Fail Definition probe_relations_convertible :
  ab_coset_eq (rm_hom f) x y = mquot_rel (ImageSubmod f) x y := eq_refl.

(* POSITIVE CONTROL at the same arguments: the two relations DO agree,
   and the biconditional that says so is available here. *)
Definition control_relations_agree :
  ab_coset_eq (rm_hom f) x y ↔ mquot_rel (ImageSubmod f) x y :=
  rmod_quotient_relations_agree f x y.

(* SECOND POSITIVE CONTROL: an [eq_refl] of the same SHAPE that does
   hold, so the probe above is not merely rejecting all [eq_refl]s
   between relation types.  Membership in the image submodule IS the
   sigma it is defined as. *)
Definition control_image_mem :
  smod_mem (ImageSubmod f) x
    = { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ x }
  := eq_refl.

End RelationBoundary.

(** ** (2) ...nor are the two quotient objects Leibniz-equal

    [RModQuotient_is_quotient_by_image] is an ISOMORPHISM in [RMod R],
    not an equality of records; the carriers agree but the setoids do
    not, so nothing stronger is available.

    Stripped, this reports a conversion failure between the two
    [RModObject] records. *)

Section ObjectBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Fail Definition probe_objects_equal :
  RModQuotient f = QuotientMod (ImageSubmod f) := eq_refl.

(* POSITIVE CONTROL: the CARRIERS do agree on the nose -- both are N's
   -- so what the probe measures is the setoid and not the carrier. *)
Definition control_carriers_agree :
  carrier (cmon_setoid (RModQuotient f))
    = carrier (cmon_setoid (QuotientMod (ImageSubmod f))) := eq_refl.

(* SECOND POSITIVE CONTROL: the isomorphism that IS available. *)
Definition control_objects_iso :
  RModQuotient f ≅[RMod R] QuotientMod (ImageSubmod f) :=
  RModQuotient_is_quotient_by_image f.

End ObjectBoundary.

(** ** (3) The first isomorphism theorem's triangle is not [eq_refl]

    Instance/Mod/Quotient/Isomorphism.v says both LEGS of the comparison
    are the two mediators by convertibility, and that the boundary which
    does NOT hold strictly is the mediator's TRIANGLE, which is `≈` and
    not Leibniz.  Both halves are pinned here, the positive one first.

    Stripped, the probe reports a conversion failure between the
    composite [RModHom] and [mod_image_cores f]: the composite's
    underlying map is [Basics.compose] of two maps, which is not the
    same TERM as the corestriction even though it sends every element to
    the same value. *)

Section TriangleBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(* POSITIVE CONTROLS: both legs are the two mediators, strictly. *)
Definition control_to_is_mediator :
  to (mod_first_isomorphism_theorem f)
    = mquot_med (KernelSub f) (mod_image_elem f) := eq_refl.

Definition control_from_is_mediator :
  from (mod_first_isomorphism_theorem f)
    = mod_image_med f (mquot_elem (KernelSub f)) := eq_refl.

Fail Definition probe_triangle_strict :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    = mod_image_cores f := eq_refl.

(* ...and the `≈` form, which is what the file states. *)
Definition control_triangle_equiv :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    ≈ mod_image_cores f :=
  mod_first_isomorphism_triangle f.

End TriangleBoundary.

(** ** (4) Quotienting a ring by the total ideal is not the zero ring
       on the nose

    Instance/Rng/Quotient.v states [rquot_total_one_is_zero] -- that
    1 ≈ 0 in R/R -- and says the quotient is the zero ring "up to the
    identification [rquot_total_collapses] supplies".  That wording is
    deliberate: the carrier of R/R is R's, not [poly_unit], so no
    equality of [RingObject]s is available and none is claimed.

    Stripped, this reports a conversion failure between the two
    [RingObject] records; the carriers alone already differ. *)

Section ZeroRingBoundary.

Context {R : RingObject}.

Fail Definition probe_total_is_zero_ring :
  QuotientRing (TotalIdeal R) = Zero_Ring := eq_refl.

(* POSITIVE CONTROL: what IS true, and strictly -- the carrier of the
   quotient is R's own. *)
Definition control_total_carrier :
  carrier (rig_setoid (QuotientRing (TotalIdeal R)))
    = carrier (rig_setoid R) := eq_refl.

(* SECOND POSITIVE CONTROL: the `≈`-level statement the file makes. *)
Definition control_total_one_is_zero :
  rig_one (QuotientRing (TotalIdeal R))
    ≈ rig_zero (QuotientRing (TotalIdeal R)) :=
  rquot_total_one_is_zero R.

End ZeroRingBoundary.

(** ** Positive controls for the two universal elements

    Not boundaries, but guards: these are the [eq_refl] claims the two
    principal files make about their own packaging, restated here so
    that a change to [AUniversalElement] which silently rebuilt the
    mediators would break this file too. *)

Definition control_mod_universal_elem {R : RingObject} {M : RModObject R}
  (S : Submodule M) :
  `1 (@aue_elem _ (MKillsFunctor S) (QuotientMod S)
        (mquot_universal_element S)) = mquot_proj S := eq_refl.

Definition control_rng_universal_elem {R : RingObject} (I : Ideal R) :
  `1 (@aue_elem _ (RKillsFunctor I) (QuotientRing I)
        (rquot_universal_element I)) = rquot_proj I := eq_refl.

(* And the ring-side reading of a left ideal's relation as the two-sided
   one, which Instance/Rng/Quotient.v claims by convertibility. *)
Definition control_lquot_is_rquot {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y := eq_refl.

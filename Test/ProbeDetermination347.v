(* The target's FULL import list is mirrored below, deliberately.  A short
   prefix is what makes a probe pass vacuously: with [Category.Instance.Sets]
   missing, the negative below failed on "Illegal application" because the
   [SetoidMorphism] coercion was out of scope, and with
   [Category.Theory.Isomorphism] missing it failed on "reference [to] not
   found" -- in both cases certifying nothing about conversion. *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Determination.

Generalizable All Variables.

(** * Boundary probe for issue #347 (maclane:IV.1:thm2, awodey:9.2:cor5)

    Adjunction/Determination.v measures one strength boundary and diagnoses
    it, but ships no [Fail] of its own, so the measurement is unguarded there.
    This file pins it from OUTSIDE the target — an in-file [Fail] renames in
    lockstep with its own definition and so cannot detect a rename — with
    positive controls naming the same constants.

    The diagnosis being guarded is that the boundary is DONOR OPACITY and that
    the cause DISCRIMINATES: [coarrow] and [coarrow_obj] of the very same
    couniversal arrow DO reduce to [eq_refl], because they are transparent
    projections of the transparent [couniversal_arrow_from_UMP], while the
    MEDIATOR does not, because it is read out of [ump_couniversal_arrows]
    whose primal donor [ump_universal_arrows] (Theory/Universal/Arrow.v:139)
    is closed with [Qed].  Controls and negative therefore sit on the SAME
    object, which is what makes the attribution meaningful rather than a
    guess about opacity in general. *)

Section Probe.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(** ** Positive controls

    Every constant named in the negative is also named here outside any
    [Fail], so a rename cannot silently vacate the guard.  The first two are
    the discriminating half of the diagnosis: on the SAME couniversal arrow,
    the object and the arrow DO reduce. *)

Example probe_ctl_obj (c : C) :
  coarrow_obj (adj_counit_couniversal A c) = U c := eq_refl.

Example probe_ctl_arrow (c : C) :
  coarrow (adj_counit_couniversal A c) = @counit C D F U A c := eq_refl.

Check @adj_counit_couniversal.
Check @adj_counit_couniversal_med.
Check @ump_couniversal_arrows.

(* This control is what makes the negative below non-vacuous, and it was
   MISSING on the first cut: [unique_obj], [to] and the [adj[_]] notation
   appeared ONLY inside the [Fail], so renaming any of them would have made
   it fail on "reference not found" while this file still compiled -- the
   very false-pass mode the header above describes.  Stating the lemma at
   its true strength here names all three outside the [Fail]. *)
Example probe_ctl_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    ≈ to adj[A] f := adj_counit_couniversal_med A c d f.

(** ** CONVERSION negative: the mediator does not reduce

    [adj_counit_couniversal_med] is stated at [≈] and not at [=].  Stripped,
    this reports a genuine unification failure between the mediator and the
    forward transpose, not a missing reference. *)

Fail Example probe_med_strict (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    = to adj[A] f := eq_refl.

End Probe.

(** ** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #347, so a
    broken [Fail] mechanism would be visible here rather than silently passing
    the negative above.  Scope-free deliberately: a numeral would risk failing
    on a missing scope delimiter instead of on the proposition. *)

Fail Example probe_347_instrument : (true = false) := eq_refl.

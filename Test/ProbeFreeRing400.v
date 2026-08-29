Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(** * Boundary probe for issue #400 (maclane:IV.8:ex2)

    Instance/Ab/Free.v, Instance/Mon/Free.v and Instance/Rng/Free.v each
    carry their own [Fail] probes.  Those guard their measurements from
    INSIDE, which is exactly what a whole-file rename cannot test: rename
    a definition and its in-file [Fail] renames with it, so the guard goes
    vacuously green.  This file restates the three cross-file boundaries
    from OUTSIDE, each against a positive control that NAMES the same
    constants, so that renaming any of them breaks this file loudly.

    Negatives are grouped BY KIND and the groups are kept lexically
    apart.  Each was stripped of its [Fail] once and the resulting error
    read, and the kind recorded here is the kind that actually fired. *)

(** ** Positive controls

    Every constant named in a negative below is also named here, outside
    any [Fail], so a rename cannot silently vacate a guard. *)

Check @free_ring_via_ab.
Check @free_ring_via_mon.
Check @free_ring_composites_agree.
Check @RngUnderlyingAb.
Check @RngUnderlyingMon.
Check @free_ring_via_mon_adjunction.
Check @free_ring_via_mon_adjunction_ab.
Check @FreeAb.
Check @free_ab_adjunction.
Check @FreeMonSets.
Check @free_mon_sets_adjunction.
Check @FreeRngAb.
Check @free_rng_ab_adjunction.
Check @MonoidRingFunctor.
Check @zmring_adjunction.
Check @Rng_Forget_Ab.
Check @Rng_Forget_Mon.
Check @Rig_Forget_Mon.
Check (Rng_Forget_Mon : Rng ⟶ MonSets).

(** ** Positive controls: what DOES hold strictly

    The two underlying-set functors of the two routes agree on objects
    and on arrows definitionally.  These are the facts that make the
    field-copying retype below possible, so they are controls for the
    conversion negatives that follow. *)

Example probe_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example probe_fmap_agree (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(** ** CONVERSION negatives

    Agreement on [fobj] and [fmap] does NOT extend to the functor
    records, nor to the [Adjunction] record built over them. *)

(* The two right adjoints are not the same record: the law fields are
   [Compose]'s obligations at different arguments. *)
Fail Example probe_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(* And the monoid route's adjunction cannot simply be ASCRIBED against
   the abelian route's right adjoint, even though every field type is
   convertible: the [Adjunction] type mentions the right adjoint as a
   whole record.  This is precisely why Instance/Rng/Free.v rebuilds it
   field by field as [free_ring_via_mon_adjunction_ab] rather than
   transporting along a natural isomorphism. *)
Fail Definition probe_ascribe_mon_at_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb
  := free_ring_via_mon_adjunction.

(** ** FORMABILITY negative

    A different KIND: not a failed conversion but a universe
    inconsistency.  The monoid route is confined to rings whose homs live
    in [Set], because [Rig_Forget_Mon]'s source is [Rig@{u Set}]; the
    abelian route is not.  What the negative fires on is the donor's
    literal [Set] meeting the RIGID declared level [puh]: unification
    cannot set a rigid level to [Set], and deleting the [Constraint]
    below leaves the negative failing with the identical message
    ("Cannot enforce Set = puh"), so the [Constraint] is INERT for the
    negative and it would be wrong to say the negative fires on it.  Its
    real work is on the POSITIVE control, which without it would not say
    "elaborates strictly above [Set]".  The control rules out the
    ascription shape, which is all a control can rule out. *)

Section ProbeMonRouteSetPin.

Universe puo puh.
Constraint Set < puh.

Check (Rng_Forget_Ab : Rng@{puo puh} ⟶ Ab).

Fail Check (Rng_Forget_Mon : Rng@{puo puh} ⟶ MonSets).

End ProbeMonRouteSetPin.

(** ** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #400,
    so that a broken [Fail] mechanism would be visible here rather than
    silently passing every negative above. *)

Fail Example probe_free_ring_instrument : (true = false) := eq_refl.

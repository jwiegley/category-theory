Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(** * Probe: the ring adjoint-functor-theorem applications are
      non-circular, and here they are at a named set and a named group

    The import list above is Instance/Rng/AFT.v's own, verbatim, plus that
    file itself; a shorter prefix is what makes a probe pass for no reason.

    WHAT THIS FILE GUARDS.  Until the PR "algebraic carriers are sets"
    (2026-09-17), [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] consumed
    [solution_set_of_adjunction] applied to the very adjunctions they were
    meant to produce, and Instance/Rng/AFT.v's header said so at length.
    They now consume solution sets built from the free-ring TERM MODEL by
    [Prop]-valued congruences.  That change is invisible to the type -- the
    two readings inhabit the same statement -- so nothing in the build
    would notice it being reverted.  This file notices: the [eq_refl]
    readbacks below name the congruence index, and the [Fail] pins that the
    new solution set is not the old singleton.

    DISCIPLINE.  Every negative is paired with a positive control naming
    the same library constants; the instrument was checked; each negative
    was re-run with its guard stripped in a copy of this whole file so the
    refusal kind could be read rather than guessed.  The kinds recorded are
    CONVERSION (two) beside the instrument check, whose refusal is a
    missing NAME. *)

(** ** Instrument check *)

Fail Check zzz_no_such_constant_rng_aft.

(** ** Positive controls *)

Check @RngCongIdx.
Check @IsRngCongruence.
Check @QRng.
Check @QRng_insert.
Check @rng_ker.
Check @rng_ker_med.
Check @Rng_Forget_Ab_solution_set_prop.
Check @Rng_Forget_solution_set_prop.
Check @free_rng_ab_via_GAFT.
Check @free_ring_via_GAFT.

(* The circular readings are KEPT and are still checkable; they are the
   comparison, not the delivery. *)
Check @Rng_Forget_Ab_solution_set_from_adjunction.
Check @Rng_Forget_solution_set_from_adjunction.
Check @free_rng_ab_via_GAFT_from_adjunction.
Check @free_ring_via_GAFT_from_adjunction.

(** ** The index readbacks: WHICH solution set each application consumes *)

Section IndexReadbacks.

Context (A : Ab).
Context (X : Sets).

(* The [Ab] half: the index is the congruence type on the free-ring terms
   over [A], and the objects are the quotients. *)
Example prng_ab_index :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = RngCongIdx A := eq_refl.

Example prng_ab_obj (i : RngCongIdx A) :
  sol_obj (Rng_Forget_Ab_solution_set_prop A) i = QRng (`1 i) (`2 i)
  := eq_refl.

(* The [Sets] half takes the SAME index, over the free abelian group on
   [X] -- the direct route, not a composite of two adjunctions. *)
Example prng_sets_index :
  sol_index (Rng_Forget_solution_set_prop X)
    = RngCongIdx (FreeAbObject X) := eq_refl.

Example prng_sets_obj (i : RngCongIdx (FreeAbObject X)) :
  sol_obj (Rng_Forget_solution_set_prop X) i = QRng (`1 i) (`2 i)
  := eq_refl.

(* And the circular ones are still the singleton, which is the contrast. *)
Example prng_circular_index :
  sol_index (Rng_Forget_Ab_solution_set_from_adjunction A) = poly_unit
  := eq_refl.

End IndexReadbacks.

(** ** NEGATIVE 1 (CONVERSION): the new solution set is not the old one

    If a later edit points [Rng_Forget_Ab_solution_set_prop] back at
    [solution_set_of_adjunction], this line stops refusing.  The control is
    [prng_circular_index] above, which IS [eq_refl] for the old one. *)

Fail Example prng_n1_prop_index_is_not_singleton (A : Ab) :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = poly_unit := eq_refl.

(** ** NEGATIVE 2 (CONVERSION): the two applications are different terms

    [free_rng_ab_via_GAFT] and [free_rng_ab_via_GAFT_from_adjunction]
    inhabit the same type and are NOT the same term.  [GAFT] is [Qed], so
    neither reduces; what this pins is that the two are not syntactically
    identified, which is what would happen if one were defined as the
    other. *)

Fail Example prng_n2_applications_differ :
  free_rng_ab_via_GAFT = free_rng_ab_via_GAFT_from_adjunction := eq_refl.

(** ** THE PAYOFF: both applications at named objects

    [ring_ab Int_Ring] is the integers as an abelian group;
    [nat_setoid_object] and [bool_setoid_object] are named sets.  Before
    this PR these lines would have exhibited a free ring obtained from an
    adjunction that was assumed in order to obtain it. *)

Section ConcreteWitnesses.

Definition prng_ZAb : Ab := ring_ab Int_Ring.

(* The free ring on the integers as an abelian group. *)
Check (`1 free_rng_ab_via_GAFT prng_ZAb).
Check (Rng_Forget_Ab_solution_set_prop prng_ZAb).
Check (free_rng_ab_via_GAFT_comparison prng_ZAb).
Check (free_rng_ab_via_GAFT_unit prng_ZAb).

(* The free ring on a named set, twice. *)
Check (`1 free_ring_via_GAFT nat_setoid_object).
Check (`1 free_ring_via_GAFT bool_setoid_object).
Check (Rng_Forget_solution_set_prop nat_setoid_object).
Check (free_ring_via_GAFT_comparison nat_setoid_object).
Check (free_ring_via_GAFT_unit nat_setoid_object).

(* And the congruence index at a named object, which is the thing that
   made the whole construction fit. *)
Check (RngCongIdx prng_ZAb).
Check (RngCongIdx (FreeAbObject nat_setoid_object)).

End ConcreteWitnesses.

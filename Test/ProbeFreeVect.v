(** * Boundary probe: what is and is not definitional in the free module
      and the free vector space.

    Companion to Instance/Mod/Free.v and Instance/Vect/Free.v (Mac Lane
    §III.1 and §IV.1, Riehl §4.0).  Those files make several strength
    claims — some things hold at Leibniz [=] or by [eq_refl], others only
    up to [≈] — and a strength claim that lives only in a header is a
    claim nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeFreeGroupoid.v: **if the [Fail]
    commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from under
    it.  So each negative probe is paired with a positive control which
    must SUCCEED, and the controls are the headline claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not failed!"
    and aborts compilation, so [Fail] here is not a no-op.  Each negative
    below was also run with the [Fail] stripped, and the error confirmed
    to be a genuine unification failure rather than a syntax, scope or
    universe error; the diagnoses are recorded beside each probe.

    The three negatives and their causes:

      - The COUNIT of the free-forgetful adjunction does not compute.  It
        is [from adj id], i.e. [unique_obj (ump_universal_arrows …)], and
        [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque,
        so no reduction is available.  The UNIT is on the other side of
        that boundary and does compute, which is the positive control
        [probe_unit_computes]; Instance/Mod/Free.v says so in terms and
        states the counit only up to [≈]
        ([free_module_counit_evaluates]).

      - The ACTION OF THE FREE FUNCTOR ON AN ARROW does not compute
        either, and for the same reason:
        [LeftAdjointFunctorFromUniversalArrows] defines [fmap] as the
        unique universal factorization, not by a formula.  That it
        relabels generators is therefore a theorem
        ([free_module_fmap_generators], the positive control here) rather
        than a computation — which is precisely why
        [free_module_naturality_in_set] needs a proof at all, while its
        sibling [free_module_naturality_in_module] closes by
        [reflexivity].

      - THE QUOTIENT IS GENUINE.  Commutativity of a formal sum is a step
        of the generated congruence [fv_eq] and not a definitional
        equality of the underlying inductive: the two formal sums
        e_true + e_false and e_false + e_true are distinct terms of
        [FVTerm].  The positive control is [fe_comm], which inhabits
        [fv_eq] between exactly those two terms.  This is what makes the
        setoid presentation of Instance/Mod/Free.v a quotient rather than
        a renaming, and it is why the linear extension needs
        [fv_eval_respects] before it is a morphism at all. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files. *)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(** ** Positive control: the unit computes

    The unit is [fmap[U] id ∘ arrow], and both factors reduce, so the
    unit of the free-forgetful adjunction IS the basis insertion on the
    nose. *)
Example probe_unit_computes (x : carrier TwoGens) :
  free_module_unit Int_Ring TwoGens x = zgen x := eq_refl.

(** ** Positive control: the linear extension computes

    The mediator is a [Fixpoint] on formal expressions, so evaluating it
    on a closed expression reduces all the way to a value of the target
    module's carrier. *)
Example probe_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

(** ** Negative: the counit does not compute

    Stripped of [Fail] this reports that [eq_refl] cannot unify the
    counit's value at a generator with the generator, the counit being
    [unique_obj] of a [Qed]-opaque uniqueness proof.  The [≈] statement
    IS available and is the control immediately below. *)
Fail Example probe_counit_computes :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) = 3%Z := eq_refl.

Example probe_counit_up_to_equiv :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) ≈ 3%Z.
Proof. exact (free_module_counit_generator Int_Ring Int_RMod 3%Z). Qed.

(** ** Negative: the free functor's action on an arrow does not compute

    Taken at the identity of the generating setoid, where a formula-based
    definition would reduce immediately. *)
Fail Example probe_fmap_computes (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    = zgen x := eq_refl.

Example probe_fmap_up_to_equiv (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    ≈ zgen x.
Proof.
  exact (@free_module_fmap_generators Int_Ring TwoGens TwoGens
           (@id Sets TwoGens) x).
Qed.

(** ** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control. *)
Fail Example probe_plus_comm_definitional :
  zplus (zgen true) (zgen false) = zplus (zgen false) (zgen true) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  fv_eq (zplus (zgen true) (zgen false)) (zplus (zgen false) (zgen true)) :=
  fe_comm _ _.

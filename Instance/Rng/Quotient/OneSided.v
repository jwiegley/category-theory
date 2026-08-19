Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * A one-sided ideal does not give a quotient ring

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
    Exercise 6 (printed p. 59) [maclane:III.1:ex6]: the quotient of a
    ring is taken by a TWO-SIDED ideal.  Instance/Rng/Quotient.v carries
    the construction and explains why both absorption laws are consumed;
    this file proves that neither can be dropped, by exhibiting a LEFT
    ideal for which the quotient relation is not a congruence for
    multiplication.

    THIS IS THE RING-LEVEL COUNTERPART of
    Instance/Grp/Quotient.v's [S3_refl_sub_not_normal], which refutes
    the normality CLOSURE condition for a particular subgroup.  Here
    [ut2_left_ideal_not_mul_congruence] refutes the CONGRUENCE itself,
    which is the property [rquot_rel_mul] establishes and the one the
    construction actually consumes; [ut2_e11_not_right_absorbing]
    separately refutes the dropped closure condition, so both readings
    are covered.

    READ THE COMPARISON PRECISELY.  An earlier draft of this header said
    the ring statement was stronger in shape because the group side left
    "and therefore the quotient would not be well defined" to the
    reader.  That was wrong, and an audit caught it: the group side
    ALREADY carries a congruence-level refutation, namely
    Instance/Grp/Congruence.v:1009's [S3_refl_sub_no_congruence] -- at
    the same subgroup, landed by #301 -- so no inference is left
    implicit there either.  What is actually different is narrower and
    is all that is claimed: the refutation here is DIRECT, where the
    group one is obtained through [congruence_iff_normal]; and it lands
    on the MULTIPLICATION congruence specifically, which is the clause
    one-sidedness is unable to supply.

    THE WITNESS.  [UT2] (Instance/Rng/Algebras/Associative.v:527) is the
    ring of upper-triangular 2×2 integer matrices, carried as triples
    (a, b, c) for [[a, b], [0, c]], and that file proves it
    non-commutative ([UT2_not_commutative]).  It is NOT the tree's only
    non-commutative [RingObject] -- Instance/Rng/MonoidRing.v:778's
    [zmring_not_commutative] exhibits a monoid ring that is not
    commutative, although it proves that by mapping INTO [UT2] -- but it
    is the smallest, and the one whose elements compute, being integer
    triples.  The left ideal is ℤ·E₁₁, the multiples of
    the matrix unit E₁₁ = [[1, 0], [0, 0]]:

        x · (a, 0, 0) = (a'·a, 0, 0)   -- absorbed on the left,
        (1, 0, 0) · (0, 1, 0) = (0, 1, 0)   -- NOT absorbed on the right.

    Non-commutativity is not merely convenient here, it is necessary:
    over a commutative ring the two absorption laws are the same
    statement, so no commutative witness could exist.  That is why this
    file must reach for [UT2] and why it is a separate file --
    Instance/Rng/Algebras/Associative.v requires Instance/Mod.v and the
    associative-algebra tower, and no consumer of quotient rings should
    inherit that dependency.

    WHAT IS NOT CLAIMED.  Nothing here says a left ideal gives no
    quotient of any kind: ℤ·E₁₁ is in particular an additive subgroup, so
    UT2/ℤ·E₁₁ is a perfectly good quotient ABELIAN GROUP, and the
    left-module structure survives as well.  What is refuted is exactly
    that the ring MULTIPLICATION descends.  Nor is the RIGHT-sided
    mirror stated: the symmetric counterexample (a right ideal that is
    not a left one) would need the transpose witness and adds nothing,
    and the header says so rather than leaving a reader to wonder. *)

(** ** ℤ·E₁₁ as a left ideal of UT2 *)

Definition ut2_col1 (x : ut2) : Type := { a : Z & x = (a, 0, 0)%Z }.

Program Definition E11Left : LeftIdeal UT2 := {| lidl_mem := ut2_col1 |}.
Next Obligation.
  intros x y Hxy [a Ha]; unfold ut2_eqT in Hxy.
  exists a; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [a Ha] [b Hb].
  inversion Ha; inversion Hb; subst.
  exists (a + b)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [a Ha].
  inversion Ha; subst.
  exists (r1 * a)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

(* Non-vacuity of the left ideal itself: E₁₁ is in it and is not zero. *)
Theorem E11Left_nontrivial :
  lidl_mem E11Left ut2_e11 * (ut2_e11 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(** ** It is NOT a right ideal *)

(* E₁₁ · E₁₂ = E₁₂, which has a nonzero entry off the first column. *)
Example ut2_e11_times_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Theorem ut2_e11_not_right_absorbing :
  lidl_mem E11Left (rig_mul UT2 ut2_e11 ut2_e12) → False.
Proof. intros [a Ha]; discriminate Ha. Qed.

(* So the fifth field of [Ideal] is not derivable from the other four:
   no [Ideal UT2] has [E11Left]'s membership predicate. *)
Theorem E11Left_is_not_an_Ideal :
  { I : Ideal UT2 & ∀ x, idl_mem I x ↔ lidl_mem E11Left x } → False.
Proof.
  intros [I HI].
  apply ut2_e11_not_right_absorbing.
  apply (fst (HI _)).
  apply idl_absorb_r.
  apply (snd (HI _)).
  exists 1%Z; reflexivity.
Qed.

(** ** ...and the quotient relation is not a congruence for
       multiplication

    The witnesses: E₁₁ ~ 0 (their difference is E₁₁, which is in the
    ideal) and E₁₂ ~ E₁₂, yet E₁₁·E₁₂ = E₁₂ is not congruent to
    0·E₁₂ = 0. *)

Lemma ut2_e11_rel_zero : lquot_rel E11Left ut2_e11 ut2_zero.
Proof. exists 1%Z; reflexivity. Qed.

Lemma ut2_e12_rel_self : lquot_rel E11Left ut2_e12 ut2_e12.
Proof. exists 0%Z; reflexivity. Qed.

Theorem ut2_left_ideal_not_mul_congruence :
  LeftIdealMulCongruence E11Left → False.
Proof.
  intro Hcong.
  pose proof (Hcong ut2_e11 ut2_zero ut2_e12 ut2_e12
                ut2_e11_rel_zero ut2_e12_rel_self) as H.
  destruct H as [a Ha].
  discriminate Ha.
Qed.

(** ** The positive half, at the same ring

    Every TWO-SIDED ideal of UT2 does give a congruence, so what the
    counterexample separates is the two-sidedness and not something about
    [UT2].  The strictly upper-triangular matrices are the witness: a
    two-sided ideal of UT2 that is proper and nontrivial, whose
    congruence is [ideal_mul_congruence] instantiated. *)

Definition ut2_strict (x : ut2) : Type := { b : Z & x = (0, b, 0)%Z }.

Program Definition StrictUpper : Ideal UT2 := {| idl_mem := ut2_strict |}.
Next Obligation.
  intros x y Hxy [b Hb]; unfold ut2_eqT in Hxy.
  exists b; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [b Hb] [c Hc].
  inversion Hb; inversion Hc; subst.
  exists (b + c)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [b Hb].
  inversion Hb; subst.
  exists (r1 * b)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[x1 x2] x3] [[r1 r2] r3] [b Hb].
  inversion Hb; subst.
  exists (b * r3)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

Definition StrictUpper_congruence : IdealMulCongruence StrictUpper :=
  ideal_mul_congruence StrictUpper.

(* Proper: E₁₁ is not strictly upper triangular. *)
Theorem StrictUpper_proper : idl_mem StrictUpper ut2_e11 → False.
Proof. intros [b Hb]; discriminate Hb. Qed.

(* Nontrivial: E₁₂ is, and is not zero. *)
Theorem StrictUpper_nontrivial :
  idl_mem StrictUpper ut2_e12 * (ut2_e12 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(* And the quotient by it does not collapse: E₁₁ stays apart from 0 in
   UT2/StrictUpper, so the two-sided construction is exercised on a
   nondegenerate non-commutative example and not only on ℤ. *)
Theorem UT2_mod_strict_not_collapsed :
  rquot_rel StrictUpper ut2_e11 ut2_zero → False.
Proof. intros [b Hb]; discriminate Hb. Qed.

Theorem UT2_mod_strict_collapses_e12 :
  rig_map (rquot_proj StrictUpper) ut2_e12
    ≈ rig_map (rquot_proj StrictUpper) ut2_zero.
Proof. exists 1%Z; reflexivity. Qed.

(* The quotient ring UT2/StrictUpper is not the zero ring. *)
Theorem UT2_mod_strict_nonzero :
  rig_one (QuotientRing StrictUpper) ≈ rig_zero (QuotientRing StrictUpper)
    → False.
Proof. intros [b Hb]; discriminate Hb. Qed.

(* It IS commutative, though UT2 is not -- the quotient of a
   non-commutative ring can be commutative, which is why "quotient" here
   is a genuine construction and not a relabelling.  On the nose: the
   two products differ only in the middle entry, which the ideal
   kills. *)
Theorem UT2_mod_strict_commutative :
  ∀ x y : carrier (rig_setoid (QuotientRing StrictUpper)),
    rig_mul (QuotientRing StrictUpper) x y
      ≈ rig_mul (QuotientRing StrictUpper) y x.
Proof.
  intros [[x1 x2] x3] [[y1 y2] y3].
  exists (x1 * y2 + x2 * y3 - (y1 * x2 + y2 * x3))%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

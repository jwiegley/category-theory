Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Rng: the category of unital rings

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.7
    (printed p. 25): the roll-call of large categories includes Rng, all
    small (unital) rings with the ring homomorphisms preserving the
    multiplicative unit [maclane:I.7:def1, maclane:I.7:construction2];
    §I.5 Exercise 4 (printed p. 21): the inclusion ℤ → ℚ is an epi of
    Rng that is not surjective [maclane:I.5:ex4].
    nLab: https://ncatlab.org/nlab/show/Ring
    Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings

    NAMING (per the issue's QA audit).  This category keeps Mac Lane's
    name [Rng] — his abbreviation for the category of UNITAL rings — and
    it IS Theory/Algebra/Rig.v's category [Ring], definitionally: a
    [RingObject] there is a rig with additive inverses, i.e. exactly a
    unital (not necessarily commutative) ring over a setoid carrier, and
    its homomorphisms are the [RigHom]s, which preserve 0, +, 1 and · —
    unit preservation is a FIELD, as Mac Lane requires — while
    preservation of negation is the theorem [RigHom_neg].  The set-level
    CLASS keeps the name [Ring]/[RingObject] (seventeen Seven Sketches
    issues consume it under that name); the CATEGORY answers to both,
    with [Rng] the Mac Lane-side entry point.  The category of
    NON-unital rings is future #362's [Rg], whence the forgetful
    functor's direction will be unambiguous.

    CONTENT.  Beyond the category itself: the forgetful functors to [Ab]
    (the additive abelian group, Instance/Ab.v) and to [Sets]; the zero
    ring is terminal ([Rng_Terminal_zero]); the integers are initial
    ([Rng_Initial_Z] — the ring-side counterpart of Rig.v's ℕ-initiality,
    with the unique homomorphism z ↦ z·1 built by sign case analysis and
    verified through the hand-rolled Type-valued recursor [Z_peano_rect]
    below — the stdlib offers only the Prop-valued [Z.peano_ind]); the
    full subcategory
    [CRng] of commutative rings (needed downstream by the matrix-category
    and GL_n issues); injections are monic and surjections are epi; and
    the headline separation, Mac Lane's Exercise I.5.4:

        [ZtoQ_epi_not_surjective] — the inclusion ℤ → ℚ is an epimorphism
        of [Rng] although it is not surjective.

    The epi half is the standard argument made constructive: a ring
    homomorphism out of ℚ is determined by its values on the image of ℤ,
    because g (1/b) is a two-sided multiplicative inverse of g b and
    two-sided inverses are unique; no fraction ever needs to be chosen,
    only cancelled.  The non-surjectivity half exhibits 1/2.

    SCOPE NOTE, disclosed.  "Monics are exactly the injections" ships
    here in the direction that needs no new machinery: injective ⇒ monic
    ([rng_injective_monic]), plus surjective ⇒ epi ([rng_surjective_epic],
    whose converse is REFUTED by the headline theorem).  The converse
    monic ⇒ injective requires probing with the free ring on one
    generator — the polynomial ring ℤ[x], which does not exist in-tree —
    exactly as Instance/Sets.v probes with the singleton and
    Instance/Top.v with the point space; it is deferred to the future
    free-ring development rather than asserted.  (The issue's own
    verification list names [Rng], [CRng], [Rng_Initial_Z],
    [Rng_Terminal_zero] and [ZtoQ_epi_not_surjective] as the audited
    artifacts.) *)

(** ** The category, under Mac Lane's name *)

Definition Rng : Category := Ring.

(** ** The forgetful functors *)

(* The additive part of a ring is an abelian group: Rig.v's [rig_cmon]
   supplies the commutative monoid, [ring_neg] the inverses. *)
Definition ring_ab (R : RingObject) : AbObject := {|
  ab_cmon := rig_cmon R;
  ab_neg := ring_neg R;
  ab_neg_respects := ring_neg_respects R;
  ab_neg_left := ring_neg_l R
|}.

#[local] Obligation Tactic := idtac.

Program Definition Rng_Forget_Ab : Rng ⟶ Ab := {|
  fobj := ring_ab;
  fmap := fun R S f => {|
    cmon_map := rig_map f;
    cmon_map_zero := rig_map_zero f;
    cmon_map_plus := rig_map_add f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

Program Definition Rng_Forget : Rng ⟶ Sets := {|
  fobj := fun R : RingObject => rig_setoid R;
  fmap := fun R S f => rig_map f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(** ** The zero ring is terminal *)

(* The one-element ring: every operation returns the point.  In a ring
   with 0 ≈ 1 every element is 0, and this is it. *)
Program Definition Zero_Rig : RigObject := {|
  rig_setoid := {| carrier := poly_unit
                 ; is_setoid := {| Setoid.equiv := fun _ _ => True
                                 ; Setoid.setoid_equiv := _ |} |};
  rig_zero := ttt;
  rig_add := fun _ _ => ttt;
  rig_one := ttt;
  rig_mul := fun _ _ => ttt
|}.
Next Obligation. equivalence. Qed.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.

Program Definition Zero_Ring : RingObject := {|
  ring_rig := Zero_Rig;
  ring_neg := fun _ => ttt
|}.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.

(* The unique homomorphism into the zero ring sends everything to the
   point; every clause holds trivially in the trivial codomain. *)
Program Definition rng_to_zero (R : RingObject) : RigHom R Zero_Ring := {|
  rig_map := {| morphism := fun _ => ttt |}
|}.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.

#[export] Program Instance Rng_Terminal_zero : @Terminal Rng := {
  terminal_obj := Zero_Ring;
  one := rng_to_zero
}.
Next Obligation. intros R f g a; constructor. Qed.

(** ** The integers are initial *)

(* The candidate ring ℤ is Rig.v's [Int_Ring].  The unique homomorphism
   sends z to the z-fold sum of 1, by sign case analysis over the n-fold
   sum [rig_iter] of Rig.v. *)

Definition zring (R : RingObject) (z : Z) : carrier (rig_setoid R) :=
  match z with
  | Z0 => rig_zero R
  | Zpos p => rig_iter R (Pos.to_nat p)
  | Zneg p => ring_neg R (rig_iter R (Pos.to_nat p))
  end.

(* Negation commutes with the candidate map — by construction on the
   positives, and by involutivity (through the Ab layer) on the
   negatives. *)
Lemma ring_neg_involutive (R : RingObject) (a : carrier (rig_setoid R)) :
  ring_neg R (ring_neg R a) ≈ a.
Proof.
  symmetry.
  apply (ab_neg_unique (ring_ab R)); simpl.
  apply (ab_neg_right (ring_ab R)).
Qed.

Lemma zring_opp (R : RingObject) (z : Z) :
  zring R (- z) ≈ ring_neg R (zring R z).
Proof.
  destruct z; simpl.
  - symmetry.
    apply (ab_neg_zero (ring_ab R)).
  - reflexivity.
  - symmetry; apply ring_neg_involutive.
Qed.

(* The Ab-layer facts, restated in ring vocabulary once so the rewrites
   below match syntactically. *)
Lemma ring_neg_r (R : RingObject) (a : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R a) ≈ rig_zero R.
Proof. exact (ab_neg_right (ring_ab R) a). Qed.

Lemma ring_neg_add (R : RingObject) (a b : carrier (rig_setoid R)) :
  ring_neg R (rig_add R a b)
    ≈ rig_add R (ring_neg R a) (ring_neg R b).
Proof. exact (ab_neg_plus (ring_ab R) a b). Qed.

(* The successor law, the engine of every preservation proof below. *)
Lemma zring_succ (R : RingObject) (z : Z) :
  zring R (Z.succ z) ≈ rig_add R (rig_one R) (zring R z).
Proof.
  destruct z; simpl.
  - reflexivity.
  - now rewrite Pos.add_1_r, Pos2Nat.inj_succ; simpl.
  - destruct p; simpl.
    + (* Zneg p~1: simpl has already exposed the successor; cancel 1
         against -1 through the negation of the sum *)
      symmetry.
      rewrite (ring_neg_add R).
      rewrite <- rig_add_assoc.
      rewrite (ring_neg_r R).
      now rewrite rig_add_zero_l.
    + (* Zneg p~0: express p~0 as succ (pred_double p) and cancel *)
      rewrite <- Pos.succ_pred_double.
      rewrite Pos2Nat.inj_succ; simpl.
      symmetry.
      rewrite (ring_neg_add R).
      rewrite <- rig_add_assoc.
      rewrite (ring_neg_r R).
      now rewrite rig_add_zero_l.
    + (* Zneg 1: succ is 0 *)
      symmetry.
      rewrite rig_add_zero_r.
      apply (ring_neg_r R).
Qed.

Lemma zring_pred (R : RingObject) (z : Z) :
  zring R (Z.pred z)
    ≈ rig_add R (ring_neg R (rig_one R)) (zring R z).
Proof.
  apply (ab_cancel_l (ring_ab R) (rig_one R)); simpl.
  rewrite <- (zring_succ R (Z.pred z)).
  rewrite Z.succ_pred.
  rewrite <- rig_add_assoc.
  rewrite (ring_neg_r R).
  now rewrite rig_add_zero_l.
Qed.

(* A Type-valued Peano recursor for ℤ, assembled from the positive one:
   the stdlib's [Z.peano_ind] eliminates only into [Prop], and the goals
   below are ≈-valued (Type).  The successor/predecessor conversions are
   definitional: [Z.succ (Zpos q)] computes to [Zpos (q + 1)] and
   [Pos.add q 1] to [Pos.succ q], dually on the negatives. *)
Definition Z_peano_rect (P : Z → Type)
  (H0 : P 0%Z)
  (HS : ∀ z, P z → P (Z.succ z))
  (HP : ∀ z, P z → P (Z.pred z)) (z : Z) : P z :=
  match z with
  | Z0 => H0
  | Zpos p => Pos.peano_rect (fun q => P (Zpos q)) (HS 0%Z H0)
                (fun q IH =>
                   eq_rect _ P (HS (Zpos q) IH) _
                     (eq_sym (Pos2Z.inj_succ q))) p
  | Zneg p => Pos.peano_rect (fun q => P (Zneg q)) (HP 0%Z H0)
                (fun q IH =>
                   eq_rect _ P (HP (Zneg q) IH) _
                     (f_equal Z.neg (Pos.add_1_r q))) p
  end.

Lemma zring_add (R : RingObject) (a b : Z) :
  zring R (a + b) ≈ rig_add R (zring R a) (zring R b).
Proof.
  revert b.
  apply (Z_peano_rect
           (fun a => ∀ b, zring R (a + b)
                            ≈ rig_add R (zring R a) (zring R b))).
  - intro b; simpl.
    now rewrite rig_add_zero_l.
  - intros x IH b.
    rewrite Z.add_succ_l.
    rewrite !zring_succ.
    rewrite IH.
    now rewrite rig_add_assoc.
  - intros x IH b.
    rewrite Z.add_pred_l.
    rewrite !zring_pred.
    rewrite IH.
    now rewrite rig_add_assoc.
Qed.

(* (-1) · x ≈ - x, needed for the multiplicative Peano step. *)
Lemma rig_mul_neg_one (R : RingObject) (x : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R (rig_one R)) x ≈ ring_neg R x.
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- (rig_mul_one_l R x) at 2.
  rewrite <- rig_distr_r.
  rewrite (ab_neg_left (ring_ab R)); simpl.
  apply rig_mul_zero_l.
Qed.

Lemma zring_mul (R : RingObject) (a b : Z) :
  zring R (a * b) ≈ rig_mul R (zring R a) (zring R b).
Proof.
  revert b.
  apply (Z_peano_rect
           (fun a => ∀ b, zring R (a * b)
                            ≈ rig_mul R (zring R a) (zring R b))).
  - intro b; simpl.
    now rewrite rig_mul_zero_l.
  - intros x IH b.
    rewrite Z.mul_succ_l.
    rewrite zring_add, IH.
    rewrite zring_succ.
    rewrite rig_distr_r.
    rewrite rig_mul_one_l.
    apply rig_add_comm.
  - intros x IH b.
    rewrite Z.mul_pred_l.
    unfold Z.sub.
    rewrite zring_add, IH.
    rewrite zring_opp.
    rewrite zring_pred.
    rewrite rig_distr_r.
    rewrite rig_mul_neg_one.
    apply rig_add_comm.
Qed.

Program Definition rng_from_Z (R : RingObject) : RigHom Int_Ring R := {|
  rig_map := {| morphism := zring R |}
|}.
Next Obligation. intros R; proper. Qed.
Next Obligation. intros R a b; apply zring_add. Qed.
Next Obligation. intros R; simpl; now rewrite rig_add_zero_r. Qed.
Next Obligation. intros R a b; apply zring_mul. Qed.

Lemma rng_from_Z_unique (R : RingObject) (h : RigHom Int_Ring R) (z : Z) :
  rig_map h z ≈ zring R z.
Proof.
  apply (Z_peano_rect (fun z => rig_map h z ≈ zring R z)).
  - apply (rig_map_zero h).
  - intros x IH.
    rewrite <- Z.add_1_l.
    rewrite (rig_map_add h 1%Z x).
    rewrite IH.
    rewrite zring_add.
    apply rig_add_respects; [| reflexivity ].
    etransitivity; [ apply (rig_map_one h) |].
    simpl; now rewrite rig_add_zero_r.
  - intros x IH.
    rewrite <- Z.sub_1_r.
    unfold Z.sub.
    rewrite (rig_map_add h x (-1)%Z).
    rewrite IH.
    rewrite zring_add.
    apply rig_add_respects; [ reflexivity |].
    (* h (-1) ≈ zring (-1) = -1 *)
    change (zring R (-1)) with (ring_neg R (rig_iter R 1)).
    transitivity (ring_neg R (rig_map h 1%Z)).
    + apply (RigHom_neg Int_Ring R h 1%Z).
    + apply ring_neg_respects.
      etransitivity; [ apply (rig_map_one h) |].
      simpl; now rewrite rig_add_zero_r.
Qed.

#[export] Program Instance Rng_Initial_Z : @Initial Rng := {
  terminal_obj := Int_Ring;
  one := rng_from_Z
}.
Next Obligation.
  intros R f g z; simpl.
  rewrite (rng_from_Z_unique R f z).
  now rewrite (rng_from_Z_unique R g z).
Qed.

(** ** The commutative full subcategory *)

Definition CRng_Sub : Subcategory Rng :=
  @Build_Subcategory Rng
    (fun R : RingObject => ∀ a b, rig_mul R a b ≈ rig_mul R b a)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CRng : Category := Sub Rng CRng_Sub.

Lemma CRng_Full : Category.Construction.Subcategory.Full Rng CRng_Sub.
Proof. intros x y ox oy g; exact I. Qed.

(* Non-vacuity: the integers are commutative, so [CRng] contains ℤ —
   as an actual object, not just a predicate instance. *)
Example Int_Ring_commutative : ∀ a b, rig_mul Int_Ring a b ≈ rig_mul Int_Ring b a.
Proof. intros a b; simpl; apply Z.mul_comm. Qed.

Definition Int_CRng : CRng := (Int_Ring; Int_Ring_commutative).

(** ** Injections are monic; surjections are epi *)

Lemma rng_injective_monic {R S : RingObject} (f : R ~{Rng}~> S) :
  (∀ a b : carrier (rig_setoid R), rig_map f a ≈ rig_map f b → a ≈ b) →
  Monic f.
Proof.
  intros Hinj.
  constructor; intros T g1 g2 Hg a.
  exact (Hinj (rig_map g1 a) (rig_map g2 a) (Hg a)).
Qed.

Lemma rng_surjective_epic {R S : RingObject} (f : R ~{Rng}~> S) :
  (∀ b : carrier (rig_setoid S), ∃ a, rig_map f a ≈ b) →
  Epic f.
Proof.
  intros Hsurj.
  constructor; intros T g1 g2 Hg b.
  destruct (Hsurj b) as [a Ha].
  rewrite <- Ha.
  exact (Hg a).
Qed.

(** ** Mac Lane I.5, Exercise 4: ℤ → ℚ is epi and not surjective *)

(* The rationals as a ring, over the stdlib [Qeq] setoid. *)
Program Definition Q_Rig : RigObject := {|
  rig_setoid := {| carrier := Q
                 ; is_setoid := {| Setoid.equiv := Qeq
                                 ; Setoid.setoid_equiv := _ |} |};
  rig_zero := 0%Q;
  rig_add := Qplus;
  rig_one := 1%Q;
  rig_mul := Qmult
|}.
Next Obligation.
  constructor; [ exact Qeq_refl | exact Qeq_sym | exact Qeq_trans ].
Qed.
Next Obligation. repeat intro; now apply Qplus_comp. Qed.
Next Obligation. repeat intro; now apply Qmult_comp. Qed.
Next Obligation. intros a b c; simpl; symmetry; apply Qplus_assoc. Qed.
Next Obligation. intros a b; simpl; apply Qplus_comm. Qed.
Next Obligation. intros a; simpl; apply Qplus_0_l. Qed.
Next Obligation. intros a b c; simpl; symmetry; apply Qmult_assoc. Qed.
Next Obligation. intros a; simpl; apply Qmult_1_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_1_r. Qed.
Next Obligation. intros a b c; simpl; apply Qmult_plus_distr_r. Qed.
Next Obligation. intros a b c; simpl; apply Qmult_plus_distr_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_0_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_0_r. Qed.

Program Definition Q_Ring : RingObject := {|
  ring_rig := Q_Rig;
  ring_neg := Qopp
|}.
Next Obligation. repeat intro; now apply Qopp_comp. Qed.
Next Obligation.
  intros a; simpl.
  rewrite Qplus_comm; apply Qplus_opp_r.
Qed.

(* The inclusion, as a ring homomorphism. *)
Program Definition ZtoQ : Int_Ring ~{Rng}~> Q_Ring := {|
  rig_map := {| morphism := inject_Z |}
|}.
Next Obligation. intros; simpl; reflexivity. Qed.
Next Obligation.
  intros a b; simpl; unfold inject_Z, Qplus; simpl; unfold Qeq; simpl; ring.
Qed.
Next Obligation. intros; simpl; reflexivity. Qed.
Next Obligation.
  intros a b; simpl; unfold inject_Z, Qmult; simpl; unfold Qeq; simpl; ring.
Qed.

(* One-sided inverses on opposite sides agree in any rig: the monoid
   argument, with exactly the two hypotheses the proof consumes. *)
Lemma rig_inv_unique (S : RigObject)
  (x u v : carrier (rig_setoid S)) :
  rig_mul S u x ≈ rig_one S → rig_mul S x v ≈ rig_one S →
  u ≈ v.
Proof.
  intros Hux Hxv.
  rewrite <- (rig_mul_one_r S u).
  rewrite <- Hxv.
  rewrite <- rig_mul_assoc.
  rewrite Hux.
  apply rig_mul_one_l.
Qed.

(* Every rational is (a/b)·b ≈ a with b := its positive denominator, and
   1/b is a two-sided inverse of b in ℚ. *)
Lemma Q_num_den (q : Q) :
  (q * inject_Z (Z.pos (Qden q)) == inject_Z (Qnum q))%Q.
Proof.
  unfold Qeq, Qmult, inject_Z; simpl.
  rewrite Pos.mul_1_r.
  ring.
Qed.

Lemma Q_inv_den (q : Q) :
  (/ inject_Z (Z.pos (Qden q)) * inject_Z (Z.pos (Qden q)) == 1)%Q.
Proof.
  rewrite Qmult_comm.
  apply Qmult_inv_r.
  discriminate.
Qed.

(* The heart of the exercise: a homomorphism out of ℚ is determined by
   its values on the integers, because it must carry 1/b to the unique
   two-sided inverse of the image of b. *)
Theorem ZtoQ_epic : Epic ZtoQ.
Proof.
  constructor; intros S g1 g2 Hg q.
  (* both maps agree on every inject_Z z *)
  assert (HZ : ∀ z : Z, rig_map g1 (inject_Z z) ≈ rig_map g2 (inject_Z z)).
  { intro z; exact (Hg z). }
  (* both images of 1/b invert the common image of b *)
  set (b := inject_Z (Z.pos (Qden q))).
  assert (Hinv1l : rig_mul S (rig_map g1 (/ b)%Q) (rig_map g1 b)
                     ≈ rig_one S).
  { rewrite <- rig_map_mul.
    etransitivity; [| apply (rig_map_one g1) ].
    apply (proper_morphism (rig_map g1)).
    apply Q_inv_den. }
  assert (Hinv2r : rig_mul S (rig_map g2 b) (rig_map g2 (/ b)%Q)
                     ≈ rig_one S).
  { rewrite <- rig_map_mul.
    etransitivity; [| apply (rig_map_one g2) ].
    apply (proper_morphism (rig_map g2)).
    rewrite Qmult_comm.
    apply Q_inv_den. }
  (* hence the images of 1/b coincide: g1(1/b) left-inverts the common
     image of b, which g2(1/b) right-inverts *)
  assert (Hinv : rig_map g1 (/ b)%Q ≈ rig_map g2 (/ b)%Q).
  { apply (rig_inv_unique S (rig_map g1 b)).
    - exact Hinv1l.
    - unfold b; rewrite (HZ (Z.pos (Qden q))).
      unfold b in Hinv2r; auto. }
  (* decompose q = (num q) · (1/b) and conclude *)
  assert (Hq : (q == inject_Z (Qnum q) * / b)%Q).
  { rewrite <- (Q_num_den q).
    fold b.
    rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r.
    - now rewrite Qmult_1_r.
    - intro H; unfold b, inject_Z, Qeq in H; simpl in H; discriminate H. }
  rewrite (proper_morphism (rig_map g1) _ _ Hq).
  rewrite (proper_morphism (rig_map g2) _ _ Hq).
  rewrite !rig_map_mul.
  apply rig_mul_respects.
  - apply (HZ (Qnum q)).
  - exact Hinv.
Qed.

(* ...and it is not surjective: 1/2 has no preimage, since inject_Z z
   ≈ 1/2 would force 2·z = 1 in ℤ.  Stated with the PROPOSITIONAL
   existential — the strongest form: refuting mere existence also
   refutes the library's data-valued ∃ (the corollary below), which is
   the exact negation of [rng_surjective_epic]'s hypothesis shape. *)
Theorem ZtoQ_not_surjective :
  (∀ q : Q, exists z : Z, inject_Z z == q)%Q → False.
Proof.
  intro Hsurj.
  destruct (Hsurj (1 # 2)%Q) as [z Hz].
  unfold Qeq, inject_Z in Hz; simpl in Hz.
  lia.
Qed.

Corollary ZtoQ_not_surjective_sigT :
  (∀ q : Q, ∃ z : Z, inject_Z z == q)%Q → False.
Proof.
  intro Hsurj.
  apply ZtoQ_not_surjective.
  intro q.
  destruct (Hsurj q) as [z Hz].
  now exists z.
Qed.

(* Mac Lane I.5 Exercise 4, packaged. *)
Definition ZtoQ_epi_not_surjective :=
  (ZtoQ_epic,
   ZtoQ_not_surjective).

(** ** Acceptance tests *)

(* The initial homomorphism computes on both signs. *)
Example zring_Z_3 : rig_map (rng_from_Z Int_Ring) 3%Z = 3%Z := eq_refl.
Example zring_Z_neg2 :
  rig_map (rng_from_Z Int_Ring) (-2)%Z = (-2)%Z := eq_refl.

(* The forgetful functors return the carrier on the nose. *)
Example rng_forget_ab_carrier (R : RingObject) :
  cmon_setoid (ab_cmon (Rng_Forget_Ab R)) = rig_setoid R := eq_refl.
Example rng_forget_carrier (R : RingObject) :
  Rng_Forget R = rig_setoid R := eq_refl.

(* ℚ really contains the non-integer the separation uses. *)
Example half_times_two : ((1 # 2) * inject_Z 2 == 1)%Q := eq_refl.

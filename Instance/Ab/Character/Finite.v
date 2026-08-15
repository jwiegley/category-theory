(** * Pontryagin duality for finite abelian groups *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Character.

Generalizable All Variables.

Import ListNotations.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.4, printed p. 17 (PDF 27) — maclane:I.4:construction3
   nLab:      https://ncatlab.org/nlab/show/Pontryagin+duality
   Wikipedia: https://en.wikipedia.org/wiki/Pontryagin_duality

   Mac Lane's §I.4 example ends with the remark that for a FINITE abelian
   group the evaluation τ_G : G → DD(G) of Instance/Ab/Character.v is an
   isomorphism, while no isomorphism G ≅ D(G) is natural.  This file
   proves the first half — [tau_iso_finite] — and the sibling
   NonNatural.v the second.

   The theorem is the substantial half: naturality of τ is a one-line
   [qz_eq_refl] (Character.v), whereas invertibility is finite
   Pontryagin duality, and its usual proof runs through the structure
   theorem for finite abelian groups.  It is proved here WITHOUT the
   structure theorem, by the character-extension route. *)

(** ** Design

    1. FINITENESS IS DATA, AND DECIDABILITY IS PART OF IT.  [FiniteCarrier]
       carries an enumeration, a proof that every element is `≈`-in it, and
       a DECIDER for `≈`.  The decider is not a convenience: the extension
       construction below defines a character by a bounded search for the
       coset index of an element, so the search must actually run, and
       "finite" without decidable equality does not make a setoid searchable.
       Instance/Ab/Character.v's [qz_eq_dec] provides the matching decider on
       the target ℚ/ℤ, and the acceptance witness at the end of this file
       exhibits both for ℤ/2.

    2. NO STRUCTURE THEOREM, NO COUNTING.  The textbook proof shows
       |D(G)| = |G| and concludes by pigeonhole.  That route needs an
       enumeration of the character group — a finite-function
       enumeration up to pointwise `≈` — which is a large amount of
       machinery for a side condition.  Instead both halves are
       obtained from ONE construction, the character-extension lemma
       [character_extend]: every character of a subgroup of a finite
       abelian group extends to the whole group.  Injectivity of τ is
       then separation ([separating_character], the cyclic character
       1/k extended), and SURJECTIVITY ([tau_surjective_finite]) is an
       induction over subgroups whose step is one more application of
       the same extension.  Only one nontrivial induction is paid for,
       and no cardinality of a set of characters is ever needed.

    2a. THE SURJECTIVITY INDUCTION, SINCE IT IS NOT THE TEXTBOOK ONE.
       Write H^ann for the characters killing H.  The statement carried
       through the induction is [Realizes]: every Ξ ∈ DD(G) that
       vanishes on H^ann ([VanishesOn]) is evaluation at some c ∈ H.
       At H = {0} this is immediate — H^ann is all of D(G), so Ξ is
       zero, which is evaluation at zero ([realizes_trivial]).  At
       H = G it IS the theorem, because G^ann = {0} and every Ξ kills
       zero, so the hypothesis is vacuous ([vanishes_of_all]).  The step
       ([realizes_step]) takes φ with φ|H = 0 and φ(a) = 1/k, notes that
       k·φ kills ⟨H,a⟩ so that Ξ(φ) has denominator k, say n/k, and then
       shows Ξ − τ(n·a) vanishes on H^ann: any χ ∈ H^ann has χ(a) = m/k,
       and χ − m·φ kills all of ⟨H,a⟩, which pins Ξ(χ) to m·n/k = χ(n·a).
       The inductive hypothesis then supplies c ∈ H with
       Ξ = τ(c + n·a).

    2b. WHAT IS NOT CLAIMED.  |D(G)| = |G| is never proved in general;
       it is only checked by hand on the ℤ/2 witness
       ([zmod2_characters]).  Nothing here is stated for infinite
       abelian groups, where the theorem is false for this dualizing
       object — ℚ/ℤ replaces the circle ℝ/ℤ precisely because the
       finite case is all that is at issue (Instance/Ab/Character.v's
       design note 1).

    3. WHY ℚ/ℤ MAKES THE EXTENSION EASY.  Extending a character across
       one new generator [a] requires a k-th root of χ(k·a) in the
       target, where k is the least positive integer with k·a already in
       the subgroup.  In ℚ/ℤ roots are computed, not chosen: divide a
       rational representative by k.  The freedom in the choice (adding
       j/k for any integer j) is exactly what is needed to force the
       value 1/k at the new generator, which is what separation consumes.

    4. SUBGROUPS AS DECIDABLE PREDICATES, CHARACTERS AS PARTIAL MAPS.  A
       subgroup is a decidable, `≈`-closed, 0/+/− closed predicate
       ([Subgroup]); a character of it is a TOTAL function on the carrier
       whose laws are only required on members ([PartialChar]).  This
       avoids building sub-objects of [Ab] and transporting characters
       along inclusions: at the end of the induction the predicate holds
       everywhere and the partial character IS an [AbHom G QZ].

    5. THE INDUCTION AND ITS MEASURE.  Both inductions are structural
       recursion on a natural number bounding the count of enumeration
       entries OUTSIDE the current subgroup ([outside_count]).
       Adjoining a non-member strictly decreases that count
       ([outside_count_generated]), and [all_or_witness] decides at each
       step between "the subgroup is everything" and a named
       non-member.  No well-founded recursion, and the fuel cannot run
       out unremarked: the case where it would have is closed by
       [outside_count_generated] itself, which would put a count of
       naturals strictly below zero.

    6. TYPE-VALUED LISTS.  The standard library's [In] and [NoDup] land
       in [Prop] and so cannot be eliminated into the [Type]-valued
       goals this library works in (Lib/Setoid.v's `≈` is a [crelation]).
       [TIn]/[LIn]/[HasDup] below are the [Type]-valued replacements, and
       [pigeon] is the pigeonhole principle over them — needed exactly
       once, to produce a positive annihilator of an element. *)

(** ** A Type-valued list toolkit *)

Section ListToolkit.

Context {A : Type}.
Context `{SA : Setoid A}.

(* Membership up to `≈`. *)
Fixpoint TIn (x : A) (l : list A) : Type :=
  match l with
  | [] => False
  | y :: l' => ((x ≈ y) + TIn x l')%type
  end.

(* Literal membership.  [In] is [Prop]-valued and its [or] cannot be
   eliminated into [Type], so it is unusable here. *)
Fixpoint LIn (x : A) (l : list A) : Type :=
  match l with
  | [] => False
  | y :: l' => ((x = y) + LIn x l')%type
  end.

Lemma LIn_TIn (x : A) (l : list A) : LIn x l → TIn x l.
Proof.
  induction l as [|y l' IH]; simpl; intro H.
  - exact H.
  - destruct H as [H|H].
    + left; rewrite H; reflexivity.
    + right; exact (IH H).
Qed.

Lemma TIn_respects (x y : A) (l : list A) : x ≈ y → TIn x l → TIn y l.
Proof.
  intro Hxy.
  induction l as [|z l' IH]; simpl; intro H.
  - exact H.
  - destruct H as [H|H].
    + left; rewrite <- Hxy; exact H.
    + right; exact (IH H).
Qed.

(* Membership up to `≈` names an actual list entry. *)
Lemma TIn_LIn (x : A) (l : list A) : TIn x l → { y : A & LIn y l ∧ x ≈ y }.
Proof.
  induction l as [|z l' IH]; simpl; intro H.
  - destruct H.
  - destruct H as [H|H].
    + exists z; split; [ left; reflexivity | exact H ].
    + destruct (IH H) as [y [Hy Hxy]].
      exists y; split; [ right; exact Hy | exact Hxy ].
Qed.

Lemma LIn_filter (p : A → bool) (x : A) (l : list A) :
  LIn x (filter p l) → LIn x l ∧ p x = true.
Proof.
  induction l as [|y l' IH]; simpl; intro H.
  - destruct H.
  - destruct (p y) eqn:Hy; simpl in H.
    + destruct H as [H|H].
      * split; [ left; exact H | rewrite H; exact Hy ].
      * destruct (IH H) as [H1 H2]; split; [ right; exact H1 | exact H2 ].
    + destruct (IH H) as [H1 H2]; split; [ right; exact H1 | exact H2 ].
Qed.

Lemma LIn_filter_intro (p : A → bool) (x : A) (l : list A) :
  LIn x l → p x = true → LIn x (filter p l).
Proof.
  induction l as [|y l' IH]; simpl; intros H Hp.
  - destruct H.
  - destruct H as [H|H].
    + subst y; rewrite Hp; simpl; left; reflexivity.
    + destruct (p y); simpl; [ right | ]; exact (IH H Hp).
Qed.

Lemma TIn_filter (p : A → bool) (x : A) (l : list A) :
  TIn x (filter p l) → TIn x l.
Proof.
  induction l as [|y l' IH]; simpl; intro H.
  - exact H.
  - destruct (p y) eqn:Hy; simpl in H.
    + destruct H as [H|H]; [ left; exact H | right; exact (IH H) ].
    + right; exact (IH H).
Qed.

Lemma filter_length_partition (p : A → bool) (l : list A) :
  (length (filter p l) + length (filter (fun y => negb (p y)) l)
     = length l)%nat.
Proof.
  induction l as [|y l' IH]; simpl; [ reflexivity | ].
  destruct (p y); simpl; lia.
Qed.

Lemma filter_head (p : A → bool) (l : list A) :
  (0 < length (filter p l))%nat → { z : A & LIn z l ∧ p z = true }.
Proof.
  induction l as [|y l' IH]; simpl; intro H.
  - lia.
  - destruct (p y) eqn:Hy.
    + exists y; split; [ left; reflexivity | exact Hy ].
    + destruct (IH H) as [z [Hz Hzp]].
      exists z; split; [ right; exact Hz | exact Hzp ].
Qed.

(* A list has a duplicate when some entry recurs, up to `≈`, later on. *)
Fixpoint HasDup (l : list A) : Type :=
  match l with
  | [] => False
  | y :: l' => (TIn y l' + HasDup l')%type
  end.

Lemma HasDup_filter (p : A → bool) (l : list A) :
  HasDup (filter p l) → HasDup l.
Proof.
  induction l as [|y l' IH]; simpl; intro H.
  - exact H.
  - destruct (p y) eqn:Hy; simpl in H.
    + destruct H as [H|H].
      * left; exact (TIn_filter p y l' H).
      * right; exact (IH H).
    + right; exact (IH H).
Qed.

(* A decider for `≈`, threaded explicitly rather than as a section
   variable: the pigeonhole proof mentions it only in the proof term, and
   this file compiles under inferred [Proof using] annotations. *)
Definition Decider := ∀ x y : A, ((x ≈ y) + (x ≈ y → False))%type.

Definition eqb_at (dec : Decider) (x y : A) : bool :=
  if dec y x then true else false.

Lemma eqb_at_true (dec : Decider) (x y : A) : eqb_at dec x y = true → y ≈ x.
Proof.
  unfold eqb_at; destruct (dec y x) as [H|H]; intro E.
  - exact H.
  - discriminate.
Qed.

Lemma eqb_at_false (dec : Decider) (x y : A) :
  eqb_at dec x y = false → y ≈ x → False.
Proof.
  unfold eqb_at; destruct (dec y x) as [H|H]; intros E Hyx.
  - discriminate.
  - exact (H Hyx).
Qed.

(* Two entries equivalent to the same element are a duplicate. *)
Lemma dup_of_two (dec : Decider) (x : A) (l : list A) :
  (1 < length (filter (eqb_at dec x) l))%nat → HasDup l.
Proof.
  induction l as [|y l' IH]; intro H; simpl in H.
  - lia.
  - destruct (eqb_at dec x y) eqn:Hy; simpl in H.
    + simpl; left.
      assert (Hpos : (0 < length (filter (eqb_at dec x) l'))%nat) by lia.
      destruct (filter_head (eqb_at dec x) l' Hpos) as [z [Hz Hzp]].
      apply (TIn_respects z y l').
      * etransitivity; [ exact (eqb_at_true dec x z Hzp) | ].
        symmetry; exact (eqb_at_true dec x y Hy).
      * exact (LIn_TIn z l' Hz).
    + simpl; right; exact (IH H).
Qed.

(* The pigeonhole principle: a list drawn from a shorter one repeats. *)
Lemma pigeon (dec : Decider) (e l : list A) :
  (∀ x, TIn x l → TIn x e) → (length e < length l)%nat → HasDup l.
Proof.
  revert l.
  induction e as [|x e' IHe]; intros l Hsub Hlen.
  - destruct l as [|y l']; simpl in Hlen; [ lia | ].
    assert (Hy : TIn y (y :: l')) by (simpl; left; reflexivity).
    destruct (Hsub y Hy).
  - destruct (Nat.ltb 1 (length (filter (eqb_at dec x) l))) eqn:Hc.
    + apply Nat.ltb_lt in Hc.
      exact (dup_of_two dec x l Hc).
    + apply Nat.ltb_ge in Hc.
      assert (Hlen2 : (length e'
                        < length (filter
                                    (fun y => negb (eqb_at dec x y)) l))%nat).
      { pose proof (filter_length_partition (eqb_at dec x) l) as Hp.
        simpl in Hlen; lia. }
      assert (Hsub2 : ∀ y, TIn y (filter (fun y => negb (eqb_at dec x y)) l)
                             → TIn y e').
      { intros y Hy.
        destruct (TIn_LIn y _ Hy) as [z [Hz Hyz]].
        destruct (LIn_filter _ z l Hz) as [Hzl Hzp].
        assert (Hzx : z ≈ x → False).
        { apply (eqb_at_false dec).
          destruct (eqb_at dec x z); simpl in Hzp;
            [ discriminate | reflexivity ]. }
        pose proof (Hsub y (TIn_filter _ y l Hy)) as Hye.
        simpl in Hye.
        destruct Hye as [Hyx|Hye]; [ | exact Hye ].
        assert (Hzx' : z ≈ x)
          by (etransitivity; [ symmetry; exact Hyz | exact Hyx ]).
        destruct (Hzx Hzx'). }
      exact (HasDup_filter _ l (IHe _ Hsub2 Hlen2)).
Qed.

(* Duplicates in an indexed family, read back as a pair of indices. *)
Lemma TIn_map_seq (f : nat → A) (m : nat) :
  ∀ (s : nat) (x : A), TIn x (map f (seq s m)) →
    { j : nat & ((s <= j)%nat ∧ (j < s + m)%nat) ∧ x ≈ f j }.
Proof.
  induction m as [|m' IH]; simpl; intros s x H.
  - destruct H.
  - destruct H as [H|H].
    + exists s; split; [ split; lia | exact H ].
    + destruct (IH (S s) x H) as [j [[H1 H2] H3]].
      exists j; split; [ split; lia | exact H3 ].
Qed.

Lemma HasDup_map_seq (f : nat → A) (m : nat) :
  ∀ s : nat, HasDup (map f (seq s m)) →
    { i : nat & { j : nat & ((i < j)%nat ∧ (j < s + m)%nat) ∧ f i ≈ f j } }.
Proof.
  induction m as [|m' IH]; simpl; intros s H.
  - destruct H.
  - destruct H as [H|H].
    + destruct (TIn_map_seq f m' (S s) (f s) H) as [j [[H1 H2] H3]].
      exists s, j; split; [ split; lia | exact H3 ].
    + destruct (IH (S s) H) as [i [j [[H1 H2] H3]]].
      exists i, j; split; [ split; lia | exact H3 ].
Qed.

End ListToolkit.

Arguments TIn {A SA} _ _.
Arguments LIn {A} _ _.
Arguments HasDup {A SA} _.
Arguments Decider {A SA}.

(** ** Finiteness as data *)

(* An enumeration complete up to `≈`, together with a decider for `≈`.
   Both are consumed: the enumeration bounds the searches, the decider
   runs them. *)
Record FiniteCarrier (G : AbObject) := {
  fc_enum : list (carrier (cmon_setoid G));
  fc_complete : ∀ a : carrier (cmon_setoid G), TIn a fc_enum;
  fc_dec : Decider (A:=carrier (cmon_setoid G))
}.

Arguments fc_enum {G} _.
Arguments fc_complete {G} _ _.
Arguments fc_dec {G} _ _ _.

(** ** Natural multiples in an abelian group *)

Fixpoint smul (G : AbObject) (n : nat) (a : carrier (cmon_setoid G))
  : carrier (cmon_setoid G) :=
  match n with
  | O => cmon_zero G
  | S n' => cmon_plus G a (smul G n' a)
  end.

(* Subtraction, written out once so the coset arithmetic below reads. *)
Definition asub (G : AbObject) (x y : carrier (cmon_setoid G))
  : carrier (cmon_setoid G) := cmon_plus G x (ab_neg G y).

#[export] Instance smul_Proper (G : AbObject) (n : nat) :
  Proper (equiv ==> equiv) (smul G n).
Proof.
  induction n as [|n' IH]; intros a b Hab; simpl.
  - reflexivity.
  - apply cmon_plus_respects; [ exact Hab | apply IH; exact Hab ].
Qed.

#[export] Instance asub_Proper (G : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (asub G).
Proof.
  intros x x' Hx y y' Hy; unfold asub.
  apply cmon_plus_respects; [ exact Hx | apply ab_neg_respects; exact Hy ].
Qed.

Lemma smul_add (G : AbObject) (m n : nat) (a : carrier (cmon_setoid G)) :
  smul G (m + n)%nat a ≈ cmon_plus G (smul G m a) (smul G n a).
Proof.
  induction m as [|m' IH]; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - rewrite IH; symmetry; apply cmon_plus_assoc.
Qed.

Lemma smul_mul (G : AbObject) (m n : nat) (a : carrier (cmon_setoid G)) :
  smul G (m * n)%nat a ≈ smul G m (smul G n a).
Proof.
  induction m as [|m' IH]; simpl; [ reflexivity | ].
  rewrite smul_add, IH; reflexivity.
Qed.

Lemma smul_of_zero (G : AbObject) (n : nat) :
  smul G n (cmon_zero G) ≈ cmon_zero G.
Proof.
  induction n as [|n' IH]; simpl; [ reflexivity | ].
  rewrite IH; apply cmon_plus_zero_l.
Qed.

Lemma smul_dist (G : AbObject) (n : nat) (a b : carrier (cmon_setoid G)) :
  smul G n (cmon_plus G a b)
    ≈ cmon_plus G (smul G n a) (smul G n b).
Proof.
  induction n as [|n' IH]; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - rewrite IH.
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
Qed.

Lemma smul_neg (G : AbObject) (n : nat) (a : carrier (cmon_setoid G)) :
  smul G n (ab_neg G a) ≈ ab_neg G (smul G n a).
Proof.
  apply ab_neg_unique.
  rewrite <- smul_dist, ab_neg_left.
  apply smul_of_zero.
Qed.

Lemma smul_hom (G H : AbObject) (f : AbHom G H) (n : nat)
      (a : carrier (cmon_setoid G)) :
  cmon_map f (smul G n a) ≈ smul H n (cmon_map f a).
Proof.
  induction n as [|n' IH]; simpl.
  - apply (cmon_map_zero f).
  - rewrite (cmon_map_plus f), IH; reflexivity.
Qed.

(* Every element of a finite abelian group has a positive annihilator.
   This is the one place the pigeonhole principle is spent: among the
   |G|+1 multiples 0·a, …, |G|·a two must agree, and their difference
   annihilates a. *)
Lemma smul_annihilator (G : AbObject) (F : FiniteCarrier G)
      (a : carrier (cmon_setoid G)) :
  { d : nat & (0 < d)%nat ∧ smul G d a ≈ cmon_zero G }.
Proof.
  pose (N := length (fc_enum F)).
  pose (l := map (fun i => smul G i a) (seq 0 (S N))).
  assert (Hsub : ∀ x, TIn x l → TIn x (fc_enum F)).
  { intros x Hx.
    destruct (TIn_map_seq (fun i => smul G i a) (S N) 0 x Hx)
      as [j [_ Hxj]].
    exact (TIn_respects _ x _ (symmetry Hxj) (fc_complete F (smul G j a))). }
  assert (Hlen : (length (fc_enum F) < length l)%nat).
  { unfold l; rewrite map_length, seq_length; unfold N; lia. }
  destruct (HasDup_map_seq (fun i => smul G i a) (S N) 0
              (pigeon (fc_dec F) _ l Hsub Hlen))
    as [i [j [[Hij _] Hval]]].
  exists (j - i)%nat; split; [ lia | ].
  apply (ab_cancel_l G (smul G i a)).
  rewrite cmon_plus_zero_r, <- smul_add.
  replace (i + (j - i))%nat with j by lia.
  symmetry; exact Hval.
Qed.

(** ** Arithmetic in ℚ/ℤ *)

(* An element of ℚ/ℤ is zero exactly when it is an integer; this is the
   only shape in which [qz_eq] is ever discharged below. *)
Lemma qz_diff_int (x y : Q) (z : Z) : (x - y) == inject_Z z → qz_eq x y.
Proof. intro H; exists z; exact H. Qed.

Lemma qz_int (x : Q) (z : Z) : x == inject_Z z → qz_eq x 0.
Proof. intro H; apply (qz_diff_int _ _ z); rewrite H; ring. Qed.

Lemma inject_Z_of_nat_nz (k : nat) :
  (0 < k)%nat → ~ (inject_Z (Z.of_nat k) == 0).
Proof.
  intros Hk H; unfold Qeq, inject_Z in H; simpl in H; lia.
Qed.

(* Natural multiples in ℚ/ℤ ARE rational multiplication.  This is the
   bridge between the group-theoretic side (orders, coset indices) and
   the arithmetic side (values of characters). *)
Lemma inject_Z_succ_nat (n : nat) :
  inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite inject_Z_plus; reflexivity.
Qed.

Lemma smul_QZ (n : nat) (q : Q) :
  smul QZ n q == inject_Z (Z.of_nat n) * q.
Proof.
  induction n as [|n' IH].
  - assert (H0 : smul QZ 0%nat q == 0) by reflexivity.
    rewrite H0; simpl; ring.
  - assert (Hs : smul QZ (S n') q == q + smul QZ n' q) by reflexivity.
    rewrite Hs, IH, inject_Z_succ_nat; ring.
Qed.

(* The fraction z/k, the canonical shape of a value of a character on an
   element of order dividing k. *)
Definition qfrac (z : Z) (k : nat) : Q :=
  inject_Z z / inject_Z (Z.of_nat k).

Lemma qfrac_mult (z : Z) (k : nat) :
  (0 < k)%nat → inject_Z (Z.of_nat k) * qfrac z k == inject_Z z.
Proof.
  intro Hk; unfold qfrac; field; exact (inject_Z_of_nat_nz k Hk).
Qed.

(* k·q ≈ 0 in ℚ/ℤ pins q to a fraction with denominator k. *)
Lemma qfrac_of_annihilated (q : Q) (k : nat) :
  (0 < k)%nat → qz_eq (smul QZ k q) 0 → { z : Z & q == qfrac z k }.
Proof.
  intros Hk [z Hz].
  exists z.
  rewrite smul_QZ in Hz.
  assert (Hq : inject_Z (Z.of_nat k) * q == inject_Z z)
    by (rewrite <- Hz; ring).
  unfold qfrac; rewrite <- Hq; field; exact (inject_Z_of_nat_nz k Hk).
Qed.

Lemma qfrac_scale (m z : Z) (k : nat) :
  (0 < k)%nat → inject_Z m * qfrac z k == qfrac (m * z) k.
Proof.
  intro Hk; unfold qfrac; rewrite inject_Z_mult; field;
    exact (inject_Z_of_nat_nz k Hk).
Qed.

(* Fractions with the same denominator agree in ℚ/ℤ when their
   numerators agree modulo that denominator. *)
Lemma qfrac_shift (z c : Z) (k : nat) :
  (0 < k)%nat → qz_eq (qfrac (z + c * Z.of_nat k) k) (qfrac z k).
Proof.
  intro Hk; apply (qz_diff_int _ _ c).
  unfold qfrac.
  rewrite inject_Z_plus, inject_Z_mult.
  field; exact (inject_Z_of_nat_nz k Hk).
Qed.

(* 1/k is a nonzero element of ℚ/ℤ once k ≥ 2 — the fact separation
   ultimately rests on. *)
Lemma qfrac_one_nonzero (k : nat) :
  (2 <= k)%nat → qz_eq (qfrac 1 k) 0 → False.
Proof.
  intros Hk [z Hz].
  assert (Hk0 : (0 < k)%nat) by lia.
  assert (Hf : qfrac 1 k == inject_Z z) by (rewrite <- Hz; ring).
  pose proof (qfrac_mult 1 k Hk0) as Hm.
  rewrite Hf, <- inject_Z_mult in Hm.
  unfold Qeq, inject_Z in Hm; simpl in Hm.
  assert (Hkz : (Z.of_nat k * z = 1)%Z) by lia.
  assert (Hk2 : (2 <= Z.of_nat k)%Z) by lia.
  destruct (Z.le_gt_cases z 0) as [Hz0|Hz0]; nia.
Qed.

(** ** Bounded minimization *)

(* The least [i < n] with [p i = true].  Used for coset indices and for
   the period of an element modulo a subgroup; both searches are bounded
   in advance, so no well-founded recursion is involved. *)
Fixpoint least_below (p : nat → bool) (n : nat) : option nat :=
  match n with
  | O => None
  | S n' => match least_below p n' with
            | Some i => Some i
            | None => if p n' then Some n' else None
            end
  end.

Lemma least_below_none (p : nat → bool) (n : nat) :
  least_below p n = None → ∀ j, (j < n)%nat → p j = false.
Proof.
  induction n as [|n' IH]; simpl; intros H j Hj.
  - lia.
  - destruct (least_below p n') as [i'|] eqn:E; [ discriminate | ].
    destruct (p n') eqn:Ep; [ discriminate | ].
    destruct (Nat.eq_dec j n') as [Heq|Hne]; [ rewrite Heq; exact Ep | ].
    apply IH; [ reflexivity | lia ].
Qed.

Lemma least_below_some (p : nat → bool) (n i : nat) :
  least_below p n = Some i →
  ((i < n)%nat ∧ p i = true) ∧ (∀ j, (j < i)%nat → p j = false).
Proof.
  revert i; induction n as [|n' IH]; simpl; intros i H.
  - discriminate.
  - destruct (least_below p n') as [i'|] eqn:E.
    + inversion H; subst i'.
      destruct (IH i eq_refl) as [[H1 H2] H3].
      repeat split; [ lia | exact H2 | exact H3 ].
    + destruct (p n') eqn:Ep; [ | discriminate ].
      inversion H; subst n'.
      repeat split; [ lia | exact Ep | ].
      intros j Hj; exact (least_below_none p i E j Hj).
Qed.

Lemma least_below_found (p : nat → bool) (n i : nat) :
  (i < n)%nat → p i = true → { j : nat & least_below p n = Some j }.
Proof.
  intros Hi Hp.
  destruct (least_below p n) as [j|] eqn:E; [ exists j; reflexivity | ].
  pose proof (least_below_none p n E i Hi) as H; rewrite Hp in H; discriminate.
Qed.

(** ** Subgroups *)

(* A subgroup is a decidable, `≈`-closed predicate containing zero and
   closed under addition and negation.  Membership is [Type]-valued, so
   a membership proof carries the witness data the constructions below
   read back out. *)
Record Subgroup (G : AbObject) := {
  sg_mem : carrier (cmon_setoid G) → Type;
  sg_dec : ∀ x, (sg_mem x + (sg_mem x → False))%type;
  sg_resp : ∀ x y, x ≈ y → sg_mem x → sg_mem y;
  sg_zero : sg_mem (cmon_zero G);
  sg_add : ∀ x y, sg_mem x → sg_mem y → sg_mem (cmon_plus G x y);
  sg_neg : ∀ x, sg_mem x → sg_mem (ab_neg G x)
}.

Arguments sg_mem {G} _ _.
Arguments sg_dec {G} _ _.
Arguments sg_resp {G} _ _ _ _ _.
Arguments sg_zero {G} _.
Arguments sg_add {G} _ _ _ _ _.
Arguments sg_neg {G} _ _ _.

Definition bmem {G : AbObject} (H : Subgroup G)
           (x : carrier (cmon_setoid G)) : bool :=
  if sg_dec H x then true else false.

Lemma bmem_true {G : AbObject} (H : Subgroup G) (x : carrier (cmon_setoid G)) :
  bmem H x = true → sg_mem H x.
Proof.
  unfold bmem; destruct (sg_dec H x) as [Hx|Hx]; intro E;
    [ exact Hx | discriminate ].
Qed.

Lemma bmem_false {G : AbObject} (H : Subgroup G) (x : carrier (cmon_setoid G)) :
  bmem H x = false → sg_mem H x → False.
Proof.
  unfold bmem; destruct (sg_dec H x) as [Hx|Hx]; intros E Hm;
    [ discriminate | exact (Hx Hm) ].
Qed.

Lemma bmem_intro {G : AbObject} (H : Subgroup G) (x : carrier (cmon_setoid G)) :
  sg_mem H x → bmem H x = true.
Proof.
  unfold bmem; destruct (sg_dec H x) as [Hx|Hx]; intro Hm;
    [ reflexivity | destruct (Hx Hm) ].
Qed.

Lemma sg_smul {G : AbObject} (H : Subgroup G) (n : nat)
      (x : carrier (cmon_setoid G)) : sg_mem H x → sg_mem H (smul G n x).
Proof.
  intro Hx; induction n as [|n' IH]; simpl.
  - exact (sg_zero H).
  - exact (sg_add H _ _ Hx IH).
Qed.

Lemma sg_sub {G : AbObject} (H : Subgroup G) (x y : carrier (cmon_setoid G)) :
  sg_mem H x → sg_mem H y → sg_mem H (asub G x y).
Proof.
  intros Hx Hy; unfold asub; exact (sg_add H _ _ Hx (sg_neg H _ Hy)).
Qed.

(* The trivial subgroup {0}. *)
Program Definition TrivialSubgroup (G : AbObject) (F : FiniteCarrier G)
  : Subgroup G := {|
  sg_mem := fun x => x ≈ cmon_zero G
|}.
Next Obligation.
  intros G F x; exact (fc_dec F x (cmon_zero G)).
Qed.
Next Obligation.
  intros G F x y Hxy Hx; simpl in *.
  rewrite <- Hxy; exact Hx.
Qed.
Next Obligation.
  intros G F; simpl; reflexivity.
Qed.
Next Obligation.
  intros G F x y Hx Hy; simpl in *.
  rewrite Hx, Hy; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros G F x Hx; simpl in *.
  rewrite Hx; apply ab_neg_zero.
Qed.

(** ** The period of an element modulo a subgroup *)

(* The least positive [k] with [k·a] already in [H].  Its minimality is
   what makes coset indices unique, hence what makes the extended
   character below well defined. *)
Record Period (G : AbObject) (H : Subgroup G)
       (a : carrier (cmon_setoid G)) := {
  per_k : nat;
  per_pos : (0 < per_k)%nat;
  per_mem : sg_mem H (smul G per_k a);
  per_least : ∀ d, (d < per_k)%nat → sg_mem H (smul G d a) → d = 0%nat
}.

Arguments per_k {G H a} _.
Arguments per_pos {G H a} _.
Arguments per_mem {G H a} _.
Arguments per_least {G H a} _ _ _ _.

(* Every element has a period: some positive multiple annihilates it,
   hence lands in [H], and the search below that bound terminates. *)
Definition period_of (G : AbObject) (F : FiniteCarrier G) (H : Subgroup G)
           (a : carrier (cmon_setoid G)) : Period G H a.
Proof.
  destruct (smul_annihilator G F a) as [d [Hd Hz]].
  pose (p := fun i => andb (Nat.ltb 0 i) (bmem H (smul G i a))).
  assert (Hpd : p d = true).
  { unfold p; apply andb_true_intro; split.
    - apply Nat.ltb_lt; exact Hd.
    - apply bmem_intro; exact (sg_resp H _ _ (symmetry Hz) (sg_zero H)). }
  destruct (least_below_found p (S d) d ltac:(lia) Hpd) as [k Hk].
  destruct (least_below_some p (S d) k Hk) as [[Hk1 Hk2] Hk3].
  unfold p in Hk2; apply andb_prop in Hk2; destruct Hk2 as [Hk2a Hk2b].
  refine {| per_k := k |}.
  - apply Nat.ltb_lt; exact Hk2a.
  - exact (bmem_true H _ Hk2b).
  - intros e He Hem.
    destruct (Nat.eq_dec e 0) as [Heq|Hne]; [ exact Heq | ].
    exfalso.
    pose proof (Hk3 e He) as Hpe.
    unfold p in Hpe.
    assert (Hlt : Nat.ltb 0 e = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt in Hpe; simpl in Hpe.
    exact (bmem_false H _ Hpe Hem).
Defined.

(** ** Elementary abelian-group rearrangements *)

Lemma asub_of_plus (G : AbObject) (x h y : carrier (cmon_setoid G)) :
  x ≈ cmon_plus G h y → asub G x y ≈ h.
Proof.
  intro Hx; unfold asub.
  rewrite Hx, cmon_plus_assoc, ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

Lemma plus_of_asub (G : AbObject) (x y : carrier (cmon_setoid G)) :
  x ≈ cmon_plus G (asub G x y) y.
Proof.
  unfold asub.
  rewrite cmon_plus_assoc, ab_neg_left.
  symmetry; apply cmon_plus_zero_r.
Qed.

(* The middle-four interchange. *)
Lemma plus_four (G : AbObject) (h u h' u' : carrier (cmon_setoid G)) :
  cmon_plus G (cmon_plus G h u) (cmon_plus G h' u')
    ≈ cmon_plus G (cmon_plus G h h') (cmon_plus G u u').
Proof.
  rewrite !cmon_plus_assoc.
  apply cmon_plus_respects; [ reflexivity | ].
  rewrite <- !cmon_plus_assoc.
  apply cmon_plus_respects; [ | reflexivity ].
  apply cmon_plus_comm.
Qed.

Lemma smul_congr_nat (G : AbObject) (m n : nat) (x : carrier (cmon_setoid G)) :
  m = n → smul G m x ≈ smul G n x.
Proof. intro E; rewrite E; reflexivity. Qed.

(** ** The subgroup generated by a subgroup and one further element *)

Section Generated.

Context {G : AbObject}.
Context (H : Subgroup G) (a : carrier (cmon_setoid G)) (P : Period G H a).

Notation k := (per_k P).

(* x lies in ⟨H, a⟩ when it is h + i·a for some member h and some
   natural i.  The index is unbounded here; [gen_reduce] brings it below
   the period, which is what makes membership decidable. *)
Definition gen_mem (x : carrier (cmon_setoid G)) : Type :=
  { i : nat & { h : carrier (cmon_setoid G) &
      sg_mem H h ∧ x ≈ cmon_plus G h (smul G i a) } }.

Lemma gen_reduce (x : carrier (cmon_setoid G)) (i : nat)
      (h : carrier (cmon_setoid G)) :
  sg_mem H h → x ≈ cmon_plus G h (smul G i a) →
  { h' : carrier (cmon_setoid G) &
      sg_mem H h' ∧ x ≈ cmon_plus G h' (smul G (i mod k)%nat a) }.
Proof.
  intros Hh Hx.
  exists (cmon_plus G h (smul G (i / k)%nat (smul G k a))); split.
  - exact (sg_add H _ _ Hh (sg_smul H _ _ (per_mem P))).
  - rewrite Hx, cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- smul_mul, <- smul_add.
    apply smul_congr_nat.
    rewrite (Nat.mul_comm (i / k)%nat k).
    apply Nat.div_mod_eq.
Qed.

Definition gen_dec (x : carrier (cmon_setoid G)) :
  (gen_mem x + (gen_mem x → False))%type.
Proof using All.
  destruct (least_below (fun i => bmem H (asub G x (smul G i a))) k)
    as [i|] eqn:E.
  - left.
    destruct (least_below_some _ k i E) as [[Hi1 Hi2] _].
    exists i, (asub G x (smul G i a)); split.
    + exact (bmem_true H _ Hi2).
    + apply plus_of_asub.
  - right.
    intros [i [h [Hh Hx]]].
    destruct (gen_reduce x i h Hh Hx) as [h' [Hh' Hx']].
    assert (Hb : (i mod k < k)%nat)
      by (apply Nat.mod_upper_bound; pose proof (per_pos P); lia).
    pose proof (least_below_none _ k E (i mod k)%nat Hb) as Hn.
    refine (bmem_false H _ Hn _).
    exact (sg_resp H h' _ (symmetry (asub_of_plus G x h' _ Hx')) Hh').
Defined.

Definition Generated : Subgroup G.
Proof using All.
  unshelve notypeclasses refine {| sg_mem := gen_mem |}.
  - (* sg_dec *)
    exact gen_dec.
  - (* sg_resp *)
    intros x y Hxy [i [h [Hh Hx]]].
    exists i, h; split; [ exact Hh | rewrite <- Hxy; exact Hx ].
  - (* sg_zero *)
    exists 0%nat, (cmon_zero G); split; [ exact (sg_zero H) | ].
    simpl; symmetry; apply cmon_plus_zero_l.
  - (* sg_add *)
    intros x y [i [h [Hh Hx]]] [j [h' [Hh' Hy]]].
    exists (i + j)%nat, (cmon_plus G h h'); split.
    + exact (sg_add H _ _ Hh Hh').
    + rewrite Hx, Hy, plus_four, smul_add; reflexivity.
  - (* sg_neg *)
    intros x [i [h [Hh Hx]]].
    assert (Hik : sg_mem H (smul G (i * k)%nat a)).
    { refine (sg_resp H (smul G i (smul G k a)) _ _ _).
      - symmetry; apply smul_mul.
      - exact (sg_smul H _ _ (per_mem P)). }
    exists (i * k - i)%nat,
      (cmon_plus G (ab_neg G h) (ab_neg G (smul G (i * k)%nat a))); split.
    + exact (sg_add H _ _ (sg_neg H _ Hh) (sg_neg H _ Hik)).
    + rewrite Hx, ab_neg_plus, cmon_plus_assoc.
      apply cmon_plus_respects; [ reflexivity | ].
      symmetry; apply ab_neg_unique.
      rewrite cmon_plus_assoc, <- smul_add.
      assert (Hle : (i <= i * k)%nat)
        by (pose proof (per_pos P); nia).
      rewrite (smul_congr_nat G (i * k - i + i)%nat (i * k)%nat a
                 ltac:(lia)).
      apply ab_neg_left.
Defined.

(* The two inclusions that make ⟨H, a⟩ what it is. *)
Lemma gen_incl (x : carrier (cmon_setoid G)) :
  sg_mem H x → sg_mem Generated x.
Proof.
  intro Hx; exists 0%nat, x; split; [ exact Hx | ].
  simpl; symmetry; apply cmon_plus_zero_r.
Qed.

Lemma gen_gen : sg_mem Generated a.
Proof.
  exists 1%nat, (cmon_zero G); split; [ exact (sg_zero H) | ].
  simpl; rewrite cmon_plus_zero_r; symmetry; apply cmon_plus_zero_l.
Qed.

(* Coset indices below the period are unique — the consequence of
   minimality that makes the extended character well defined. *)
Lemma gen_index_unique (x : carrier (cmon_setoid G)) (i j : nat)
      (h h' : carrier (cmon_setoid G)) :
  (i < k)%nat → (j < k)%nat →
  sg_mem H h → sg_mem H h' →
  x ≈ cmon_plus G h (smul G i a) →
  x ≈ cmon_plus G h' (smul G j a) →
  i = j.
Proof.
  intros Hi Hj Hh Hh' Hx Hx'.
  (* Symmetric in i and j, so it suffices to rule out i < j. *)
  assert (Hkey : ∀ p q : nat, (p < k)%nat → (q < k)%nat → (p <= q)%nat →
            ∀ u u' : carrier (cmon_setoid G),
            sg_mem H u → sg_mem H u' →
            x ≈ cmon_plus G u (smul G p a) →
            x ≈ cmon_plus G u' (smul G q a) → p = q).
  { intros p q Hp Hq Hpq u u' Hu Hu' Hxu Hxu'.
    assert (Hsplit : u ≈ cmon_plus G u' (smul G (q - p)%nat a)).
    { apply (ab_cancel_l G (smul G p a)).
      rewrite (cmon_plus_comm G (smul G p a) u).
      rewrite <- Hxu, Hxu'.
      rewrite (cmon_plus_comm G (smul G p a)
                 (cmon_plus G u' (smul G (q - p)%nat a))).
      rewrite cmon_plus_assoc.
      apply cmon_plus_respects; [ reflexivity | ].
      rewrite <- smul_add.
      apply smul_congr_nat; lia. }
    assert (Hd : smul G (q - p)%nat a ≈ asub G u u').
    { rewrite Hsplit.
      symmetry; apply asub_of_plus; apply cmon_plus_comm. }
    assert (Hm : sg_mem H (smul G (q - p)%nat a))
      by exact (sg_resp H _ _ (symmetry Hd) (sg_sub H _ _ Hu Hu')).
    pose proof (per_least P (q - p)%nat ltac:(lia) Hm) as Hz.
    lia. }
  destruct (Nat.le_ge_cases i j) as [Hle|Hle].
  - exact (Hkey i j Hi Hj Hle h h' Hh Hh' Hx Hx').
  - symmetry; exact (Hkey j i Hj Hi Hle h' h Hh' Hh Hx' Hx).
Qed.

End Generated.

Arguments gen_mem {G} _ _ _.
Arguments Generated {G} _ _ _.

(** ** Congruence helpers for ℚ/ℤ *)

Lemma qz_plus_cong (x x' y y' : Q) :
  qz_eq x x' → qz_eq y y' → qz_eq (x + y) (x' + y').
Proof. intros H1 H2; exact (cmon_plus_respects QZ x x' H1 y y' H2). Qed.

Lemma qz_neg_cong (x y : Q) : qz_eq x y → qz_eq (- x) (- y).
Proof. intro H; exact (ab_neg_respects QZ x y H). Qed.

Lemma inject_nat_congr (i j : nat) :
  i = j → inject_Z (Z.of_nat i) == inject_Z (Z.of_nat j).
Proof. intro E; rewrite E; reflexivity. Qed.

Lemma inject_nat_add (i j : nat) :
  inject_Z (Z.of_nat (i + j)%nat)
    == inject_Z (Z.of_nat i) + inject_Z (Z.of_nat j).
Proof. rewrite Nat2Z.inj_add, inject_Z_plus; reflexivity. Qed.

(** ** Characters of a subgroup *)

(* A character of [H] is a total map on the carrier whose laws are
   demanded only on members.  Nothing is asserted about its values
   elsewhere; the extension below overwrites them. *)
Record PartialChar (G : AbObject) (H : Subgroup G) := {
  pc_map : carrier (cmon_setoid G) → Q;
  pc_respects : ∀ x y, sg_mem H x → x ≈ y → qz_eq (pc_map x) (pc_map y);
  pc_zero : qz_eq (pc_map (cmon_zero G)) 0;
  pc_plus : ∀ x y, sg_mem H x → sg_mem H y →
              qz_eq (pc_map (cmon_plus G x y)) (pc_map x + pc_map y)
}.

Arguments pc_map {G H} _ _.
Arguments pc_respects {G H} _ _ _ _ _.
Arguments pc_zero {G H} _.
Arguments pc_plus {G H} _ _ _ _ _.

Definition ZeroChar (G : AbObject) (H : Subgroup G) : PartialChar G H.
Proof.
  unshelve notypeclasses refine {| pc_map := fun _ => 0 |}.
  - intros x y Hx Hxy; apply qz_eq_refl.
  - apply qz_eq_refl.
  - intros x y Hx Hy; apply qz_of_Qeq; ring.
Defined.

(* Once the predicate holds everywhere, a partial character IS a
   character: this is where the induction cashes out. *)
Definition pc_total (G : AbObject) (H : Subgroup G) (χ : PartialChar G H)
           (Hall : ∀ x, sg_mem H x) : AbHom G QZ.
Proof.
  unshelve notypeclasses refine
    {| cmon_map := {| morphism :=
         (pc_map χ : carrier (cmon_setoid G) → carrier (cmon_setoid QZ)) |} |}.
  - intros x y Hxy; exact (pc_respects χ x y (Hall x) Hxy).
  - exact (pc_zero χ).
  - intros x y; exact (pc_plus χ x y (Hall x) (Hall y)).
Defined.

(* Conversely a genuine character restricts to a partial one, which is
   how the surjectivity induction feeds characters back in. *)
Definition pc_of_hom (G : AbObject) (H : Subgroup G) (φ : AbHom G QZ)
  : PartialChar G H.
Proof.
  unshelve notypeclasses refine {| pc_map := cmon_map φ |}.
  - intros x y Hx Hxy; exact (proper_morphism (cmon_map φ) x y Hxy).
  - exact (cmon_map_zero φ).
  - intros x y Hx Hy; exact (cmon_map_plus φ x y).
Defined.

(** ** Extending a character across one new generator *)

Section Extend.

Context {G : AbObject}.
Context (H : Subgroup G) (a : carrier (cmon_setoid G)) (P : Period G H a).
Context (χ : PartialChar G H) (v : Q).

Notation k := (per_k P).

(* The choice of value at the new generator is constrained exactly by
   [Hv]: k·v must agree, in ℚ/ℤ, with the value χ already assigns to
   k·a.  Any k-th root will do, and the freedom among them is used by
   [separating_character] below. *)
Context (Hv : qz_eq (inject_Z (Z.of_nat k) * v) (pc_map χ (smul G k a))).

Lemma gen_unfold (x : carrier (cmon_setoid G)) :
  sg_mem (Generated H a P) x → gen_mem H a x.
Proof. intro Hx; exact Hx. Qed.

Lemma gen_fold (x : carrier (cmon_setoid G)) :
  gen_mem H a x → sg_mem (Generated H a P) x.
Proof. intro Hx; exact Hx. Qed.

(* Every member of ⟨H, a⟩ decomposes with an index below the period. *)
Lemma gen_decomp (x : carrier (cmon_setoid G)) :
  sg_mem (Generated H a P) x →
  { i : nat & { h : carrier (cmon_setoid G) &
      ((i < k)%nat ∧ sg_mem H h) ∧ x ≈ cmon_plus G h (smul G i a) } }.
Proof.
  intro Hx.
  destruct (gen_unfold x Hx) as [i [h [Hh Hxd]]].
  destruct (gen_reduce H a P x i h Hh Hxd) as [h' [Hh' Hx']].
  exists (i mod k)%nat, h'; split; [ split | exact Hx' ].
  - apply Nat.mod_upper_bound; pose proof (per_pos P); lia.
  - exact Hh'.
Qed.

(* The coset index of x, by bounded search. *)
Definition gidx (x : carrier (cmon_setoid G)) : nat :=
  match least_below (fun i => bmem H (asub G x (smul G i a))) k with
  | Some i => i
  | None => 0%nat
  end.

Definition ext_map (x : carrier (cmon_setoid G)) : Q :=
  pc_map χ (asub G x (smul G (gidx x) a))
    + inject_Z (Z.of_nat (gidx x)) * v.

Lemma gidx_spec (x : carrier (cmon_setoid G)) (i : nat)
      (h : carrier (cmon_setoid G)) :
  (i < k)%nat → sg_mem H h → x ≈ cmon_plus G h (smul G i a) → gidx x = i.
Proof using All.
  intros Hi Hh Hx.
  unfold gidx.
  destruct (least_below (fun i => bmem H (asub G x (smul G i a))) k)
    as [j|] eqn:E.
  - destruct (least_below_some _ k j E) as [[Hj1 Hj2] _].
    exact (gen_index_unique H a P x j i _ h Hj1 Hi
             (bmem_true H _ Hj2) Hh (plus_of_asub G x (smul G j a)) Hx).
  - destruct (bmem_false H _ (least_below_none _ k E i Hi)
                (sg_resp H h _ (symmetry (asub_of_plus G x h _ Hx)) Hh)).
Qed.

(* The characteristic property: on any decomposition with index below
   the period, the extension is χ on the H-part plus i copies of v. *)
Lemma ext_map_spec (x : carrier (cmon_setoid G)) (i : nat)
      (h : carrier (cmon_setoid G)) :
  (i < k)%nat → sg_mem H h → x ≈ cmon_plus G h (smul G i a) →
  qz_eq (ext_map x) (pc_map χ h + inject_Z (Z.of_nat i) * v).
Proof using All.
  intros Hi Hh Hx.
  unfold ext_map.
  rewrite (gidx_spec x i h Hi Hh Hx).
  apply qz_plus_cong; [ | apply qz_eq_refl ].
  apply (pc_respects χ).
  - exact (sg_resp H h _ (symmetry (asub_of_plus G x h _ Hx)) Hh).
  - exact (asub_of_plus G x h (smul G i a) Hx).
Qed.

Lemma ext_map_extends (x : carrier (cmon_setoid G)) :
  sg_mem H x → qz_eq (ext_map x) (pc_map χ x).
Proof using All.
  intro Hx.
  eapply qz_eq_trans.
  - apply (ext_map_spec x 0%nat x (per_pos P) Hx).
    simpl; symmetry; apply cmon_plus_zero_r.
  - apply qz_of_Qeq; simpl; ring.
Qed.

Lemma ext_map_zero : qz_eq (ext_map (cmon_zero G)) 0.
Proof using All.
  eapply qz_eq_trans; [ apply ext_map_extends, (sg_zero H) | ].
  exact (pc_zero χ).
Qed.

Lemma ext_map_plus (x y : carrier (cmon_setoid G)) :
  sg_mem (Generated H a P) x → sg_mem (Generated H a P) y →
  qz_eq (ext_map (cmon_plus G x y)) (ext_map x + ext_map y).
Proof using All.
  intros Hx Hy.
  destruct (gen_decomp x Hx) as [i [h [[Hi Hh] Hxd]]].
  destruct (gen_decomp y Hy) as [j [h' [[Hj Hh'] Hyd]]].
  assert (Hsum : cmon_plus G x y
                   ≈ cmon_plus G (cmon_plus G h h') (smul G (i + j)%nat a)).
  { rewrite Hxd, Hyd, plus_four, smul_add; reflexivity. }
  eapply qz_eq_trans;
    [ | apply qz_eq_sym, qz_plus_cong;
        [ exact (ext_map_spec x i h Hi Hh Hxd)
        | exact (ext_map_spec y j h' Hj Hh' Hyd) ] ].
  destruct (Nat.ltb (i + j)%nat k) eqn:Hc.
  - apply Nat.ltb_lt in Hc.
    eapply qz_eq_trans;
      [ exact (ext_map_spec _ (i + j)%nat (cmon_plus G h h') Hc
                 (sg_add H _ _ Hh Hh') Hsum) | ].
    eapply qz_eq_trans;
      [ apply qz_plus_cong;
        [ exact (pc_plus χ h h' Hh Hh') | apply qz_eq_refl ] | ].
    apply qz_of_Qeq; rewrite inject_nat_add; ring.
  - apply Nat.ltb_ge in Hc.
    assert (Hm : (i + j - k < k)%nat) by (pose proof (per_pos P); lia).
    assert (Hsum2 : cmon_plus G x y
                      ≈ cmon_plus G
                          (cmon_plus G (cmon_plus G h h') (smul G k a))
                          (smul G (i + j - k)%nat a)).
    { rewrite Hsum.
      rewrite (cmon_plus_assoc G (cmon_plus G h h') (smul G k a)
                 (smul G (i + j - k)%nat a)).
      rewrite <- smul_add.
      apply cmon_plus_respects; [ reflexivity | ].
      apply smul_congr_nat; lia. }
    eapply qz_eq_trans;
      [ exact (ext_map_spec _ (i + j - k)%nat
                 (cmon_plus G (cmon_plus G h h') (smul G k a)) Hm
                 (sg_add H _ _ (sg_add H _ _ Hh Hh') (per_mem P)) Hsum2) | ].
    eapply qz_eq_trans;
      [ apply qz_plus_cong;
        [ exact (pc_plus χ _ _ (sg_add H _ _ Hh Hh') (per_mem P))
        | apply qz_eq_refl ] | ].
    eapply qz_eq_trans;
      [ apply qz_plus_cong;
        [ apply qz_plus_cong;
          [ exact (pc_plus χ h h' Hh Hh')
          | apply qz_eq_sym; exact Hv ]
        | apply qz_eq_refl ] | ].
    apply qz_of_Qeq.
    assert (Hmi : inject_Z (Z.of_nat (i + j - k)%nat)
                    == inject_Z (Z.of_nat i) + inject_Z (Z.of_nat j)
                         - inject_Z (Z.of_nat k)).
    { rewrite <- inject_nat_add.
      rewrite <- (inject_nat_congr ((i + j - k) + k)%nat (i + j)%nat
                    ltac:(lia)).
      rewrite inject_nat_add; ring. }
    rewrite Hmi; ring.
Qed.

Lemma ext_map_respects (x y : carrier (cmon_setoid G)) :
  sg_mem (Generated H a P) x → x ≈ y → qz_eq (ext_map x) (ext_map y).
Proof using All.
  intros Hx Hxy.
  destruct (gen_decomp x Hx) as [i [h [[Hi Hh] Hxd]]].
  eapply qz_eq_trans; [ exact (ext_map_spec x i h Hi Hh Hxd) | ].
  apply qz_eq_sym.
  apply (ext_map_spec y i h Hi Hh).
  rewrite <- Hxy; exact Hxd.
Qed.

Definition ExtendChar : PartialChar G (Generated H a P).
Proof using All.
  unshelve notypeclasses refine {| pc_map := ext_map |}.
  - exact ext_map_respects.
  - exact ext_map_zero.
  - exact ext_map_plus.
Defined.

(* The value at the new generator is exactly the chosen root, provided
   the generator was genuinely new. *)
Lemma ext_map_at_gen : (sg_mem H a → False) → qz_eq (ext_map a) v.
Proof using All.
  intro Hna.
  assert (Hk2 : (2 <= k)%nat).
  { pose proof (per_pos P) as Hp.
    destruct (Nat.eq_dec k 1%nat) as [He|Hne]; [ | lia ].
    exfalso; apply Hna.
    refine (sg_resp H (smul G k a) a _ (per_mem P)).
    rewrite He; simpl; apply cmon_plus_zero_r. }
  eapply qz_eq_trans.
  - apply (ext_map_spec a 1%nat (cmon_zero G) ltac:(lia) (sg_zero H)).
    simpl; rewrite cmon_plus_zero_r; symmetry; apply cmon_plus_zero_l.
  - eapply qz_eq_trans;
      [ apply qz_plus_cong; [ exact (pc_zero χ) | apply qz_eq_refl ] | ].
    apply qz_of_Qeq; simpl; ring.
Qed.

End Extend.

(** ** The measure: enumeration entries outside a subgroup *)

Lemma LIn_length {A : Type} (x : A) (l : list A) :
  LIn x l → (0 < length l)%nat.
Proof.
  destruct l as [|y r]; simpl; intro H; [ destruct H | lia ].
Qed.

Lemma filter_length_lt {A : Type} (l : list A) (p q : A → bool) :
  (∀ x, q x = true → p x = true) →
  ∀ z, LIn z l → p z = true → q z = false →
  (length (filter q l) < length (filter p l))%nat.
Proof.
  intros Hpq z.
  induction l as [|y r IH]; simpl; intros Hz Hp Hq.
  - destruct Hz.
  - destruct Hz as [Hz|Hz].
    + subst y.
      rewrite Hp, Hq; simpl.
      assert (Hle : (length (filter q r) <= length (filter p r))%nat).
      { clear IH Hp Hq.
        induction r as [|w s IHs]; simpl; [ lia | ].
        destruct (q w) eqn:Hqw.
        - rewrite (Hpq w Hqw); simpl; lia.
        - destruct (p w); simpl; lia. }
      lia.
    + specialize (IH Hz Hp Hq).
      destruct (q y) eqn:Hqy.
      * rewrite (Hpq y Hqy); simpl; lia.
      * destruct (p y); simpl; lia.
Qed.

Definition outside (G : AbObject) (F : FiniteCarrier G) (H : Subgroup G)
  : list (carrier (cmon_setoid G)) :=
  filter (fun x => negb (bmem H x)) (fc_enum F).

Definition outside_count (G : AbObject) (F : FiniteCarrier G)
           (H : Subgroup G) : nat := length (outside G F H).

(* Either the subgroup is everything, or the enumeration names an
   element outside it.  This is the case split both inductions run on. *)
Definition all_or_witness (G : AbObject) (F : FiniteCarrier G)
           (H : Subgroup G) :
  ((∀ x, sg_mem H x)
     + { a : carrier (cmon_setoid G) & sg_mem H a → False })%type.
Proof.
  destruct (outside G F H) as [|z r] eqn:E.
  - left; intro x.
    destruct (TIn_LIn x (fc_enum F) (fc_complete F x)) as [y [Hy Hxy]].
    destruct (bmem H y) eqn:Hb.
    + exact (sg_resp H y x (symmetry Hxy) (bmem_true H y Hb)).
    + exfalso.
      assert (Hin : LIn y (outside G F H)).
      { unfold outside; apply LIn_filter_intro;
          [ exact Hy | rewrite Hb; reflexivity ]. }
      rewrite E in Hin; exact Hin.
  - right; exists z.
    assert (Hin : LIn z (outside G F H)) by (rewrite E; left; reflexivity).
    unfold outside in Hin.
    destruct (LIn_filter _ z (fc_enum F) Hin) as [_ Hb].
    apply bmem_false.
    destruct (bmem H z); [ discriminate | reflexivity ].
Defined.

(* Adjoining a non-member strictly decreases the measure. *)
Lemma outside_count_generated (G : AbObject) (F : FiniteCarrier G)
      (H : Subgroup G) (a : carrier (cmon_setoid G)) (P : Period G H a) :
  (sg_mem H a → False) →
  (outside_count G F (Generated H a P) < outside_count G F H)%nat.
Proof.
  intro Hna.
  destruct (TIn_LIn a (fc_enum F) (fc_complete F a)) as [y [Hy Hay]].
  assert (Hpq : ∀ x, negb (bmem (Generated H a P) x) = true
                       → negb (bmem H x) = true).
  { intros x Hx.
    destruct (bmem H x) eqn:Hb; [ | reflexivity ].
    exfalso.
    assert (Hg : bmem (Generated H a P) x = true)
      by (apply bmem_intro, gen_incl, (bmem_true H x Hb)).
    rewrite Hg in Hx; discriminate. }
  assert (Hp : negb (bmem H y) = true).
  { destruct (bmem H y) eqn:Hb; [ | reflexivity ].
    exfalso; exact (Hna (sg_resp H y a (symmetry Hay) (bmem_true H y Hb))). }
  assert (Hq : negb (bmem (Generated H a P) y) = false).
  { assert (Hg : sg_mem (Generated H a P) y)
      by exact (sg_resp _ a y Hay (gen_gen H a P)).
    rewrite (bmem_intro _ y Hg); reflexivity. }
  unfold outside_count, outside.
  exact (filter_length_lt (fc_enum F) _ _ Hpq y Hy Hp Hq).
Qed.

(** ** The character-extension theorem *)

(* Division in ℚ is total away from zero, so a k-th root in ℚ/ℤ is
   computed rather than chosen. *)
Definition root_of (k : nat) (q : Q) : Q := q / inject_Z (Z.of_nat k).

Lemma root_of_spec (k : nat) (q : Q) :
  (0 < k)%nat → inject_Z (Z.of_nat k) * root_of k q == q.
Proof.
  intro Hk; unfold root_of; field; exact (inject_Z_of_nat_nz k Hk).
Qed.

Lemma character_extend_aux (G : AbObject) (F : FiniteCarrier G) (n : nat) :
  ∀ H : Subgroup G, (outside_count G F H <= n)%nat →
  ∀ χ : PartialChar G H,
  { φ : AbHom G QZ & ∀ x, sg_mem H x → qz_eq (cmon_map φ x) (pc_map χ x) }.
Proof.
  induction n as [|n' IH]; intros H Hn χ;
    destruct (all_or_witness G F H) as [Hall|[a Hna]].
  - exists (pc_total G H χ Hall); intros x Hx; apply qz_eq_refl.
  - exfalso.
    pose proof (outside_count_generated G F H a (period_of G F H a) Hna).
    lia.
  - exists (pc_total G H χ Hall); intros x Hx; apply qz_eq_refl.
  - pose proof (period_of G F H a) as P.
    pose proof (per_pos P) as Hk.
    refine (let v := root_of (per_k P) (pc_map χ (smul G (per_k P) a)) in _).
    assert (Hv : qz_eq (inject_Z (Z.of_nat (per_k P)) * v)
                       (pc_map χ (smul G (per_k P) a)))
      by (apply qz_of_Qeq; apply root_of_spec; exact Hk).
    destruct (IH (Generated H a P)
                ltac:(pose proof (outside_count_generated G F H a P Hna); lia)
                (ExtendChar H a P χ v Hv)) as [φ Hφ].
    exists φ; intros x Hx.
    eapply qz_eq_trans; [ exact (Hφ x (gen_incl H a P x Hx)) | ].
    exact (ext_map_extends H a P χ v Hv x Hx).
Qed.

Theorem character_extend (G : AbObject) (F : FiniteCarrier G)
        (H : Subgroup G) (χ : PartialChar G H) :
  { φ : AbHom G QZ & ∀ x, sg_mem H x → qz_eq (cmon_map φ x) (pc_map χ x) }.
Proof.
  exact (character_extend_aux G F (outside_count G F H) H (le_n _) χ).
Qed.

(* The form both consumers use: extend across one prescribed new
   generator, with a prescribed value there. *)
Theorem character_extend_at (G : AbObject) (F : FiniteCarrier G)
        (H : Subgroup G) (χ : PartialChar G H)
        (a : carrier (cmon_setoid G)) (P : Period G H a) (v : Q) :
  (sg_mem H a → False) →
  qz_eq (inject_Z (Z.of_nat (per_k P)) * v) (pc_map χ (smul G (per_k P) a)) →
  { φ : AbHom G QZ &
      (∀ x, sg_mem H x → qz_eq (cmon_map φ x) (pc_map χ x))
        ∧ qz_eq (cmon_map φ a) v }.
Proof.
  intros Hna Hv.
  destruct (character_extend G F (Generated H a P)
              (ExtendChar H a P χ v Hv)) as [φ Hφ].
  exists φ; split.
  - intros x Hx.
    eapply qz_eq_trans; [ exact (Hφ x (gen_incl H a P x Hx)) | ].
    exact (ext_map_extends H a P χ v Hv x Hx).
  - eapply qz_eq_trans; [ exact (Hφ a (gen_gen H a P)) | ].
    exact (ext_map_at_gen H a P χ v Hv Hna).
Qed.

(** ** Separation: a character that does not kill a given element *)

Lemma period_ge_two (G : AbObject) (H : Subgroup G)
      (a : carrier (cmon_setoid G)) (P : Period G H a) :
  (sg_mem H a → False) → (2 <= per_k P)%nat.
Proof.
  intro Hna.
  pose proof (per_pos P) as Hp.
  destruct (Nat.eq_dec (per_k P) 1%nat) as [He|Hne]; [ | lia ].
  exfalso; apply Hna.
  refine (sg_resp H (smul G (per_k P) a) a _ (per_mem P)).
  rewrite He; simpl; apply cmon_plus_zero_r.
Qed.

(* The value of a character on a decomposed element.  Used throughout
   the surjectivity argument. *)
Lemma hom_decomp (G : AbObject) (φ : AbHom G QZ)
      (x h a : carrier (cmon_setoid G)) (i : nat) :
  x ≈ cmon_plus G h (smul G i a) →
  qz_eq (cmon_map φ x)
        (cmon_map φ h + inject_Z (Z.of_nat i) * cmon_map φ a).
Proof.
  intro Hx.
  eapply qz_eq_trans; [ exact (proper_morphism (cmon_map φ) x _ Hx) | ].
  eapply qz_eq_trans; [ exact (cmon_map_plus φ h (smul G i a)) | ].
  apply qz_plus_cong; [ apply qz_eq_refl | ].
  eapply qz_eq_trans; [ exact (smul_hom G QZ φ i a) | ].
  apply qz_of_Qeq; apply smul_QZ.
Qed.

(* The character forced to 1/k on a new generator and to zero on the
   old subgroup.  Both consumers of the extension theorem use exactly
   this shape. *)
Lemma cyclic_character (G : AbObject) (F : FiniteCarrier G)
      (H : Subgroup G) (a : carrier (cmon_setoid G)) (P : Period G H a)
      (Hna : sg_mem H a → False) :
  { φ : AbHom G QZ &
      (∀ x, sg_mem H x → qz_eq (cmon_map φ x) 0)
        ∧ qz_eq (cmon_map φ a) (qfrac 1 (per_k P)) }.
Proof.
  assert (Hv : qz_eq (inject_Z (Z.of_nat (per_k P)) * qfrac 1 (per_k P))
                 (pc_map (ZeroChar G H) (smul G (per_k P) a))).
  { apply (qz_int _ 1%Z); apply qfrac_mult; exact (per_pos P). }
  destruct (character_extend_at G F H (ZeroChar G H) a P
              (qfrac 1 (per_k P)) Hna Hv) as [φ [Hφ0 Hφa]].
  exists φ; split; [ | exact Hφa ].
  intros x Hx; exact (Hφ0 x Hx).
Qed.

Theorem separating_character (G : AbObject) (F : FiniteCarrier G)
        (a : carrier (cmon_setoid G)) :
  (a ≈ cmon_zero G → False) →
  { φ : AbHom G QZ & qz_eq (cmon_map φ a) 0 → False }.
Proof.
  intro Hna0.
  assert (Hna : sg_mem (TrivialSubgroup G F) a → False) by exact Hna0.
  pose proof (period_of G F (TrivialSubgroup G F) a) as P.
  destruct (cyclic_character G F (TrivialSubgroup G F) a P Hna)
    as [φ [_ Hφa]].
  exists φ; intro Hz.
  apply (qfrac_one_nonzero (per_k P)
           (period_ge_two G (TrivialSubgroup G F) a P Hna)).
  exact (qz_eq_trans _ _ _ (qz_eq_sym _ _ Hφa) Hz).
Qed.

(** ** Injectivity of the evaluation *)

(* [ab_map_neg] with the negation of ℚ/ℤ spelt as [Qopp], so that [ring]
   recognises it. *)
Lemma hom_neg (G : AbObject) (φ : AbHom G QZ) (y : carrier (cmon_setoid G)) :
  qz_eq (cmon_map φ (ab_neg G y)) (- cmon_map φ y).
Proof. exact (ab_map_neg φ y). Qed.

Theorem tau_injective_finite (G : AbObject) (F : FiniteCarrier G) :
  AbInjective (tau G).
Proof.
  intros x y Hxy.
  destruct (fc_dec F x y) as [He|Hne]; [ exact He | ].
  exfalso.
  assert (Hd : asub G x y ≈ cmon_zero G → False).
  { intro Hd0; apply Hne.
    etransitivity; [ exact (plus_of_asub G x y) | ].
    rewrite Hd0; apply cmon_plus_zero_l. }
  destruct (separating_character G F (asub G x y) Hd) as [φ Hφ].
  apply Hφ.
  unfold asub.
  eapply qz_eq_trans; [ exact (cmon_map_plus φ x (ab_neg G y)) | ].
  eapply qz_eq_trans;
    [ apply qz_plus_cong; [ apply qz_eq_refl | exact (hom_neg G φ y) ] | ].
  eapply qz_eq_trans;
    [ apply qz_plus_cong; [ exact (Hxy φ) | apply qz_eq_refl ] | ].
  apply qz_of_Qeq; cbn; ring.
Qed.

(** ** Further ℚ/ℤ helpers *)

Lemma qz_scale (n : Z) (x y : Q) :
  qz_eq x y → qz_eq (inject_Z n * x) (inject_Z n * y).
Proof.
  intros [z Hz]; exists (n * z)%Z.
  rewrite inject_Z_mult, <- Hz; ring.
Qed.

Lemma qz_sub_zero (x y : Q) : qz_eq (x + - y) 0 → qz_eq x y.
Proof. intros [z Hz]; exists z; rewrite <- Hz; ring. Qed.

Lemma qz_zero_sub (x y : Q) : qz_eq x y → qz_eq (x + - y) 0.
Proof. intros [z Hz]; exists z; rewrite <- Hz; ring. Qed.

Lemma qz_move (x y w : Q) : qz_eq (x + - y) w → qz_eq x (w + y).
Proof. intros [z Hz]; exists z; rewrite <- Hz; ring. Qed.

Lemma qfrac_congr (z z' : Z) (k : nat) : z = z' → qfrac z k = qfrac z' k.
Proof. intro E; rewrite E; reflexivity. Qed.

(* An element annihilated by k is a fraction with denominator k whose
   numerator can be taken in [0, k). *)
Lemma qfrac_nat_form (q : Q) (k : nat) :
  (0 < k)%nat → qz_eq (smul QZ k q) 0 →
  { m : nat & (m < k)%nat ∧ qz_eq q (qfrac (Z.of_nat m) k) }.
Proof.
  intros Hk Hann.
  destruct (qfrac_of_annihilated q k Hk Hann) as [z Hz].
  assert (Hb : (0 <= z mod Z.of_nat k < Z.of_nat k)%Z)
    by (apply Z.mod_pos_bound; lia).
  exists (Z.to_nat (z mod Z.of_nat k)); split; [ lia | ].
  eapply qz_eq_trans; [ apply qz_of_Qeq; exact Hz | ].
  assert (Hsplit : z = (Z.of_nat (Z.to_nat (z mod Z.of_nat k))
                          + (z / Z.of_nat k) * Z.of_nat k)%Z).
  { rewrite Z2Nat.id by lia.
    pose proof (Z.div_mod z (Z.of_nat k) ltac:(lia)); lia. }
  rewrite (qfrac_congr z _ k Hsplit).
  apply qfrac_shift; exact Hk.
Qed.

(** ** Evaluation of the pointwise operations on characters *)

Lemma char_plus_eval (G : AbObject) (χ ψ : AbHom G QZ)
      (x : carrier (cmon_setoid G)) :
  qz_eq (cmon_map (cmon_plus (D_ob G) χ ψ) x)
        (cmon_map χ x + cmon_map ψ x).
Proof. apply qz_eq_refl. Qed.

Lemma char_neg_eval (G : AbObject) (χ : AbHom G QZ)
      (x : carrier (cmon_setoid G)) :
  qz_eq (cmon_map (ab_neg (D_ob G) χ) x) (- cmon_map χ x).
Proof. apply qz_eq_refl. Qed.

(* A natural multiple of a character is the rational multiple of its
   values, since the character group's addition is pointwise. *)
Lemma smul_char (G : AbObject) (n : nat) (φ : AbHom G QZ)
      (x : carrier (cmon_setoid G)) :
  qz_eq (cmon_map (smul (D_ob G) n φ) x)
        (inject_Z (Z.of_nat n) * cmon_map φ x).
Proof.
  eapply qz_eq_trans;
    [ exact (smul_hom (D_ob G) QZ (tau_component x) n φ) | ].
  apply qz_of_Qeq; apply smul_QZ.
Qed.

(* The value of a character that kills H, on an element of ⟨H, a⟩. *)
Lemma ann_char_value (G : AbObject) (H : Subgroup G)
      (a : carrier (cmon_setoid G)) (k : nat) (Hk : (0 < k)%nat)
      (χ : AbHom G QZ) (m : Z)
      (Hχ0 : ∀ y, sg_mem H y → qz_eq (cmon_map χ y) 0)
      (Hχa : qz_eq (cmon_map χ a) (qfrac m k))
      (x h : carrier (cmon_setoid G)) (i : nat) :
  sg_mem H h → x ≈ cmon_plus G h (smul G i a) →
  qz_eq (cmon_map χ x) (qfrac (Z.of_nat i * m)%Z k).
Proof.
  intros Hh Hxd.
  eapply qz_eq_trans; [ exact (hom_decomp G χ x h a i Hxd) | ].
  eapply qz_eq_trans;
    [ apply qz_plus_cong;
      [ exact (Hχ0 h Hh) | exact (qz_scale (Z.of_nat i) _ _ Hχa) ] | ].
  apply qz_of_Qeq.
  rewrite (qfrac_scale (Z.of_nat i) m k Hk); ring.
Qed.

(** ** Surjectivity of the evaluation *)

(* [Ann G H χ]: χ kills H.  [VanishesOn G H Ξ]: Ξ kills every character
   that kills H — the annihilator of the annihilator, at the level of
   the double dual.  [Realizes] is the conclusion of the induction. *)
Definition Ann (G : AbObject) (H : Subgroup G) (χ : AbHom G QZ) : Type :=
  ∀ x, sg_mem H x → qz_eq (cmon_map χ x) 0.

Definition VanishesOn (G : AbObject) (H : Subgroup G)
           (Ξ : AbHom (D_ob G) QZ) : Type :=
  ∀ χ : AbHom G QZ, Ann G H χ → qz_eq (cmon_map Ξ χ) 0.

Definition Realizes (G : AbObject) (H : Subgroup G)
           (Ξ : AbHom (D_ob G) QZ) : Type :=
  { c : carrier (cmon_setoid G) & sg_mem H c
      ∧ (∀ χ : AbHom G QZ, qz_eq (cmon_map Ξ χ) (cmon_map χ c)) }.

(* When the subgroup is everything its annihilator is trivial, so the
   hypothesis of the induction becomes vacuous. *)
Lemma vanishes_of_all (G : AbObject) (H : Subgroup G) :
  (∀ x, sg_mem H x) → ∀ Ξ : AbHom (D_ob G) QZ, VanishesOn G H Ξ.
Proof.
  intros Hall Ξ χ Hχ.
  eapply qz_eq_trans; [ | exact (cmon_map_zero Ξ) ].
  apply (proper_morphism (cmon_map Ξ)).
  intro x; exact (Hχ x (Hall x)).
Qed.

(* Base case: a functional killing every character is the evaluation at
   zero. *)
Lemma realizes_trivial (G : AbObject) (F : FiniteCarrier G)
      (Ξ : AbHom (D_ob G) QZ) :
  VanishesOn G (TrivialSubgroup G F) Ξ → Realizes G (TrivialSubgroup G F) Ξ.
Proof.
  intro HΞ.
  exists (cmon_zero G); split; [ simpl; reflexivity | ].
  intro χ.
  eapply qz_eq_trans.
  - apply HΞ.
    intros x Hx.
    eapply qz_eq_trans;
      [ exact (proper_morphism (cmon_map χ) x (cmon_zero G) Hx) | ].
    exact (cmon_map_zero χ).
  - apply qz_eq_sym; exact (cmon_map_zero χ).
Qed.

(* The induction step.  The correction term is τ(n·a) for the numerator
   n of Ξ(φ), where φ is the character with φ|H = 0 and φ(a) = 1/k. *)
Lemma realizes_step (G : AbObject) (F : FiniteCarrier G)
      (H : Subgroup G) (a : carrier (cmon_setoid G)) (P : Period G H a)
      (Hna : sg_mem H a → False) :
  (∀ Ξ, VanishesOn G H Ξ → Realizes G H Ξ) →
  ∀ Ξ, VanishesOn G (Generated H a P) Ξ → Realizes G (Generated H a P) Ξ.
Proof.
  intros IH Ξ HΞ.
  pose proof (per_pos P) as Hk.
  destruct (cyclic_character G F H a P Hna) as [φ [Hφ0 Hφa]].
  assert (Hφval : ∀ (x h : carrier (cmon_setoid G)) (i : nat),
             sg_mem H h → x ≈ cmon_plus G h (smul G i a) →
             qz_eq (cmon_map φ x) (qfrac (Z.of_nat i * 1)%Z (per_k P)))
    by (intros x h i Hh Hxd;
        exact (ann_char_value G H a (per_k P) Hk φ 1%Z Hφ0 Hφa x h i Hh Hxd)).
  (* k·φ kills ⟨H, a⟩. *)
  assert (Hkφ : Ann G (Generated H a P) (smul (D_ob G) (per_k P) φ)).
  { intros x Hx.
    destruct (gen_decomp H a P x Hx) as [i [h [[Hi Hh] Hxd]]].
    eapply qz_eq_trans; [ exact (smul_char G (per_k P) φ x) | ].
    eapply qz_eq_trans;
      [ exact (qz_scale (Z.of_nat (per_k P)) _ _ (Hφval x h i Hh Hxd)) | ].
    apply (qz_int _ (Z.of_nat i * 1)%Z).
    apply qfrac_mult; exact Hk. }
  (* Hence Ξ(φ) has denominator k. *)
  assert (HΞφ : qz_eq (smul QZ (per_k P) (cmon_map Ξ φ)) 0).
  { eapply qz_eq_trans;
      [ apply qz_eq_sym; exact (smul_hom (D_ob G) QZ Ξ (per_k P) φ) | ].
    exact (HΞ _ Hkφ). }
  destruct (qfrac_nat_form (cmon_map Ξ φ) (per_k P) Hk HΞφ) as [n [Hnb Hn]].
  (* On the annihilator of H, Ξ agrees with evaluation at n·a. *)
  assert (Hcorr : ∀ χ : AbHom G QZ, Ann G H χ →
                    qz_eq (cmon_map Ξ χ) (cmon_map χ (smul G n a))).
  { intros χ Hχ0.
    assert (Hka : qz_eq (smul QZ (per_k P) (cmon_map χ a)) 0).
    { eapply qz_eq_trans;
        [ apply qz_eq_sym; exact (smul_hom G QZ χ (per_k P) a) | ].
      exact (Hχ0 _ (per_mem P)). }
    destruct (qfrac_nat_form (cmon_map χ a) (per_k P) Hk Hka) as [m [Hmb Hm]].
    (* χ − m·φ kills ⟨H, a⟩ *)
    assert (Hψ : Ann G (Generated H a P)
                   (cmon_plus (D_ob G) χ
                      (ab_neg (D_ob G) (smul (D_ob G) m φ)))).
    { intros x Hx.
      destruct (gen_decomp H a P x Hx) as [i [h [[Hi Hh] Hxd]]].
      assert (Hχx : qz_eq (cmon_map χ x)
                      (qfrac (Z.of_nat i * Z.of_nat m)%Z (per_k P)))
        by exact (ann_char_value G H a (per_k P) Hk χ (Z.of_nat m)
                    Hχ0 Hm x h i Hh Hxd).
      assert (Hmφx : qz_eq (cmon_map (smul (D_ob G) m φ) x)
                       (qfrac (Z.of_nat m * (Z.of_nat i * 1))%Z (per_k P))).
      { eapply qz_eq_trans; [ exact (smul_char G m φ x) | ].
        eapply qz_eq_trans;
          [ exact (qz_scale (Z.of_nat m) _ _ (Hφval x h i Hh Hxd)) | ].
        apply qz_of_Qeq; apply qfrac_scale; exact Hk. }
      eapply qz_eq_trans; [ exact (char_plus_eval G χ _ x) | ].
      eapply qz_eq_trans;
        [ apply qz_plus_cong;
          [ exact Hχx
          | eapply qz_eq_trans;
              [ exact (char_neg_eval G (smul (D_ob G) m φ) x)
              | exact (qz_neg_cong _ _ Hmφx) ] ] | ].
      apply qz_of_Qeq.
      rewrite (qfrac_congr (Z.of_nat m * (Z.of_nat i * 1))%Z
                 (Z.of_nat i * Z.of_nat m)%Z (per_k P) ltac:(lia)).
      ring. }
    (* so Ξ(χ) = m·Ξ(φ) *)
    assert (Hev : qz_eq
                    (cmon_map Ξ (cmon_plus (D_ob G) χ
                       (ab_neg (D_ob G) (smul (D_ob G) m φ))))
                    (cmon_map Ξ χ
                       + - (inject_Z (Z.of_nat m) * cmon_map Ξ φ))).
    { eapply qz_eq_trans;
        [ exact (cmon_map_plus Ξ χ
                   (ab_neg (D_ob G) (smul (D_ob G) m φ))) | ].
      apply qz_plus_cong; [ apply qz_eq_refl | ].
      eapply qz_eq_trans;
        [ exact (hom_neg (D_ob G) Ξ (smul (D_ob G) m φ)) | ].
      apply qz_neg_cong.
      eapply qz_eq_trans; [ exact (smul_hom (D_ob G) QZ Ξ m φ) | ].
      apply qz_of_Qeq; apply smul_QZ. }
    assert (HΞχ : qz_eq (cmon_map Ξ χ)
                    (inject_Z (Z.of_nat m) * cmon_map Ξ φ)).
    { apply qz_sub_zero.
      exact (qz_eq_trans _ _ _ (qz_eq_sym _ _ Hev) (HΞ _ Hψ)). }
    assert (H1 : qz_eq (cmon_map χ (smul G n a))
                   (qfrac (Z.of_nat n * Z.of_nat m)%Z (per_k P))).
    { eapply qz_eq_trans; [ exact (smul_hom G QZ χ n a) | ].
      eapply qz_eq_trans; [ apply qz_of_Qeq; apply smul_QZ | ].
      eapply qz_eq_trans; [ exact (qz_scale (Z.of_nat n) _ _ Hm) | ].
      apply qz_of_Qeq; apply qfrac_scale; exact Hk. }
    assert (H2 : qz_eq (inject_Z (Z.of_nat m) * cmon_map Ξ φ)
                   (qfrac (Z.of_nat m * Z.of_nat n)%Z (per_k P))).
    { eapply qz_eq_trans; [ exact (qz_scale (Z.of_nat m) _ _ Hn) | ].
      apply qz_of_Qeq; apply qfrac_scale; exact Hk. }
    eapply qz_eq_trans; [ exact HΞχ | ].
    eapply qz_eq_trans; [ exact H2 | ].
    apply qz_eq_sym.
    eapply qz_eq_trans; [ exact H1 | ].
    rewrite (qfrac_congr (Z.of_nat n * Z.of_nat m)%Z
               (Z.of_nat m * Z.of_nat n)%Z (per_k P) ltac:(lia)).
    apply qz_eq_refl. }
  (* Ξ − τ(n·a) vanishes on the annihilator of H, so the inductive
     hypothesis applies to it. *)
  assert (HVan : VanishesOn G H
            (cmon_plus (D_ob (D_ob G)) Ξ
               (ab_neg (D_ob (D_ob G)) (tau_component (smul G n a))))).
  { intros χ Hχ.
    eapply qz_eq_trans; [ exact (char_plus_eval (D_ob G) Ξ _ χ) | ].
    eapply qz_eq_trans;
      [ apply qz_plus_cong;
        [ apply qz_eq_refl
        | exact (char_neg_eval (D_ob G)
                   (tau_component (smul G n a)) χ) ] | ].
    exact (qz_zero_sub _ _ (Hcorr χ Hχ)). }
  destruct (IH _ HVan) as [c [Hc Hcχ]].
  exists (cmon_plus G c (smul G n a)); split.
  - apply (gen_fold H a P).
    exists n, c; split; [ exact Hc | reflexivity ].
  - intro χ.
    assert (Hev : qz_eq
                    (cmon_map (cmon_plus (D_ob (D_ob G)) Ξ
                       (ab_neg (D_ob (D_ob G))
                          (tau_component (smul G n a)))) χ)
                    (cmon_map Ξ χ + - cmon_map χ (smul G n a))).
    { eapply qz_eq_trans; [ exact (char_plus_eval (D_ob G) Ξ _ χ) | ].
      apply qz_plus_cong; [ apply qz_eq_refl | ].
      exact (char_neg_eval (D_ob G) (tau_component (smul G n a)) χ). }
    eapply qz_eq_trans;
      [ apply qz_move;
        exact (qz_eq_trans _ _ _ (qz_eq_sym _ _ Hev) (Hcχ χ)) | ].
    apply qz_eq_sym; exact (cmon_map_plus χ c (smul G n a)).
Qed.

Lemma tau_surjective_aux (G : AbObject) (F : FiniteCarrier G) (n : nat) :
  ∀ H : Subgroup G, (outside_count G F H <= n)%nat →
  (∀ Ξ, VanishesOn G H Ξ → Realizes G H Ξ) →
  ∀ Ξ : AbHom (D_ob G) QZ,
    { c : carrier (cmon_setoid G) &
        ∀ χ : AbHom G QZ, qz_eq (cmon_map Ξ χ) (cmon_map χ c) }.
Proof.
  induction n as [|n' IH]; intros H Hn HQ Ξ;
    destruct (all_or_witness G F H) as [Hall|[a Hna]].
  - destruct (HQ Ξ (vanishes_of_all G H Hall Ξ)) as [c [_ Hc]].
    exists c; exact Hc.
  - exfalso.
    pose proof (outside_count_generated G F H a (period_of G F H a) Hna).
    lia.
  - destruct (HQ Ξ (vanishes_of_all G H Hall Ξ)) as [c [_ Hc]].
    exists c; exact Hc.
  - refine (IH (Generated H a (period_of G F H a)) _ _ Ξ).
    + pose proof (outside_count_generated G F H a (period_of G F H a) Hna).
      lia.
    + exact (realizes_step G F H a (period_of G F H a) Hna HQ).
Qed.

Theorem tau_surjective_finite (G : AbObject) (F : FiniteCarrier G) :
  AbSurjective (tau G).
Proof.
  intro Ξ.
  destruct (tau_surjective_aux G F
              (outside_count G F (TrivialSubgroup G F))
              (TrivialSubgroup G F) (le_n _) (realizes_trivial G F) Ξ)
    as [c Hc].
  exists c; intro χ; apply qz_eq_sym; exact (Hc χ).
Qed.

(** ** The theorem *)

(* A bijective homomorphism of abelian groups is invertible.  The
   inverse is a genuine construction: [AbSurjective] is [Type]-valued,
   so the preimage is data, and injectivity makes the choice
   irrelevant. *)
Definition ab_inverse (G K : AbObject) (f : G ~{Ab}~> K)
           (Hinj : AbInjective f) (Hsurj : AbSurjective f) : K ~{Ab}~> G.
Proof.
  unshelve notypeclasses refine
    {| cmon_map := {| morphism := fun b => projT1 (Hsurj b) |} |}.
  - intros b b' Hbb.
    apply Hinj.
    etransitivity; [ exact (projT2 (Hsurj b)) | ].
    etransitivity; [ exact Hbb | ].
    symmetry; exact (projT2 (Hsurj b')).
  - apply Hinj.
    etransitivity; [ exact (projT2 (Hsurj (cmon_zero K))) | ].
    symmetry; exact (cmon_map_zero f).
  - intros b b'.
    apply Hinj.
    etransitivity; [ exact (projT2 (Hsurj (cmon_plus K b b'))) | ].
    etransitivity; [ | symmetry; exact (cmon_map_plus f _ _) ].
    apply cmon_plus_respects;
      [ symmetry; exact (projT2 (Hsurj b))
      | symmetry; exact (projT2 (Hsurj b')) ].
Defined.

Program Definition ab_bijective_iso (G K : AbObject) (f : G ~{Ab}~> K)
        (Hinj : AbInjective f) (Hsurj : AbSurjective f)
  : @Isomorphism Ab G K := {|
  to   := f;
  from := ab_inverse G K f Hinj Hsurj
|}.
Next Obligation.
  intros G K f Hinj Hsurj b.
  exact (projT2 (Hsurj b)).
Qed.
Next Obligation.
  intros G K f Hinj Hsurj x.
  apply Hinj.
  exact (projT2 (Hsurj (cmon_map f x))).
Qed.

(* Both halves at once, the natural waypoint. *)
Theorem tau_bijective_finite (G : AbObject) (F : FiniteCarrier G) :
  AbInjective (tau G) ∧ AbSurjective (tau G).
Proof.
  split; [ exact (tau_injective_finite G F) | exact (tau_surjective_finite G F) ].
Qed.

(* Mac Lane §I.4: for a finite abelian group the evaluation
   τ_G : G → DD(G) is an isomorphism.  Naturality is
   Instance/Ab/Character.v's [tau_natural]; the two together are the
   statement that τ is a natural isomorphism on finite abelian groups. *)
Theorem tau_iso_finite (G : AbObject) (F : FiniteCarrier G) :
  @Isomorphism Ab G (DD G).
Proof.
  exact (ab_bijective_iso G (DD G) (tau G)
           (tau_injective_finite G F) (tau_surjective_finite G F)).
Defined.

(** ** Acceptance: ℤ/2 *)

(* The cyclic group of order two, on [bool] with exclusive or.  Every
   element is its own inverse, so [ab_neg] is the identity.  Built with
   [unshelve notypeclasses refine] rather than [Program] so that every
   field is discharged explicitly and in a known order. *)
Definition ZMod2 : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := {| cmon_setoid := {| carrier := bool;
                                    is_setoid := eq_Setoid bool |};
                  cmon_zero := false;
                  cmon_plus := xorb |};
    ab_neg := fun b : bool => b
  |}.
  - (* cmon_plus_respects *)
    intros x x' Hx y y' Hy.
    assert (Hx' : x = x') by exact Hx.
    assert (Hy' : y = y') by exact Hy.
    rewrite Hx', Hy'; reflexivity.
  - (* cmon_plus_assoc *) intros x y z; destruct x, y, z; reflexivity.
  - (* cmon_plus_comm *) intros x y; destruct x, y; reflexivity.
  - (* cmon_plus_zero_l *) intros x; destruct x; reflexivity.
  - (* ab_neg_respects *) intros x y Hxy; exact Hxy.
  - (* ab_neg_left *) intros x; destruct x; reflexivity.
Defined.

Definition ZMod2Finite : FiniteCarrier ZMod2.
Proof.
  unshelve notypeclasses refine (@Build_FiniteCarrier ZMod2 [false; true] _ _).
  - (* fc_complete *)
    intro a; destruct a; simpl;
      [ right; left; reflexivity | left; reflexivity ].
  - (* fc_dec *)
    intros x y; destruct (bool_dec x y) as [He|He];
      [ left; exact He | right; exact He ].
Defined.

(* The two characters of ℤ/2, by hand. *)
Definition zmod2_char_zero : AbHom ZMod2 QZ := char_zero ZMod2.

Definition zmod2_char_half : AbHom ZMod2 QZ.
Proof.
  unshelve notypeclasses refine
    (@Build_CMonHom ZMod2 QZ
       (@Build_SetoidMorphism
          (carrier (cmon_setoid ZMod2)) _ (carrier (cmon_setoid QZ)) _
          (fun b : bool => if b then 1#2 else 0) _) _ _).
  - (* proper_morphism *)
    intros x y Hxy.
    assert (Hxy' : x = y) by exact Hxy.
    rewrite Hxy'; apply qz_eq_refl.
  - (* cmon_map_zero *) apply qz_eq_refl.
  - (* cmon_map_plus *)
    intros x y; destruct x, y; simpl.
    + (* 1/2 + 1/2 is the integer 1, hence zero in ℚ/ℤ *)
      apply qz_eq_sym; apply (qz_int _ 1%Z); reflexivity.
    + apply qz_of_Qeq; ring.
    + apply qz_of_Qeq; ring.
    + apply qz_of_Qeq; ring.
Defined.

(* 1/2 is not 0 in ℚ/ℤ, so the two characters are genuinely distinct. *)
Example zmod2_chars_distinct :
  (zmod2_char_half ≈ zmod2_char_zero) → False.
Proof.
  intro H.
  destruct (H true) as [z Hz].
  unfold Qeq in Hz; simpl in Hz; lia.
Qed.

(* And these are ALL of them: the character group of ℤ/2 has exactly
   two elements, so |D(ℤ/2)| = |ℤ/2| — the counting fact the general
   proof deliberately avoids, here checked by hand on the witness. *)
Example zmod2_characters (χ : AbHom ZMod2 QZ) :
  ((χ ≈ zmod2_char_zero) + (χ ≈ zmod2_char_half))%type.
Proof.
  assert (Hann : qz_eq (smul QZ 2%nat (cmon_map χ true)) 0).
  { assert (Hs : qz_eq (smul QZ 2%nat (cmon_map χ true))
                       (cmon_map χ true + cmon_map χ true)).
    { apply qz_of_Qeq.
      change (smul QZ 2%nat (cmon_map χ true))
        with (cmon_map χ true + (cmon_map χ true + 0))%Q.
      ring. }
    eapply qz_eq_trans; [ exact Hs | ].
    eapply qz_eq_trans;
      [ apply qz_eq_sym; exact (cmon_map_plus χ true true) | ].
    exact (cmon_map_zero χ). }
  destruct (qfrac_nat_form (cmon_map χ true) 2%nat ltac:(lia) Hann)
    as [m [Hmb Hm]].
  destruct m as [|m']; [ left | destruct m' as [|m'']; [ right | lia ] ].
  - intro b; destruct b.
    + eapply qz_eq_trans; [ exact Hm | ].
      apply qz_of_Qeq; reflexivity.
    + eapply qz_eq_trans; [ exact (cmon_map_zero χ) | apply qz_eq_refl ].
  - intro b; destruct b.
    + eapply qz_eq_trans; [ exact Hm | ].
      apply qz_of_Qeq; reflexivity.
    + eapply qz_eq_trans; [ exact (cmon_map_zero χ) | apply qz_eq_refl ].
Qed.

(* The theorem instantiates at the witness. *)
Definition zmod2_tau_iso : @Isomorphism Ab ZMod2 (DD ZMod2) :=
  tau_iso_finite ZMod2 ZMod2Finite.

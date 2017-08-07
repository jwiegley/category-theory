Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.

Generalizable All Variables.

Ltac simpl_eq :=
  repeat unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym,
                prod_rect in *.

Open Scope lazy_bool_scope.

Definition rev_list_rect (A : Type) (P : list A -> Type) (H : P [])
           (H0 : ∀ (a : A) (l : list A), P (rev l) -> P (rev (a :: l)))
           (l : list A) : P (rev l) :=
  list_rect (λ l0 : list A, P (rev l0)) H
            (λ (a : A) (l0 : list A) (IHl : P (rev l0)), H0 a l0 IHl) l.

Definition rev_rect (A : Type) (P : list A -> Type)
           (H : P []) (H0 : ∀ (x : A) (l : list A), P l -> P (l ++ [x]))
           (l : list A) : P l :=
  (λ E : rev (rev l) = l,
     eq_rect (rev (rev l)) (λ l0 : list A, P l0)
        (rev_list_rect A P H
        (λ (a : A) (l0 : list A) (H1 : P (rev l0)), H0 a (rev l0) H1)
        (rev l)) l E) (rev_involutive l).

Lemma last_rcons A (x y : A) l :
  last (l ++ [x]) y = x.
Proof.
  induction l; simpl.
    reflexivity.
  rewrite IHl; clear IHl.
  destruct l; auto.
Qed.

Lemma last_app_cons A (x : A) xs y ys :
  last (xs ++ y :: ys) x = last (y :: ys) x.
Proof.
  generalize dependent y.
  generalize dependent xs.
  induction ys using rev_ind; simpl; intros.
    apply last_rcons.
  rewrite last_rcons.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite last_rcons.
  destruct ys; auto.
Qed.

Lemma last_cons A (x : A) y ys :
  last (y :: ys) x = last ys y.
Proof.
  generalize dependent x.
  induction ys using rev_ind; simpl; intros.
    reflexivity.
  rewrite !last_rcons.
  destruct ys; auto.
Qed.

Lemma match_last {A} {a : A} {xs x} :
  match xs with
  | [] => a
  | _ :: _ => last xs x
  end = last xs a.
Proof.
  induction xs; auto.
  rewrite !last_cons; reflexivity.
Qed.

Lemma Forall_app {A} p (l1 l2: list A) :
  Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof.
  intros.
  rewrite !Forall_forall.
  split; intros.
    split; intros;
    apply H; apply in_or_app.
      left; trivial.
    right; trivial.
  apply in_app_or in H0.
  destruct H, H0; eauto.
Qed.

Lemma last_Forall A (x y : A) l P :
  last l x = y -> Forall P l -> P x -> P y.
Proof.
  generalize dependent x.
  destruct l using rev_ind; simpl; intros.
    now subst.
  rewrite last_rcons in H; subst.
  apply Forall_app in H0.
  destruct H0.
  now inversion H0.
Qed.

Fixpoint list_beq {A : Type} (eq_A : A -> A -> bool) (X Y : list A)
         {struct X} : bool :=
  match X with
  | [] => match Y with
          | [] => true
          | _ :: _ => false
          end
  | x :: x0 =>
      match Y with
      | [] => false
      | x1 :: x2 => eq_A x x1 &&& list_beq eq_A x0 x2
      end
  end.

Lemma list_beq_eq {A} (R : A -> A -> bool) xs ys :
  (∀ x y, R x y = true -> x = y) ->
  list_beq R xs ys = true -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs; simpl; intros.
    destruct ys; congruence.
  destruct ys.
    discriminate.
  destruct (R a a0) eqn:Heqe.
    apply H in Heqe; subst.
    erewrite IHxs; eauto.
  discriminate.
Qed.

Lemma list_beq_refl {A} (R : A -> A -> bool) xs :
  (∀ x, R x x = true) -> list_beq R xs xs = true.
Proof.
  intros.
  induction xs; auto; simpl.
  now rewrite H.
Qed.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Nat_eq_dec' : ∀ (x y : nat), x = y \/ x ≠ y.
Proof. intros; destruct (Nat.eq_dec x y); auto. Qed.

Lemma Nat_eq_dec_refl (x : nat) :
  Nat.eq_dec x x = left (@eq_refl (nat) x).
Proof.
  destruct (Nat.eq_dec x x); [| contradiction].
  refine (K_dec_on_type (nat) x (Nat_eq_dec' x)
            (fun H => @left _ _ H = @left _ _ (@eq_refl (nat) x)) _ _); auto.
Qed.

Lemma Nat_eqb_refl (x : nat) : Nat.eqb x x = true.
Proof. now apply Nat.eqb_eq. Qed.

Lemma Pos_eq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Pos_eq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Pos_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Pos_eqb_refl (x : positive) : Pos.eqb x x = true :=
  match x with
  | xI x => Pos_eqb_refl x
  | xO x => Pos_eqb_refl x
  | xH => eq_refl
  end.

Definition nth_safe {a} (xs : list a) (n : nat) (H : (n < length xs)%nat) : a.
Proof.
  induction xs; simpl in *; auto.
  contradiction (Nat.nlt_0_r n).
Defined.

Definition nth_pos {a} (xs : list a) (n : positive) (default : a) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    exact default.
  destruct n using Pos.peano_rect.
    exact a0.
  exact (IHxs n).
Defined.

Definition within_bounds {A} (x : positive) (xs : list A) : Prop :=
  (Nat.pred (Pos.to_nat x) < length xs)%nat.

Definition Pos_to_fin {n} (x : positive) :
  (Nat.pred (Pos.to_nat x) < n)%nat -> Fin.t n := Fin.of_nat_lt.

Definition nth_pos_bounded {a} (xs : list a) (n : positive)
           (H : within_bounds n xs) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    unfold within_bounds in H; simpl in H; omega.
  destruct n using Pos.peano_rect.
    exact a0.
  clear IHn.
  apply IHxs with (n:=n).
  unfold within_bounds in *.
  simpl in H.
  rewrite Pos2Nat.inj_succ in H.
  simpl in H.
  apply lt_S_n.
  rewrite Nat.succ_pred_pos; auto.
  apply Pos2Nat.is_pos.
Defined.

Lemma Fin_eq_dec' : ∀ n (x y : Fin.t n), x = y \/ x ≠ y.
Proof. intros; destruct (Fin.eq_dec x y); auto. Qed.

Lemma Fin_eq_dec_refl n (x : Fin.t n) :
  Fin.eq_dec x x = left (@eq_refl (Fin.t n) x).
Proof.
  destruct (Fin.eq_dec x x).
    refine (K_dec_on_type (Fin.t n) x (Fin_eq_dec' n x)
              (fun H => @left _ _ H = @left _ _ (@eq_refl (Fin.t n) x)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Fin_eqb_refl n (x : Fin.t n) : Fin.eqb x x = true :=
  match x with
  | @Fin.F1 m'    => Nat_eqb_refl m'
  | @Fin.FS n0 p' => Fin_eqb_refl n0 _
  end.

Lemma Fin_eqb_eq n (x y : Fin.t n) (H : Fin.eqb x y = true) : x = y.
Proof.
  induction x.
    revert H.
    apply Fin.caseS with (p:=y); intros; eauto.
    simpl in H; discriminate.
  revert H.
  apply Fin.caseS' with (p:=y); intros; eauto.
    simpl in H; discriminate.
  simpl in H.
  f_equal.
  now apply IHx.
Defined.

Import EqNotations.

Fixpoint nth_fin {a} (xs : list a) (n : Fin.t (length xs)) : a :=
  match xs as xs' return length xs = length xs' -> a with
  | nil => fun H => Fin.case0 _ (rew H in n)
  | cons x xs' => fun H =>
    match n in Fin.t n' return length xs = n' -> a with
    | Fin.F1 => fun _ => x
    | @Fin.FS n0 x => fun H0 =>
        nth_fin
          xs' (rew (eq_add_S n0 (length xs')
                             (rew [fun n => n = S (length xs')] H0 in H)) in x)
    end eq_refl
  end eq_refl.

Class Equality (A : Type) := {
  Eq_eq := @eq A;
  Eq_eq_refl x := eq_refl;

  Eq_eqb : A -> A -> bool;
  Eq_eqb_refl x : Eq_eqb x x = true;

  Eq_eqb_eq x y : Eq_eqb x y = true -> x = y;

  Eq_eq_dec  (x y : A) : { x = y } + { x ≠ y };
  Eq_eq_dec_refl x : Eq_eq_dec x x = left (@Eq_eq_refl x)
}.

Program Instance Pos_Eq : Equality positive := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Program Instance Fin_Eq (n : nat) : Equality (Fin.t n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin.eqb_eq n x y);

  Eq_eq_dec      := Fin.eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.

Program Instance option_Eq `{Equality A} : Equality (option A) := {
  Eq_eqb         := _;
  Eq_eqb_refl x  := _;

  Eq_eqb_eq x y  := _;

  Eq_eq_dec      := _;
  Eq_eq_dec_refl := _
}.
Next Obligation.
  destruct X.
    destruct X0.
      exact (Eq_eqb a a0).
    exact false.
  destruct X0.
    exact false.
  exact true.
Defined.
Next Obligation.
  destruct x; simpl; auto.
  apply Eq_eqb_refl.
Defined.
Next Obligation.
  destruct x, y; simpl in H0.
  - now apply Eq_eqb_eq in H0; subst.
  - discriminate.
  - discriminate.
  - reflexivity.
Defined.
Next Obligation.
  destruct x, y.
  - destruct (Eq_eq_dec a a0); subst.
      left; reflexivity.
    right; intros.
    inversion H0.
    contradiction.
  - right; intros; discriminate.
  - right; intros; discriminate.
  - left; reflexivity.
Defined.
Next Obligation.
  destruct x; simpl; auto.
  rewrite Eq_eq_dec_refl.
  unfold eq_rec_r, eq_rec; simpl_eq.
  remember (Eq_eq_refl a) as p.
  clear -p.
Admitted.

Program Instance list_Eq `{Equality A} : Equality (list A) := {
  Eq_eqb         := list_beq Eq_eqb;
  Eq_eqb_refl x  := list_beq_refl Eq_eqb x Eq_eqb_refl;

  Eq_eqb_eq x y  := list_beq_eq Eq_eqb x y Eq_eqb_eq;

  Eq_eq_dec      := list_eq_dec Eq_eq_dec;
  Eq_eq_dec_refl := _
}.
Next Obligation.
  induction x; simpl; auto.
  unfold sumbool_rec, sumbool_rect.
  rewrite Eq_eq_dec_refl, IHx.
  reflexivity.
Qed.

Program Instance prod_Eq `{Equality A} `{Equality B} : Equality (prod A B) := {
  Eq_eqb           := prod_eqb Eq_eqb Eq_eqb;
  Eq_eqb_refl      := _;

  Eq_eqb_eq x y    := _;

  Eq_eq_dec        := prod_eq_dec Eq_eq_dec Eq_eq_dec;
  Eq_eq_dec_refl x := prod_eq_dec_refl _ _ x Eq_eq_dec Eq_eq_dec
}.
Next Obligation.
  unfold prod_eqb; simpl.
  now rewrite !Eq_eqb_refl.
Defined.
Next Obligation.
  unfold prod_eqb in H1; simpl in H1.
  apply andb_true_iff in H1.
  destruct H1.
  apply Eq_eqb_eq in H1.
  apply Eq_eqb_eq in H2.
  now subst.
Defined.

Ltac equalities' :=
  match goal with
  | [ H : (_ &&& _) = true |- _ ]      => rewrite <- andb_lazy_alt in H
  | [ |- (_ &&& _) = true ]            => rewrite <- andb_lazy_alt
  | [ H : (_ && _) = true |- _ ]       => apply andb_true_iff in H
  | [ |- (_ && _) = true ]             => apply andb_true_iff; split
  | [ H : _ /\ _ |- _ ]                => destruct H
  | [ H : _ ∧ _ |- _ ]                 => destruct H
  | [ H : ∃ _, _ |- _ ]                => destruct H

  | [ H : context[Pos.eq_dec ?N ?M] |- _ ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M) in H
  | [ |- context[Pos.eq_dec ?N ?M] ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M)
  | [ H : context[(?N =? ?M)%positive] |- _ ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M) in H
  | [ |- context[(?N =? ?M)%positive] ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M)

  | [ H : context[@Fin.eq_dec ?N ?X ?Y] |- _ ] =>
    replace (@Fin.eq_dec N X Y) with (Eq_eq_dec X Y) in H
  | [ |- context[Fin.eq_dec ?N ?X ?Y] ] =>
    replace (@Fin.eq_dec N X Y) with (Eq_eq_dec X Y)
  | [ H : context[@Fin.eqb ?N ?X ?Y] |- _ ] =>
    replace (@Fin.eqb ?N ?X ?Y) with (Eq_eqb X Y) in H
  | [ |- context[@Fin.eqb ?N ?X ?Y] ] =>
    replace (@Fin.eqb ?N ?X ?Y) with (Eq_eqb X Y)

  | [ |- Eq_eqb ?X ?X = true ]     => apply Eq_eqb_refl
  | [ H : Eq_eqb _ _ = true |- _ ] => apply Eq_eqb_eq in H
  | [ |- Eq_eqb _ _ = true ]       => apply Eq_eqb_eq

  | [ H : context[match Eq_eq_dec ?X ?X with _ => _ end] |- _ ] =>
    rewrite (Eq_eq_dec_refl X) in H
  | [ |- context[match Eq_eq_dec ?X ?X with _ => _ end] ] =>
    rewrite (Eq_eq_dec_refl X)
  | [ H : context[match Eq_eq_dec ?X ?Y with _ => _ end] |- _ ] =>
    destruct (Eq_eq_dec X Y); subst
  | [ |- context[match Eq_eq_dec ?X ?Y with _ => _ end] ] =>
    destruct (Eq_eq_dec X Y); subst

  | [ H : list_beq _ _ _ = true |- _ ] => apply list_beq_eq in H
  | [ |- list_beq _ _ _ = true ]       => apply list_beq_eq
  end.

Ltac equalities :=
  try equalities';
  repeat (
    equalities';
    subst; simpl; auto;
    try discriminate;
    try tauto;
    try intuition idtac;
    subst; simpl; auto).

Polymorphic Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
  equiv := fun x y => match x, y with
    | Some x, Some y => x ≈ y
    | None, None => True
    | _, _ => False
    end
}.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Qed.

Inductive partial (P : Type) : Type :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

Section Symmetric_Product2.

Variable A : Type.
Variable leA : A -> A -> Prop.

Inductive symprod2 : A * A -> A * A -> Prop :=
  | left_sym2 :
    forall x x':A, leA x x' -> forall y:A, symprod2 (x, y) (x', y)
  | right_sym2 :
    forall y y':A, leA y y' -> forall x:A, symprod2 (x, y) (x, y')
  | both_sym2 :
    forall (x x':A) (y y':A),
      leA x x' ->
      leA y y' ->
      symprod2 (x, y) (x', y').

Lemma Acc_symprod2 :
  forall x:A, Acc leA x -> forall y:A, Acc leA y -> Acc symprod2 (x, y).
Proof.
  induction 1 as [x _ IHAcc]; intros y H2.
  induction H2 as [x1 H3 IHAcc1].
  apply Acc_intro; intros y H5.
  inversion_clear H5; auto with sets.
  apply IHAcc; auto.
  apply Acc_intro; trivial.
Defined.

Lemma wf_symprod2 :
  well_founded leA -> well_founded symprod2.
Proof.
  red.
  destruct a.
  apply Acc_symprod2; auto with sets.
Defined.

End Symmetric_Product2.

Lemma list_rect2 : ∀ (A : Type) (P : list A -> list A -> Type),
  P [] [] ->
  (∀ (a : A) (l1 : list A), P l1 [] -> P (a :: l1) []) ->
  (∀ (b : A) (l2 : list A), P [] l2 -> P [] (b :: l2)) ->
  (∀ (a b : A) (l1 l2 : list A), P l1 l2 -> P (a :: l1) (b :: l2))
    -> ∀ l1 l2 : list A, P l1 l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1; simpl in *; intros;
  induction l2; auto.
Qed.

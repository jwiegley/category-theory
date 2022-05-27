Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Export Category.Lib.Setoid.
Require Export Category.Lib.Tactics.

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope lazy_bool_scope.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P eq_refl -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x eq_refl p.
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

Theorem Pos_eqb_eq (p q : positive) : (p =? q)%positive = true <-> p=q.
Proof.
 revert q. induction p; destruct q; simpl; rewrite ?IHp; split; congruence.
Qed.

Fixpoint Pos_eqb_refl (x : positive) : Pos.eqb x x = true :=
  match x with
  | xI x => Pos_eqb_refl x
  | xO x => Pos_eqb_refl x
  | xH => eq_refl
  end.

Lemma N_eq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (N.eq_dec x y); auto.
Qed.

Lemma N_eq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (N_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
    reflexivity.
  contradiction.
Qed.

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
    unfold within_bounds in H; simpl in H. exfalso. inversion H.
  destruct n using Pos.peano_rect.
    exact a0.
  clear IHn.
  apply IHxs with (n:=n).
  unfold within_bounds in *.
  simpl in H.
  rewrite Pnat.Pos2Nat.inj_succ in H.
  simpl in H.
  apply Lt.lt_S_n.
  rewrite Nat.succ_pred_pos; auto.
  apply Pnat.Pos2Nat.is_pos.
Defined.

Lemma Nat_eqb_eq n m : Nat.eqb n m = true <-> n = m.
Proof.
 revert m.
 induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
 - now intros ->.
 - now injection 1.
Defined.

Lemma Fin_eqb_eq : forall n (p q : Fin.t n), Fin.eqb p q = true <-> p = q.
Proof.
  apply Fin.rect2; simpl; intros.
  - split; intros ; [ reflexivity | now apply Nat_eqb_eq ].
  - now split.
  - now split.
  - split; intros.
    * f_equal.
      now apply H.
    * apply Fin.FS_inj in H0.
      now apply H.
Defined.

Lemma Fin_eqb_eq' n (x y : Fin.t n) (H : Fin.eqb x y = true) : x = y.
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

Lemma Fin_eq_dec {n} (x y : Fin.t n): {x = y} + {x <> y}.
Proof.
case_eq (Fin.eqb x y); intros.
- left; now apply Fin_eqb_eq.
- right. intros Heq. apply <- Fin_eqb_eq in Heq. congruence.
Defined.

Lemma Fin_eq_dec' : ∀ n (x y : Fin.t n), x = y \/ x ≠ y.
Proof. intros; destruct (Fin_eq_dec x y); auto. Qed.

Lemma Fin_eq_dec_refl n (x : Fin.t n) :
  Fin_eq_dec x x = left (@eq_refl (Fin.t n) x).
Proof.
  destruct (Fin_eq_dec x x).
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

#[global]
Program Instance Pos_Eq : Equality positive := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos_eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

#[global]
Program Instance Fin_Eq (n : nat) : Equality (Fin.t n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin_eqb_eq n x y);

  Eq_eq_dec      := Fin_eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.

(*
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
*)

Import ListNotations.

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

#[global]
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

(* Products can be compared for boolean equality if their members can be. *)
Definition prod_eqb {A B} (A_eqb : A -> A -> bool) (B_eqb : B -> B -> bool)
           (x y : A * B) : bool :=
  A_eqb (fst x) (fst y) && B_eqb (snd x) (snd y).

(* Products can be compared for decidable equality if their members can be. *)
Program Definition prod_eq_dec {A B}
        (A_eq_dec : forall x y : A, {x = y} + {x ≠ y})
        (B_eq_dec : forall x y : B, {x = y} + {x ≠ y})
        (x y : A * B) : {x = y} + {x ≠ y} :=
  match A_eq_dec (fst x) (fst y) with
  | in_left =>
    match B_eq_dec (snd x) (snd y) with
    | in_left  => in_left
    | in_right => in_right
    end
  | in_right => in_right
  end.
Next Obligation. simpl in *; congruence. Qed.

Lemma prod_eq_dec' :
  ∀ (A B : Type) (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
    (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y)
    (x y : A ∧ B), x = y \/ x ≠ y.
Proof.
  intros.
  destruct x, y; simpl.
  destruct (A_eq_dec a a0); subst.
    destruct (B_eq_dec b b0); subst.
      left; reflexivity.
    right; congruence.
  right; congruence.
Qed.

Lemma prod_eq_dec_refl (A B : Type) n
      (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
      (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y) :
  prod_eq_dec A_eq_dec B_eq_dec n n = left (@eq_refl (A ∧ B) n).
Proof.
  destruct (prod_eq_dec _ _ n n).
    refine (K_dec_on_type (A ∧ B) n (prod_eq_dec' _ _ A_eq_dec B_eq_dec n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl (A ∧ B) n)) _ _).
    reflexivity.
  contradiction.
Qed.

#[global]
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
  simplify;
  match goal with
  | [ H : (?X; _) = (?X; _) |- _ ] =>
    try (apply Eqdep_dec.inj_pair2_eq_dec in H; [|apply Eq_eq_dec])

  | [ H : context[Pos.eq_dec ?N ?M] |- _ ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M) in H
  | [ |- context[Pos.eq_dec ?N ?M] ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M)
  | [ H : context[(?N =? ?M)%positive] |- _ ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M) in H
  | [ |- context[(?N =? ?M)%positive] ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M)

  | [ H : context[@Fin_eq_dec ?N ?X ?Y] |- _ ] =>
    replace (@Fin_eq_dec N X Y) with (Eq_eq_dec X Y) in H
  | [ |- context[Fin_eq_dec ?N ?X ?Y] ] =>
    replace (@Fin_eq_dec N X Y) with (Eq_eq_dec X Y)
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

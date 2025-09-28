Require Import Coq.Lists.List.

Require Export Category.Lib.Tactics.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

Definition rev_list_rect (A : Type) (P : list A → Type) (H : P [])
           (H0 : ∀ (a : A) (l : list A), P (rev l) → P (rev (a :: l)))
           (l : list A) : P (rev l) :=
  list_rect (λ l0 : list A, P (rev l0)) H
            (λ (a : A) (l0 : list A) (IHl : P (rev l0)), H0 a l0 IHl) l.

Definition rev_rect (A : Type) (P : list A → Type)
           (H : P []) (H0 : ∀ (x : A) (l : list A), P l → P (l ++ [x]))
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
  last l x = y → Forall P l → P x → P y.
Proof.
  generalize dependent x.
  destruct l using rev_ind; simpl; intros.
    now subst.
  rewrite last_rcons in H; subst.
  apply Forall_app in H0.
  destruct H0.
  now inversion H0.
Qed.

Lemma map_inj {A B : Type} (f : A → B)
      (f_inj : ∀ x y, f x = f y → x = y) xs ys :
  List.map f xs = List.map f ys → xs = ys.
Proof.
  generalize dependent ys.
  induction xs, ys; simpl; intros; auto; try inv H.
  apply f_inj in H1; subst.
  f_equal.
  now apply IHxs.
Qed.

Local Set Warnings "-intuition-auto-with-star".

(* The only inductive types from the standard library used in this development
   are products and sums, so we must show how they interact with constructive
   setoids. *)

#[global]
Program Instance prod_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A * B) := {
  equiv := fun x y => (fst x ≈ fst y) * (snd x ≈ snd y)
}.

#[global]
Program Instance pair_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv ==> equiv) (@pair A B).

#[global]
Program Instance fst_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@fst A B).

#[global]
Program Instance snd_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@snd A B).

Corollary let_fst {x y} (A : x * y) `(f : x → z) :
  (let (x, _) := A in f x) = f (fst A).
Proof. destruct A; auto. Qed.

Corollary let_snd {x y} (A : x * y) `(f : y → z) :
  (let (_, y) := A in f y) = f (snd A).
Proof. destruct A; auto. Qed.

Corollary let_projT1 {A P} (S : @sigT A P) `(f : A → z) :
  (let (x, _) := S in f x) = f (projT1 S).
Proof. destruct S; auto. Qed.

Corollary let_projT2 {A P} (S : @sigT A P) `(f : ∀ x, P x → z) :
  (let (x, y) := S in f x y) = f (projT1 S) (projT2 S).
Proof. destruct S; auto. Qed.

#[global]
Program Instance sum_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A + B) := {
  equiv := fun x y =>
    match x with
    | inl x =>
      match y with
      | inl y => equiv x y
      | inr y => False
      end
    | inr x =>
      match y with
      | inl y => False
      | inr y => equiv x y
      end
    end
}.
Next Obligation.
  equivalence; destruct x, y; try destruct z; intuition; auto with *.
Qed.

#[global]
Program Instance inl_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inl A B).

#[global]
Program Instance inr_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inr A B).

#[global]
Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
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

#[global]
Program Instance Some_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv) (@Some A).

Fixpoint list_equiv `{Setoid A} (xs ys : list A) : Type :=
  match xs, ys with
  | nil, nil => True
  | x :: xs, y :: ys => x ≈ y ∧ list_equiv xs ys
  | _, _ => False
  end.

#[global]
Program Instance list_equivalence `{Setoid A} : Equivalence list_equiv.
Next Obligation.
  induction x; simpl; simplify; auto.
  reflexivity.
Qed.
Next Obligation.
  induction x, y; simpl; intros; simplify; auto.
  now symmetry.
Qed.
Next Obligation.
  induction x, y, z; simpl; intros;
  simplify; auto; try contradiction.
  - now transitivity a0.
  - firstorder.
Qed.

#[global]
Program Instance list_setoid `{Setoid A} : Setoid (list A) := {
  equiv := list_equiv
}.

#[global]
Program Instance cons_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@cons A).

#[global]
Program Instance app_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@app A).
Next Obligation.
  proper.
  generalize dependent y.
  induction x, y; simpl; intros; auto.
  - contradiction.
  - contradiction.
  - simplify; auto.
Qed.

Lemma length_remove A (A_eq_dec : ∀ x y : A, { x = y } + { x ≠ y }) x xs :
  (length (remove A_eq_dec x xs) <= length xs)%nat.
Proof.
  induction xs; auto.
  simpl.
  destruct (A_eq_dec x a); subst.
    apply PeanoNat.Nat.le_le_succ_r, IHxs.
  simpl.
  apply le_n_S, IHxs.
Qed.

Section Symmetric_Product2.

Variable A : Type.
Variable leA : A → A → Prop.

Inductive symprod2 : A * A → A * A → Prop :=
  | left_sym2 :
    ∀ x x':A, leA x x' → ∀ y:A, symprod2 (x, y) (x', y)
  | right_sym2 :
    ∀ y y':A, leA y y' → ∀ x:A, symprod2 (x, y) (x, y')
  | both_sym2 :
    ∀ (x x':A) (y y':A),
      leA x x' ->
      leA y y' ->
      symprod2 (x, y) (x', y').

Lemma Acc_symprod2 :
  ∀ x:A, Acc leA x → ∀ y:A, Acc leA y → Acc symprod2 (x, y).
Proof.
  induction 1 as [x _ IHAcc]; intros y H2.
  induction H2 as [x1 H3 IHAcc1].
  apply Acc_intro; intros y H5.
  inversion_clear H5; auto with sets.
  apply IHAcc; auto.
  apply Acc_intro; trivial.
Defined.

Lemma wf_symprod2 :
  well_founded leA → well_founded symprod2.
Proof.
  red.
  destruct a.
  apply Acc_symprod2; auto with sets.
Defined.

End Symmetric_Product2.

Lemma list_rect2 : ∀ (A : Type) (P : list A → list A → Type),
  P [] [] ->
  (∀ (a : A) (l1 : list A), P l1 [] → P (a :: l1) []) ->
  (∀ (b : A) (l2 : list A), P [] l2 → P [] (b :: l2)) ->
  (∀ (a b : A) (l1 l2 : list A), P l1 l2 → P (a :: l1) (b :: l2))
    → ∀ l1 l2 : list A, P l1 l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1; simpl in *; intros;
  induction l2; auto.
Qed.

#[global]
Program Instance nat_setoid : Setoid nat.

#[global]
Program Instance fun_setoid {A : Type} `{Setoid B} : Setoid (A → B) := {
  equiv := fun f g => ∀ x, f x ≈ g x
}.
Next Obligation.
  equivalence.
  now rewrite X, X0.
Qed.

Arguments fun_setoid A B {_}.

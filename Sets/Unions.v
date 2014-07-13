Require Export Singletons.
Require Export Separation.

(* This file contains exercises from Paul Halmos book, Naive Set Theory, and
   from a few other places. *)

Theorem union_empty : Union ∅ = ∅.
Proof.
  extension.
  - apply Union_E in H. destruct H. inv H.
    contradiction (Empty_E x0).
  - apply Union_I with (Y := ∅). auto.
    contradiction (Empty_E x).
Qed.

Hint Resolve union_empty.

Theorem union_sing : forall A, Union (Sing A) = A.
Proof. intros. compute. extension; obvious_BUR. Qed.

Hint Resolve union_sing.

Theorem union_one : Union One = ∅.
Proof. compute. apply union_sing. Qed.

Theorem union_X_two : forall X, X ∈ Two → Union X = ∅.
Proof.
  intros. unfold Two in H.
  apply UPair_E in H.
  inversion H.
  rewrite <- union_empty.
  f_equal. assumption. rewrite H0.
  compute. apply union_sing.
Qed.

Theorem union_two : Union Two = One.
Proof.
  compute. extension.
  apply Union_E in H. destruct H. inv H.
    apply UPair_E in H1. inv H1.
      contradiction (Empty_E x).
      assumption.
  apply Union_I with (Y := {∅, ∅}).
    assumption.
    apply UPair_I2.
Qed.

Theorem union_comm : forall A B, A ∪ B = B ∪ A.
Proof. obvious_BUR. Qed.

Theorem union_assoc : forall A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof. obvious_BUR. Qed.

Theorem union_idem : forall A, A ∪ A = A.
Proof. obvious_BUR. Qed.

Theorem union_incl : forall A B, A ⊆ B ↔ A ∪ B = B.
Proof.
  intros. split; intros. obvious_BUR.
  compute. intros. rewrite <- H. union_1.
Qed.

Definition Inter (M : set) : set :=
  Sep (Union M) (fun x : set => ∀ A : set, A ∈ M → x ∈ A).

Lemma Inter_I : ∀ x M, inh_set M → (∀ A, A ∈ M → x ∈ A) → x ∈ Inter M.
Proof.
  intros. unfold Inter.
  apply Sep_I. inv H. specialize (H0 x0).
    apply Union_I with (Y := x0); auto.
    auto.
Qed.

Hint Resolve Inter_I.

Lemma Inter_E : ∀ x M, x ∈ Inter M → inh_set M ∧ ∀ A, A ∈ M → x ∈ A.
Proof.
  intros. unfold Inter in H.
  apply Sep_E in H. inv H.
  apply Union_E in H0. destruct H0. inv H.
  split.
    specialize (H1 x0).
    unfold inh_set. exists x0. auto.
  auto.
Qed.

Hint Resolve Inter_E.

Definition BinInter (A B : set) : set := Inter (UPair A B).

Lemma BinInter_I : ∀ A B a: set, a ∈ A ∧ a ∈ B → a ∈ BinInter A B.
Proof.
  intros. unfold BinInter. inv H.
  apply Inter_I.
    unfold inh_set. exists A. pair_1.
    intros. pair_e H.
Qed.

Hint Resolve BinInter_I.

Lemma BinInter_E : ∀ A B x, x ∈ BinInter A B → x ∈ A ∧ x ∈ B.
Proof.
  intros. unfold BinInter in H.
  apply Inter_E in H. inv H.
  unfold inh_set in H0. destruct H0.
  split; obvious_BUR.
Qed.

Hint Resolve BinInter_E.

Notation "X ∩ Y" := (BinInter X Y) (at level 69).

Ltac inter := apply BinInter_I ; split ; try auto.
Ltac inter_e H :=
  apply BinInter_E in H ; try (first [ inv H | destruct H ]) ; try auto.

Ltac obvious :=
  repeat (try obvious_BUR; match goal with
  | [ H : ?X ∈ (?A ∩ ?B) |- _ ] => inter_e H
  | [ |- ?X ∈ (?A ∩ ?B) ] => inter
  end; auto).

Theorem inter_zero : forall A, A ∩ ∅ = ∅.
Proof.
  intros. extension.
  inter_e H. inter.
  contradiction (Empty_E x).
Qed.

Theorem inter_comm : forall A B, A ∩ B = B ∩ A.
Proof. intros. extension; obvious. Qed.

Theorem inter_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. intros. extension; obvious. Qed.

Theorem inter_idem : forall A, A ∩ A = A.
Proof. intros. extension; obvious. Qed.

Theorem inter_incl : forall A B, A ⊆ B ↔ A ∩ B = A.
Proof.
  intros. split; intros. extension; obvious.
  unfold Subq. intros. rewrite <- H in H0. inter_e H0.
Qed.

Theorem union_distr : forall A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof. intros. extension; obvious. Qed.

Theorem inter_distr : forall A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof. intros. extension; obvious. Qed.

(* Exercise.  A necessary and sufficient condition that (A ∩ B) ∪ C = A ∩ (B ∪
   C) is that C ⊆ A.  Observe that the condition has nothing to do with the
   set B.
*)
Theorem union_assoc_ns : forall A B C, (A ∩ B) ∪ C = A ∩ (B ∪ C) ↔ C ⊆ A.
Proof.
  intros. split; intros.
  - apply inter_incl.
    extension.
    + obvious.
    + apply BinInter_I. split.
        assumption.
        apply extensionality_E in H. inv H.
          unfold Subq in *.
          specialize (H1 x).
          specialize (H2 x).
          apply BinInter_E in H1.
            inv H1. auto.
            apply Union_I with (Y := C).
              assumption.
              apply UPair_I2.
  - rewrite union_distr.
    extension.
    + rewrite inter_comm with (B := C).
      pose (inter_incl C A). inv i.
      rewrite H1; assumption.
    + rewrite inter_comm with (B := C) in H0.
      pose (inter_incl C A). inv i.
      rewrite H1 in H0; assumption.
Qed.

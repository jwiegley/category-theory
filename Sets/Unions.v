Require Export Structures.

(* This file contains exercises from Paul Halmos book, Naive Set Theory, and
   from a few other places. *)

Theorem union_empty : Union ∅ = ∅.
Proof.
  extension.
  - apply Union_E in H. destruct H. inv H.
    contradiction (Empty_E x0).
  - apply Union_I with (Y := ∅).
      assumption.
      contradiction (Empty_E x).
Qed.

Hint Resolve union_empty.

Theorem union_sing : forall A, Union (Sing A) = A.
Proof.
  intros. symmetry. compute. extension.
  apply Union_I with (Y := A). apply H. apply UPair_I1.
  apply Union_E in H. destruct H. inv H.
  apply UPair_E in H1. inv H1; assumption.
Qed.

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
Proof.
  intros. extension; union_e H.
Qed.

Theorem union_assoc : forall A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  intros. extension; union_e H.
  union_e H. union_e H.
Qed.

Theorem union_idem : forall A, A ∪ A = A.
Proof.
  intros. extension. union_e H. union_1.
Qed.

Theorem union_incl : forall A B, A ⊆ B ↔ A ∪ B = B.
Proof.
  intros. split; intros.
  extension. union_e H0. union_2.
  compute. intros. rewrite <- H. union_1.
Qed.

Theorem inter_zero : forall A, A ∩ ∅ = ∅.
Proof.
  intros. extension.
  inter_e H. inter.
  contradiction (Empty_E x).
Qed.

Theorem inter_comm : forall A B, A ∩ B = B ∩ A.
Proof.
  intros. extension; inter_e H.
Qed.

Theorem inter_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  intros. extension.
  inter_e H. inter_e H1.
  inter_e H. inter_e H0.
Qed.

Theorem inter_idem : forall A, A ∩ A = A.
Proof.
  intros. extension. inter_e H. inter.
Qed.

Theorem inter_incl : forall A B, A ⊆ B ↔ A ∩ B = A.
Proof.
  intros. split; intros.
  extension. inter_e H0. inter.
  unfold Subq. intros. rewrite <- H in H0. inter_e H0.
Qed.

Theorem union_distr : forall A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  intros. extension.
  inter_e H. union_e H1.
  union_e H. inter_e H. inter_e H.
Qed.

Theorem inter_distr : forall A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof.
  intros. extension.
  union_e H.
  inter_e H. inter_e H.
  union_e H0. union_e H1.
Qed.

(* Exercise.  A necessary and sufficient condition that (A ∩ B) ∪ C = A ∩ (B ∪
   C) is that C ⊆ A.  Observe that the condition has nothing to do with the
   set B.
*)
Theorem union_assoc_ns : forall A B C, (A ∩ B) ∪ C = A ∩ (B ∪ C) ↔ C ⊆ A.
Proof.
  intros. split; intros.
  - apply inter_incl.
    extension.
    + apply BinInter_E in H0. inv H0; assumption.
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

Require Export Structures.

(* This file contains exercises from Paul Halmos book, Naive Set Theory, and
   from a few other places. *)

Theorem union_empty : Union ∅ = ∅.
Proof.
  extension.
  - apply Union_E in H.
    pose Empty_E.
    inversion H. inversion H0.
    apply n in H2.
    contradiction H2.
  - apply Union_I with (Y := ∅).
    + apply H.
    + pose Empty_E.
      apply n in H.
      contradiction H.
Qed.

Hint Resolve union_empty.

Theorem union_sing : forall A, Union (Sing A) = A.
Proof.
  intros. symmetry. compute. extension.
  apply Union_I with (Y := A). apply H. apply UPair_I1.
  union_e H. apply UPair_E in H1. inv H1; assumption.
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
  union_e H.
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
  apply Union_I with (Y := x0). assumption.
  rewrite pair_agnostic. assumption.
  apply Union_I with (Y := x0). assumption.
  rewrite pair_agnostic. assumption.
Qed.

Theorem union_assoc : forall A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  intros. extension; union_e H.
  apply UPair_E in H1. inv H1.
    apply Union_I with (Y := (A ∪ B)).
      apply Union_I with (Y := A).
        assumption.
        apply UPair_I1.
      apply UPair_I1.
    apply Union_E in H0. destruct H0. inv H.
    apply UPair_E in H1. inv H1.
      apply Union_I with (Y := (A ∪ B)).
        apply Union_I with (Y := B).
          assumption.
          apply UPair_I2.
        apply UPair_I1.
      apply Union_I with (Y := C).
        assumption.
        apply UPair_I2.
  apply UPair_E in H1. inv H1.
    apply Union_E in H0. inv H0. inv H.
      apply UPair_E in H1. inv H1.
        apply Union_I with (Y := A).
          assumption.
          apply UPair_I1.
        apply Union_I with (Y := (B ∪ C)).
          apply Union_I with (Y := B).
            assumption.
            apply UPair_I1.
          apply UPair_I2.
    apply Union_I with (Y := (B ∪ C)).
      apply Union_I with (Y := C).
        assumption.
        apply UPair_I2.
      apply UPair_I2.
Qed.

Theorem union_idem : forall A, A ∪ A = A.
Proof.
  intros. extension. union_e H.
  apply UPair_E in H1. inv H1; assumption.
  apply Union_I with (Y := A). assumption.
  apply UPair_I1.
Qed.

Theorem union_incl : forall A B, A ⊆ B ↔ A ∪ B = B.
Proof.
  intros. split; intros.
  - extension.
    + apply Union_E in H0.
      destruct H0. inv H0.
      apply UPair_E in H2. inv H2; compute in H; auto.
    + apply Union_I with (Y := B). assumption.
      apply UPair_I2.
  - compute. intros. rewrite <- H.
    apply Union_I with (Y := A). assumption.
    apply UPair_I1.
Qed.

Theorem inter_zero : forall A, A ∩ ∅ = ∅.
Admitted.

Theorem inter_comm : forall A B, A ∩ B = B ∩ A.
Admitted.

Theorem inter_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Admitted.

Theorem inter_idem : forall A, A ∩ A = A.
Admitted.

Theorem inter_incl : forall A B, A ⊆ B ↔ A ∩ B = A.
Admitted.

Theorem union_distr : forall A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Admitted.

Theorem inter_distr : forall A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Admitted.

(* Exercise.  A necessary and sufficient condition that (A ∩ B) ∪ C = A ∩ (B ∪
   C) is that C ⊆ A.  Observe that the condition has nothing to do with the
   set B.
*)
Theorem union_assoc_ns : forall A B C, (A ∩ B) ∪ C = A ∩ (B ∪ C) ↔ C ⊆ A.
Proof.
  intros. split; intros.
  - apply inter_incl.
    extension.
    apply BinInter_E in H0. inv H0; assumption.
    apply BinInter_I. split.
      assumption.
      admit.
  - apply extensionality; unfold Subq in *; intros.
    apply Union_E in H0.
      destruct H0. inv H0.
      apply BinInter_I. split.
        apply UPair_E in H2. inv H2.
          apply BinInter_E in H1. inv H1.
            assumption.
          apply H. assumption.
        apply Union_I with (Y := B).
          apply UPair_E in H2. inv H2.
            apply BinInter_E in H1. inv H1.
              assumption.
            admit.
          apply UPair_I1.
    apply BinInter_E in H0. inv H0.
      apply Union_E in H2. destruct H2. inv H0.
      apply UPair_E in H3. inv H3.
      apply Union_I with (Y := (A ∩ B)).
        apply BinInter_I. split; assumption.
        apply UPair_I1.
        apply Union_I with (Y := C).
          assumption.
          apply UPair_I2.
Abort.

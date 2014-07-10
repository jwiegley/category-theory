Require Export Pairs.
Require Export Families.

Definition CProd (A B : set) : set :=
  FamUnion A (fun a => Repl (fun b => ⟨a,b⟩) B).

Notation "A × B" := (CProd A B) (at level 69).

Lemma CProd_I : ∀ a A b B, a ∈ A → b ∈ B → ⟨a, b⟩ ∈ CProd A B.
Proof.
  intros. unfold CProd.
  apply FamUnion_I with (x := a).
    auto.
    apply Repl_I. auto.
Qed.

Hint Resolve CProd_I.

Lemma CProd_E1 : ∀ p A B, p ∈ CProd A B → π1 p ∈ A ∧ π2 p ∈ B.
Proof.
  intros. unfold CProd in H.
  split;
  apply FamUnion_E in H; destruct H; inv H;
  apply Repl_E in H1; destruct H1; inv H.
   rewrite Pair_E1. auto.
   rewrite Pair_E2. auto.
Qed.

Hint Resolve CProd_E1.

Lemma CProd_E2 : ∀ p A B, p ∈ CProd A B → is_pair p.
Proof.
  intros. unfold CProd in H. unfold is_pair.
  apply FamUnion_E in H. destruct H. inv H.
  apply Repl_E in H1. destruct H1. inv H.
  exists x. exists x0. reflexivity.
Qed.

Hint Resolve CProd_E2.

Lemma empty_cross : ∀ B, ∅ × B = ∅.
Proof.
  intros.
  rewrite <- (Pair_E1 ∅ B).
  extension.
    apply FamUnion_E in H. destruct H. inv H.
    apply Repl_E in H1. destruct H1. inv H.
    rewrite Pair_E1 in H0.
    contradiction (Empty_E x0).
  apply FamUnion_I with (x := x). auto.
  rewrite Pair_E1 in H.
  contradiction (Empty_E x).
Qed.

Hint Resolve empty_cross.

Lemma cross_empty : ∀ A, A × ∅ = ∅.
Proof.
  intros.
  rewrite <- (Pair_E2 A ∅).
  extension.
    apply FamUnion_E in H. destruct H. inv H.
    apply Repl_E in H1. destruct H1. inv H.
    rewrite Pair_E2 in H1.
    contradiction (Empty_E x1).
  apply FamUnion_I with (x := x).
    rewrite Pair_E2 in H.
    contradiction (Empty_E x).
  rewrite Pair_E2 in H.
  contradiction (Empty_E x).
Qed.

Hint Resolve cross_empty.

Require Export Unions.

Definition ord_pair (x y : set) : set := UPair (Sing x) (UPair x y).

Notation "⟨ a , b ⟩" := (ord_pair a b) (at level 69).

Lemma Pair_Union : forall a b, Union(⟨a, b⟩) = {a, b}.
Proof.
  intros. unfold ord_pair.
  extension. union_e H. sing_e H. rewrite H. pair_1.
  apply Union_I with (Y := {a, b}). assumption. pair_2.
Qed.

Hint Resolve Pair_Union.

Lemma Pair_Inter : forall a b, Inter(⟨a, b⟩) = Sing a.
Proof.
  intros. unfold ord_pair.
  extension. inter_e H.
  inter. sing_e H. rewrite H. pair_1.
Qed.

Hint Resolve Pair_Inter.

Definition π1 (p : set) : set := Union (Inter p).
Definition π2 (p : set) : set :=
  Union (Sep (Union p) (fun x : set => x ∈ Inter p → Union p = Inter p)).

Lemma Pair_E1 : forall x y, π1(⟨x, y⟩) = x.
Proof.
  intros.
  unfold π1, ord_pair.
  extension.
    apply Union_E in H. destruct H. inv H.
      inter_e H1. sing_e H. rewrite <- H. auto.
    apply Union_I with (Y := x).
      assumption. inter.
Qed.

Hint Resolve Pair_E1.

Lemma Pair_E2 : forall x y, π2(⟨x, y⟩) = y.
Proof with auto.
  intros.
  unfold π2.
  extension.
  - apply Union_E in H. destruct H. inv H.
    apply Sep_E in H1. inv H1.
    rewrite Pair_Union in *.
    pair_e H.
    rewrite Pair_Inter in *.
    apply US_ex in H2. inv H2. auto.
    sing.
  - apply Union_I with (Y := y)...
    apply Sep_I.
      apply Union_I with (Y := {x, y})...
      auto. unfold ord_pair...
    intros.
    rewrite Pair_Union.
    rewrite Pair_Inter.
    inter_e H0.
    extension. pair_e H0.
    sing_e H0. rewrite H0...
Qed.

Hint Resolve Pair_E2.

Ltac ordpair_e1 H := apply Pair_E1 in H; try (inv H); try auto.
Ltac ordpair_e2 H := apply Pair_E2 in H; try (inv H); try auto.

Lemma Pair_Char : forall a b c d, ⟨a, b⟩ = ⟨c, d⟩ ↔ a = c ∧ b = d.
Proof with auto.
  intros. split; intros.
    split.
      rewrite <- Pair_E1 with (y := d).
      rewrite <- H...
    rewrite <- Pair_E2 with (x := c).
    rewrite <- H...
  inv H...
Qed.

Hint Resolve Pair_Char.

Definition is_pair (p : set) : Prop := ∃ x, ∃ y, p = ⟨x, y⟩.

Lemma ord_pair_eta : ∀ p, is_pair p ↔ p = ⟨π1 p, π2 p⟩.
Proof with auto.
  intros. split; intros.
  - destruct H. destruct H.
    rewrite H.
    rewrite Pair_E1.
    rewrite Pair_E2.
    auto.
  - unfold is_pair.
    exists (π1 p).
    exists (π2 p).
    auto.
Qed.

Hint Resolve ord_pair_eta.

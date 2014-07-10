Require Export Pairs.

Definition CProd (A B : set) : set :=
  FamUnion A (fun a => Repl (fun b => ⟨a,b⟩) B).

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
  intros. unfold CProd in H. unfold π1, π2.
  split.
    apply FamUnion_E in H. destruct H. inv H.
    apply Repl_E in H1. destruct H1. inv H.
Admitted.

Hint Resolve CProd_E1.

Lemma CProd_E2 : ∀ p A B, p ∈ CProd A B → is_pair p.
Proof.
  intros. unfold CProd in H. unfold is_pair.
  apply FamUnion_E in H. destruct H. inv H.
  apply Repl_E in H1. destruct H1. inv H.
  exists x. exists x0. reflexivity.
Qed.

Hint Resolve CProd_E2.

(* Lemma 9. For all sets B, ∅ × B = ∅. *)
(* Lemma 10. For all sets A, A × ∅ = ∅. *)

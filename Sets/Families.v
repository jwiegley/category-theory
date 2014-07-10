Require Export Unions.

Definition FamUnion (X : set) (F : set → set) : set := Union (Repl F X).

Lemma FamUnion_I : ∀ X F x y, x ∈ X → y ∈ (F x) → y ∈ (FamUnion X F).
Proof.
  intros. compute.
  apply Union_I with (Y := F x). auto.
  apply Repl_I. auto.
Qed.

Hint Resolve FamUnion_I.

Lemma FamUnion_E : ∀ X F y, y ∈ (FamUnion X F) → ∃ x, x ∈ X ∧ y ∈ (F x ).
Proof.
  intros. compute in H.
  apply Union_E in H. destruct H. inv H.
  apply Repl_E in H1. destruct H1. inv H.
  exists x0. split; auto.
Qed.

Hint Resolve FamUnion_E.

(* Properties of the union over families of indexed sets.

   1. ∪ x∈∅ Fx = ∅
   2. (∀x ∈ X, Fx ∈ 2) −→ (∃x ∈ X, Fx = 1) −→ ∪ x∈X Fx = 1
   3. inhset X −→ (∀x ∈ X, Fx = C) −→ ∪ x∈X Fx = C
   4. (∀x ∈ X, Fx = ∅) −→ ∪ x∈X Fx = ∅
   5. (∀x ∈ X, Fx ∈ 2) −→ ∪ x∈X Fx ∈ 2
*)

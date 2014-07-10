Require Export Unions.

Definition ord_pair (x y : set) : set := UPair (Sing x) (UPair x y).

Notation "⟨ a , b ⟩" := (ord_pair a b) (at level 69).

Definition π1 (p : set) : set := Union (Inter p).
Definition π2 (p : set) : set :=
  Union (Sep (Union p) (fun x : set => x ∈ Inter p → Union p = Inter p)).

(* Lemma 7. For all sets x and y, π1 ⟨x, y⟩ = x *)

(* Lemma 8. For all sets x and y, π2 ⟨x, y⟩ = y *)

(* Theorem 10 (Characteristic Property of Ordered Pairs).

   For all sets a, b, c and d, ⟨a, b⟩ = ⟨c, d⟩ ↔ a = c ∧ b = d *)

Definition is_pair (p : set) : Prop := ∃ x, ∃ y, p = ⟨x, y⟩.

Lemma ord_pair_eta : ∀ p, is_pair p ↔ p = ⟨π1 p, π2 p⟩.
Proof.
  intros. split; intros.
  extension.
    admit.
    apply UPair_E in H0. inv H0.
      unfold is_pair in H. unfold π1.
      destruct H. destruct H.
      rewrite H. unfold ord_pair, Inter.
Admitted.

Hint Resolve ord_pair_eta.

Require Export Axioms.

Definition Sing (x : set): set := {x, x}.

Lemma Sing_I : ∀ x, x ∈ (Sing x).
Proof. intros. compute. auto. Qed.

Lemma Sing_E : ∀ x y, y ∈ (Sing x) → y = x.
Proof.
  intros. compute in *.
  apply UPair_E in H. inversion H; auto.
Qed.

Definition Zero := ∅.
Definition One := Sing ∅.
Definition Two := { ∅, One }.

(* We have the following properties of the powerset equation with respect to
   the defined sets 0, 1 and 2.

   1. 𝒫(0) = 1
   2. 𝒫(1) = 2
*)

Definition FamUnion (X : set) (F : set → set) : set := Union (Repl F X).

Lemma FamUnion_I : ∀ X F x y, x ∈ X → y ∈ (F x) → y ∈ (FamUnion X F).
Admitted.
Lemma FamUnion_E : ∀ X F y, y ∈ (FamUnion X F) → ∃ x, x ∈ X ∧ y ∈ (F x ).
Admitted.

(* Properties of the union over families of indexed sets.

   1. ∪ x∈∅ Fx = ∅
   2. (∀x ∈ X, Fx ∈ 2) −→ (∃x ∈ X, Fx = 1) −→ ∪ x∈X Fx = 1
   3. inhset X −→ (∀x ∈ X, Fx = C) −→ ∪ x∈X Fx = C
   4. (∀x ∈ X, Fx = ∅) −→ ∪ x∈X Fx = ∅
   5. (∀x ∈ X, Fx ∈ 2) −→ ∪ x∈X Fx ∈ 2
*)

Definition Sep (X : set) (P : set → Prop) : set :=
  ε (inhabits _ ∅) (fun Z => ∀ x, x ∈ Z → x ∈ X ∧ P x ).

(* (Definition of Separation is correct). For all bounding sets X and for all
   predicates on sets P, the set Sep X P, mathematically {x ∈ X | P x}, is
   exactly the subset of X where all elements satisfy P, formally:

   ∀x : set, x ∈ {x ∈ X | P x} ↔ x ∈ X ∧ P x.
*)

(*------------------------------------------------------------------------*)
Lemma SepI : ∀ X, ∀ P : set → Prop, ∀ x, x ∈ X → P x → x ∈ (Sep X P).
Admitted.
Lemma SepE1 : ∀ X P x, x ∈ (Sep X P) → x ∈ X.
Admitted.
Lemma SepE2 : ∀ X P x, x ∈ (Sep X P) → P x.
Admitted.
Lemma SepE : ∀ X P x, x ∈ (Sep X P) → x ∈ X ∧ P x.
Admitted.

Definition Inter (M : set) : set :=
  Sep (Union M) (fun x : set => ∀ A : set, A ∈ M → x ∈ A).

Lemma InterI : ∀ x M, inh_set M → (∀ A, A ∈ M → x ∈ A) → x ∈ Inter M.
Admitted.
Lemma InterE : ∀ x M, x ∈ Inter M → inh_set M ∧ ∀ A, A ∈ M → x ∈ A.
Admitted.

Definition BinInter (A B : set) : set := Inter (UPair A B).

Lemma BinInter_I : ∀ A B a: set, a ∈ A ∧ a ∈ B → a ∈ BinInter A B.
Admitted.
Lemma BinInter_E : ∀ A B x, x ∈ BinInter A B → x ∈ A ∧ x ∈ B.
Admitted.

Notation "X ∩ Y" := (BinInter X Y) (at level 69).

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
Admitted.

Definition CProd (A B : set) : set :=
  FamUnion A (fun a => Repl (fun b => ⟨a,b⟩) B).

Lemma CProdI : ∀ a A b B, a ∈ A → b ∈ B → ⟨a, b⟩ ∈ CProd A B.
Admitted.
Lemma CProdE1 : ∀ p A B, p ∈ CProd A B → π1 p ∈ A ∧ π2 p ∈ B.
Admitted.
Lemma CProdE2 : ∀ p A B, p ∈ CProd A B → is_pair p.
Admitted.

(* Lemma 9. For all sets B, ∅ × B = ∅. *)
(* Lemma 10. For all sets A, A × ∅ = ∅. *)

Require Export Axioms.

Definition Sep (X : set) (P : set → Prop) : set :=
  ε (inhabits _ ∅) (fun Z => ∀ x, x ∈ Z → x ∈ X ∧ P x ).

(* (Definition of Separation is correct). For all bounding sets X and for all
   predicates on sets P, the set Sep X P, mathematically {x ∈ X | P x}, is
   exactly the subset of X where all elements satisfy P, formally:

   ∀x : set, x ∈ {x ∈ X | P x} ↔ x ∈ X ∧ P x.
*)

(*------------------------------------------------------------------------*)
Lemma Sep_I : ∀ X, ∀ P : set → Prop, ∀ x, x ∈ X → P x → x ∈ (Sep X P).
Admitted.

Hint Resolve Sep_I.

Lemma Sep_E1 : ∀ X P x, x ∈ (Sep X P) → x ∈ X.
Admitted.

Hint Resolve Sep_E1.

Lemma Sep_E2 : ∀ X P x, x ∈ (Sep X P) → P x.
Admitted.

Lemma Sep_E : ∀ X P x, x ∈ (Sep X P) → x ∈ X ∧ P x.
Admitted.

Hint Resolve Sep_E.

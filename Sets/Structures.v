Require Export Axioms.

Definition Sing (x : set): set := {x, x}.

Lemma Sing_I : ∀ x, x ∈ (Sing x).
Proof. intros. compute. auto. Qed.

Hint Resolve Sing_I.

Lemma Sing_E : ∀ x y, y ∈ (Sing x) → y = x.
Proof.
  intros. compute in *.
  apply UPair_E in H. inversion H; auto.
Qed.

Hint Resolve Sing_E.

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

Definition Inter (M : set) : set :=
  Sep (Union M) (fun x : set => ∀ A : set, A ∈ M → x ∈ A).

Lemma Inter_I : ∀ x M, inh_set M → (∀ A, A ∈ M → x ∈ A) → x ∈ Inter M.
Proof.
  intros. unfold Inter.
  apply Sep_I. inv H. specialize (H0 x0).
    apply Union_I with (Y := x0). auto. auto.
    intros. auto.
Qed.

Hint Resolve Inter_I.

Lemma Inter_E : ∀ x M, x ∈ Inter M → inh_set M ∧ ∀ A, A ∈ M → x ∈ A.
Proof.
  intros. unfold Inter in H.
  apply Sep_E in H. inv H.
  apply Union_E in H0. destruct H0. inv H.
  split.
    specialize (H1 x0). unfold inh_set. exists x0. auto.
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
  split.
    apply H1. pair_1.
    pair_e H.
Qed.

Hint Resolve BinInter_E.

Notation "X ∩ Y" := (BinInter X Y) (at level 69).

Ltac inter := apply BinInter_I ; split ; try auto.
Ltac inter_e H :=
  apply BinInter_E in H ; try (first [ inv H | destruct H ]) ; try auto.

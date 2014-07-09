Require Export Coq.Unicode.Utf8.

Inductive False : Prop := .

Notation "⊥" := (False).

Definition not (A : Prop) : Prop := A → ⊥.

Inductive and (A B : Prop) : Prop := conj : A → B → and A B.

Inductive or (A B : Prop) : Prop :=
  | or_introl : A → or A B
  | or_intror : B → or A B.

Inductive ex (A : Type) (P : A → Prop) : Prop :=
  ex_intro : ∀ x : A, P x → ex A P.

Definition XM : Prop := ∀ P : Prop, P ∨ ¬P.

Axiom classic : XM.

Definition IXM : Type := ∀ P : Prop, P + ¬P.
Definition DIT : Type := ∀ T : Type, T + (T → ⊥).

Inductive inhabited (A : Type) : Prop := inhabits : A -> inhabited A.

Axiom ε_statement : ∀ {A : Type} (P : A → Prop),
  inhabited A → { x : A | (exists x, P x) → P x }.

Definition ε {A : Type} (i : inhabited A) (P : A → Prop) : A :=
  proj1_sig (ε_statement P i).

Definition ε_spec {A : Type} (i : inhabited A) (P : A → Prop) :
  (exists x, P x) → P (ε i P) := proj2_sig (ε_statement P i).

(**************************************************************************)

Parameter set : Type.

Parameter In : set → set → Prop.

Notation "x ∈ X" := (In x X) (at level 69).
Notation "x ∉ X" := (not (In x X)) (at level 69).

Definition Subq : set → set → Prop :=
  fun X Y => ∀ (x : set), x ∈ X → x ∈ Y.

Notation "X ⊆ Y" := (Subq X Y) (at level 69).

Lemma Subq_refl : ∀ (A : set), A ⊆ A.
Proof. compute. auto. Qed.

Lemma Subq_trans : ∀ (A B C : set), A ⊆ B → B ⊆ C → A ⊆ C.
Proof. compute. auto. Qed.

(* Axiom 1 (Extensionality). Two sets X and Y are equal if they contain the
   same elements. *)

Axiom extensionality : ∀ X Y : set, X ⊆ Y → Y ⊆ X → X = Y.

Hint Resolve extensionality.

(* Axiom 2 (∈-induction). The membership relation on sets satisfies the
   induction principle. *)

Axiom In_ind : ∀ P : set → Prop,
  (∀ X : set, (∀ x, x ∈ X → P x) → P X) →
  (∀ X : set, P X).

(* Axiom 3 (The empty set). There ∃ a set which does not contain any
   elements.  We call this set the empty set and denote it by ∅. *)

Parameter Empty : set.

Notation "∅" := (Empty).

Axiom Empty_E : ∀ x : set, x ∉ ∅.

Hint Resolve Empty_E.

Definition inh_set (S : set) := ∃ w, w ∈ S.

(* Axiom 4 (Pairing). For all sets y and z there ∃ a set containing
   exactly y and z as elements. We call this set the unordered pair of y and z
   and denote it by {y,z}. *)

Parameter UPair : set → set → set.

Axiom UPair_I1 : ∀ y z : set, y ∈ (UPair y z).
Axiom UPair_I2 : ∀ y z : set, z ∈ (UPair y z).
Axiom UPair_E : ∀ x y z : set, x ∈ (UPair y z) → x = y ∨ x = z.

Hint Resolve UPair_I1.
Hint Resolve UPair_I2.
Hint Resolve UPair_E.

Notation "{ a , b }" := (UPair a b) (at level 69).

(* The axiomatic pairing of sets a and b is agnostic with respect to their
   ordering. *)

Theorem pair_agnostic : ∀ a b, {a, b} = {b, a}.
Proof.
  intros.
  pose extensionality.
  specialize (e (UPair a b) (UPair b a)).
  apply e; compute; intros;
    apply UPair_E in H; inversion H; rewrite H0; auto.
Qed.

(* Axiom 5 (Union). Given a collection of sets X, there ∃ a set whose
   elements are exactly those which are a member of at least one of the sets
   in the collection X.  We call this set the union over X and denote it by
   ∪. *)

Parameter Union : set → set.

Notation "X ∪ Y" := (Union (UPair X Y)) (at level 69).

Axiom Union_I : ∀ X x Y : set, x ∈ Y → Y ∈ X → x ∈ (Union X).
Axiom Union_E : ∀ X x : set,
  x ∈ (Union X) → ∃ Y : set, x ∈ Y ∧ Y ∈ X.

(* Axiom 6 (Powerset). Given a set X, there ∃ a set which contains as its
   elements exactly those sets which are the subsets of X. We call this set the
   powerset of X and denote it by 𝒫(X). *)

Parameter Power : set → set.

Axiom Power_I : ∀ X Y : set, Y ⊆ X → Y ∈ (Power X).
Axiom Power_E : ∀ X Y : set, Y ∈ (Power X) → Y ⊆ X.

(* Axiom 7 (Replacement). Given a unary set former F and a set X, there ∃
   a set which contains exactly those elements obtained by applying F to each
   element in X. We denote this construction with {F x | x ∈ X}. *)

Parameter Repl : (set → set) → set → set.

Axiom Repl_I : ∀ (X : set) (F : set → set) (x : set),
  x ∈ X → (F x) ∈ (Repl F X).
Axiom Repl_E : ∀ (X : set) (F : set → set) (y : set),
  y ∈ (Repl F X) → ∃ x : set, x ∈ X ∧ y = F x.

(**************************************************************************)

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

(* We have the following properties of the union operation with respect
   to the defined sets ∅, 1 and 2: 

   1. ∪ ∅ = ∅
   2. ∪ {X} = X
   3. ∪ 1 = ∅
   4. X ∈ 2 −→ ∪ X = ∅
   5. ∪ 2 = 1
*)

Theorem union_empty : Union ∅ = ∅.
Proof.
  apply extensionality; compute; intros.
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

(* We have the following properties of the powerset equation with respect to
   the defined sets 0, 1 and 2.

   1. 𝒫(0) = 1
   2. 𝒫(1) = 2
*)

Definition BinUnion (A B : set) : set := Union (UPair A B).

Lemma BinUnion_I1 : ∀ A B a: set, a ∈ A → a ∈ BinUnion A B.
Lemma BinUnion_I2 : ∀ A B b: set, b ∈ B → b ∈ BinUnion A B.
Lemma BinUnion_E : ∀ A B x, x ∈ BinUnion A B → x ∈ A ∨ x ∈ B.

Definition FamUnion (X : set) (F : set → set) : set := Union (Repl F X).

Lemma FamUnion_I : ∀ X F x y, x ∈ X → y ∈ (F x) → y ∈ (FamUnion X F).
Lemma FamUnion_E : ∀ X F y,
  y ∈ (FamUnion X F) → ∃ x, x ∈ X ∧ y ∈ (F x ).

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
Lemma SepI : ∀ X, ∀ P : set → Prop, ∀ x,
  x ∈ X → P x → x ∈ (Sep X P).
Lemma SepE1 : ∀ X P x, x ∈ (Sep X P) → x ∈ X.
Lemma SepE2 : ∀ X P x, x ∈ (Sep X P) → P x.
Lemma SepE : ∀ X P x, x ∈ (Sep X P) → x ∈ X ∧ P x.

Definition Inter (M : set) : set :=
  Sep (Union M) (fun x : set => ∀ A : set, A ∈ M → x ∈ A).

Lemma InterI : ∀ x M, inh_set M → (∀ A, A ∈ M → x ∈ A) → x ∈ Inter M.
Lemma InterE : ∀ x M, x ∈ Inter M → inh_set M ∧ ∀ A, A ∈ M → x ∈ A.

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

Definition CProd (A B : set) : set :=
  FamUnion A (fun a => Repl (fun b => ⟨a,b⟩) B).

Lemma CProdI : ∀ a A b B, a ∈ A → b ∈ B → ⟨a, b⟩ ∈ CProd A B.
Lemma CProdE1 : ∀ p A B, p ∈ CProd A B → π1 p ∈ A ∧ π2 p ∈ B.
Lemma CProdE2 : ∀ p A B, p ∈ CProd A B → is_pair p.

(* Lemma 9. For all sets B, ∅ × B = ∅. *)
(* Lemma 10. For all sets A, A × ∅ = ∅. *)

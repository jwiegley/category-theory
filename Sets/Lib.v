Require Export Coq.Unicode.Utf8.

Ltac inv H := inversion H; subst; clear H.

Inductive False : Prop := .

Notation "⊥" := (False).

Definition not (A : Prop) : Prop := A → ⊥.

Inductive and (A B : Prop) : Prop := conj : A → B → and A B.

Inductive or (A B : Prop) : Prop :=
  | or_introl : A → or A B
  | or_intror : B → or A B.

Inductive ex (A : Type) (P : A → Prop) : Prop :=
  ex_intro : ∀ witness : A, P witness → ex A P.

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

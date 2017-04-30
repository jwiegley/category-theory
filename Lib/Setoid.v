Set Warnings "-notation-overridden".

Require Export Lib.Foundation.
Require Export Coq.Classes.CEquivalence.
Require Export Coq.Classes.CRelationClasses.
Require Export Coq.Classes.CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Infix "<-->" := iffT (at level 100) : category_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :> Equivalence equiv
}.

Infix "≈" := equiv (at level 79) : category_scope.

Program Instance setoid_refl `(sa : Setoid A) :
  Reflexive equiv.
Obligation 1. apply setoid_equiv. Qed.

Program Instance setoid_sym `(sa : Setoid A) :
  Symmetric equiv.
Obligation 1. apply setoid_equiv; auto. Qed.

Program Instance setoid_trans `(sa : Setoid A) :
  Transitive equiv.
Obligation 1.
  apply setoid_equiv.
  destruct sa; simpl in *.
  destruct setoid_equiv0.
  eapply Equivalence_Transitive; eauto.
Qed.

Delimit Scope signature_scope with signature.

Notation "f ++> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f ==> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f --> g" := (respectful (Basics.flip f) g)%signature
  (right associativity, at level 55) : signature_scope.

Arguments Proper {A}%type R%signature m.
Arguments respectful {A B}%type (R R')%signature _ _.

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Reflexive ?X) =>
  unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) =>
  unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) =>
  unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) =>
  apply Build_Equivalence.
Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 8 (respectful _ _ _ _) =>
  unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity : category_laws.
Hint Extern 6 (?X ≈ ?Y) =>
  apply Equivalence_Symmetric : category_laws.
Hint Extern 7 (?X ≈ ?Z) =>
  match goal with
    [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y
  end : category_laws.

Ltac equivalence := constructor; repeat intro; simpl; cat; intuition.
Ltac proper := repeat intro; simpl; cat; intuition.

Global Obligation Tactic :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    | _ => simpl; intros; cat; intuition
    end].

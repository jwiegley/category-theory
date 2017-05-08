Set Warnings "-notation-overridden".

Require Export Lib.Foundation.
Require Export Coq.Classes.CEquivalence.
Require Export Coq.Classes.CRelationClasses.
Require Export Coq.Classes.CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Infix "<-->" := iffT (at level 100) : category_theory_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :> Equivalence equiv
}.

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

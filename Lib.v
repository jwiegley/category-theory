Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.JMeq
  Coq.Program.Tactics
  Coq.Logic.ProofIrrelevance
  FunctionalExtensionality.

Generalizable All Variables.

Close Scope nat_scope.
Delimit Scope category_scope with category.
Open Scope category_scope.

Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Setoid A := {
  equiv : relation A;
  setoid_equiv :> Equivalence equiv
}.

Program Instance setoid_refl `(sa : Setoid A) : Reflexive equiv.
Obligation 1. apply setoid_equiv. Defined.

Program Instance setoid_sym `(sa : Setoid A) : Symmetric equiv.
Obligation 1. apply setoid_equiv; auto. Defined.

Program Instance setoid_trans `(sa : Setoid A) : Transitive equiv.
Obligation 1.
  apply setoid_equiv.
  destruct sa; simpl in *.
  destruct setoid_equiv0.
  eapply Equivalence_Transitive; eauto.
Defined.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.

(* Proof irrelevant equality. *)
Definition proof_eq {P : Prop} (x y : P) := (x = y)%type.

Hint Unfold proof_eq.
Hint Unfold Basics.compose.
Hint Unfold Basics.arrow.
Hint Unfold Basics.impl.
Hint Unfold Datatypes.id.

Program Instance proof_eq_equivalence {P : Prop} : Equivalence (@proof_eq P).

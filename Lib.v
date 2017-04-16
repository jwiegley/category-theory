Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Classes.RelationClasses
  Coq.Classes.CMorphisms
  Coq.Classes.CRelationClasses
  Coq.Logic.JMeq
  Coq.Program.Tactics
  Coq.Logic.ProofIrrelevance
  FunctionalExtensionality.

Generalizable All Variables.

Close Scope nat_scope.
Close Scope type_scope.

Notation "f -> g" := (f -> g)%type : category_scope.

Open Scope category_scope.
Delimit Scope category_scope with category.

Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Class Setoid A := {
  equiv : crelation A;
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

Infix "<<>>" := iffT (at level 199).
Infix "//\\" := Datatypes.prod (at level 198).

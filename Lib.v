Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Logic.JMeq
  Coq.Program.Tactics
  Coq.Logic.ProofIrrelevance
  FunctionalExtensionality.

Require Export
  Coq.Classes.Morphisms
  Coq.Classes.SetoidClass.

Close Scope nat_scope.
Close Scope type_scope.

Notation "f -> g" := (f -> g)%type : category_scope.

Open Scope category_scope.
Delimit Scope category_scope with category.

Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(* Proof irrelevant equality. *)
Definition proof_eq {P : Prop} (x y : P) := (x = y)%type.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.

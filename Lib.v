Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Logic.JMeq
  Coq.Program.Tactics
  FunctionalExtensionality.

Require Export
  Coq.Classes.Morphisms
  Coq.Classes.Equivalence
  Coq.Classes.RelationClasses.

Close Scope nat_scope.
Close Scope type_scope.

Notation "f -> g" := (f -> g)%type : category_scope.

Open Scope category_scope.
Delimit Scope category_scope with category.

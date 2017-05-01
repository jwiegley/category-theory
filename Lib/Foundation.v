Set Warnings "-notation-overridden".

Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Program.Program.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.
Delimit Scope category_scope with category.
Open Scope category_scope.

Infix "\o" := Basics.compose (at level 40, left associativity) : category_scope.

Notation "`` x" := (@projT1 _ _ x) (at level 0) : category_scope.
Notation "( x ; y )" := (existT _ x y) (at level 0) : category_scope.

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Hint Unfold Basics.compose.
Hint Unfold Basics.arrow.
Hint Unfold Datatypes.id.

Arguments Basics.compose {_ _ _} _ _ /.
Arguments Basics.arrow _ _ /.
Arguments Datatypes.id {_} _ /.

Ltac cat :=
  try split;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

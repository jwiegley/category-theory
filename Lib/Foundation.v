Set Warnings "-notation-overridden".

Require Export
  Coq.Init.Datatypes
  Coq.Program.Program.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.
Declare Scope category_theory_scope.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.

Notation "`` x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "( x ; y )" := (existT _ x y) (at level 0) : category_theory_scope.

Notation "`1 x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "`2 x" := (@projT2 _ _ x) (at level 0) : category_theory_scope.
Notation "`3 x" := (@projT3 _ _ x) (at level 0) : category_theory_scope.

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

#[export] Hint Unfold Basics.compose : core.
#[export] Hint Unfold Basics.arrow : core.
#[export] Hint Unfold Datatypes.id : core.

Arguments Basics.compose {_ _ _} _ _ /.
Arguments Basics.arrow _ _ /.
Arguments Datatypes.id {_} _ /.

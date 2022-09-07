Require Export Coq.Program.Program.
Require Export Coq.Classes.CMorphisms.

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

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (~x)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.

Notation "P ∨ Q" := ({ P } + { Q })
  (at level 85, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

From Coq Require Export Program.
From Coq Require Export CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.

(* nLab: https://ncatlab.org/nlab/show/setoid
   Wikipedia: https://en.wikipedia.org/wiki/Setoid

   Foundational plumbing shared by the whole library. There is no single
   mathematical object defined here; instead this file fixes the global
   conventions under which everything downstream is built:

   - The library is setoid-based (see Lib/Setoid.v): a type is equipped with a
     chosen equivalence relation `≈` standing in for equality, in the sense of
     Bishop sets / setoids. To make those equivalences and the `Proper`
     machinery `Type`-valued rather than `Prop`-valued, we work in `Type`
     throughout and use Coq's `CMorphisms`/`CRelationClasses` (the `Type`-valued
     analogues of `Morphisms`/`RelationClasses`).

   - Accordingly the logical connectives are rebound to their constructive,
     `Type`-valued forms in `category_theory_scope`: `exists`/`∃` denote `sigT`,
     `∧` denotes `prod`, `∨` denotes `sum`, and `↔` denotes `iffT`. These carry
     computational content, unlike the `Prop`-valued `ex`/`and`/`or`/`iff`.

   - Notation also supplies the sigma-type projections `` ``x `` / `` `1 x `` /
     `` `2 x `` / `` `3 x `` (the latter projecting a two-predicate `sigT2`) and
     the pairing `( x ; y )`, plus unicode forms for `∀`, `→`, `¬`, `≠`, and
     `λ`. *)

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
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (x → False)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.
Infix "∨" := sum (at level 85, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 10, x binder, y binder, t at level 200, right associativity) :
  category_theory_scope.

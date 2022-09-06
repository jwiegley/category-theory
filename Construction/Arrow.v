Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.

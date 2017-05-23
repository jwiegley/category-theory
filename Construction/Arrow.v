Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.

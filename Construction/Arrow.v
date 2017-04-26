Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Instance Arrow `{C : Category} : Category := (Identity ↓ Identity).

Notation "C ⃗" := (@Arrow C) (at level 90).

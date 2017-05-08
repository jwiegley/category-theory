Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Section Identity.

Context `{C : Category}.
Context `{D : Category}.

Global Program Definition Id : C ⟶ C := {|
  fobj := fun X => X;
  fmap := fun _ _ f => f
|}.

End Identity.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 9, format "Id[ C ]") : category_scope.

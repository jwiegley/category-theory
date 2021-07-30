Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section TerminalFunctor.

Context `{F : C ⟶ D}.
Context `{@Terminal C}.
Context `{@Terminal D}.

Class TerminalFunctor := {
  fobj_one_iso : 1 ≅ F 1;

  fmap_one {X : C} : fmap one ≈ to fobj_one_iso ∘ @one _ _ (F X)
}.

End TerminalFunctor.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Initial.

Notation "'InitialFunctor' F" := (@TerminalFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@InitialFunctor C D F" := (@TerminalFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.

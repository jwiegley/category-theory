Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Functor.Hom.
Require Export Category.Functor.Construction.Product.
Require Export Category.Functor.Opposite.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Adjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class Adjunction_Hom := {
  hom_adj : HomFunctor _ ○ F^op ∏⟶ Id ≅[Fun] HomFunctor _ ○ Id ∏⟶ U
}.

End Adjunction.

Arguments Adjunction_Hom {C D} F%functor U%functor.

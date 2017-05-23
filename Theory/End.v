Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Wedge.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class End `(F : C^op ∏ C ⟶ D) := {
  Fin : Wedge F;

  (* This just restates the fact that limits are terminal objects in the
     category of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  fin {N : Wedge F} : N ~> Fin;
  fin_unique {N : Wedge F} (f g : N ~> Fin) : f ≈ g;

  ump_ends {N : Wedge F} {X : C} :
    wedge_map[Fin] ∘ fin ≈ @wedge_map _ _ _ N X
}.

Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).

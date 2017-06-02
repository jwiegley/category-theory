Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Wedge.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class End `(F : C^op ∏ C ⟶ D) := {
  Fin : Wedge F;

  (* This just restates the fact that limits are terminal objects in the
     category of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  fin {W : Wedge F} : W ~> Fin;
  fin_unique {W : Wedge F} (f g : W ~> Fin) : f ≈ g;

  ump_ends {W : Wedge F} {x : C} :
    wedge_map[Fin] ∘ fin ≈ @wedge_map _ _ _ W x
}.

Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Wedge.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section End.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.

Class End := {
  Fin : Wedge;

  (* This just restates the fact that limits are terminal objects in the
     category of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  fin {N : Wedge} : N ~> Fin;
  fin_unique {N : Wedge} (f g : N ~> Fin) : f ≈ g;

  ump_ends {N : Wedge} {X : D} :
    wedge_map[Fin] ∘ fin ≈ @wedge_map _ _ _ N X
}.

End End.

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Initial.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Distributive.

Context `{C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Bicartesian C _ _}.
Context `{@Initial C}.

Class Distributive := {
  distr_prod_coprod {X Y Z} : X × (Y + Z) ≅ X × Y + X × Z;
  distr_zero {X} : X × Zero ≅ Zero
}.

End Distributive.

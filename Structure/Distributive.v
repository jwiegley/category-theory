Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Bicartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Distributive.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Initial C}.

Class Distributive := {
  distr_prod_coprod {x y z} : @Isomorphism C (x × (y + z)) (x × y + x × z);
  distr_zero {x} : x × 0 ≅ 0
}.

End Distributive.

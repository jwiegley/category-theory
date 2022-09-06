Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.

Generalizable All Variables.

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

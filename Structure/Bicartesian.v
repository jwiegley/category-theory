Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Bicartesian.

Context `{C : Category}.
Context `{Cart : @Cartesian C}.
Context `{Cocart : @Cocartesian C}.

Set Warnings "-non-primitive-record".

Class Bicartesian := {
  bicartesian_is_cartesian := Cart;
  bicartesian_is_cocartesian := Cocart
}.

Coercion bicartesian_is_cartesian : Bicartesian >-> Cartesian.
Coercion bicartesian_is_cocartesian : Bicartesian >-> Cocartesian.

Corollary fork_merge {X Y Z W : C}
          (f : X ~> Y) (g : X ~> Z) (h : W ~> Y) (i : W ~> Z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat.
Qed.

End Bicartesian.

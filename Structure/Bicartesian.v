Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Bicartesian.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.

Corollary fork_merge {x y z w : C}
          (f : x ~> y) (g : x ~> z) (h : w ~> y) (i : w ~> z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat;
  apply (@fork_respects (C^op)); cat.
Qed.

End Bicartesian.

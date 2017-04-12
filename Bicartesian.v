Require Import Lib.
Require Export Cartesian.
Require Export Cocartesian.

Generalizable All Variables.
Set Primitive Projection.
Set Universe Polymorphism.

Class Bicartesian `(_ : Cartesian C) `{@Initial C _} `{@Cocartesian C _ _}.

Corollary fork_merge `{Cartesian C} `{@Initial C _} `{@Cocartesian C _ _}
          {X Y Z W : C} (f : X ~> Y) (g : X ~> Z) (h : W ~> Y) (i : W ~> Z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat.
Qed.

Require Import Lib.
Require Export Cartesian.
Require Export Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Bicartesian.

Context `{C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.

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

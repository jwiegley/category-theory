Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

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

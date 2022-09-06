Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section ProductCartesian.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

Program Instance Product_Cartesian : @Cartesian (C ∏ D) := {
  product_obj := fun x y => (fst x × fst y, snd x × snd y);

  fork := fun _ _ _ f g => (fst f △ fst g, snd f △ snd g);
  exl  := fun x y => (exl, exl);
  exr  := fun x y => (exr, exr)
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  simplify; rewrites; cat;
  rewrite fork_comp; cat.
Qed.

End ProductCartesian.

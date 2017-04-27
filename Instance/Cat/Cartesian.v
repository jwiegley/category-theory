Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Cat_Cartesian : @Cartesian Cat := {
  Prod := @Product;
  fork := fun _ _ _ F G =>
            {| fobj := fun x => (F x, G x)
             ; fmap := fun _ _ f => (fmap[F] f, fmap[G] f) |};
  exl := fun _ _ =>
            {| fobj := fst
             ; fmap := fun _ _ => fst |};
  exr := fun _ _ =>
            {| fobj := snd
             ; fmap := fun _ _ => snd |};
}.
Next Obligation. proper; apply fmap_respects; auto. Qed.
Next Obligation. rewrite !fmap_comp; intuition. Qed.
Next Obligation.
  proper.
  destruct (H X0); clear H.
  destruct (H0 X0); clear H0.
  exists (x1, x2).
  destruct H1, H.
  exists (x3, x4).
  firstorder.
Qed.
Next Obligation.
  simpl; split; intros.
    firstorder.
  intuition.
  destruct (H0 X0); clear H0.
  destruct (H1 X0); clear H1.
  exists (x, x0).
  destruct H, H0.
  exists (x1, x2).
  firstorder.
Qed.

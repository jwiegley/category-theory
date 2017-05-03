Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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
Next Obligation. simplify; rewrite !fmap_comp; intuition. Qed.
Next Obligation.
  proper.
  constructive; simplify; simpl.
  all:swap 3 5.
  all:swap 4 6.
  - apply (transform[to X0]).
  - apply (transform[to X1]).
  - apply (transform[from X0]).
  - apply (transform[from X1]).
  - apply natural_transformation.
  - apply natural_transformation.
  - apply natural_transformation.
  - apply natural_transformation.
  - destruct X0; simpl.
    destruct to, from; simpl in *;
    apply iso_to_from.
  - destruct X1; simpl.
    destruct to, from; simpl in *.
    apply iso_to_from.
  - destruct X0; simpl.
    destruct to, from; simpl in *.
    apply iso_from_to.
  - destruct X1; simpl.
    destruct to, from; simpl in *.
    apply iso_from_to.
Qed.
Next Obligation.
  intros; simplify.
  - constructive; destruct X0; simpl in *.
    all:swap 2 3.
    + apply to.
    + apply from.
    + destruct to; apply natural_transformation.
    + destruct from; apply natural_transformation.
    + apply iso_to_from.
    + apply iso_from_to.
  - constructive; destruct X0; simpl in *.
    all:swap 2 3.
    + apply to.
    + apply from.
    + destruct to; apply natural_transformation.
    + destruct from; apply natural_transformation.
    + apply iso_to_from.
    + apply iso_from_to.
  - intros; simplify.
    destruct x, y; simpl in *.
    constructive; simplify; simpl; firstorder.
    + destruct to; apply natural_transformation.
    + destruct to0; apply natural_transformation.
    + destruct from; apply natural_transformation.
    + destruct from0; apply natural_transformation.
Qed.

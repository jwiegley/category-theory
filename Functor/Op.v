Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Op `(F : C ⟶ D) : C^op ⟶ D^op := {|
  fobj := @fobj C D F;
  fmap := fun X Y f => @fmap C D F Y X (op f);
  fmap_respects := fun X Y f g fg =>
    @fmap_respects C D F Y X f g fg;
  fmap_id := fun X => @fmap_id C D F X;
  fmap_comp := fun X Y Z f g => @fmap_comp C D F Z Y X g f
|}.

Notation "F ^op" := (@Op _ _ F)
  (at level 7, format "F ^op") : functor_scope.

Lemma Op_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof.
  unfold Op; simpl.
  destruct F; simpl.
  f_equal.
Qed.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (op f).

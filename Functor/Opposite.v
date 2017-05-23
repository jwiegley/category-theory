Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op :=
  @Build_Functor (C^op) (D^op) F
    (λ (X Y : C ^op) (f : X ~{ C ^op }~> Y), @fmap C D F Y X f)
    (λ (X Y : C ^op) (f g : X ~{ C ^op }~> Y), @fmap_respects _ _ F Y X f g)
    (λ X : C ^op, fmap_id)
    (λ (X Y Z : C ^op) (f : Y ~{ C ^op }~> Z)
      (g : X ~{ C ^op }~> Y), @fmap_comp _ _ F _ _ _ g f).

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op") : functor_scope.

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (op f).

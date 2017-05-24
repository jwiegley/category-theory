Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.Isomorphism.
Require Import Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Opposite_Adjunction_Iso `(F : D ⟶ C) `(U : C ⟶ D)
        (A : Adjunction_Iso F U) :
  Adjunction_Iso (U^op) (F^op) := {|
  adj := fun X Y =>
    {| to          := from (@adj _ _ _ _ A Y X)
     ; from        := to (@adj _ _ _ _ A Y X)
     ; iso_to_from := iso_from_to (@adj _ _ _ _ A Y X)
     ; iso_from_to := iso_to_from (@adj _ _ _ _ A Y X) |};

  to_adj_nat_l   := fun _ _ _ f g => @from_adj_nat_r _ _ _ _ A _ _ _ g f;
  to_adj_nat_r   := fun _ _ _ f g => @from_adj_nat_l _ _ _ _ A _ _ _ g f;
  from_adj_nat_l := fun _ _ _ f g => @to_adj_nat_r  _ _ _ _ A _ _ _ g f;
  from_adj_nat_r := fun _ _ _ f g => @to_adj_nat_l  _ _ _ _ A _ _ _ g f
|}.

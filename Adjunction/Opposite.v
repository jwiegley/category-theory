Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Opposite_Adjunction `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  U^op ⊣ F^op := {|
  unit := 
    {| to          := from (@adj_iso _ _ _ _ A Y X)
     ; from        := to (@adj_iso _ _ _ _ A Y X)
     ; iso_to_from := iso_from_to (@adj_iso _ _ _ _ A Y X)
     ; iso_from_to := iso_to_from (@adj_iso _ _ _ _ A Y X) |};

  adj_left_nat_l'  := fun _ _ _ f g => @adj_right_nat_r' _ _ _ _ A _ _ _ g f;
  adj_left_nat_r'  := fun _ _ _ f g => @adj_right_nat_l' _ _ _ _ A _ _ _ g f;
  adj_right_nat_l' := fun _ _ _ f g => @adj_left_nat_r'  _ _ _ _ A _ _ _ g f;
  adj_right_nat_r' := fun _ _ _ f g => @adj_left_nat_l'  _ _ _ _ A _ _ _ g f
|}.

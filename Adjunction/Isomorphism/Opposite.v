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

Program Definition Opposite_Adjunction_Iso `(F : D ⟶ C) `(U : C ⟶ D)
        (A : F ⊣ U) :
  U^op ⊣ F^op := {|
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

Notation "N ^op" := (@Opposite_Adjunction_Iso _ _ _ _ N)
  (at level 7, format "N ^op") : adjunction_scope.

Corollary Opposite_Adjunction_Iso_invol `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  (A^op)^op = A.
Proof. reflexivity. Qed.

Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Export Category.Adjunction.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Opposite_Adjunction_Transform
        `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  U^op ∹ F^op := {|
  unit := _;
  counit := _
|}.
Next Obligation.
  transform; simpl; intros.
  - apply counit.
  - apply (@naturality_sym _ _ _ _ counit).
  - apply (@naturality _ _ _ _ counit).
Defined.
Next Obligation.
  transform; simpl; intros.
  - apply unit.
  - apply (@naturality_sym _ _ _ _ unit).
  - apply (@naturality _ _ _ _ unit).
Defined.
Next Obligation.
  apply fmap_counit_unit.
Defined.
Next Obligation.
  apply counit_fmap_unit.
Defined.

Corollary Opposite_Adjunction_Transform_invol
          `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  Opposite_Adjunction_Transform
    (U^op) (F^op) (Opposite_Adjunction_Transform F U A) = A.
Proof. reflexivity. Qed.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Product.
Require Export Category.Structure.Monoidal.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class StrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  strength_nat : (* (⨂) ○ second F ⟹ F ○ (⨂) *)
    (@Compose (C ∏ C) (C ∏ C) C (@tensor C _) (second F))
      ~{[C ∏ C, C]}~>
    (@Compose (C ∏ C) C C F (@tensor C _));

  strength {X Y} : X ⨂ F Y ~> F (X ⨂ Y) := transform[strength_nat] (X, Y);

  strength_id_left {X} :
    fmap[F] (to unit_left) ∘ strength ≈ to (@unit_left _ _ (F X));
  strength_assoc {X Y Z} :
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ X Y (F Z))
      ≈ fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ strength
}.

(*
Section Strong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.
Context `{@StrongFunctor C _ F}.

Lemma strength_id_left {X} :
  fmap[F] (to unit_left) ∘ strength ≈ to (@unit_left _ _ (F X)).
Proof.
  unfold strength.
  destruct H0; simpl in *; clear H0 strength0;
  destruct strength_nat0; simpl in *.

  strength_naturality {X Y Z} :
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ X Y (F Z))
      ≈ fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ strength
*)

Class RightStrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (* (⨂) ○ first F ⟹ F ○ (⨂) *)
    (@Compose (C × C) (C × C) C (@tensor C _) (first F))
      ~{[C × C, C]}~>
    (@Compose (C × C) C C F (@tensor C _));

  rstrength {X Y} : F X ⨂ Y ~> F (X ⨂ Y) := transform[rstrength_nat] (X, Y);

  rrstrength_id_right {X} :
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F X));
  rstrength_assoc {X Y Z} :
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F X) Y Z)
      ≈ fmap[F] (from (@tensor_assoc _ _ X Y Z)) ∘ rstrength
}.

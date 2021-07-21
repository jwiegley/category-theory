Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section RelevantMonoidal.

Context {C : Category}.

Class RelevantMonoidal `{@Monoidal C} := {
  is_symmetric :> SymmetricMonoidal;

  diagonal {x} : x ~> x ⨂ x;
  diagonal_natural : natural (@diagonal);

  (* These properties are given by Kosta Došen and Zoran Petrić in their 2007
     publication, "Relevant Categories and Partial Functions". *)

  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  diagonal_tensor_assoc {x} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal x;

  twist_diagonal {x} :
    twist ∘ diagonal ≈ @diagonal x;

  twist2 {x y z w} : (x ⨂ y) ⨂ (z ⨂ w) ~> (x ⨂ z) ⨂ (y ⨂ w) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  diagonal_twist2 {x y} :
    @diagonal (x ⨂ y) ≈ twist2 ∘ diagonal ⨂ diagonal
}.

Lemma twist2_natural `{@Monoidal C} `{@RelevantMonoidal _} :
  natural (@twist2 _ _).
Proof.
  unfold twist2; simpl; intros.
  transitivity ((g ⨂ i) ⨂ h ⨂ j ∘ tensor_assoc⁻¹ ∘
                        id{C} ⨂ (tensor_assoc ∘ twist ⨂ id{C} ∘ tensor_assoc⁻¹) ∘ tensor_assoc).
  { rewrite comp_assoc.
    apply compose_respects.
    2: reflexivity.
    rewrite comp_assoc.
    apply compose_respects.
    2: reflexivity.
    apply compose_respects.
    2: reflexivity.
    etransitivity.
    { apply compose_respects.
      2: reflexivity.
      transitivity ((@id C y ⨂ i) ⨂ h ⨂ j).
      2: reflexivity.
      etransitivity.
      { apply compose_respects.
        - rewrite <- bimap_comp.
          reflexivity.
        - reflexivity.
      }
      rewrite <- bimap_comp.
      apply bimap_respects.
      - normal.
        reflexivity.
      - rewrite id_right.
        apply bimap_id_left_right.
    }
    rewrite <- bimap_comp.
    apply bimap_respects.
    - apply bimap_id_left_right.
    - apply id_right.
  }
  transitivity (tensor_assoc⁻¹ ∘ id{C} ⨂ (tensor_assoc ∘ twist ⨂ id{C} ∘ tensor_assoc⁻¹)
                               ∘ tensor_assoc ∘ (g ⨂ h) ⨂ i ⨂ j).
  2: {
    symmetry.
    rewrite comp_assoc_sym.
    rewrite comp_assoc_sym.
    rewrite comp_assoc_sym.
    apply compose_respects.
    1: reflexivity.
    etransitivity.
    { apply compose_respects.
      1: reflexivity.
      etransitivity.
      { apply compose_respects.
        1: reflexivity.
        rewrite <- bimap_comp.
        apply bimap_respects.
        - apply bimap_id_left_right.
        - apply id_left.
      }
      rewrite <- bimap_comp.
      apply bimap_respects.
      - apply id_left.
      - apply id_right.
    }
    rewrite <- bimap_comp.
    apply bimap_respects.
    - apply id_left.
    - apply bimap_id_left_right.
  }
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  comp_left.
  comp_right.
  transitivity (g ⨂ (i ⨂ h ⨂ j ∘ tensor_assoc ∘ twist ⨂ id{C} ∘ tensor_assoc⁻¹)).
  { rewrite <- bimap_comp.
    etransitivity.
    { apply bimap_respects.
      - apply id_right.
      - reflexivity.
    }
    apply bimap_respects.
    1: reflexivity.
    normal.
    reflexivity.
  }
  transitivity (g ⨂ (tensor_assoc ∘ twist ⨂ id{C} ∘ tensor_assoc⁻¹ ∘ h ⨂ i ⨂ j)).
  2: {
    normal.
    reflexivity.
  }
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  rewrite <- !bimap_comp.
  apply bimap_respects.
  - apply bimap_twist.
  - cat.
Qed.

End RelevantMonoidal.

Notation "∆ x" := (@diagonal _ _ _ x)
  (at level 9, format "∆ x") : morphism_scope.

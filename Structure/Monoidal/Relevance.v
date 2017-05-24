Set Warnings "-notation-overridden".

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

Section RelevanceMonoidal.

Context {C : Category}.

Class RelevanceMonoidal `{@Monoidal C} := {
  is_symmetric :> SymmetricMonoidal;

  diagonal {X} : X ~> X ⨂ X;
  diagonal_natural : natural (@diagonal);

  (* These properties are given by Kosta Došen and Zoran Petrić in their 2007
     publication, "Relevant Categories and Partial Functions". *)

  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  diagonal_tensor_assoc {X} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal X;

  twist_diagonal {X} :
    twist ∘ diagonal ≈ @diagonal X;

  twist2 {X Y Z W} : (X ⨂ Y) ⨂ (Z ⨂ W) ~> (X ⨂ Z) ⨂ (Y ⨂ W) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  diagonal_twist2 {X Y} :
    @diagonal (X ⨂ Y) ≈ twist2 ∘ diagonal ⨂ diagonal
}.

Lemma twist2_natural `{@Monoidal C} `{@RelevanceMonoidal _} :
  natural (@twist2 _ _).
Proof.
  unfold twist2; simpl; intros; normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  comp_right.
  comp_left.
  normal.
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  normal.
  bimap_right.
  pose proof (fst twist_natural _ _ h _ _ i); simpl in X0.
  normal; assumption.
Qed.

End RelevanceMonoidal.

Notation "∆ X" := (@diagonal _ _ _ X)
  (at level 9, format "∆ X") : morphism_scope.

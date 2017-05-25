Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Proofs.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SemicartesianProofs.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

Lemma proj_left_tensor_id {X Y Z} :
  proj_left ⨂ id ≈ id[X] ⨂ @proj_right _ _ _ Y Z ∘ tensor_assoc.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_right.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

Lemma proj_right_tensor_id {X Y Z} :
  id ⨂ proj_right ≈ @proj_left _ _ _ X Y ⨂ id[Z] ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_left.
  rewrite inverse_triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  normal; reflexivity.
Qed.

Lemma proj_left_left {X Y Z} :
  proj_left ∘ proj_left ≈ @proj_left _ _ _ X (Y ⨂ Z) ∘ tensor_assoc.
Proof.
  unfold proj_left; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_right).
  rewrite to_unit_right_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_right.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [reflexivity|].
  apply unit_terminal.
Qed.

Lemma proj_right_right {X Y Z} :
  proj_right ∘ proj_right ≈ @proj_right _ _ _ (X ⨂ Y) Z ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_right; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_left).
  rewrite to_unit_left_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_left.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [|reflexivity].
  apply unit_terminal.
Qed.

Corollary proj_left_natural {X Y Z W} (f : X ~> Y) (g : Z ~> W) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary proj_right_natural {X Y Z W} (f : X ~> Y) (g : Z ~> W) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End SemicartesianProofs.

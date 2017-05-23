Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Monoidal.

Context {C : Category}.

(* A semi-cartesian monoidal category is basically an assertion that the unit
   is terminal. *)

Class SemicartesianMonoidal `{@Monoidal C} := {
  eliminate {X} : X ~> I;

  unit_terminal {X} (f g : X ~> I) : f ≈ g;

  proj_left  {X Y} : X ⨂ Y ~> X := unit_right ∘ id ⨂ eliminate;
  proj_right {X Y} : X ⨂ Y ~> Y := unit_left  ∘ eliminate ⨂ id
}.

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

Lemma proj_left_tensor_id `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z} :
  proj_left ⨂ id ≈ id[X] ⨂ @proj_right _ _ Y Z ∘ tensor_assoc.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_right.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

Lemma proj_right_tensor_id `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z} :
  id ⨂ proj_right ≈ @proj_left _ _ X Y ⨂ id[Z] ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_left.
  rewrite inverse_triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  normal; reflexivity.
Qed.

Lemma proj_left_left `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z} :
  proj_left ∘ proj_left ≈ @proj_left _ _ X (Y ⨂ Z) ∘ tensor_assoc.
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

Lemma proj_right_right `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z} :
  proj_right ∘ proj_right ≈ @proj_right _ _ (X ⨂ Y) Z ∘ tensor_assoc⁻¹.
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

Corollary proj_left_natural `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z W}
          (f : X ~> Y) (g : Z ~> W) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary proj_right_natural `{@Monoidal C} `{@SemicartesianMonoidal _} {X Y Z W}
          (f : X ~> Y) (g : Z ~> W) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End Monoidal.

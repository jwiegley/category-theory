Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Pure.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.
Context `{@StrongFunctor C _ F}.
Context `{@LaxMonoidalFunctor C C _ _ F}.

Definition pure {A} : A ~> F A :=
  fmap unit_right ∘ strength ∘ id[A] ⨂ lax_pure ∘ unit_right⁻¹.

Lemma pure_natural : natural (@pure).
Proof.
  simpl; intros.
  unfold pure.
  normal.
  rewrite to_unit_right_natural.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  pose proof (strength_natural _ _ g I I id); simpl in X0.
  normal.
  rewrite X0.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- from_unit_right_natural.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  rewrite fmap_id; cat.
Qed.

Lemma fmap_pure {a b} (f : a ~> b) : pure ∘ f ≈ fmap f ∘ pure.
Proof.
  symmetry.
  sapply pure_natural.
Qed.

End Pure.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 9, format "pure[ F ]") : morphism_scope.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Cartesian.
Require Export Category.Structure.Monoidal.Cartesian.Proofs.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianMonoidalCartesian.

Context `{@Monoidal C}.
Context `{@CartesianMonoidal C _}.

Global Program Definition CartesianMonoidal_Cartesian : @Cartesian C := {|
  Prod := fun X Y => (X ⨂ Y)%object;
  fork := fun X _ _ f g => f ⨂ g ∘ ∆X;
  exl  := fun _ _ => proj_left;
  exr  := fun _ _ => proj_right
|}.
Next Obligation. apply is_relevance. Defined.
Next Obligation.
  proper.
  rewrite X0, X1.
  reflexivity.
Qed.
Next Obligation.
  split; intros.
    split.
      rewrite X0; clear X0.
      rewrite comp_assoc.
      rewrite proj_left_natural.
      rewrite <- comp_assoc.
      rewrite proj_left_diagonal; cat.
    rewrite X0; clear X0;
    rewrite comp_assoc.
    rewrite proj_right_natural.
    rewrite <- comp_assoc.
    rewrite proj_right_diagonal; cat.
  rewrite <- (fst X0), <- (snd X0).
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrite comp_assoc.
  rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidalCartesian.

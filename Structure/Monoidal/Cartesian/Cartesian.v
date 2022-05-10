Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Relevant.
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
  product_obj := fun x y => (x ⨂ y)%object;
  fork := fun x _ _ f g => f ⨂ g ∘ ∆x;
  exl  := fun _ _ => proj_left;
  exr  := fun _ _ => proj_right
|}.
Next Obligation. apply is_relevance. Defined.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  split; intros.
    split.
      rewrites.
      rewrite comp_assoc.
      rewrite proj_left_natural.
      rewrite <- comp_assoc.
      rewrite proj_left_diagonal; cat.
    rewrites.
    rewrite comp_assoc.
    rewrite proj_right_natural.
    rewrite <- comp_assoc.
    rewrite proj_right_diagonal; cat.
  rewrite <- (fst X), <- (snd X).
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrite comp_assoc.
  rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidalCartesian.

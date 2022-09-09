Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoidal.Cartesian.Proofs.

Generalizable All Variables.

Section CartesianMonoidalCartesian.

Context `{@CartesianMonoidal C}.

Program Definition CartesianMonoidal_Cartesian : @Cartesian C := {|
  product_obj := fun x y => (x ⨂ y)%object;
  Cartesian.fork := @fork _ _;
  exl  := fun _ _ => proj_left;
  exr  := fun _ _ => proj_right
|}.
Next Obligation.
  unfold fork.
  split; intros.
  - split.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_left_natural.
      rewrite <- comp_assoc.
      rewrite proj_left_diagonal; cat.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_right_natural.
      rewrite <- comp_assoc.
      rewrite proj_right_diagonal; cat.
  - rewrite <- (fst X), <- (snd X).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidalCartesian.

Coercion CartesianMonoidal_Cartesian : CartesianMonoidal >-> Cartesian.

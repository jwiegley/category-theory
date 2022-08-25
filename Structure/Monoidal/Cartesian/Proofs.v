Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Proofs.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Semicartesian.Proofs.
Require Export Category.Structure.Monoidal.Relevant.
Require Export Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianMonoidal.

Context `{@Monoidal C}.
Context `{@CartesianMonoidal C _}.

Corollary unit_left_eliminate {x y} (f : x ~> y) :
  unit_left ∘ eliminate ⨂ f ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_right_diagonal.
  unfold proj_right.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural as X0; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary unit_right_eliminate {x y} (f : x ~> y) :
  unit_right ∘ f ⨂ eliminate ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_left_diagonal.
  unfold proj_left.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X.
  rewrite <- X; clear X.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Lemma eliminate_right_diagonal {x} :
  id[x] ⨂ eliminate ∘ ∆x ≈ unit_right⁻¹.
Proof.
  apply (iso_to_monic unit_right).
  rewrite comp_assoc.
  rewrite unit_right_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma eliminate_left_diagonal {x} :
  eliminate ⨂ id[x] ∘ ∆x ≈ unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite comp_assoc.
  rewrite unit_left_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_left_id_diagonal {x y} :
  proj_left ⨂ id ∘ ∆(x ⨂ y) ≈ tensor_assoc ∘ ∆x ⨂ id.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ _ x _ id x _ id y _ eliminate y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_left, !id_right in X0.
  unfold proj_left.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  unfold braid2 in X0.
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- triangle_identity_left.
  normal.
  Set Printing Implicit.
  rewrite unit_left_braid.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  normal.
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_right_id_diagonal {x y} :
  proj_right ⨂ id ∘ ∆(x ⨂ y)
    ≈ tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ ∆y.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ _ x _ eliminate x _ id y _ id y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold braid2 in X0.
  unfold proj_right.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  repeat comp_left.
  rewrite comp_assoc.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Corollary proj_right_left_diagonal {x y} :
  proj_right ⨂ proj_left ∘ ∆(x ⨂ y) ≈ braid.
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_right_id_diagonal.
  unfold proj_left, proj_right.
  normal.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite triangle_identity_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to.
  normal.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- to_unit_right_natural.
  symmetry.
  rewrite <- id_right at 1.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry.
  normal.
  spose (@from_tensor_assoc_natural _ _ x _ y _ y _ id id eliminate) as X0.
  rewrite bimap_id_id in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap _ _)).
  rewrites.
  normal.
  rewrite eliminate_right_diagonal.
  rewrite <- triangle_identity_right.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

Corollary proj_left_right_diagonal {x y} :
  proj_left ⨂ proj_right ∘ ∆(x ⨂ y) ≈ id[x ⨂ y].
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_left_id_diagonal.
  rewrite comp_assoc.
  unfold proj_right.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite eliminate_right_diagonal.
  normal.
  rewrite <- triangle_identity.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

Program Instance diagonal_monic {x} :
  Monic ∆x.
Next Obligation.
  rewrite <- unit_left_eliminate.
  rewrite <- (unit_left_eliminate g2).
  rewrite <- (@eliminate_comp _ _ _ _ _ g1) at 1.
  rewrite <- (@eliminate_comp _ _ _ _ _ g2) at 1.
  rewrite <- (id_left g1) at 2.
  rewrite <- (id_left g2) at 2.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrites.
  srewrite diagonal_natural.
  reflexivity.
Qed.

Corollary proj_left_braid {x y} :
  proj_left ∘ braid ≈ @proj_right _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_right_eliminate.
  reflexivity.
Qed.

Corollary proj_right_braid {x y} :
  proj_right ∘ braid ≈ @proj_left _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_left_eliminate.
  reflexivity.
Qed.

#[global] Program Definition CartesianMonoidal_Cartesian : @Cartesian C := {|
  product_obj := fun x y => (x ⨂ y)%object;
  fork := fun x _ _ f g => f ⨂ g ∘ ∆x;
  exl  := fun _ _ => proj_left;
  exr  := fun _ _ => proj_right
|}.
Next Obligation.
  apply cartesian_is_relevant.
Defined.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  - rewrites.
    rewrite comp_assoc.
    rewrite proj_left_natural.
    rewrite <- comp_assoc.
    rewrite proj_left_diagonal; cat.
  - rewrites.
    rewrite comp_assoc.
    rewrite proj_right_natural.
    rewrite <- comp_assoc.
    rewrite proj_right_diagonal; cat.
  - rewrites.
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidal.

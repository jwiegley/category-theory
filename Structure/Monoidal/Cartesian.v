Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Relevance.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianMonoidal.

Context {C : Category}.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

Class CartesianMonoidal `{@Monoidal C} := {
  is_semicartesian :> @SemicartesianMonoidal C _;
  is_relevance     :> @RelevanceMonoidal C _;

  proj_left_diagonal  {X} : proj_left  ∘ diagonal ≈ id[X];
  proj_right_diagonal {X} : proj_right ∘ diagonal ≈ id[X];

  unit_left_twist  {X} : unit_left  ∘ @twist _ _ _ X I ≈ unit_right;
  unit_right_twist {X} : unit_right ∘ @twist _ _ _ I X ≈ unit_left
}.

Corollary unit_left_eliminate `{@Monoidal C} `{@CartesianMonoidal _}
          {X Y} (f : X ~> Y) :
  unit_left ∘ eliminate ⨂ f ∘ ∆X ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_right_diagonal.
  unfold proj_right.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary unit_right_eliminate `{@Monoidal C} `{@CartesianMonoidal _}
          {X Y} (f : X ~> Y) :
  unit_right ∘ f ⨂ eliminate ∘ ∆X ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_left_diagonal.
  unfold proj_left.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Lemma eliminate_right_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X} :
  id[X] ⨂ eliminate ∘ ∆X ≈ unit_right⁻¹.
Proof.
  apply (iso_monic unit_right).
  rewrite comp_assoc.
  rewrite unit_right_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma eliminate_left_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X} :
  eliminate ⨂ id[X] ∘ ∆X ≈ unit_left⁻¹.
Proof.
  apply (iso_monic unit_left).
  rewrite comp_assoc.
  rewrite unit_left_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_left_id_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_left ⨂ id ∘ ∆(X ⨂ Y) ≈ tensor_assoc ∘ ∆X ⨂ id.
Proof.
  rewrite diagonal_twist2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  pose proof (@twist2_natural _ _ _ X _ id X _ id Y _ eliminate Y _ id); simpl in X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_left, !id_right in X0.
  unfold proj_left.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  unfold twist2 in X0.
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
  rewrite unit_left_twist.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  normal.
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_right_id_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_right ⨂ id ∘ ∆(X ⨂ Y)
    ≈ tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc⁻¹ ∘ id[X] ⨂ ∆Y.
Proof.
  rewrite diagonal_twist2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  pose proof (@twist2_natural _ _ _ X _ eliminate X _ id Y _ id Y _ id);
  simpl in X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold twist2 in X0.
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

Corollary proj_right_left_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_right ⨂ proj_left ∘ ∆(X ⨂ Y) ≈ twist.
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
  pose proof (@from_tensor_assoc_natural _ _ X _ Y _ Y _ id id eliminate).
  rewrite bimap_id_id in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap _ _)).
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_right_diagonal.
  rewrite <- triangle_identity_right.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

Corollary proj_left_right_diagonal `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_left ⨂ proj_right ∘ ∆(X ⨂ Y) ≈ id[X ⨂ Y].
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

Local Obligation Tactic := intros; simplify; simpl in *; intros; normal.

Program Instance diagonal_monic `{@Monoidal C} `{@CartesianMonoidal _} {X} :
  Monic ∆X.
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
  rewrite X0.
  srewrite diagonal_natural.
  reflexivity.
Qed.

Corollary proj_left_twist `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_left ∘ twist ≈ @proj_right _ _ _ X Y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_right_eliminate.
  reflexivity.
Qed.

Corollary proj_right_twist `{@Monoidal C} `{@CartesianMonoidal _} {X Y} :
  proj_right ∘ twist ≈ @proj_left _ _ _ X Y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_left_eliminate.
  reflexivity.
Qed.

Global Program Definition SymmetricCartesianMonoidal_Cartesian
       `{@Monoidal C} `{@CartesianMonoidal _} :
  @Cartesian C := {|
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
  - rewrite X0; clear X0.
    rewrite comp_assoc.
    rewrite proj_left_natural.
    rewrite <- comp_assoc.
    rewrite proj_left_diagonal; cat.
  - rewrite X0; clear X0;
    rewrite comp_assoc.
    rewrite proj_right_natural.
    rewrite <- comp_assoc.
    rewrite proj_right_diagonal; cat.
  - rewrite <- x, <- y.
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidal.

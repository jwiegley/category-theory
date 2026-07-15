Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** Identity and composition of K-enriched functors, together with the left
    and right whiskering of a V-natural transformation by an enriched functor.

    These assemble the categorical structure on K-categories: EnrichedId and
    EnrichedCompose give the identity and composite 1-cells, while the two
    whiskerings supply the horizontal action of 1-cells on V-natural 2-cells
    that Fun.v needs to build the enriched functor category. *)

(** The identity enriched functor: the object map is the identity and each
    hom-object map is the identity K-morphism id[x ⟿ y]. *)

Program Definition EnrichedId {K : Category} `{@Monoidal K}
        (C : Enriched K) : EnrichedFunctor K C C := {|
  efobj := fun x => x;
  efmap := fun x y => id
|}.
Next Obligation.
  (* preserves identity: id ∘ eid ≈ eid, by id_left *)
  intros.
  simpl.
  now rewrite id_left.
Qed.
Next Obligation.
  (* preserves composition: ecompose ∘ id ⨂ id ≈ id ∘ ecompose.
     bimap id id ≈ id collapses the left tensor, id_left the right. *)
  intros.
  simpl.
  rewrite bimap_id_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** Composition of enriched functors G ∘ F: compose object maps and compose
    the hom-object maps in K. *)

Program Definition EnrichedCompose {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        (G : EnrichedFunctor K D E) (F : EnrichedFunctor K C D) :
  EnrichedFunctor K C E := {|
  efobj := fun x => efobj (efobj x);
  efmap := fun x y => efmap ∘ efmap
|}.
Next Obligation.
  (* preserves identity: (efmap G ∘ efmap F) ∘ eid ≈ eid.
     Reassociate, apply F.efmap_id then G.efmap_id. *)
  intros.
  simpl.
  rewrite <- comp_assoc.
  rewrite (efmap_id (EnrichedFunctor := F)).
  rewrite (efmap_id (EnrichedFunctor := G)).
  reflexivity.
Qed.
Next Obligation.
  (* preserves composition:
       ecompose ∘ (efmap G ∘ efmap F) ⨂ (efmap G ∘ efmap F)
         ≈ (efmap G ∘ efmap F) ∘ ecompose.
     Split the tensor with bimap_comp, then use G.efmap_comp and
     F.efmap_comp. *)
  intros.
  simpl.
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := G)).
  rewrite <- comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := F)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(** Left whiskering: given a V-natural transformation σ : F ⟹ G between
    F, G : C ⟶ D and an enriched functor H : D ⟶ E, produce a V-natural
    transformation H∘F ⟹ H∘G whose component at x is efmap H ∘ σ_x. *)

Program Definition EnrichedWhiskerLeft {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K D E)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose H F) (EnrichedCompose H G) := {|
  etransform := fun x => efmap ∘ etransform x
|}.
Next Obligation.
  (* enaturality of the left whisker at x, y.
     LHS:  ecompose ∘ ((efmap H ∘ σ_y) ⨂ (efmap H ∘ efmap F)) ∘ unit_left⁻¹
     Split the tensor, pull ecompose ∘ (efmap H ⨂ efmap H) through
     H.efmap_comp, then apply σ's enaturality, and reassemble the RHS. *)
  intros.
  simpl.
  (* split each tensor of composites into a composite of tensors *)
  rewrite !bimap_comp.
  (* expose ecompose ∘ (efmap H ⨂ efmap H) on both sides and collapse it
     through H.efmap_comp into efmap H ∘ ecompose *)
  rewrite !comp_assoc.
  rewrite !(efmap_comp (EnrichedFunctor := H)).
  (* factor efmap H off the far left and finish by σ's enaturality *)
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite !comp_assoc.
  apply (enaturality (EnrichedTransform := σ)).
Qed.

(** Right whiskering: given σ : F ⟹ G between F, G : C ⟶ D and an enriched
    functor H : B ⟶ C, produce F∘H ⟹ G∘H whose component at x is σ_{H x}. *)

Program Definition EnrichedWhiskerRight {K : Category} `{@Monoidal K}
        {B C D : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K B C)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose F H) (EnrichedCompose G H) := {|
  etransform := fun x => etransform (efobj x)
|}.
Next Obligation.
  (* enaturality of the right whisker at x, y.
     LHS:  ecompose ∘ (σ_{Hy} ⨂ (efmap F ∘ efmap H)) ∘ unit_left⁻¹
     Split the tensor: (id ⨂ efmap H) ∘ unit_left⁻¹ ≈ unit_left⁻¹ ∘ efmap H
     by from_unit_left_natural; then apply σ's enaturality, and turn the
     RHS coercion back with from_unit_right_natural. *)
  intros.
  simpl.
  (* pad each component transform with an identity so the tensor becomes a
     tensor of composites, then split it *)
  rewrite <- (id_right (etransform (efobj y))).
  rewrite <- (id_right (etransform (efobj x))).
  rewrite !bimap_comp.
  (* right-associate so bimap id (efmap H) ∘ unit_left⁻¹ and
     bimap (efmap H) id ∘ unit_right⁻¹ appear as bare subterms, then slide
     the unitors past efmap H *)
  rewrite <- !comp_assoc.
  rewrite from_unit_left_natural.
  rewrite from_unit_right_natural.
  (* factor efmap H off the far right and finish by σ's enaturality *)
  rewrite !comp_assoc.
  apply compose_respects; [ | reflexivity ].
  apply (enaturality (EnrichedTransform := σ)).
Qed.

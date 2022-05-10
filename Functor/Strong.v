Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Hom.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.
Require Export Category.Construction.Product.
Require Export Category.Functor.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class StrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  strength {x y} : x ⨂ F y ~> F (x ⨂ y);
  strength_natural : natural (@strength);

  strength_id_left {x} :
    fmap[F] (to unit_left) ∘ strength
      << I ⨂ F x ~~> F x >>
    to (@unit_left _ _ (F x));

  strength_assoc {x y z} :
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ strength
      << (x ⨂ y) ⨂ F z ~~> F (x ⨂ y ⨂ z) >>
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ x y (F z))
}.

Class RightStrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (⨂) ◯ F ∏⟶ Id ⟹ F ◯ (⨂);

  rstrength {x y} : F x ⨂ y ~> F (x ⨂ y) := transform[rstrength_nat] (x, y);

  rrstrength_id_right {x} :
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F x));
  rstrength_assoc {x y z} :
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F x) y z)
      ≈ fmap[F] (from (@tensor_assoc _ _ x y z)) ∘ rstrength
}.

Require Import Category.Functor.Product.

Section Strong.

Context `{@Monoidal C}.
Context {F : C ⟶ C}.

Global Program Instance Id_StrongFunctor : StrongFunctor Id[C] := {
  strength := fun _ _ => id
}.

Local Obligation Tactic := program_simpl.

Global Program Instance Compose_StrongFunctor (F G : C ⟶ C) :
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F ◯ G) := {
  strength := fun _ _ => fmap[F] strength ∘ strength
}.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (strength0 _ _)).
  rewrite <- strength_natural0; clear strength_natural0.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- strength_natural1; clear strength_natural1.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_id_left1.
  apply strength_id_left0.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_assoc1.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite strength_assoc0.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  specialize (strength_natural0
                x x (id[x]) (y ⨂ G z)%object (G (y ⨂ z))%object
                (strength1 y z)).
  rewrite !bimap_id_id in strength_natural0.
  rewrite !fmap_id in strength_natural0.
  rewrite !id_right in strength_natural0.
  rewrite strength_natural0.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- bimap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

End Strong.

Notation "strength[ F ]" := (@strength _ _ F%functor _ _ _)
  (at level 9, format "strength[ F ]") : morphism_scope.

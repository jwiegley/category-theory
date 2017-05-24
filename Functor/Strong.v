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

Class StrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  strength {X Y} : X ⨂ F Y ~> F (X ⨂ Y);
  strength_natural : natural (@strength);

  strength_id_left {X} :
    fmap[F] (to unit_left) ∘ strength
      << I ⨂ F X ~~> F X >>
    to (@unit_left _ _ (F X));

  strength_assoc {X Y Z} :
    fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ strength
      << (X ⨂ Y) ⨂ F Z ~~> F (X ⨂ Y ⨂ Z) >>
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ X Y (F Z))
}.

Class RightStrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (⨂) ○ F ∏⟶ Id ⟹ F ○ (⨂);

  rstrength {X Y} : F X ⨂ Y ~> F (X ⨂ Y) := transform[rstrength_nat] (X, Y);

  rrstrength_id_right {X} :
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F X));
  rstrength_assoc {X Y Z} :
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F X) Y Z)
      ≈ fmap[F] (from (@tensor_assoc _ _ X Y Z)) ∘ rstrength
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
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F ○ G) := {
  strength := fun _ _ => fmap[F] strength ∘ strength
}.
Next Obligation.
  destruct H0, H1; simpl in *.
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
  destruct H0, H1; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_id_left1.
  apply strength_id_left0.
Qed.
Next Obligation.
  destruct H0, H1; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_assoc1.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite strength_assoc0.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  specialize (strength_natural0
                X X (id[X]) (Y ⨂ G Z)%object (G (Y ⨂ Z))%object
                (strength1 Y Z)).
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

Class StrongTransformation {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@StrongFunctor _ _ F}
      {G : C ⟶ C} `{@StrongFunctor _ _ G} (N : F ⟹ G) := {
  strength_transform {X Y} :
    strength[G] ∘ id[X] ⨂ transform[N] Y ≈ transform[N] _ ∘ strength[F]
}.

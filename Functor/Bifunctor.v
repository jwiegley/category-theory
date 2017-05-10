Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A bifunctor is any functor from a product category to another category; so
   we don't need to formalize it separately here, but there are certain helper
   function related to bifunctors. *)

Section Bifunctor.

Context `{C : Category}.
Context `{D : Category}.
Context `{E : Category}.

(* A bimap takes two arrows in C and D, and lifts them to an arrow in E over
   some bifunctor F : C ∏ D ⟶ E. *)
Definition bimap `{F : C ∏ D ⟶ E} {X W : C} {Y Z : D}
           (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  F (X, Y) ~{E}~> F (W, Z) := @fmap (C ∏ D) E F (X, Y) (W, Z) (f, g).

Corollary bimap_fmap `{F : C ∏ D ⟶ E} {X W : C} {Y Z : D}
      (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  @fmap (C ∏ D) E F (X, Y) (W, Z) (f, g) = bimap f g.
Proof. reflexivity. Defined.

Global Program Instance bimap_respects `{F : C ∏ D ⟶ E} {X W : C} {Y Z : D} :
  Proper (equiv ==> equiv ==> equiv) (@bimap F X W Y Z).
Next Obligation.
  proper.
  unfold bimap.
  apply fmap_respects.
  split; assumption.
Qed.

Lemma bimap_comp `{F : C ∏ D ⟶ E}
      `(f : Y ~{C}~> Z) `(h : X ~{C}~> Y)
      `(g : V ~{D}~> W) `(i : U ~{D}~> V) :
  bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  reflexivity.
Qed.

Lemma bimap_id_id `{F : C ∏ D ⟶ E} {X Y} :
  bimap (id[X]) (id[Y]) ≈ id.
Proof.
  destruct F; simpl.
  apply fmap_id.
Qed.

Hint Rewrite @bimap_id_id : categories.

Lemma bimap_comp_id_left `{F : C ∏ D ⟶ E} {W}
      `(f : Y ~{D}~> Z) `(g : X ~{D}~> Y) :
  bimap (id[W]) (f ∘ g) ≈ bimap id f ∘ bimap id g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

Lemma bimap_comp_id_right `{F : C ∏ D ⟶ E} {W}
      `(f : Y ~{C}~> Z) `(g : X ~{C}~> Y) :
  bimap (f ∘ g) (id[W]) ≈ bimap f id ∘ bimap g id.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

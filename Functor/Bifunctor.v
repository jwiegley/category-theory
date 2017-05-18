Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
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

Lemma bimap_id_id `{F : C ∏ D ⟶ E} {X Y} :
  bimap (id[X]) (id[Y]) ≈ id.
Proof.
  destruct F; simpl.
  apply fmap_id.
Qed.

Lemma bimap_comp `{F : C ∏ D ⟶ E} {X Y Z W U V}
      (f : Y ~{C}~> Z) (h : X ~{C}~> Y)
      (g : V ~{D}~> W) (i : U ~{D}~> V) :
  bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  reflexivity.
Qed.

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

Lemma bimap_id_right_left `{F : C ∏ D ⟶ E} {W}
      `(f : Z ~{C}~> W) `(g : X ~{D}~> Y) :
  bimap f id ∘ bimap id g ≈ bimap f g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

Lemma bimap_id_left_right `{F : C ∏ D ⟶ E} {W}
      `(f : Z ~{D}~> W) `(g : X ~{C}~> Y) :
  bimap id f ∘ bimap g id ≈ bimap g f.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

Global Program Instance bifunctor_respects {F : C ∏ D ⟶ E} :
  Proper ((fun p q => Isomorphism (fst p) (fst q) *
                      Isomorphism (snd p) (snd q))
            ==> Isomorphism) F.
Next Obligation.
  proper; simpl in *.
  isomorphism.
  - exact (bimap x0 y0).
  - exact (bimap (x0⁻¹) (y0⁻¹)).
  - rewrite <- bimap_comp.
    rewrite !iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite <- bimap_comp.
    rewrite !iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

Hint Rewrite @bimap_id_id : categories.

Ltac bimap_left :=
  apply bimap_respects; [reflexivity|].

Ltac bimap_right :=
  apply bimap_respects; [|reflexivity].

Ltac normal :=
  repeat
    match goal with
    | [ |- context [?F ∘ (?G ∘ ?H)] ] =>
      rewrite (comp_assoc F G H)

    | [ |- context [fmap[?F] ?G ∘ fmap[?F] _] ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G)

    | [ |- context [fmap[?F] id] ] =>
      rewrite <- (@fmap_id _ _ F)

    | [ |- context [bimap ?F _ ∘ bimap _ _] ] =>
      rewrite <- (bimap_comp F)
    | [ |- context [(?F ∘ bimap ?G _) ∘ bimap _ _] ] =>
      rewrite <- (comp_assoc F (bimap _ _));
      rewrite <- (bimap_comp G)

    | [ |- context [id ∘ ?F] ] => rewrite (id_left F)
    | [ |- context [?F ∘ id] ] => rewrite (id_right F)

    | [ |- context [bimap id id] ] =>
      rewrite bimap_id_id
    | [ |- context [bimap ?F id ∘ bimap id ?G] ] =>
      rewrite (bimap_id_right_left F)
    | [ |- context [bimap id ?F ∘ bimap ?G id] ] =>
      rewrite (bimap_id_left_right F G)

    | [ H : context [fmap[?F] ?G ∘ fmap[?F] _] |- _ ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G) in H
    | [ H : context [bimap ?F id ∘ bimap id ?G] |- _ ] =>
      rewrite (bimap_id_right_left F) in H
    | [ H : context [bimap id ?F ∘ bimap ?G id] |- _ ] =>
      rewrite (bimap_id_left_right F G) in H
    | [ H : context [bimap ?F _ ∘ bimap _ _] |- _ ] =>
      rewrite <- (bimap_comp F) in H
    | [ H : context [(?F ∘ bimap ?G _) ∘ bimap _ _] |- _ ] =>
      rewrite <- (comp_assoc F (bimap _ _)) in H;
      rewrite <- (bimap_comp G) in H
    | [ H : context [id ∘ ?F] |- _ ] => rewrite (id_left F) in H
    | [ H : context [?F ∘ id] |- _ ] => rewrite (id_right F) in H
    end.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance ProductFunctor
        `{C : Category} `{D : Category} `{F : C ⟶ D}
        `{J : Category} `{K : Category} `{G : J ⟶ K} :
  (C ∏ J) ⟶ (D ∏ K) := {
  fobj := fun x => (F (fst x), G (snd x));
  fmap := fun _ _ f => (fmap[F] (fst f), fmap[G] (snd f))
}.
Next Obligation.
  proper.
    rewrite a; reflexivity.
  rewrite b; reflexivity.
Qed.
Next Obligation.
  simplify; simpl in *; apply fmap_comp.
Qed.

Notation "F ∏⟶ G" := (@ProductFunctor _ _ F _ _ G) (at level 9).

Program Definition ProductFunctor_proj1
        `{C : Category} `{D : Category}
        `{J : Category} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) {A : J} : C ⟶ D.
Proof.
  destruct F; simpl in *.
  functor; intros.
  - apply (fst (fobj (X, A))).
  - apply (fmap (X, A) (Y, A) (f, id)).
  - proper; simpl in *.
    apply fmap_respects; split; cat.
  - apply fmap_id.
  - simpl.
    specialize (fmap_comp (X, A) (Y, A) (Z, A) (f, id) (g, id)).
    simpl in fmap_comp.
    destruct fmap_comp.
    rewrite <- e.
    rewrite id_left.
    reflexivity.
Defined.

Program Definition ProductFunctor_proj2
        `{C : Category} `{D : Category}
        `{J : Category} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) {A : C} : J ⟶ K.
Proof.
  destruct F; simpl in *.
  functor; intros.
  - apply (snd (fobj (A, X))).
  - apply (fmap (A, X) (A, Y) (id, f)).
  - proper; simpl in *.
    apply fmap_respects; split; cat.
  - apply fmap_id.
  - simpl.
    specialize (fmap_comp (A, X) (A, Y) (A, Z) (id, f) (id, g)).
    simpl in fmap_comp.
    destruct fmap_comp.
    rewrite <- e0.
    rewrite id_left.
    reflexivity.
Defined.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* ProductFunctor is a mapping between product categories. *)

Program Instance ProductFunctor
        {C : Category} {D : Category} {F : C ⟶ D}
        {J : Category} {K : Category} {G : J ⟶ K} :
  (C ∏ J) ⟶ (D ∏ K) := {
  fobj := fun x => (F (fst x), G (snd x));
  fmap := fun _ _ f => (fmap[F] (fst f), fmap[G] (snd f));
  fmap_respects := fun x y f g eqv =>
    (fmap_respects (fst x) (fst y) (fst f) (fst g) (fst eqv),
     fmap_respects (snd x) (snd y) (snd f) (snd g) (snd eqv));
  fmap_id := fun x =>
    (@fmap_id C D F (fst x), @fmap_id J K G (snd x));
  fmap_comp := fun x y z f g =>
    (@fmap_comp C D F (fst x) (fst y) (fst z) (fst f) (fst g),
     @fmap_comp J K G (snd x) (snd y) (snd z) (snd f) (snd g))
}.

Notation "F ∏⟶ G" := (@ProductFunctor _ _ F _ _ G) (at level 9).

Program Definition ProductFunctor_swap
        {C : Category} {D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : (J ∏ C) ⟶ (K ∏ D) := {|
  fobj := fun x => Swap (F (Swap x));
  fmap := fun _ _ f => _
|}.
Next Obligation.
  simpl in *.
  split; apply F; split; assumption.
Defined.
Next Obligation.
  proper; simpl; simplify; simpl in *.
    rewrite !let_snd.
    rewrites; reflexivity.
  rewrite !let_fst.
  rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite !let_fst, !let_snd; cat.
Qed.
Next Obligation.
  simpl in *.
  rewrite !let_fst, !let_snd; simplify;
  rewrite ?fst_comp, ?snd_comp;
  rewrite <- fmap_comp; reflexivity.
Qed.

(* If we have a monoidal structural for one of the categories, we can project
   out one or the other side of the [ProductFunctor]. *)

Program Definition ProductFunctor_fst
        {C : Category} {D : Category}
        {J : Category} `{@Monoidal J} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : C ⟶ D := {|
  fobj := fun x => fst (F (x, I));
  fmap := fun x y f => fst (@fmap _ _ F (x, I) (y, I) (f, id));
  fmap_respects := fun x y f g eqv =>
    fst (@fmap_respects _ _ F (x, I) (y, I) (f, id) (g, id)
                        (eqv, reflexivity _));
  fmap_id := fun x => fst (@fmap_id _ _ F (x, I));
  fmap_comp := fun x y z f g =>
    _ (fst (@fmap_comp _ _ F (x, I) (y, I) (z, I) (f, id) (g, id)))
|}.
Next Obligation.
  intros.
  rewrite fst_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.

Program Definition ProductFunctor_snd
        {C : Category} `{@Monoidal C} `{D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : J ⟶ K := {|
  fobj := fun x => snd (F (I, x));
  fmap := fun x y f => snd (@fmap _ _ F (I, x) (I, y) (id, f));
  fmap_respects := fun x y f g eqv =>
    snd (@fmap_respects _ _ F (I, x) (I, y) (id, f) (id, g)
                        (reflexivity _, eqv));
  fmap_id := fun x => snd (@fmap_id _ _ F (I, x));
  fmap_comp := fun x y z f g =>
    _ (snd (@fmap_comp _ _ F (I, x) (I, y) (I, z) (id, f) (id, g)))
|}.
Next Obligation.
  intros.
  rewrite snd_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.

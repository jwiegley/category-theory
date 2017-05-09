Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
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
        `{C : Category} `{D : Category}
        `{J : Category} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : (J ∏ C) ⟶ (K ∏ D) := {|
  fobj := fun x => Product_swap (F (Product_swap x));
  fmap := fun _ _ f => _
|}.
Next Obligation.
  simpl in *.
  split; apply F; split; assumption.
Defined.
Next Obligation.
  proper; simpl; simplify; simpl in *.
    rewrite !let_snd.
    rewrite a, b; reflexivity.
  rewrite !let_fst.
  rewrite a, b; reflexivity.
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

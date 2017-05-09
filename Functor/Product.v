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

Program Definition ProductFunctor_swap
        `{C : Category} `{D : Category}
        `{J : Category} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : (J ∏ C) ⟶ (K ∏ D) := {|
  fobj := fun x => Product_swap (F (Product_swap x));
  fmap := fun _ _ f => _
|}.
Next Obligation.
  simpl in *; split;
  apply F; split; assumption.
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
  rewrite bimap_fmap;
  rewrite bimap_comp;
  reflexivity.
Qed.

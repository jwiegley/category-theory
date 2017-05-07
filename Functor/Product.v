Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cartesian.
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
Next Obligation.
  simpl.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.

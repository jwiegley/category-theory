Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Structure.Monoidal.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Local Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal {C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => Compose (fst p) (snd p)
     ; fmap := fun F G N =>
         {| transform := fun x =>
              fst N (snd G x) ∘ fmap[fst F] (snd N x) |}
     |};
  I := Id
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- !comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- naturality.
  rewrite comp_assoc.
  normal.
  rewrite <- naturality.
  reflexivity.
Qed.
Next Obligation.
  proper; simpl in *.
  rewrite x0, y0.
  reflexivity.
Qed.
Next Obligation.
  rewrite !fmap_id; cat.
Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  apply compose_respects.
    reflexivity.
  rewrite <- !naturality.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.
Next Obligation. normal; rewrite !fmap_id; reflexivity. Qed.

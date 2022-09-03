Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Structure.Monoidal.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal {C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => fst p ◯ snd p
     ; fmap := fun F G N =>
         {| transform := fun x =>
              fst N (snd G x) ∘ fmap[fst F] (snd N x) |}
     |};
  I := Id
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (naturality[snd N]).
  rewrite fmap_comp.
  comp_left.
  apply naturality.
Qed.
Next Obligation.
  rewrite naturality.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply naturality_sym.
Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite !fmap_id; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  apply compose_respects.
    reflexivity.
  rewrite <- !naturality.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.
Next Obligation. normal; rewrite !fmap_id; reflexivity. Qed.

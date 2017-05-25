Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Cat is the category of all small categories:

    objects               Categories
    arrows                Functors
    arrow equivalence     Natural Isomorphisms
    identity              Identity Functor
    composition           Horizontal composition of Functors *)

Program Instance Cat : Category := {
  ob      := Category;
  hom     := @Functor;
  homset  := fun _ _ => {| equiv := fun F G => F ≅[Fun] G |};
  id      := @Id;
  compose := @Compose
}.
Next Obligation. equivalence; transitivity y; auto. Qed.
Next Obligation.
  proper.
  constructive.
  all:swap 2 4.
  - apply (transform[to X0] (y0 X2) ∘ fmap (transform[to X1] X2)).
  - apply (transform[from X0] (x0 X2) ∘ fmap (transform[from X1] X2)).
  - rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- !naturality.
    rewrite !fmap_comp.
    rewrite comp_assoc.
    reflexivity.
  - rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- !naturality.
    rewrite !fmap_comp.
    rewrite comp_assoc.
    reflexivity.
  - rewrite comp_assoc.
    rewrite (naturality[X0⁻¹]).
    rewrite <- !comp_assoc.
    rewrite <- !fmap_comp.
    rewrite (naturality[X1⁻¹]).
    reflexivity.
  - rewrite comp_assoc.
    rewrite (naturality[X0⁻¹]).
    rewrite <- !comp_assoc.
    rewrite <- !fmap_comp.
    rewrite (naturality[X1⁻¹]).
    reflexivity.
  - destruct X0 as [to0 from0 iso_to_from0 ?];
    destruct X1 as [to1 from1 iso_to_from1 ?]; simpl in *.
    rewrite <- naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (transform[to0] _)).
    rewrite iso_to_from0; cat.
    rewrite <- fmap_comp.
    rewrite iso_to_from1; cat.
  - destruct X0 as [to0 from0 ? iso_from_to0 ?];
    destruct X1 as [to1 from1 ? iso_from_to1 ?]; simpl in *.
    rewrite <- naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (transform[from0] _)).
    rewrite iso_from_to0; cat.
    rewrite <- fmap_comp.
    rewrite iso_from_to1; cat.
Qed.
Next Obligation. constructive; cat. Qed.
Next Obligation. constructive; cat. Qed.
Next Obligation. constructive; cat. Qed.
Next Obligation. constructive; cat. Qed.

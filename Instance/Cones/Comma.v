Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Construction.Comma.
Require Export Category.Functor.Diagonal.
Require Export Category.Instance.Cones.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Cones_to_Comma `(F : [J, C]) : Cones F ⟶ (Δ ↓ =(F)).
Proof.
  functor; simpl; intros.
  - exists (vertex_obj[X], ()).
    transform; simpl; intros.
    + apply vertex_map.
    + abstract (rewrite id_right; apply ump_cones).
    + abstract (rewrite id_right; symmetry; apply ump_cones).
  - exists (`1 f, ()); abstract (simpl; intros; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

Theorem Cones_from_Comma `(F : [J, C]) : (Δ ↓ =(F)) ⟶ Cones F.
Proof.
  functor; simpl; intros.
  - construct; simpl; intros.
    + exact (fst ``X).
    + exact (transform[`2 X] _).
    + abstract (rewrite (naturality[`2 X]); cat).
  - destruct f; simpl in *.
    exists (fst x0); abstract (intros; rewrite e; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

(* Wikipedia: "We can define the category of cones to F as the comma category
  (Δ ↓ F). Morphisms of cones are then just morphisms in this category. This
  equivalence is rooted in the observation that a natural map between constant
  functors Δ(N), Δ(M) corresponds to a morphism between N and M. In this
  sense, the diagonal functor acts trivially on arrows. In similar vein,
  writing down the definition of a natural map from a constant functor Δ(N) to
  F yields the same diagram as the above. As one might expect, a morphism from
  a cone (N, ψ) to a cone (L, φ) is just a morphism N → L such that all the
  "obvious" diagrams commute." *)

Theorem Cones_Comma `(F : [J, C]) : Cones F ≅[Cat] (Δ ↓ =(F)).
Proof.
  isomorphism; simpl; intros.
  - apply Cones_to_Comma.
  - apply Cones_from_Comma.
  - constructive.
    + exists (id, ()); abstract cat.
    + exists (id, ()); abstract cat.
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
  - constructive.
    + exists id; abstract (intros; cat).
    + exists id; abstract (intros; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
Qed.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Instance.Cones.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Wikipedia: "We can define the category of cones to F as the comma category
  (Δ ↓ F). Morphisms of cones are then just morphisms in this category. This
  equivalence is rooted in the observation that a natural map between constant
  functors Δ(N), Δ(M) corresponds to a morphism between N and M. In this
  sense, the diagonal functor acts trivially on arrows. In similar vein,
  writing down the definition of a natural map from a constant functor Δ(N) to
  F yields the same diagram as the above. As one might expect, a morphism from
  a cone (N, ψ) to a cone (L, φ) is just a morphism N → L such that all the
  "obvious" diagrams commute." *)

(* jww (2017-05-26): At the moment this proof exhausts Coq's memory, bug #5551 *)

(*
Theorem Cones_Comma `(F : J ⟶ C) :
  Cones F ≅[Cat] (Diagonal J ↓ @Const Fun F).
Proof.
  isomorphism; simpl; intros.
  - functor; simpl; intros.
    + exists (vertex, ()).
      transform; simpl; intros.
      * apply vertex_map.
      * abstract (rewrite id_right; apply ump_cones).
      * abstract (rewrite id_right; symmetry; apply ump_cones).
    + exists (`1 f, ()); simpl; intros; cat.
    + abstract proper.
    + abstract cat.
    + abstract cat.
  - functor; simpl; intros.
    + construct; simpl; intros.
      * exact (fst ``X).
      * exact (transform[`2 X] _).
      * abstract (rewrite (naturality[`2 X]); cat).
    + destruct f; simpl in *.
      exists (fst x); intros.
      rewrite e; cat.
    + abstract proper.
    + abstract cat.
    + abstract cat.
  - constructive; try exists (id, ()); abstract cat.
  - constructive; try exists id; intros; abstract cat.
Qed.
*)

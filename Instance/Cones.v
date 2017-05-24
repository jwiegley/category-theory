Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Constant.
Require Export Category.Construction.Comma.

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
  "obvious" diagrams commute (see the first diagram in the next section)." *)

Definition Cones `(F : J ⟶ C) (N : C) := (Constant J N ↓ F).

Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.

(*
Program Instance Cones_Terminal `(F : J ⟶ C) (N : C) :
  @Terminal (Cones F N) := {
  One := ((_, _); _)
}.
*)

Definition Cocones `{F : J ⟶ C} (N : C) := (F ↓ Constant J N).

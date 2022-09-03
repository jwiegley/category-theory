Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Export Category.Structure.Cone.

Generalizable All Variables.
Set Primitive Projections.
(* jww (2022-09-03): Anamoly in 8.12+ *)
(* Set Universe Polymorphism. *)
Unset Transparent Obligations.

(* A natural transformation Δd ⟹ F (where Δd is the Constant functor on d) is
   the same as a cone over F (whose vertex is d). *)

Theorem Cone_Transform `(F : J ⟶ C) (d : C) :
  Δ[J](d) ⟹ F ↔ { c : Cone F | vertex_obj = d }.
Proof.
  split; intros.
  - unshelve eexists.
    + unshelve econstructor; intros.
      * exact d.
      * apply X.
      * simpl.
        rewrite (naturality[X]); cat.
    + reflexivity.
  - transform; simpl; intros;
    destruct X; subst.
    + apply x0.
    + cat; apply ump_cones.
    + cat; symmetry; apply ump_cones.
Qed.

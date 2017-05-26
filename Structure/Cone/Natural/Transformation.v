Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Export Category.Structure.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A natural transformation Δd ⟹ F (where Δd is the Constant functor on d) is
   the same as a cone over F (whose vertex is d). *)

Theorem Cone_Transform {J : Category} {C : Category} (F : J ⟶ C) (d : C) :
  Diagonal J d ⟹ F <--> { c : Cone F | vertex = d }.
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
    + apply x.
    + cat; apply ump_cones.
    + cat; symmetry; apply ump_cones.
Qed.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

Class CartesianFunctor := {
  fobj_prod_iso {X Y : C} : F (X × Y) ≅ F X × F Y;

  prod_in  := fun X Y => from (@fobj_prod_iso X Y);
  prod_out := fun X Y => to   (@fobj_prod_iso X Y);

  fmap_exl {X Y : C} : fmap (@exl C _ X Y) ≈ exl ∘ prod_out _ _;
  fmap_exr {X Y : C} : fmap (@exr C _ X Y) ≈ exr ∘ prod_out _ _;
  fmap_fork {X Y Z : C} (f : X ~> Y) (g : X ~> Z) :
    fmap (f △ g) ≈ prod_in _ _ ∘ fmap f △ fmap g
}.

Arguments prod_in {_ _ _} /.
Arguments prod_out {_ _ _} /.

Context `{@CartesianFunctor}.

Corollary prod_in_out (X Y : C) :
  prod_in ∘ prod_out ≈ @id _ (F (X × Y)).
Proof.
  intros.
  exact (iso_from_to fobj_prod_iso).
Qed.

Hint Rewrite @prod_in_out : functors.

Corollary prod_out_in (X Y : C) :
  prod_out ∘ prod_in ≈ @id _ (F X × F Y).
Proof.
  intros.
  exact (iso_to_from fobj_prod_iso).
Qed.

Hint Rewrite @prod_out_in : functors.

Corollary prod_in_inj {X Y Z : C} (f g : F X ~> F X × F Y) :
  prod_in ∘ f ≈ prod_in ∘ g <--> f ≈ g.
Proof.
  split; intros Hprod.
    rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hprod.
  reflexivity.
Qed.

Corollary prod_out_inj {X Y Z : C} (f g : F X ~> F (Y × Z)) :
  prod_out ∘ f ≈ prod_out ∘ g <--> f ≈ g.
Proof.
  split; intros Hprod.
    rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hprod.
  reflexivity.
Qed.

End CartesianFunctor.

Arguments prod_in {_ _ _ _ _ _ _ _} /.
Arguments prod_out {_ _ _ _ _ _ _ _} /.

Hint Rewrite @prod_in_out : functors.
Hint Rewrite @prod_out_in : functors.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cocartesian.

Notation "'CocartesianFunctor' F" := (@CartesianFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@CocartesianFunctor C D F" :=
  (@CartesianFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.

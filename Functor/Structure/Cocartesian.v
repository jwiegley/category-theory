Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CocartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cocartesian C}.
Context `{@Cocartesian D}.

Class CocartesianFunctor := {
  fobj_coprod_iso {X Y : C} : F (X + Y) ≅ F X + F Y;

  coprod_in  := fun X Y => from (@fobj_coprod_iso X Y);
  coprod_out := fun X Y => to   (@fobj_coprod_iso X Y);

  fmap_inl {X Y : C} : fmap (@inl C _ X Y) ≈ coprod_in _ _ ∘ inl;
  fmap_inr {X Y : C} : fmap (@inr C _ X Y) ≈ coprod_in _ _ ∘ inr;
  fmap_merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∘ coprod_out _ _
}.

Arguments coprod_in {_ _ _} /.
Arguments coprod_out {_ _ _} /.

Context `{@CocartesianFunctor}.

Corollary coprod_in_out {X Y : C} :
  coprod_in ∘ coprod_out ≈ @id _ (F (X + Y)).
Proof. apply iso_from_to. Qed.

Hint Rewrite @coprod_in_out : functors.

Corollary coprod_out_in {X Y : C} :
  coprod_out ∘ coprod_in ≈ @id _ (F X + F Y).
Proof. apply iso_to_from. Qed.

Hint Rewrite @coprod_out_in : functors.

Corollary coprod_in_surj {X Y Z : C} (f g : F (X + Y) ~> F X) :
  f ∘ coprod_in ≈ g ∘ coprod_in <--> f ≈ g.
Proof.
  split; intros Hcoprod.
    rewrite <- id_right.
    rewrite <- coprod_in_out.
    rewrite comp_assoc.
    rewrite Hcoprod.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hcoprod.
  reflexivity.
Qed.

Corollary coprod_out_inj {X Y Z : C} (f g : F Y + F Z ~> F X) :
  f ∘ coprod_out ≈ g ∘ coprod_out <--> f ≈ g.
Proof.
  split; intros Hcoprod.
    rewrite <- id_right.
    rewrite <- coprod_out_in.
    rewrite comp_assoc.
    rewrite Hcoprod.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hcoprod.
  reflexivity.
Qed.

End CocartesianFunctor.

Arguments coprod_in {_ _ _ _ _ _ _ _} /.
Arguments coprod_out {_ _ _ _ _ _ _ _} /.

Hint Rewrite @coprod_in_out : functors.
Hint Rewrite @coprod_out_in : functors.

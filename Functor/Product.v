Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A product of functors over some object in a monoidal category. *)

#[global] Program Instance Product
        {C : Category} {D : Category} `{@Monoidal D}
        {F : C ⟶ D} {G : C ⟶ D} : C ⟶ D := {
  fobj := fun x => (F x ⨂ G x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f
}.
Next Obligation.
  proper;
  apply bimap_respects;
  now apply fmap_respects.
Qed.
Next Obligation. normal; reflexivity. Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A product of functors over some object in a monoidal category. *)

Program Definition Product
        `{C : Category} `{D : Category} `{@Monoidal D}
        `{F : C ⟶ D} `{G : C ⟶ D} : C ⟶ D := {|
  fobj := fun x => F x ⨂ G x;
  fmap := fun _ _ f => bimap (fmap[F] f) (fmap[G] f)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  unfold split.
  rewrite !fmap_id.
  rewrite bimap_id_id.
  reflexivity.
Qed.
Next Obligation.
  unfold split.
  rewrite <- bimap_comp.
  rewrite <- !fmap_comp.
  reflexivity.
Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.

(* This is a special case of the monoidal Product above, but that does not
   require a terminal object since we never use monoidal unit. *)

Require Import Category.Structure.Cartesian.

Program Definition CartesianProduct `{C : Category} `{D : Category}
        `{@Cartesian D} (F : C ⟶ D) (G : C ⟶ D) : C ⟶ D := {|
  fobj := fun x => Prod (F x) (G x);
  fmap := fun _ _ f => (fmap f ∘ exl) △ (fmap f ∘ exr)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite exl_fork, exr_fork.
  rewrite !comp_assoc.
  rewrite !fmap_comp.
  reflexivity.
Qed.

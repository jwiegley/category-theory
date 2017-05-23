Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Import Category.Functor.Product.Internal.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Symmetric.
Require Export Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Local Obligation Tactic :=
  unfold proj_left, proj_right; simpl;
  cat_simpl; try split; intros; unfork; cat.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition InternalProduct_Monoidal
        {C : Category} `{@Cartesian C} `{@Terminal C} : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := One
|}.

Program Definition InternalProduct_SymmetricMonoidal
        {C : Category} `{@Cartesian C} `{@Terminal C} :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  twist := fun X Y =>
    {| to   := @swap C _ X Y
     ; from := @swap C _ Y X
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.

Program Definition InternalProduct_CartesianMonoidal
        {C : Category} `{@Cartesian C} `{@Terminal C} :
  @CartesianMonoidal C InternalProduct_Monoidal := {|
  is_semicartesian := {| eliminate := fun _ => one |};
  is_relevance := {| diagonal  := fun _ => id △ id |}
|}.
Next Obligation.
  apply InternalProduct_SymmetricMonoidal.
Defined.
Next Obligation.
  apply fork_respects.
    apply one_unique.
  reflexivity.
Qed.

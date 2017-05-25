Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* jww (2017-05-24): TODO
Definition Opposite_Adjunction `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  U^op ⊣ F^op :=
  @Build_Adjunction (C^op) (D^op) (F^op) (U^op)
    {| transform  := counit
     ; naturality := fun X Y f => @naturality C C _ _ counit Y X f |}
    {| transform := unit
     ; naturality := fun X Y f => @naturality D D _ _ unit Y X f |}
    (* (@counit C D F U A) *)
    (* ((@unit C D F U A)^op) *)
    (@fmap_counit_unit C D F U A)
    (@counit_fmap_unit C D F U A).
*)

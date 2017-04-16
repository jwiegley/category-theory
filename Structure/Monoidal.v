Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Monoidal.

Context `{C : Category}.

(* jww (2017-04-15): Need to define products of categories *)
(*
Class Monoidal := {
  tensor : C × C ⟶ C
}.
*)

End Monoidal.

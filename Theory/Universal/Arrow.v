Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(* A universal arrow. *)

Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.

Class Arrow (x : C) (U : D ⟶ C) := {
  arr_initial : @Initial (Const x ↓ U);
  arr_obj := snd (`1 (@Zero _ arr_initial));

  arr : x ~> U arr_obj;

  ump_arrows {y : D} (h : x ~> U y) :
    ∃ g : arr_obj ~> y, fmap[U] g ∘ arr ≈ h
}.

End UniversalArrow.

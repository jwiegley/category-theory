Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Cartesian.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The category of propositions. *)

Program Definition Props : Category := {|
  obj     := Prop;
  hom     := Basics.impl;
  (* By proof irrelevance, two statement P -> Q of the same type are taken to
     always be the same implication. *)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
|}.

#[global]
Program Instance Props_Terminal : @Terminal Props := {
  terminal_obj := True;
  one := fun _ _ => I
}.

#[global]
Program Instance Props_Initial : @Initial Props := {
  terminal_obj := False;
  one := fun _ _ => False_rect _ _
}.

#[global]
Program Instance Props_Cartesian : @Cartesian Props := {
  product_obj := and;
  fork := fun _ _ _ f g x => conj (f x) (g x);
  exl  := fun _ _ p => proj1 p;
  exr  := fun _ _ p => proj2 p
}.

#[global]
Program Instance Props_Cocartesian : @Cocartesian Props := {
  product_obj := or;
  fork := fun _ _ _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;
  exr  := fun _ _ p => or_intror p
}.

#[global]
Program Instance Props_Closed : @Closed Props _ := {
  exponent_obj := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.

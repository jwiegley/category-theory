Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The category of propositions. *)

Program Definition Props : Category := {|
  ob      := Prop;
  hom     := Basics.impl;
  (* By proof irrelevance, two statement P -> Q of the same type are taken to
     always be the same implication. *)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
|}.

Program Instance Props_Terminal : @Terminal Props := {
  One := True;
  one := fun _ _ => I
}.

Program Instance Props_Initial : @Initial Props := {
  One := False;
  one := fun _ _ => False_rect _ _
}.

Program Instance Props_Cartesian : @Cartesian Props := {
  Prod := and;
  fork := fun _ _ _ f g x => conj (f x) (g x);
  exl  := fun _ _ p => proj1 p;
  exr  := fun _ _ p => proj2 p
}.

Program Instance Props_Cocartesian : @Cocartesian Props := {
  Prod := or;
  fork := fun _ _ _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;
  exr  := fun _ _ p => or_intror p
}.

Program Instance Props_Closed : @Closed Props _ := {
  Exp := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.

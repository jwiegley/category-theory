Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* The category of propositions. *)

Program Definition Props : Category := {|
  obj     := Prop;
  hom     := Basics.impl;
  (* By proof irrelevance, two statement P → Q of the same type are taken to
     always be the same implication. *)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
|}.

#[export]
Program Instance Props_Terminal : @Terminal Props := {
  terminal_obj := True;
  one := fun _ _ => I
}.

#[export]
Program Instance Props_Initial : @Initial Props := {
  terminal_obj := False;
  one := fun _ _ => False_rect _ _
}.

#[export]
Program Instance Props_Cartesian : @Cartesian Props := {
  product_obj := and;
  isCartesianProduct _ _ := {|
    fork := fun _ f g x => conj (f x) (g x);
    exl  := fun p => proj1 p;
    exr  := fun p => proj2 p
  |}
}.

#[export]
Program Instance Props_Cocartesian : @Cocartesian Props := {
  product_obj := or;
  isCartesianProduct _ _ := {|
  fork := fun _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun p => or_introl p;
  exr  := fun p => or_intror p
  |}
}.

#[export]
Program Instance Props_Closed : @Closed Props _ := {
  exponent_obj := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.

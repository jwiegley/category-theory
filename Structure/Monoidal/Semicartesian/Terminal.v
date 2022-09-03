Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Terminal.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SemicartesianMonoidalTerminal.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

#[global] Program Definition SemicartesianMonoidal_Terminal : @Terminal C := {|
  terminal_obj := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

End SemicartesianMonoidalTerminal.

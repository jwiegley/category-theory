Require Import Category.Lib.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

Section SemicartesianMonoidalTerminal.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

Program Definition SemicartesianMonoidal_Terminal : @Terminal C := {|
  terminal_obj := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

End SemicartesianMonoidalTerminal.

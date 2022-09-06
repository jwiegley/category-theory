Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.

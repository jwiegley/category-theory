Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Instance.Parallel.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.

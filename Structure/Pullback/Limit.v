Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Span.

Definition Pullback_Limit {C : Category} (F : Cospan C) := Limit F.
Arguments Pullback_Limit {_%category} F%functor /.

Definition Pushout_Limit {C : Category} (F : Span C) := Colimit F.
Arguments Pushout_Limit {_%category} F%functor /.

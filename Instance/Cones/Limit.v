Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Instance.Cones.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Limit_Cones `(F : J ⟶ C) `{T : @Terminal (Cones F)} :
  Limit F := {|
  Lim := @One _ T;
  limit_terminal := fun N => `1 @one _ T N;
  ump_limits     := fun N => `2 @one _ T N
|}.
Next Obligation.
  refine (@one_unique _ T N (@one _ T N) (f; _)); intros.
Admitted.

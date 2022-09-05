Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Cones.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A limit is a terminal object in the category of cones. *)
Program Definition Limit_Cones `(F : J ⟶ C) `{T : @Terminal (Cones F)} :
  Limit F := {|
  limit_cone := @terminal_obj _ T;
  ump_limits := fun N =>
    {| unique_obj := `1 @one _ T N
     ; unique_property := `2 @one _ T N
     ; uniqueness       := fun v H => @one_unique _ T N (@one _ T N) (v; H) |}
|}.

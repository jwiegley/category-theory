Require Import Category.Lib.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Sets.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.
Unset Transparent Obligations.

Section BiCCC.

Definition π1 {C D : Category} : C × D -> C := exl.
Definition π2 {C D : Category} : C × D -> D := exr.

(* This is just a product object in Cat. *)
Program Instance Product `{C : Category} `{D : Category} : Category := {
  ob      := C × D;
  hom     := fun A B =>
               @Prod Sets _ {| carrier := π1 A ~{C}~> π1 B |}
                            {| carrier := π2 A ~{D}~> π2 B |};
  homset  := fun X Y : C × D =>
               {| equiv := fun f g =>
                    equiv (π1 X) (π1 Y) //\\ equiv (π2 X) (π2 Y) |};
  id      := fun A => split id id;
  compose := fun X Y Z f g =>
               tt
}.
}.

Program Instance Diag `{C : Category} : C ⟶ (C × C) := {
  fobj := fun A => A × A;
  fmap := fun _ _ f => f × f
}.
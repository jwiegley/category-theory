Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Semigroupoid := {
  semi_obj : Type;

  semi_uhom := Type : Type;
  semi_hom : semi_obj -> semi_obj -> semi_uhom;
  semi_homset :> ∀ X Y, Setoid (semi_hom X Y);

  semi_compose {x y z} (f: semi_hom y z) (g : semi_hom x y) : semi_hom x z;

  semi_compose_respects x y z :>
    Proper (equiv ==> equiv ==> equiv) (@semi_compose x y z);

  semi_dom {x y} (f: semi_hom x y) := x;
  semi_cod {x y} (f: semi_hom x y) := y;

  semi_comp_assoc {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose f (semi_compose g h) ≈ semi_compose (semi_compose f g) h;
  semi_comp_assoc_sym {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose (semi_compose f g) h ≈ semi_compose f (semi_compose g h)
}.

Definition to_Semigroupoid (C : Category) : Semigroupoid := {|
  semi_obj              := obj;
  semi_hom              := hom;
  semi_homset           := homset;
  semi_compose          := @compose C;
  semi_compose_respects := compose_respects;
  semi_comp_assoc       := @comp_assoc C;
  semi_comp_assoc_sym   := @comp_assoc_sym C;
|}.

Coercion to_Semigroupoid : Category >-> Semigroupoid.

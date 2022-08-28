Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Import EqNotations.

(* A discrete category has no arrows except for identity morphisms. *)

Inductive DiscHom {C : Category} (x : C) : C → Type :=
  | DiscId : DiscHom x x.

Derive Signature NoConfusion Subterm for DiscHom.

Program Instance DiscHom_EqDec {C : Category} {x y : C} : EqDec (DiscHom x y).
Next Obligation.
  destruct x0.
  - dependent destruction y0.
    now left.
Defined.

Program Definition Discrete (C : Category) : Category := {|
  obj := C;
  hom := DiscHom;
  homset := λ _ _, {| equiv := λ f g, f = g |};
  id := DiscId;
  compose := λ x y z, _;
|}.
Next Obligation. now destruct f. Defined.
Next Obligation. now destruct f. Qed.
Next Obligation. now destruct f, g. Qed.
Next Obligation. now destruct f, g. Qed.

Notation "C '₀'" := (Discrete C) (at level 0).

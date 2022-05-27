Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Structure.BiCCC.
Require Export Category.Instance.Coq.
Require Export Category.Instance.AST.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Repr (A : Type) := {
  repr : Obj;
  convert : A -> (1 ~> repr)
}.

Arguments Repr A : clear implicits.
Arguments repr A {_}.

#[global]
Program Instance prod_Repr
        `{HA : @Repr A}
        `{HB : @Repr B} :
  Repr (@Datatypes.prod A B) := {
  repr := Prod_ (@repr A HA) (@repr B HB);
  convert := fun p => convert (fst p) △ convert (snd p)
}.

#[global]
Program Instance unit_Repr : Repr (unit : Type) := {
  repr := One_;
  convert := fun _ => one
}.

#[global]
Program Instance false_Repr : Repr False := {
  repr := Zero_;
  convert := fun _ => False_rect _ _
}.

#[global]
Program Instance bool_Repr : Repr bool := {
  repr := Coprod_ One_ One_;
  convert := fun b => if b then inl else inr
}.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Instance.Coq.
Require Import Category.Instance.AST.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Repr (A : Type) := {
  repr : Obj;
  convert : A → (1 ~> repr)
}.

Arguments Repr A : clear implicits.
Arguments repr A {_}.

#[export]
Program Instance prod_Repr
        `{HA : @Repr A}
        `{HB : @Repr B} :
  Repr (@Datatypes.prod A B) := {
  repr := Prod_ (@repr A HA) (@repr B HB);
  convert := fun p => convert (fst p) △ convert (snd p)
}.

#[export]
Program Instance unit_Repr : Repr (unit : Type) := {
  repr := One_;
  convert := fun _ => one
}.

#[export]
Program Instance false_Repr : Repr False := {
  repr := Zero_;
  convert := fun _ => False_rect _ _
}.

#[export]
Program Instance bool_Repr : Repr bool := {
  repr := Coprod_ One_ One_;
  convert := fun b => if b then inl else inr
}.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.AST.

Generalizable All Variables.
Set Transparent Obligations.

(** * Representing Coq data types in the free bicartesian closed category *)

(* nLab: https://ncatlab.org/nlab/show/global+element
   Wikipedia: https://en.wikipedia.org/wiki/Global_element

   A [Repr A] equips a Coq type [A] with an object [repr : Obj] of the free
   bicartesian closed category [AST] and a [convert] map sending each value of
   [A] to a *global element* (point) of [repr] — a morphism [1 ~> repr] out of
   the terminal object. In [Set] a morphism [1 ~> x] is exactly a choice of one
   element of [x], so [convert] realises each inhabitant of [A] as the
   categorical point picking it out.

   The instances below follow the type formers: a [prod] is represented by a
   product object, with [convert] pairing the two component points ([△]); [unit]
   by the terminal object [1], whose unique point is [one]; [False] by the
   initial object [0], where [convert] is vacuous (there are no values, so the
   degenerate point [1 ~> 0] is never produced); and [bool] by the coproduct
   [1 + 1], whose two canonical points [inl]/[inr] name [true]/[false]. *)
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

Require Import Lib.
Require Export BiCCC.
Require Export Constant.

Generalizable All Variables.

Definition arrow (A B : Type) := A -> B.

Global Program Instance Coq_Category : Category Type := {
  hom     := arrow;
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x);
  eqv     := fun _ _ => eq
}.

Global Program Instance Coq_Terminal : Terminal Type := {
  terminal_category := Coq_Category;
  One := unit : Type;
  one := fun _ a => tt
}.
Obligation 1.
  extensionality x.
  destruct (f x), (g x).
  reflexivity.
Qed.

Global Program Instance Coq_Cartesian : Cartesian Type := {
  cartesian_terminal := Coq_Terminal;
  Prod := prod;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Global Program Instance Coq_Closed : Closed Type := {
  closed_cartesian := Coq_Cartesian;
  Exp := arrow;
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.
Obligation 2.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.
Obligation 3.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Global Program Instance Coq_Initial : Initial Type := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.
Obligation 2.
  extensionality x.
  contradiction.
Qed.

Global Program Instance Coq_Cocartesian : Cocartesian Type := {
  Coprod := sum;
  merge := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  inl  := fun _ _ p => Datatypes.inl p;
  inr  := fun _ _ p => Datatypes.inr p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  destruct x; auto.
Qed.

Global Program Instance Coq_Bicartesian : Bicartesian Coq_Cartesian.

Global Program Instance Coq_BiCCC : BiCCC Coq_Closed.

Global Program Instance Coq_Constant : Constant Type := {
  Const := fun A => A;
  constant := fun _ => Basics.const
}.

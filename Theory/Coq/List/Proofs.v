Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.List.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Program Definition list_Functor : IsFunctor list_Functor := {|
  a_fmap := list_Functor;
|}.
Next Obligation.
  proper.
  induction x1; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.

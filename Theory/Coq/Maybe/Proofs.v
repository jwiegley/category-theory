Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Maybe.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Program Definition Maybe_Functor : IsFunctor Maybe_Functor := {|
  a_fmap := Maybe_Functor;
|}.
Next Obligation.
  proper.
  destruct x1; simpl; auto.
  now rewrite H.
Qed.
Next Obligation.
  now destruct x0.
Qed.
Next Obligation.
  now destruct x0.
Qed.

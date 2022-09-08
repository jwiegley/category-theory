Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Either.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Program Definition Either_Functor {E} : IsFunctor (@Either_Functor E) := {|
  a_fmap := @Either_Functor E;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.

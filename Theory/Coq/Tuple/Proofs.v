Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Tuple.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Program Definition Tuple_Functor {x} : IsFunctor (Tuple_Functor x) := {|
  a_fmap := Tuple_Functor x;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.

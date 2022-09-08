Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

Class Traversable `{Functor T} :=
  sequence : ∀ `{Applicative F} x, T (F x) → F (T x).

Arguments Traversable T {_}.
Arguments sequence {T _ _ F _ _ x} _.

(* Tupersable is a specialization of Traversable that applies only to tuples,
   and thus does not require that tuples be Applicative. *)

Class Tupersable {x} `{Functor T} := {
  sequenceT {y} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable x T {_}.
Arguments sequenceT {x T _ _ y} a _.

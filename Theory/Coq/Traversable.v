Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

Class Traversable@{d c} {T : Type@{d} → Type@{c}} `{Functor T} :=
  sequence : ∀ `{Applicative@{d c} F} {x : Type@{d}}, T (F x) → F (T x).

Arguments Traversable T {_}.

(* Tupersable is a specialization of Traversable that applies only to tuples,
   and thus does not require that tuples be Applicative. *)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} `{Functor T} := {
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable x T {_}.

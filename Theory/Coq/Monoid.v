Require Import Category.Lib.
Require Import Category.Theory.Coq.Semigroup.

Generalizable All Variables.

Class Monoid `{Semigroup m} := {
  mempty : m;
}.

Arguments Monoid m {_}.

Require Import Category.Lib.

Generalizable All Variables.

Class Semigroup (m : Type) := {
  mappend : m -> m -> m
}.

Arguments mappend {m _ } _ _.

Infix "⊗" := mappend (at level 40).

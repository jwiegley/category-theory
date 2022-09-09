Require Import Category.Lib.

Generalizable All Variables.

Class Foldable@{d c} {F : Type@{d} → Type@{c}} :=
  foldr : ∀ {x y : Type@{d}}, (x -> y -> y) -> y -> F x -> y.

Arguments Foldable : clear implicits.

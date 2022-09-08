Require Import Category.Lib.

Generalizable All Variables.

Class Foldable (F : Type -> Type) :=
  foldr : ∀ x y, (x -> y -> y) -> y -> F x -> y.

Arguments foldr {F _ x y} _ _ _.

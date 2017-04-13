Require Import Lib.
Require Export Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Class Constant `(T : Terminal ob) := {
  Const : ob -> Type;
  constant {A} (x : Const A) : One ~{T}~> A
}.

Arguments Constant ob {_}.

Definition constant_terminal `(_ : @Constant C T) : Terminal C := T.

Coercion constant_terminal : Constant >-> Terminal.

Class ConstantFunctor `(_ : Constant C) `(Dcat : Constant D) := {
  constant_closed_functor :> Functor C D;

  unmap_one : fobj One ~{Dcat}~> One;

  map_const {A} (x : @Const C _ _ A) : @Const D _ _ (fobj A);

  fmap_constant {A : C} (x : Const A) :
    fmap (constant x) ≈ constant (map_const x) ∘ unmap_one;
}.

Arguments ConstantFunctor C {_ _} D {_ _}.

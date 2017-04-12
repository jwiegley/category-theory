Require Import Lib.
Require Export Terminal.

Generalizable All Variables.

Class Constant `(_ : Terminal ob) := {
  Const : ob -> Type;
  constant {A} (x : Const A) : One ~{ob}~> A
}.

Arguments Constant ob {_}.

Class ConstantFunctor `(_ : Constant C) `(_ : Constant D) := {
  constant_closed_functor :> Functor C D;

  unmap_one : fobj One ~{D}~> One;

  map_const {A} (x : @Const C _ _ A) : @Const D _ _ (fobj A);

  fmap_constant {A : C} (x : Const A) :
    fmap (constant x) ≈ constant (map_const x) ∘ unmap_one;
}.

Arguments ConstantFunctor C {_ _} D {_ _}.

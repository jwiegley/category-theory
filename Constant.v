Require Import Lib.
Require Export Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Constant.

Context `{C : Category}.
Context `{@Terminal C}.

Class Constant := {
  Const : ob -> Type;
  constant {A} (x : Const A) : One ~{C}~> A
}.

End Constant.

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT}.
Context `{@Constant D DT}.

Class ConstantFunctor := {
  unmap_one : F One ~{D}~> One;

  map_const {A} (x : @Const C _ _ A) : @Const D _ _ (F A);

  fmap_constant {A : C} (x : Const A) :
    fmap (constant x) ≈ constant (map_const x) ∘ unmap_one;
}.

End ConstantFunctor.

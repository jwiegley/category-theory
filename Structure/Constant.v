Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Constant.

Context `{C : Category}.
Context `{@Terminal C}.

Class Constant (A : Type) := {
  Const : ob;
  constant (x : A) : One ~{C}~> Const
}.

End Constant.

Arguments Const {_ _} A {_}.

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT T}.
Context `{@Constant D DT T}.

Class ConstantFunctor := {
  unmap_one : F One ~{D}~> One;

  map_const {x : T} : Const T ~> F (Const T);

  fmap_constant (x : T) :
    fmap (constant x) ≈ @map_const x ∘ constant x ∘ unmap_one;
}.

End ConstantFunctor.

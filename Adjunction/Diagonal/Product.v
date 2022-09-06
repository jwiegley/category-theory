Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Product.Internal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(* The diagonal functor on C is left adjoint to the internal product functor
   on C. *)
(* jww (2021-08-04): Is it right to use Diagonal_Product here? *)

#[global]
Program Instance Diagonal_Product_Adjunction (C : Category) `{@Cartesian C} :
  Diagonal_Product C ⊣ ×(C) := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => fst f △ snd f |}
     ; from := {| morphism := fun f => (exl ∘ f, exr ∘ f) |} |}
}.
Next Obligation. proper; apply fork_respects; auto. Qed.
Next Obligation. rewrite fork_comp; cat. Qed.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.
Next Obligation. split; unfork. Qed.

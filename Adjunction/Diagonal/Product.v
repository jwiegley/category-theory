Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Functor.Diagonal.
Require Export Category.Functor.Product.Internal.
Require Export Category.Structure.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(* The diagonal functor on C is left adjoint to the internal product functor
   on C. *)
(* jww (2021-08-04): Is it right to use Diagonal_Product here? *)

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

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Product.Internal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* The diagonal functor on C is left adjoint to the internal product functor
   on C. *)
(* jww (2021-08-04): Is it right to use Diagonal_Product here? *)


#[export]
Program Instance Diagonal_Product_Adjunction (C : Category) `{@Cartesian C} :
  Diagonal_Product C ⊣ ×(C) := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => fst f △ snd f |}
     ; from := {| morphism := fun f => (exl ∘ f, exr ∘ f) |} |}
  }.
(* #[local] Set Transparent Obligations. *)
Next Obligation. typeclasses eauto. Defined.
Next Obligation. 
  revert H o o0 o1; intros C_isCartesian x y z. 
  intros [f1 f2] [g1 g2] [eq1 eq2]; simpl in *.
  rewrite eq1, eq2.
  reflexivity. Qed.
Next Obligation.
  symmetry. 
  rewrite ump_products; split;  reflexivity. Qed.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.
Next Obligation. split; unfork. Qed.

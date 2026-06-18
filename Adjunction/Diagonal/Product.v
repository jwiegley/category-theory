Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Product.Internal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The diagonal–product adjunction Δ ⊣ × *)

(* nLab: https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   In a cartesian category C the binary product functor ×(C) : C ∏ C ⟶ C is
   right adjoint to the binary diagonal Δ = Diagonal_Product C : C ⟶ C ∏ C
   (so that, dually, the coproduct is left adjoint to Δ): nLab records that
   "C is J-cocomplete (J-complete) iff Δ has a left (right) adjoint", and the
   two-object discrete case is exactly the binary product/coproduct. The
   adjunction is presented here in hom-set form, as the family of bijections

       (Δ x ~{C ∏ C}~> p)  ≅  (x ~{C}~> ×(C) p)

   natural in x : C and p : C ∏ C. Spelling out the left side: a morphism
   Δ x ~> p is a pair (f, g) with f : x ~> fst p and g : x ~> snd p, while the
   right side is a single arrow x ~> fst p × snd p. The forward transpose
   [to] pairs the components, (f, g) ↦ f △ g, and the inverse [from] splits an
   arrow by postcomposing with the projections, h ↦ (exl ∘ h, exr ∘ h). That
   these are mutually inverse and natural is precisely the universal property
   of the product (the [fork]/projection laws of Structure/Cartesian.v), which
   is why the obligations below discharge by [unfork] and [fork_comp]. *)

#[export]
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

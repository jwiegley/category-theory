Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal product as a bifunctor ×(C) : C ∏ C ⟶ C. *)

(* nLab: https://ncatlab.org/nlab/show/product
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   In a cartesian category C, the binary product is functorial: it assembles
   into a bifunctor ×(C) : C ∏ C ⟶ C from the product category C ∏ C (the
   "product of categories", Construction/Product.v) back into C. This is the
   product *bifunctor*, distinct from a product *of two functors*.

   On objects it sends a pair (x, y) to the product object x × y. On a
   morphism (f, g) : (x, y) ~> (x', y') of C ∏ C — that is, a pair of a
   morphism f : x ~> x' and a morphism g : y ~> y' in C — it yields the
   "cartesian product of morphisms" f × g : x × y ~> x' × y', the unique arrow
   characterized by exl ∘ (f × g) ≈ f ∘ exl and exr ∘ (f × g) ≈ g ∘ exr. By
   the universal property of the product this is the pairing

       (f ∘ exl) △ (g ∘ exr) : x × y ~> x' × y',

   which is exactly the [split] combinator of Structure/Cartesian.v applied to
   the two components. The functor laws hold because pairing is determined by
   the projections: ×(C) preserves id since exl △ exr ≈ id, and preserves
   composition by [fork_comp] together with associativity. *)

#[export]
Program Instance InternalProductFunctor `(C : Category) `{@Cartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p × snd p;
  fmap := fun _ _ p => (fst p ∘ exl) △ (snd p ∘ exr)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.

Notation "×( C )" := (@InternalProductFunctor C _)
  (at level 0, format "×( C )") : functor_scope.

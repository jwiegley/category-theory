Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/distributive+category
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

   A (finitary) distributive category is a category with finite products and
   finite coproducts in which products distribute over coproducts. Concretely,
   for all objects the canonical morphism

       x × y + x × z ~> x × (y + z),

   induced by the coproduct injections via x × inl and x × inr, is an
   isomorphism (the binary distributivity law), and likewise the canonical
   morphism

       0 ~> x × 0

   into the nullary product is an isomorphism (the nullary law, equivalently
   x × 0 ≅ 0). Together these say that the functor x × - preserves finite
   coproducts. The two sources state the canonical map in the direction
   x × y + x × z ~> x × (y + z); since we record an [Isomorphism] rather than a
   directed map, the orientation chosen below is immaterial.

   The nullary law does not follow from binary distributivity in general (it
   must be assumed), and one of its consequences is that the initial object of
   a distributive category is strict. Every bicartesian closed category is
   distributive, because x × - then has a right adjoint and so preserves all
   colimits (see [Structure.BiCCC]). *)

Section Distributive.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Initial C}.

Class Distributive := {
  (* Binary distributivity: x × - preserves binary coproducts. *)
  distr_prod_coprod {x y z} : @Isomorphism C (x × (y + z)) (x × y + x × z);
  (* Nullary law: x × - preserves the initial (nullary coproduct) object. *)
  distr_zero {x} : x × 0 ≅ 0
}.

End Distributive.

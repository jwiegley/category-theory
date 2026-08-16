Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Cocartesian.

Generalizable All Variables.

(** * The exponential laws at Cat: isomorphisms of functor categories *)

(* nLab: https://ncatlab.org/nlab/show/Cat
   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category

   [Cat] is cartesian (Instance/Cat/Cartesian.v, with
   [product_obj := @Product], the product of categories [C ∏ D]), cocartesian
   (Instance/Cat/Cocartesian.v, [product_obj := @Coproduct], read in the
   opposite category, so the coproduct object is [C ∐ D]) and closed
   (Instance/Cat/Cartesian/Closed.v, [exponent_obj := @Fun], so the internal
   hom is the functor category [C, D]).

   Instantiating the four exponential laws there therefore turns them into
   isomorphisms OF FUNCTOR CATEGORIES, and the curried law is the currying of
   [Cat_Closed] internalized: [C ∏ D, E] ≅ [C, [D, E]] says that a functor of
   two variables is a functor into a functor category, which is exactly the
   content of the transposition [exp_iso] that [Cat_Closed] supplies.

   Each of the four statements below is TYPED as an isomorphism between
   explicitly spelled functor categories and INHABITED by the generic
   instance, so the two readings are checked to agree by conversion: nothing
   here is asserted in prose.  The four natural upgrades of
   Structure/Cartesian/Closed/Natural.v are instantiated at [Cat] as well.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.5
   Exercise 2 (printed p. 44) is the source of the four laws; this file
   answers work item 3 of jwiegley/category-theory#284, which asks what they
   say at [Cat].  It lives under Instance/ rather than beside the general
   development because Structure/ files must not depend on Instance/. *)

Section CatExponential.

(** ** The four laws, read as isomorphisms of functor categories *)

(* Currying: a functor out of a product category is a functor into a functor
   category. *)
Example Cat_exp_prod_l (C D E : Cat) :
  @Isomorphism Cat ([C ∏ D, E]) ([C, [D, E]]) :=
  @exp_prod_l Cat _ _ C D E.

(* A functor into a product category is a pair of functors. *)
Example Cat_exp_prod_r (C D E : Cat) :
  @Isomorphism Cat ([C, D ∏ E]) ([C, D] ∏ [C, E]) :=
  @exp_prod_r Cat _ _ C D E.

(* Distributivity of the product of categories over their coproduct. *)
Example Cat_prod_coprod_r (C D E : Cat) :
  @Isomorphism Cat (C ∏ (D ∐ E)) ((C ∏ D) ∐ (C ∏ E)) :=
  @prod_coprod_r Cat _ _ _ C D E.

(* A functor out of a coproduct category is a pair of functors. *)
Example Cat_exp_coprod (C D E : Cat) :
  @Isomorphism Cat ([D ∐ E, C]) ([D, C] ∏ [E, C]) :=
  @exp_coprod Cat _ _ _ C D E.

(** ** The same four, upgraded to natural isomorphisms

    These are the isomorphisms of Structure/Cartesian/Closed/Natural.v taken
    at [C := Cat]; each lives in a functor category whose domain is a product
    of copies of [Cat] and [Cat^op]. *)

Example Cat_exp_prod_l_natural :
  @Isomorphism ([(Cat^op ∏ Cat^op) ∏ Cat, Cat])
    (@ExpProdL_LHS Cat _ _) (@ExpProdL_RHS Cat _ _) :=
  @exp_prod_l_natural Cat _ _.

Example Cat_exp_prod_r_natural :
  @Isomorphism ([Cat^op ∏ (Cat ∏ Cat), Cat])
    (@ExpProdR_LHS Cat _ _) (@ExpProdR_RHS Cat _ _) :=
  @exp_prod_r_natural Cat _ _.

Example Cat_prod_coprod_r_natural :
  @Isomorphism ([Cat ∏ (Cat ∏ Cat), Cat])
    (@ProdCoprodR_LHS Cat _ _) (@ProdCoprodR_RHS Cat _ _) :=
  @prod_coprod_r_natural Cat _ _ _.

Example Cat_exp_coprod_natural :
  @Isomorphism ([(Cat^op ∏ Cat^op) ∏ Cat, Cat])
    (@ExpCoprod_LHS Cat _ _ _) (@ExpCoprod_RHS Cat _ _) :=
  @exp_coprod_natural Cat _ _ _.

End CatExponential.

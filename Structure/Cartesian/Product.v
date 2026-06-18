Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section ProductCartesian.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

(* nLab: https://ncatlab.org/nlab/show/product+category
   nLab: https://ncatlab.org/nlab/show/functor+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   Binary products in a product category are computed componentwise. If C and
   D both have binary products, then so does C ∏ D, with the structure taken
   factorwise in each coordinate. On objects x = (c, d) and y = (c', d'),

       (c, d) × (c', d') = (c × c', d × d'),

   and the projections and pairing are pairs of the corresponding maps in C
   and D:

       exl       = (exl, exl)
       exr       = (exr, exr)
       (f, f') △ (g, g') = (f △ g, f' △ g').

   This is the special case, for the discrete two-object diagram shape, of the
   general fact that limits in a functor category [J, D] are computed
   pointwise whenever D has them: a product category C ∏ D inherits any limit
   that both factors possess. The universal mapping property [ump_products]
   therefore holds because it holds separately in each coordinate. *)

Program Instance Product_Cartesian : @Cartesian (C ∏ D) := {
  product_obj := fun x y => (fst x × fst y, snd x × snd y);  (* (c×c', d×d') *)

  fork := fun _ _ _ f g => (fst f △ fst g, snd f △ snd g);   (* pairing, componentwise *)
  exl  := fun x y => (exl, exl);                             (* left projection,  componentwise *)
  exr  := fun x y => (exr, exr)                              (* right projection, componentwise *)
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  simplify; rewrites; cat;
  rewrite fork_comp; cat.
Qed.

End ProductCartesian.

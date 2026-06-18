Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The strict category of categories *)

(* nLab: https://ncatlab.org/nlab/show/strict+category
   nLab: https://ncatlab.org/nlab/show/Cat
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

   StrictCat is the category of categories where functors are compared by a
   *strict* relation, in which objects are equal on the nose rather than merely
   isomorphic:

    objects               Categories
    arrows                Functors
    arrow equivalence     Strict equality of functors ([Functor_StrictEq_Setoid])
    identity              Identity Functor
    composition           Horizontal composition of Functors

   Strict equivalence: two functors F, G : C ⟶ D are identified when there is a
   proof [eq_on_obj : ∀ x, F x = G x] of propositional equality on objects,
   together with a coherence condition forcing the morphism maps to agree once
   [fmap F f] and [fmap G f] are transported along [eq_on_obj] into a common
   hom-setoid. This matches the nLab notion of a strict category, whose objects
   carry a genuine equality relation (a *set* of objects), and the resulting
   equality of strict functors: [Ob(F) = Ob(G)] together with compatible
   agreement of the underlying morphism actions.

   Difference from [Cat]: the sibling category [Cat] uses [Functor_Setoid],
   which identifies functors only up to natural isomorphism (object maps related
   by [F x ≅ G x]); its isomorphisms are therefore *equivalences* of categories.
   StrictCat instead uses [Functor_StrictEq_Setoid] with [F x = G x], so it is
   the strict 1-category in which an isomorphism is a genuine (on-the-nose)
   isomorphism of categories. Under the axiom of choice this strict 1-category
   is equivalent, as a bicategory, to the weak [Cat]. *)

#[export]
Instance StrictCat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_StrictEq_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects_stricteq;
  id_left          := @fun_strict_equiv_id_left;
  id_right         := @fun_strict_equiv_id_right;
  comp_assoc       := @fun_strict_equiv_comp_assoc;
  comp_assoc_sym   := fun a b c d f g h =>
    symmetry (@fun_strict_equiv_comp_assoc a b c d f g h)
}.

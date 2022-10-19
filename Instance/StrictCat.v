Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* StrictCat is the category of categories, with setoid structure given by
   objectwise equality.

    objects               Categories
    arrows                Functors
    arrow equivalence     Pointwise equality of objects
    identity              Identity Functor
    composition           Horizontal composition of Functors
 *)

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

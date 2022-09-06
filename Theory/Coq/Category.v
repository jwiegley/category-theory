Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(* [Coq] represents the category of Coq types and functions.

   This category is meant to be used for programming, and so it, and the
   constructions built on it, differ from the conventions of the main category
   theory library -- even though we show that all constructions map into the
   concepts of that library.

   For example, morphisms here are compared by definitional equality. This
   requires functional extensionality to be assumed in most proofs, but frees
   the programmer from maintaining towers of setoids, especially when
   higher-order functions are involved (for example, consider a simple proof
   such as [f = g → fmap ap f = fmap ap g]; for this to work over Setoids, a
   Proper instance for fmap is required that takes the Proper instance for ap
   into account).

   While the larger library [Category.Theory] assumes that proofs are a
   primary interest, and so uses Setoid plumbing everywhere, in this sub-
   library it is assumed that computational results are the main interest, and
   so some axioms are considered justified to relieve the proof burden. *)

#[global]
Program Instance Coq : Category := {
  obj     := Type;
  hom     := λ x y, x → y;
  homset  := λ _ _, eq_Setoid _;
  id      := λ _ x, x;
  compose := λ _ _ _ f g x, f (g x)
}.

Arguments id {Category}%category_scope {x}%object_scope : simpl never.
Arguments compose {Category}%category_scope {x y z}%object_scope
  (f g)%homset_scope : simpl never.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).
Notation "$ x" := (λ f, f x) (at level 60).

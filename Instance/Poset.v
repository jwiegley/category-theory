Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The category of a partially-ordered set. *)

(* nLab: https://ncatlab.org/nlab/show/poset
   Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

   A partially-ordered set forms a category directly from its preorder,
   since a poset is precisely a preorder (a [Proset]) satisfying the extra
   antisymmetry condition: x ≤ y ≤ x implies x = y. Antisymmetry adds nothing
   to the underlying [Category] construction (the hom-sets are unchanged); it
   only makes the resulting thin category skeletal, so that isomorphic objects
   are equal. nLab characterizes a poset as exactly "a skeletal thin category",
   equivalently "a skeletal (0,1)-category". (See also [Pos], the category of
   posets, whose objects are posets and whose morphisms are monotone maps.)

   Wikipedia: "Every poset (and every preorder) may be considered as a category
   in which every hom-set has at most one element. More explicitly, let
   hom(x, y) = {(x, y)} if x ≤ y (and otherwise the empty set) and
   (y, z) ∘ (x, y) = (x, z). Such categories are sometimes called thin.

   Posets are equivalent to one another if and only if they are isomorphic. In
   a poset, the smallest element, if it exists, is an initial object, and the
   largest element, if it exists, is a terminal object. Also, every preordered
   set is equivalent to a poset. Finally, every subcategory of a poset is
   isomorphism-closed." *)

Lemma eq_equiv {C : Type} : @Equivalence C eq.
Proof.
  split; auto. intros x y z; apply eq_trans.
Qed.

Definition Poset {C : Type} `{R : relation C}
           `(P : PreOrder C R) `{@Antisymmetric C eq eq_equiv R} : Category := Proset P.

Section Examples.
Definition LessThanEqualTo_Category : Category :=
  @Poset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).
End Examples.

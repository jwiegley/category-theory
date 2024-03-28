Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* Any partially-ordered set forms a category (directly from its preorder,
   since it simply adds antisymmetry). See also [Pos], the category of
   partially-ordered sets (where the sets are the objects, and morphisms are
   monotonic mappings.

   Wikipedia: "Every poset (and every preorder) may be considered as a
   category in which every hom-set has at most one element. More explicitly,
   let hom(x, y) = {(x, y)} if x ≤ y (and otherwise the empty set) and (y, z)
   ∘ (x, y) = (x, z). Such categories are sometimes called posetal.

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

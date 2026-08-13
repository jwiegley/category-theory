Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Skeleton.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Partial orders are exactly the skeletal preorders *)

(* nLab: https://ncatlab.org/nlab/show/poset
   nLab: https://ncatlab.org/nlab/show/skeleton
   Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

   Fong & Spivak define a partial order as a preorder satisfying x ≅ y → x
   = y (Seven Sketches in Compositionality, §1.2.2, remark 35, p. 13),
   observing that this condition is skeletality in categorical language; and
   Instance/Poset.v's own header has long said that antisymmetry "only makes
   the resulting thin category skeletal, so that isomorphic objects are
   equal", citing nLab's characterization of a poset as "a skeletal thin
   category".  Until Theory/Skeleton.v there was no [Skeletal] predicate to
   say it with, and the fact was exemplified only by two per-instance
   antisymmetry lemmas in the regression-guard file Test/Poset.v.

   [Proset_Skeletal_iff_Antisymmetric] states it, in both directions, for an
   arbitrary preorder.  The forward direction works because a [Proset]'s
   hom-setoid identifies all parallel morphisms (Instance/Proset.v), so both
   isomorphism laws are trivially satisfied and an isomorphism [x ≅ y] is
   exactly a pair of relation proofs.  [Poset_Skeletal] is the corollary for
   Instance/Poset.v's [Poset], which is DEFINITIONALLY a [Proset] — the
   antisymmetry argument does not appear in the body — and [Nat_le_Skeletal]
   instantiates it at (nat, ≤).

   Riehl computes that "the skeleton of a preorder is a poset" (Category
   Theory in Context, §1.5, Example 1.5.18, p. 37).  The honest in-tree form
   of that clause is [skeleton_of_proset_antisymmetric]: given a [Skeleton]
   of a preorder, its carriers satisfy antisymmetry.  The posetal
   REFLECTION — that every preorder HAS a skeleton — is a different
   statement and is not made here; see the note at the end of
   Theory/Skeleton.v. *)

Section ProsetSkeletal.
Context {A : Type}.
Context {R : relation A}.
Variable P : PreOrder R.

(** ** Seven Sketches §1.2.2 remark 35, both directions *)

Theorem Proset_Skeletal_iff_Antisymmetric :
  (Skeletal (Proset P) → @Antisymmetric A eq eq_equiv R) *
  (@Antisymmetric A eq eq_equiv R → Skeletal (Proset P)).
Proof.
  split.
  - intros Sk x y Rxy Ryx.
    apply (Sk x y).
    exists Rxy Ryx; exact I.
  - intros Anti x y i.
    exact (Anti x y (to i) (from i)).
Qed.

Theorem Poset_Skeletal `{Anti : @Antisymmetric A eq eq_equiv R} :
  Skeletal (@Poset A R P Anti).
Proof. intros x y i. exact (Anti x y (to i) (from i)). Qed.

(* Both Instance/Proset.v and Instance/Poset.v define a constant of this
   name, and this file imports both, so the name is qualified explicitly rather than left to import order. *)

Lemma Nat_le_Skeletal : Skeletal Poset.LessThanEqualTo_Category.
Proof.
  intros x y i.
  exact (partial_order_antisym PeanoNat.Nat.le_partialorder x y (to i) (from i)).
Qed.

(** ** Riehl Example 1.5.18: the skeleton of a preorder is a poset *)

Theorem skeleton_of_proset_antisymmetric (S : Skeleton (Proset P))
        (a b : skel_cat S) :
  R (`1 a) (`1 b) → R (`1 b) (`1 a) → `1 a = `1 b.
Proof.
  intros f g.
  apply (f_equal (fun z : skel_cat S => `1 z)).
  apply (skeleton_is_skeletal S).
  exists (f; skel_full S _ _ `2 a `2 b f) (g; skel_full S _ _ `2 b `2 a g);
    exact I.
Qed.

(* A poset is its own skeleton, by the trivial route of
   [Skeleton_of_Skeletal].  This is a convenience for callers who want a
   [Skeleton] datum over an order; the content is in the theorems above. *)

Definition Proset_Skeleton (Anti : @Antisymmetric A eq eq_equiv R) :
  Skeleton (Proset P) :=
  Skeleton_of_Skeletal (snd Proset_Skeletal_iff_Antisymmetric Anti).

End ProsetSkeletal.

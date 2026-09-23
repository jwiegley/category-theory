Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * FinSet is well-powered *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/FinSet
   Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   book p. 130: a category is well-powered when the subobjects of each
   object form a small set.  For the skeleton of finite sets this is the
   elementary fact that a finite set of size n has 2^n subsets, and the
   formal witness below reads it off the subobject classifier: the index
   at [n] is the hom-set [n ~> Ω], the characteristic functions
   [Fin.t n → Fin.t 2].

   WHAT IS DELIVERED.  [FinSet_WellPowered : WellPowered FinSet], an
   instance of Structure/WellPowered.v's [Classifier_WellPowered] at
   Instance/FinSet/Classifier.v's [FinSet_Pullbacks] and
   [FinSet_Classifier], and [FinSet_wp_index], the index read back at
   [eq_refl] as the functions [Fin.t n → Fin.t 2].  Both are
   unconditional: FinSet's classifier is the one in the tree that needs
   no hypothesis.  Every other [SubobjectClassifier] constructed in tree
   takes one -- [Untruncate] (Instance/Sets/Classifier/OneLevel.v's
   [Sets_Classifier], Instance/Fun/Classifier.v's [Fun_Classifier],
   [Fun_Classifier_cov] and [Fun_Classifier_small]), [IEM]
   ([Sets_Classifier_IEM], [Fun_Classifier_IEM]), [DecImage]
   ([Sets_Classifier_dec]) or [SmallClassifierExt]
   ([classifier_of_small]) -- by a grep for definitions whose type is a
   [SubobjectClassifier].

   UNIVERSES, measured with [Set Printing Universes. About
   FinSet_WellPowered.]:

     FinSet_WellPowered@{o h s t u v u0 u1} :
       WellPowered@{o h h s t} FinSet@{o h u v}
     (* Set < u, h < t, o <= s, h <= s, and stdlib bounds *)

   The index sits at the hom universe [h] itself, the pinned reading of
   Structure/WellPowered.v, and no bound relates the object universe [o]
   to [h]: FinSet's objects are numerals, so the trivial witness
   [trivial_small] would also serve wherever [o <= h], but the classifier
   witness holds at every instantiation.

   NOT DELIVERED.  FinSet is finitely complete (Instance/FinSet/Limit.v's
   [FinSet_FinitelyComplete]) and carries no [Complete] instance, as it
   lacks infinite products, so Structure/WellPowered.v's intersection
   theorem, which takes [Complete], does not apply here; the binary meets
   of subobjects of a finite set are Theory/Subobject/Lattice.v's
   [sub_meet] at
   [FinSet_Pullbacks], as the header of Instance/FinSet/Subobject.v
   records.  No co-well-poweredness witness for FinSet is attempted. *)

Definition FinSet_WellPowered@{o h s t u v +|
    Set < u, h < t, o <= s, h <= s +} :
  WellPowered@{o h h s t} FinSet@{o h u v} :=
  Classifier_WellPowered FinSet@{o h u v}.

(* The index at [n]: the characteristic functions of the subsets of n. *)
Example FinSet_wp_index (n : FinSet) :
  wp_index (FinSet_WellPowered n) = (Fin.t n → Fin.t 2) := eq_refl.

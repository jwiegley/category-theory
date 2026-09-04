Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * The two forgetful functors off the category of adjunctions *)

(* nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
     "Transformations of Adjoints", book p. 101, the display immediately
     after the paragraph naming A^(adj)X.

   Mac Lane: "Also there are two evident 'forgetful' functors to the
   ordinary functor categories, as follows:"

       A^X  ←  A^(adj)X ,     [A^(adj)X]^op  →  X^A

   and under that display he draws, for an arrow <sigma, tau> of
   A^(adj)X, the two legs

       F  ←--- <F, G, eta, eps> ---→  G
       |               |                 ^
    sigma          <sigma, tau>         tau
       v               v                 |
       F' ←-- <F', G', eta', eps'> --→  G'

   -- sigma pointing DOWN, from F to F', and tau pointing UP, from G' to G.
   The upward tau is exactly why the second functor is displayed on the
   OPPOSITE of the category of adjunctions.

   LETTERS.  His F : X ⟶ A is the left adjoint and G : A ⟶ X the right
   one, so his X is this file's D and his A is this file's C.  Then A^X,
   the functors X ⟶ A, is [D, C], the category the LEFT adjoints live in;
   and X^A, the functors A ⟶ X, is [C, D], where the RIGHT adjoints live.
   The two displayed functors are therefore

       AdjForgetLeft  C D :  Adj C D        ⟶ [D, C]
       AdjForgetRight C D : (Adj C D)^op    ⟶ [C, D]

   HOW THE CONTRAVARIANCE IS EXPRESSED.  Not by a bespoke notion of a
   contravariant functor, and not by any transport: the source is
   literally [(Adj C D)^op], Construction/Opposite.v's opposite category,
   which is what the book displays.  An arrow x ⟶ y of [(Adj C D)^op] IS
   an arrow y ⟶ x of [Adj C D], that is a [ConjPair y x], whose
   [conj_right] field already has type
   [adjobj_right x ⟹ adjobj_right y] -- the right adjoints of a conjugate
   pair run backward in [Adj C D], so they run forward out of its
   opposite.  So the arrow action of the second functor is the bare field
   projection [conj_right], with nothing inserted, and its two functor
   laws close by [reflexivity], as do the first functor's.

   BEYOND THE DISPLAY: BOTH FUNCTORS ARE FULL AND FAITHFUL.  Mac Lane does
   not say this on that page, and it is not needed for the display, but it
   is what makes the word "forgetful" precise here: neither functor loses
   information, because a conjugate pair is determined by either of its
   legs.  Faithfulness is Instance/Adj.v's [conj_pair_right_unique] and
   [conj_pair_left_unique]; fullness is Conjugate.v's
   [conjugate_conj_mate] and [conjugate_conj_mate_inv], which say that
   every transformation of left adjoints has [conj_mate] as a conjugate
   and every transformation of right adjoints has [conj_mate_inv].  Both
   [Full] instances therefore have a CHOSEN preimage, and it is the mate;
   [fmap_sur] holds by [reflexivity] in both.

   COST.  This file's transitive in-project closure is 21 modules
   excluding itself: Instance/Adj.v's own 19, plus Instance/Adj.vo itself,
   plus Instance/Fun.vo.  Construction/Opposite.vo was already inside that
   19, so the contravariant reading costs nothing extra.

   NOT DELIVERED.  Nothing here says either functor is essentially
   surjective, nor identifies the image of [AdjForgetLeft] with the left
   adjoints inside [D, C]; that would need "a functor with a right adjoint
   is in the image", which is not stated anywhere below.  No equivalence
   of [Adj C D] with any subcategory is claimed.  Nothing relates these to
   Instance/Adjoints.v, whose objects are categories rather than
   adjunctions between two fixed ones, nor to the 2-categorical picture of
   Theory/Bicategory/Mates.v.  No naturality of either functor in C or D
   is stated, and there is no concrete witness at a named pair of
   categories. *)

(* The first forgetful functor: an adjunction to its left adjoint, a
   conjugate pair to its sigma. *)
Program Definition AdjForgetLeft (C D : Category) : Adj C D ⟶ [D, C] := {|
  fobj := fun x => adjobj_left x;
  fmap := fun _ _ f => conj_left f
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* The second, on the OPPOSITE of the category of adjunctions: an
   adjunction to its right adjoint, a conjugate pair to its tau. *)
Program Definition AdjForgetRight (C D : Category) :
  (Adj C D)^op ⟶ [C, D] := {|
  fobj := fun x => adjobj_right x;
  fmap := fun _ _ f => conj_right f
|}.
Next Obligation. intros f g [_ Hr]; exact Hr. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the tau of a conjugate pair is determined by its sigma. *)
#[export]
Program Instance AdjForgetLeft_Faithful (C D : Category) :
  Faithful (AdjForgetLeft C D).
Next Obligation.
  split; [ exact X | now apply conj_pair_right_unique ].
Qed.

(* Full: every sigma has a conjugate, namely its mate. *)
#[export]
Program Instance AdjForgetLeft_Full (C D : Category) :
  Full (AdjForgetLeft C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := g
     ; conj_right := conj_mate (adjobj_adj y) (adjobj_adj x) g |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ g). Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the sigma of a conjugate pair is determined by its tau. *)
#[export]
Program Instance AdjForgetRight_Faithful (C D : Category) :
  Faithful (AdjForgetRight C D).
Next Obligation.
  split; [ now apply conj_pair_left_unique | exact X ].
Qed.

(* Full: every tau has a conjugate, namely its inverse mate. *)
#[export]
Program Instance AdjForgetRight_Full (C D : Category) :
  Full (AdjForgetRight C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := conj_mate_inv (adjobj_adj x) (adjobj_adj y) g
     ; conj_right := g |}
|}.
Next Obligation. exact (conjugate_conj_mate_inv _ _ g). Qed.
Next Obligation. reflexivity. Qed.

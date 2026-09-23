Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(** * The injections of a coproduct meet in the zero subobject *)

(* nLab:      https://ncatlab.org/nlab/show/disjoint+coproduct
   nLab:      https://ncatlab.org/nlab/show/zero+object
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Free_product

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 Exercise 1 (book p. 128, PDF p. 137) asks, of the free product of
   two groups, that its two injections be monic and that their images
   meet in the trivial subgroup, and it names a method.  The in-repo
   catalog's statement summary of the exercise
   (doc/plan/books/maclane/inventory/V.json, entry maclane:V.7:ex1, book
   page 128) reads, on this half: "Using the product G x H, show also
   that the two coproduct injections G -> G + H and H -> G + H are monic,
   and that their images intersect in the identity subgroup."  That
   method is not the one used here (NO [Cartesian] HYPOTHESIS, below).
   The same section (book p. 126, PDF
   p. 135) defines the intersection of two subobjects as their pullback,
   which Theory/Subobject/Lattice.v carries as [sub_meet] (#445).  nLab's
   "disjoint coproduct" names the general property: a coproduct is
   disjoint when its coprojections are monic and their pullback is
   initial.  This file proves that property, in the subobject form Mac Lane
   asks for, for EVERY binary coproduct in a category with a zero object
   and pullbacks -- the group statement is its instance at [Grp]
   (Instance/Grp/Colimit.v's [Grp_free_product_meet_trivial]).

   ** WHAT IS CONSUMED

   Structure/Bicartesian/Matrix.v's [inl_Monic] and [inr_Monic] (each
   injection is split by the copairing of the identity with the zero
   morphism), Theory/Subobject/Lattice.v's [sub_meet], [sub_bot],
   [sub_bot_least] and [sub_le_antisym], Structure/ZeroObject.v's
   [zero_mor] with [zero_mor_left] and [zero_mor_right], and
   Structure/Cocartesian.v's [inl_merge] and [inr_merge].

   ** WHAT IS BUILT

   [zero_initial_monic]: the arrow out of a zero object is monic, since
   its domain is also terminal.  [sub_inl], [sub_inr]: the two summands as
   subobjects of x + y.  [coprod_bot]: the bottom subobject of x + y,
   Lattice.v's [sub_bot] at the zero object.  [inl_pullback_leg_zero] and
   [inr_pullback_leg_zero]: both legs of the chosen pullback of the
   injections are zero morphisms -- apply the retraction [id ▽ zero_mor]
   (respectively [zero_mor ▽ id]) to the commuting square.
   [coproduct_injections_meet_trivial]: the meet of the two injections is
   the bottom subobject, [sub_meet sub_inl sub_inr ≈ coprod_bot].
   [coproduct_injections_pullback_zero]: the pullback of the injections is
   isomorphic to the zero object -- nLab's form -- read off the
   isomorphism of domains the subobject equivalence carries.

   NO [Cartesian] HYPOTHESIS.  The exercise's own method, the product
   G × H, is in this library Structure/Semiadditive.v's comparison map
   [can_comparison] from x + y to x × y, whose composites with the
   injections are [id △ zero_mor] and [zero_mor △ id]; it is the route
   the scouting prototype for this file took, and it assumes products as
   well.  It is deliberately NOT followed: the retraction alone suffices,
   and the theorem is stated over [ZeroObject], [Cocartesian] and
   [HasPullbacks] only: measured by [About], its binders are [C], [Z],
   [CC], [PB], [x] and [y], with no [Cartesian] among them.  (Issue #450's
   text asks for the two properties, listing generated subgroups and
   #445's subobject intersection as what they need, and does not mention
   the product: the product route is the book's hint, not the issue's.)

   ** STRENGTHS, STRICTEST FIRST

   The meet is NOT the bottom subobject on the nose: measured in a scratch
   file, [Example e : sub_meet (sub_inl x y) (sub_inr x y) = coprod_bot x y
   := eq_refl] is refused with "cannot unify "sub_meet (sub_inl x y)
   (sub_inr x y)" and "coprod_bot x y"" -- the two domains are the chosen
   pullback and the zero object, distinct objects.  The theorem is `≈` in
   the setoid of subobjects, which is an isomorphism of domains commuting
   with the monos; it ends in [Defined], so that isomorphism is the data
   [coproduct_injections_pullback_zero] projects.  The two leg lemmas are
   `≈` of morphisms.

   ** UNIVERSES, MEASURED

   By [About] under [Set Printing Universes], dropping bounds on stdlib
   globals: [zero_initial_monic@{u u0}], [sub_inl@{u u0}],
   [sub_inr@{u u0}], [coprod_bot@{u u0}] and the two leg lemmas are over
   [Category@{u u0 u0}] with EMPTY constraint blocks; the theorem and its
   corollary are [@{u u0 u1 u2}] with [u0 < u2], [u <= u1] and [u0 <= u1],
   the extra two universes being those of Lattice.v's subobject order
   ([sub_le_antisym@{u u0 u1 u2}] carries the same three constraints).  The
   identification of hom and proof universes is Lattice.v's ([sub_meet]
   is over [Category@{u u0 u0}] there), not this file's.

   ** THE COST OF REUSING [inl_Monic]

   Structure/Bicartesian/Matrix.v requires Category.Instance.Coq, so the
   dependency closure of this file, measured by iterating the build's
   coqdep output (.Makefile.coq.d) to a fixed point and counting modules
   OTHER than the file itself, is 75 modules against
   Theory/Subobject/Lattice.v's 48.  Of the 75, 27 are outside Lattice.v's
   closure; one of them is Lattice.v itself, and each of the other 26
   lies in Matrix.v's closure counted with Matrix.v included.  That is
   the price of not writing the two retractions a second time; Lattice.v
   itself requires neither Matrix.v nor Structure/ZeroObject.v, which is
   why this is a new file and not an appendix to it.

   ** NON-VACUITY

   Instance/Grp/Colimit.v instantiates the theorem at [Grp], at the
   coproduct the adjoint functor theorem produces, with Instance/Grp.v's
   [Grp_Zero] -- usable there since #450 wrote out that constant's
   universes -- and exhibits a nontrivial coproduct (the AFT coproduct of
   Z/2 with itself).

   ** AXIOMS

   Every constant of this file reports "Closed under the global context".

   ** NOT DELIVERED

   No version for categories without a zero object.  In [Sets] the
   pullback of the two injections is the empty set, but there is no
   retraction of [inl] out of x + y when x is empty and y is not, so the
   argument here does not apply and a different one (through a strict
   initial object; Lattice.v's [zero_monic_of_strict] is its first step)
   is not made.  No indexed or n-ary form.  No
   converse, and no statement that disjointness characterizes anything.
   No image factorization is used or needed: the injections are monic, so
   each is its own image. *)

(** ** The arrow out of a zero object is monic *)

Section ZeroMonic.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(* Two arrows into the zero object agree because the zero object is also
   terminal; carrying them across the coincidence isomorphism makes that
   visible, and the cancellation hypothesis of [Monic] is never used. *)
Lemma zero_initial_monic (w : C) : Monic (@zero C (@zero_initial C Z) w).
Proof.
  constructor; intros v g1 g2 _.
  transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g1)).
  - rewrite comp_assoc, iso_from_to; cat.
  - transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g2)).
    + apply compose_respects; [reflexivity|].
      apply (@one_unique C (@zero_terminal C Z)).
    + rewrite comp_assoc, iso_from_to; cat.
Qed.

End ZeroMonic.

(** ** The two injections of a coproduct meet in the bottom subobject *)

Section CoproductMeet.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context `{PB : @HasPullbacks C}.
Context (x y : C).

(* The two summands as subobjects of the coproduct, monic by
   Structure/Bicartesian/Matrix.v's [inl_Monic] and [inr_Monic]. *)
Definition sub_inl : SubObj (x + y) :=
  {| sub_dom := x; sub_mono := inl; sub_is_monic := inl_Monic x y |}.

Definition sub_inr : SubObj (x + y) :=
  {| sub_dom := y; sub_mono := inr; sub_is_monic := inr_Monic x y |}.

(* The bottom subobject of the coproduct: the zero object, included by the
   arrow out of it. *)
Definition coprod_bot : SubObj (x + y) :=
  @sub_bot C (@zero_initial C Z) (x + y) (zero_initial_monic (x + y)).

(* Each leg of the chosen pullback of the two injections is the zero
   morphism: apply the retraction [id ▽ zero_mor] (resp. [zero_mor ▽ id])
   to the commuting square. *)
Lemma inl_pullback_leg_zero :
  pullback_fst _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@id C x ▽ @zero_mor C Z y x) ∘ inl ∘ pullback_fst _ _ P).
  - rewrite inl_merge; cat.
  - rewrite <- comp_assoc, (pullback_commutes _ _ P), comp_assoc, inr_merge.
    apply zero_mor_right.
Qed.

Lemma inr_pullback_leg_zero :
  pullback_snd _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@zero_mor C Z x y ▽ @id C y) ∘ inr ∘ pullback_snd _ _ P).
  - rewrite inr_merge; cat.
  - rewrite <- comp_assoc, <- (pullback_commutes _ _ P), comp_assoc,
      inl_merge.
    apply zero_mor_right.
Qed.

Theorem coproduct_injections_meet_trivial :
  sub_meet sub_inl sub_inr ≈ coprod_bot.
Proof.
  apply sub_le_antisym.
  - exists (from (@zero_coincide C Z) ∘ @one C (@zero_terminal C Z) _).
    simpl.
    rewrite inl_pullback_leg_zero, zero_mor_left.
    unfold zero_mor; rewrite comp_assoc; reflexivity.
  - apply sub_bot_least.
Defined.

(* The same fact in nLab's form: the pullback of the two injections is the
   zero object, read off the isomorphism the subobject equivalence
   carries. *)
Definition coproduct_injections_pullback_zero :
  Pull (@inl C CC x y) (@inr C CC x y) (pullback inl inr)
    ≅ @initial_obj C (@zero_initial C Z) :=
  `1 coproduct_injections_meet_trivial.

End CoproductMeet.

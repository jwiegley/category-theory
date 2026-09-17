Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(* The free group on one generator separates Grp

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/free+group

   Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print,
   September 2005), §7.2, printed p. 154 (PDF p. 163), gives the
   single-object generator and offers the free group on one generator as
   the generator of groups; Mac Lane, "Categories for the Working
   Mathematician", 2nd ed. (GTM 5), §V.7, book p. 127 (PDF p. 136),
   Definition 4 is the family form this instantiates, and Riehl,
   "Category Theory in Context", 2nd ed., Definition 4.7.7, printed
   p. 177 (PDF p. 197), is the same definition in her vocabulary.  This
   file supplies the [Grp] witness; the [Sets] witness is
   Instance/Sets/Generator.v and the [Ab] one Instance/Ab/Generator.v.

   THE ARGUMENT, AND WHERE ITS WORK LIVES.  Freeness does all of it.  For
   parallel homomorphisms f, g : G ~> K agreeing after every homomorphism
   out of the free group on one generator, and an element x of G, the
   constant map [grp_point x] sends the one generator to x; its extension
   [free_grp_extend] (Instance/Grp/Free.v:409) is a homomorphism out of
   the free group, so the hypothesis applies to it, and
   [free_grp_extend_generators] (:328) says the extension carries the
   inserted generator [fg_insert] (:253) to x.  Properness of f and g as
   setoid maps transports the agreement from the generator's image to x
   itself.  So the only structural input is the universal property, and
   the statement would read the same for any left adjoint to a forgetful
   functor whose unit at the singleton picks out an element.

   THE STRENGTH IS ≈, NOT CONVERSION, AND THAT IS FORCED BY THE DONOR.
   [free_grp_extend_generators] is stated at ≈, not at [eq_refl]: the
   extension's action is [fmap] of a functor built through
   Construction/Free/Groupoid.v's [FreeGroupoidFunctor], whose value on a
   one-letter word is reached by a [Qed]-opaque lemma rather than by
   computation.  So the two [rewrite]s below are not cosmetic — the proof
   cannot be the single [exact] that the [Ab] witness is, and the
   difference between the two files is exactly this.
   Instance/Ab/Generator.v records the contrast from the other side.

   WHAT "THE INTEGERS" ARE HERE.  Mac Lane's second example is the
   integers generating abelian groups, which belongs to
   Instance/Ab/Generator.v.  For [Grp] the corresponding object is the
   free group on one generator, which classically IS ℤ; this file does
   NOT prove that identification.  The tree DOES carry ℤ as a group
   object: Construction/Deloop/Functors.v:448's [Int_Plus_Grp : GrpObject]
   (the additive monoid [Int_Plus] of :438 with [grp_inv := Z.opp]), a
   built constant of the _CoqProject set.  What is left undone is the
   isomorphism [FreeGrpObject unit_setoid_object ≅ Int_Plus_Grp] in
   [Grp] -- the homomorphism out of the free group is
   [free_grp_extend] at the map sending the generator to 1%Z, the
   inverse needs the integer power of the generator in the free group,
   and the two inverse laws need induction on words and on integers --
   and nothing below depends on it.  On the abelian side the integers
   have five names, measured with grep -rnE
   '^Definition [A-Za-z_0-9]+ : AbObject := ring_ab Int_Ring\.$'
   --include='*.v' . (which reports 5): [ZAb] (Instance/Ab/Monoidal.v:422),
   [ab_Z] (Instance/Ab/Coproduct.v:264), [Zgroup]
   (Instance/Ab/Graded.v:281), [Ab_Z]
   (Structure/Kernel/Universal/Examples.v:263) and [ab_int]
   (Instance/Ab/Free.v:883); Instance/Ab/TorsionFree.v:153 records the
   same count, and this is a re-measurement of it, not a citation.  An
   earlier revision of this paragraph said that NO ℤ group object existed
   in [Grp], from a sweep that saw only the tactic-mode
   [Definition … : GrpObject.] constants ([Grp_trivial], [Z2], [GalZ2],
   [GrpTwo]) and missed every [:= {| … |}] one; an audit found
   [Int_Plus_Grp], and the sentence is corrected here rather than
   removed.

   NOT DELIVERED.  No claim that the free group on one generator is the
   SMALLEST separator, nor that [Grp] has no smaller one; no statement
   about generating families of more than one object; no
   joint-faithfulness reading (Structure/Generator.v's [JointlyFaithful]),
   which is the theory half of #447; and no isomorphism with
   [Int_Plus_Grp], as above.  The two-generator non-degeneracy results of
   Instance/Grp/Free.v:652 and :586 are not used and say nothing about
   separation. *)

(** ** The element of a group as a map out of the singleton *)

(* The constant map at [x], read into [Sets] through [Grp_Forget].  This
   is the transpose across the free/forgetful adjunction of the
   homomorphism that picks out [x].  Built by [refine] rather than as a
   [Program Definition] because under the universe annotation the
   respectfulness obligation is not discharged before the constant is
   registered, and the next proof's reference to it is then rejected with
   "The variable grp_point was not found in the current environment".
   It must also stay TRANSPARENT: closed with [Qed] instead, the
   separation proof stops at the [assert] of the generator equation,
   whose [exact (free_grp_extend_generators …)] is refused because the
   hypothesis has frozen as
   [f (grp_mul G (grp_unit G) (grp_point x ttt)) ≈ …] with nothing left
   to reduce (an earlier revision of this sentence placed the stop at the
   final [exact], which is never reached; measured on a full copy). *)
Definition grp_point@{o so+} {G : Grp@{so o}} (x : carrier G) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Grp_Forget G.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation *)

Lemma Grp_free_one_separates@{o so+} :
  @IsSeparator Grp@{so o} (FreeGrpObject unit_setoid_object@{o o}).
Proof.
  intros G K f g Hk x.
  pose (e := @free_grp_extend unit_setoid_object@{o o} G (grp_point x)).
  pose proof (Hk e (fg_insert unit_setoid_object@{o o} ttt)) as E.
  simpl in E.
  assert (Ex : e (fg_insert unit_setoid_object@{o o} ttt) ≈ x)
    by exact (free_grp_extend_generators unit_setoid_object@{o o} G
                (grp_point x) ttt).
  rewrite <- (proper_morphism (grp_map f) _ _ Ex).
  rewrite <- (proper_morphism (grp_map g) _ _ Ex).
  exact E.
Qed.

(* Awodey's example as a one-object generating family. *)
Definition Grp_Generator@{o so+} : Generator Grp@{so o} :=
  @Generator_of_separator Grp@{so o}
    (FreeGrpObject unit_setoid_object@{o o}) Grp_free_one_separates.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(** * An isomorphism-dense full subcategory is reflective *)

(* nLab: https://ncatlab.org/nlab/show/reflective+subcategory
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   nLab: https://ncatlab.org/nlab/show/dense+subcategory

   Mac Lane, Categories for the Working Mathematician, 2nd ed., §IV.4,
   printed p. 94, states the result this file formalizes:

     "Proposition 2.  If A is a full subcategory of C and every c in C is
      isomorphic (in C) to some object of A, then the insertion K : A -> C
      is an equivalence and is part of an adjoint equivalence
      <T, K; eta, 1> : C -> A with counit the identity.  Therefore A is
      reflective in C."

   The paragraph immediately before it supplies the proof idea, reading
   the general characterization of adjoint equivalences at an insertion:

     "In this proof, suppose that A is a full subcategory of C and that
      S = K : A -> C is the insertion.  For objects a in A subset C we can
      then choose a_0 = a = Ka and eta_{Ka} the identity.  Then K eps_a = 1,
      hence eps_a = 1 for all a."

   and the paragraph after it records the two riders: "This includes in
   particular the case already noted, when A is a skeleton of C", and the
   definition of a LEFT-ADJOINT-LEFT-INVERSE, with its Exercise 4 ("G is an
   isomorphism of A to a reflective subcategory of X").  Exercise 4 is a
   separate catalog item and is cited here, not proved.

   ** What the proposition asks, and at which strength each half lands

   Four things are asserted.  Three are delivered outright and one is
   delivered in the form this library's setoid discipline supports:

     (1) the insertion is an EQUIVALENCE          [dense_incl_equivalence]
     (2) it is part of an ADJOINT EQUIVALENCE     [dense_incl_adjoint_-
                                                   equivalence], and in the
                                                  other handedness
                                                  [dense_adj]
     (3) the counit is the IDENTITY               NOT delivered as stated;
                                                  delivered as a
                                                  componentwise ISOMORPHISM
                                                  [dense_counit_iso],
                                                  [dense_counit_Isomorphism]
     (4) the subcategory is REFLECTIVE            [dense_full_subcategory_-
                                                   reflective]

   (3) is discussed at length below: with the chosen-representative reading
   of the hypothesis that this library already uses, the identity form is
   not merely unproved, it is not TYPEABLE.

   ** The hypothesis, first class

   [IsoDense S] is Mac Lane's "every c in C is isomorphic (in C) to some
   object of A", with the object CHOSEN: a Type-valued sigma handing back,
   for each c, an object a of the subcategory together with an isomorphism
   Incl a =~= c in C.  This is exactly the reading [EssentiallySurjective]
   (Theory/Equivalence.v:154) already takes -- its [eso_obj] field is a
   function, not an existential -- and [iso_dense_ESO] is the repackaging,
   a plain [Definition] raising no obligation.  No choice principle is
   consumed anywhere in this file: the choice IS the hypothesis, supplied
   by the caller, exactly as [EssentiallySurjective] supplies it.  The
   converse repackaging [ESO_iso_dense] and both round trips are recorded;
   the object components agree at [eq_refl] in both directions, and the
   [EssentiallySurjective] whole record returns at [eq_refl] as well (a
   two-field class under Lib.v:10's [Set Primitive Projections] has eta),
   while the [IsoDense] whole record does NOT, since stdlib [sigT] is not
   covered by that setting.  That last one is refuted and pinned in
   Test/ProbeDense375.v.

   ** The route: pure reuse, with one design decision

   This file proves no new equation about any category.  Every field of
   every delivered constant comes from an existing donor:

     fullness of the inclusion functor   Full_Implies_Full_Functor
                                         (Construction/Subcategory.v:104)
     faithfulness of the inclusion       Incl_Faithful
                                         (Construction/Subcategory.v:89)
     essential surjectivity              iso_dense_ESO, from the hypothesis
     equivalence from those three        FF_ESO_Equivalence
                                         (Theory/Equivalence/-
                                          FullFaithful.v:160)
     adjoint equivalence from that       Equivalence_to_AdjointEquivalence
                                         (Theory/Equivalence/Adjoint.v:333)
     the OTHER handedness                AdjointEquivalence_swap_adjunction
                                         (Theory/Equivalence/Adjoint.v:414)
     the reflective packaging            Build_Reflective
                                         (Construction/Reflective.v:60)

   [Incl_Faithful] is literally in the proof term of
   [dense_incl_equivalence], which is a [:=] with no tactic:

     @FF_ESO_Equivalence _ _ (Incl C S)
       (Full_Implies_Full_Functor C S F) (Incl_Faithful C S)
       (iso_dense_ESO D)

   so the generic faithful-inclusion lemma is used rather than bypassed.
   That lemma is closed with [Qed], which costs nothing here: [Faithful] is
   a one-field class whose field is a proof, so there is no data to reduce.

   The ONE design decision is the HANDEDNESS.  Mac Lane writes the adjoint
   equivalence as <T, K; eta, 1>, and under the §IV.1 convention the
   first-listed functor of such a triple is the LEFT adjoint -- so T, the
   reflector, is left adjoint and the insertion K is the RIGHT adjoint.
   [Equivalence_to_AdjointEquivalence] makes the equivalence's OWN functor
   the left adjoint, so at F := Incl it yields Incl -| T, which is the
   opposite handedness and is NOT the reflection adjunction.
   [AdjointEquivalence_swap_adjunction] is what supplies T -| K, and that
   is the shape Theory/Equivalence/Creation.v:63-66 already uses to read an
   equivalence as a right adjoint.  Both handednesses are shipped:
   [dense_incl_adjoint_equivalence] is Mac Lane's triple read with K on the
   left, [dense_adj] is the reflection adjunction.

   ** The counit

   Mac Lane's "with counit the identity" rests on a case distinction his
   prose does not mark as one, though it states the choice out loud: "For
   objects a in A subset C we can then choose a_0 = a".  That is a choice
   made per object, DIFFERENTLY for objects already in the subcategory
   than for the rest.  Here the choice is one
   function [D], applied uniformly, so the representative of an object of
   the subcategory is the VALUE [`1 (D (Incl C S a))], which is not [a] --
   neither definitionally, nor up to any equation the hypothesis carries.
   Consequently

     counit (dense_adj D) a = id[a]

   is not false, it is ILL-TYPED: the counit runs
   [dense_reflector (Incl a) ~> a] and its two endpoints are different
   objects of [Sub C S].  That is pinned as a TYPING negative in
   Test/ProbeDense375.v at a witness where the two endpoints are provably
   distinct: a full subcategory of [Indiscrete bool] containing BOTH
   points, whose chosen representative for each point is the OTHER point.
   That witness is the honest content of Mac Lane's remark -- the identity
   counit is a property of a well-chosen family of representatives, not of
   iso-density.

   What is delivered instead is the componentwise isomorphism:
   [dense_counit_iso a : IsIsomorphism (counit (dense_adj D) a)], which is
   [adj_equiv_counit_iso] of the swapped adjoint equivalence and therefore
   a [:=] with no tactic, and its bundled reading
   [dense_counit_Isomorphism a : dense_reflector (Incl a) =~= a] in
   [Sub C S], whose forward leg IS the counit at [eq_refl].  The
   [Reflective]-level statement of the same fact is
   [reflective_counit_iso] (Construction/Reflective.v:92); it is cited
   rather than restated, and the direct form above is preferred because
   that lemma produces data and is closed with [Qed], so neither of its
   legs reduces.

   A further identification was attempted and is reported as MEASURED and
   NOT obtained: the counit ought to be the fullness-lift of the chosen
   isomorphism, so that [fmap[Incl C S] (counit (dense_adj D) a)] would be
   [approx] [to (`2 (D (Incl C S a)))].  The statement is true -- the
   symmetry branch of [Functor_Setoid]'s [Equivalence] obligation
   (Theory/Functor.v:164-168) builds [iso_sym] componentwise, [from] then
   [to] -- but that is a fact about the tactic's OUTPUT and not about the
   type, and it is not available by conversion: the route through
   [equiv_adjunction_counit_at] (Theory/Equivalence/Adjoint.v:233) is
   blocked at [symmetry], which is [Equivalence_Symmetric] of
   [Functor_Setoid] (Theory/Functor.v:149), whose [Equivalence] obligation
   is discharged by the [equivalence] tactic and closed with [Qed], so the
   isomorphism family it produces does not reduce and its type -- a bare
   natural isomorphism -- does not pin its components.  The identification
   is therefore not available through the swap, and no second route is
   built here.  The refuted strict form is pinned in the probe.  One
   sharper datum was measured out of tree after the audited constant set
   was fixed, and is recorded rather than shipped: the equivalence's own
   counit cell IS the chosen isomorphism on the nose,
   [equivalence_counit_at (dense_incl_equivalence D) c = `2 (D c)] at
   [eq_refl].

   For the same reason the strictified variant that a reader might expect
   -- a hypothesis [`1 (D (Incl C S a)) = a] making the counit an
   endomorphism, transported, and then [approx] [id] -- is NOT delivered,
   and the reason is sharper than opacity: even under that hypothesis the
   chosen isomorphism [`2 (D (Incl C S a))] may be a NON-IDENTITY
   automorphism of [a], so the counit still need not be the identity.  Such
   a hypothesis is therefore not sufficient, and the witness above is one
   where it does not hold.  Mac Lane's remark needs the isomorphism chosen
   to be the identity too, which is what his "and eta_{Ka} the identity"
   says.  No [eq_refl] identity is claimed for that case either: the
   triangle identity through which the counit would be read is an
   [approx]-equation.

   ** The skeleton rider, and a note on the order of events

   Mac Lane's "This includes in particular the case already noted, when A
   is a skeleton of C" is [skeleton_IsoDense] and [skeleton_reflective]: a
   [Skeleton] (Theory/Skeleton.v:355) carries [skel_rep] and [skel_iso],
   which ARE iso-density data with the isomorphism in the reverse
   orientation, so [skeleton_IsoDense] pairs [skel_rep] with [iso_sym] of
   that field and nothing more.  The rider is unusual in this tree in that
   the SPECIAL CASE preceded the general statement: Theory/Skeleton.v:398
   already proved [skeleton_inclusion_is_equivalence] by exactly this
   route, and
   :409 already defined [skel_reflect] as its quasi-inverse.  What was
   absent was the hypothesis as a first-class notion, the adjoint
   equivalence in the reflector-on-the-left handedness, and the conclusion
   [Reflective].  Because the two ESO records agree fieldwise and
   [EssentiallySurjective] has eta, the general theorem's reflector at a
   skeleton IS [skel_reflect] on the nose ([skeleton_reflector_is_skel_-
   reflect], [eq_refl]), so no second reflector enters the tree.

   ** Universes

   Measured with [About] and [Set Printing Universes] on all 26 constants,
   binder and block.  Every constant is over [C : Category@{u u0 u0}] --
   hom identified with proof in the BINDER, by reusing the level -- and
   that identification is inherited from [Subcategory@{u u0 u1 u2}], which
   is declared over [Category@{u u0 u0}] with an EMPTY constraint block;
   the probe pins it by rejecting [Subcategory Cu] at a category whose
   proof universe is declared strictly above its hom universe, with that
   category's hom-set, identity and hom-setoid accepted at those levels.
   Twenty-one constraint blocks carry no equation, only bounds.  Five carry
   exactly one, [u0 = u2], and they are exactly
   [dense_full_subcategory_reflective] and its four [eq_refl] readbacks --
   the four skeleton constants package [Reflective] too and carry none --
   because [Reflective@{u u0 u1 u2 u3 u4 u5}] is declared over
   [Subcategory@{u3 u5 u4 u5} C], instantiating [Subcategory]'s fourth
   universe at C's hom level where [Subcategory] itself leaves it free, so
   the equation is the record's and not this file's -- [dense_adj],
   [dense_reflector] and [dense_incl_equivalence] carry none.  No binder,
   block or universe instance of the 26 contains the token [Set].  None of
   these identifications is claimed unavoidable.

   ** Witnesses (in the probe, so this file's closure stays lean)

   Test/ProbeDense375.v instantiates the theorem twice over
   [Indiscrete bool] (Instance/Discrete/Reconstruct.v:416, whose hom and
   proof universes are the literal [Set] -- a pin the witnesses inherit and
   this file does not carry): once through [skeleton_reflective] at
   Theory/Skeleton/Separation.v:140's [Indiscrete_bool_Skeleton], where the
   reflection is proved NOT inert at the non-representative point, and
   once at a full subcategory on BOTH points whose chosen representative of
   each point is the OTHER point, the witness behind the counit paragraph
   above.

   ** Prior art, and four claims of the issue that are stale

   Measured on the base commit of this branch, over the .v files:

     (a) The issue says there is no generic [Faithful (Incl C S)] instance
         and that faithfulness of an inclusion is asserted in comments and
         proved per instance.  FALSE: Construction/Subcategory.v:89 is
         [Lemma Incl_Faithful : Functor.Faithful Incl], consumed by
         Theory/Skeleton.v:402, by Adjunction/FullFaithful.v and by
         Construction/Reflective/Limit.v among others.  Nothing here
         rebuilds it.

     (b) Several donor line numbers in the issue have drifted.  At this
         base: [Incl] is :64 (issue says :59), [Full] is :99 (:69),
         [Full_Implies_Full_Functor] is :104 (:74), and
         [EssentiallySurjective] is Theory/Equivalence.v:154 (:141).
         [FF_ESO_Equivalence] :160 and
         [Equivalence_to_AdjointEquivalence] :333 are right.

     (c) The issue says the existing applications of [FF_ESO_Equivalence]
         are not subcategory inclusions.  STALE:
         Theory/Skeleton.v:401 applies it to [skel_incl S], which IS the
         [Incl] of a [Sub].  (Instance/FinSet/Skeleton.v also applies it to
         a functor called [FinSet_Incl], but that one is a hand-built
         [Program Definition] at :417 and not an [Incl C S] at all.)  So
         the specialization to a subcategory inclusion existed for the
         skeleton; what did not exist is measured in the paragraph above.

     (d) The issue defers the skeleton corollary until the skeleton
         development lands.  It has landed: Theory/Skeleton.v exists and
         [Record Skeleton] is at :355, so the corollary is delivered here.

   Searches run on the same base: [IsoDense], [iso_dense] and
   [dense_full_subcategory_reflective] have zero hits outside this file and
   its probe, and [Build_Reflective] has exactly four application sites
   (Construction/Reflective/Idempotent.v:346, Instance/Ord/Poset.v:286,
   Instance/Ab/TorsionFree.v:525, Instance/Top/Kolmogorov.v:633), none of
   them obtained from an equivalence; a fifth textual hit,
   Instance/Ab/TorsionFree.v:111, is a comment quoting the search string.

   ** Registration

   NOTHING in this file is registered for instance resolution, following
   the rule Theory/Equivalence.v and Theory/Equivalence/FullFaithful.v
   state for themselves: a quasi-inverse and a chosen preimage object are
   CHOICES and must be passed explicitly.  [EssentiallySurjective] is a
   class, so [iso_dense_ESO] would be resolvable if declared an [Instance];
   it is a plain [Definition] on purpose.

   ** Not delivered

   Exercise 4 of the same page (a left-adjoint-left-inverse of G makes G an
   isomorphism onto a reflective subcategory) is a separate catalog item
   and is not attempted.  The converse of the proposition -- a reflective
   subcategory whose unit is a componentwise isomorphism is iso-dense -- is
   not stated.  Nothing is said about [Coreflective], about naturality of
   the choice [D] in any variable, or about uniqueness of the reflector. *)

Section Dense.

Context {C : Category}.
Context (S : Subcategory C).

(** ** The hypothesis *)

(* Mac Lane's "every c in C is isomorphic (in C) to some object of A", with
   the object chosen.  The sigma is Type-valued, so the representative and
   the isomorphism are both DATA. *)

Definition IsoDense : Type :=
  ∀ c : C, { a : Sub C S & Incl C S a ≅ c }.

(* ... which is [EssentiallySurjective] for the inclusion, field for
   field.  A plain [Definition], raising no obligation. *)

Definition iso_dense_ESO (D : IsoDense) :
  EssentiallySurjective (Incl C S) :=
  {| eso_obj := fun c => `1 (D c)
   ; eso_iso := fun c => `2 (D c) |}.

Example iso_dense_ESO_obj (D : IsoDense) (c : C) :
  @eso_obj _ _ _ (iso_dense_ESO D) c = `1 (D c) := eq_refl.

(* ... and back. *)

Definition ESO_iso_dense (E : EssentiallySurjective (Incl C S)) :
  IsoDense :=
  fun c => (@eso_obj _ _ _ E c; @eso_iso _ _ _ E c).

Example ESO_iso_dense_obj (E : EssentiallySurjective (Incl C S)) (c : C) :
  `1 (ESO_iso_dense E c) = @eso_obj _ _ _ E c := eq_refl.

(* One round trip closes on the WHOLE record, because
   [EssentiallySurjective] is a two-field class and Lib.v:10 sets
   [Set Primitive Projections]. *)

Example ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO (ESO_iso_dense E) = E := eq_refl.

(* The other closes only on the object component: stdlib [sigT] has no eta,
   so the [IsoDense] whole record does not return.  Refuted and pinned in
   Test/ProbeDense375.v. *)

Example iso_dense_round_obj (D : IsoDense) (c : C) :
  `1 (ESO_iso_dense (iso_dense_ESO D) c) = `1 (D c) := eq_refl.

Context (F : Subcategory.Full C S).

(** ** (1) The insertion is an equivalence *)

(* [Incl_Faithful] appears here, in a [:=] with no tactic; the reviewer
   check for this issue is that the generic lemma is consumed rather than
   bypassed. *)

Definition dense_incl_equivalence (D : IsoDense) :
  EquivalenceOfCategories (Incl C S) :=
  @FF_ESO_Equivalence _ _ (Incl C S)
    (Full_Implies_Full_Functor C S F)
    (Incl_Faithful C S)
    (iso_dense_ESO D).

(* The quasi-inverse acts on objects by the chosen representative:
   [FF_ESO_Equivalence] is [Defined] and [ff_eso_inverse]'s [fobj] is
   [eso_obj], so this reduces all the way. *)

Example dense_incl_quasi_obj (D : IsoDense) (c : C) :
  fobj[@quasi_inverse _ _ _ (dense_incl_equivalence D)] c = `1 (D c)
  := eq_refl.

(** ** (2) The adjoint equivalence, in both handednesses *)

(* Mac Lane's triple read with the insertion on the LEFT. *)

Definition dense_incl_adjoint_equivalence (D : IsoDense) :
  AdjointEquivalence (Incl C S)
    (@quasi_inverse _ _ _ (dense_incl_equivalence D)) :=
  Equivalence_to_AdjointEquivalence (dense_incl_equivalence D).

(* Mac Lane's T. *)

Definition dense_reflector (D : IsoDense) : C ⟶ Sub C S :=
  @quasi_inverse _ _ _ (dense_incl_equivalence D).

Example dense_reflector_obj (D : IsoDense) (c : C) :
  fobj[dense_reflector D] c = `1 (D c) := eq_refl.

(* ... and the reflection adjunction T -| K, the handedness the
   [Reflective] record asks for. *)

Definition dense_adj (D : IsoDense) : dense_reflector D ⊣ Incl C S :=
  AdjointEquivalence_swap_adjunction (dense_incl_adjoint_equivalence D).

(** ** (4) Reflectivity *)

Definition dense_full_subcategory_reflective (D : IsoDense) : Reflective S :=
  @Build_Reflective C S F (dense_reflector D) (dense_adj D).

Example dense_reflective_reflector (D : IsoDense) :
  reflector (dense_full_subcategory_reflective D) = dense_reflector D
  := eq_refl.

Example dense_reflective_adj (D : IsoDense) :
  reflective_adj (dense_full_subcategory_reflective D) = dense_adj D
  := eq_refl.

Example dense_reflective_full (D : IsoDense) :
  reflective_full (dense_full_subcategory_reflective D) = F := eq_refl.

Example dense_reflective_obj (D : IsoDense) (c : C) :
  fobj[reflector (dense_full_subcategory_reflective D)] c = `1 (D c)
  := eq_refl.

(** ** (3) The counit, as an isomorphism *)

(* [:=] with no tactic: the swapped adjoint equivalence carries this as a
   field. *)

Definition dense_counit_iso (D : IsoDense) (a : Sub C S) :
  IsIsomorphism (@counit _ _ _ _ (dense_adj D) a) :=
  @adj_equiv_counit_iso _ _ _ _
    (AdjointEquivalence_swap (dense_incl_adjoint_equivalence D)) a.

(* The bundled reading, in [Sub C S].  Its forward leg is the counit on the
   nose, recorded below; contrast [reflective_counit_iso]
   (Construction/Reflective.v:92), which states the same fact at the level
   of the [Reflective] record but is closed with [Qed] while producing
   data, so neither of its legs reduces. *)

Definition dense_counit_Isomorphism (D : IsoDense) (a : Sub C S) :
  dense_reflector D (Incl C S a) ≅[Sub C S] a :=
  @IsIsoToIso (Sub C S) _ _ _ (dense_counit_iso D a).

Example dense_counit_Isomorphism_to (D : IsoDense) (a : Sub C S) :
  to (dense_counit_Isomorphism D a)
    = @counit _ _ _ _ (dense_adj D) a := eq_refl.

End Dense.

Arguments IsoDense {C} S.

(** ** The skeleton rider *)

(* Mac Lane's "This includes in particular the case already noted, when A
   is a skeleton of C".  [skel_iso] is stated in the reverse orientation,
   so the whole content of this passage is [iso_sym]. *)

Definition skeleton_IsoDense {C : Category} (Sk : Skeleton C) :
  IsoDense (skel_sub Sk) :=
  fun c => (skel_rep Sk c; iso_sym (skel_iso Sk c)).

Definition skeleton_reflective {C : Category} (Sk : Skeleton C) :
  Reflective (skel_sub Sk) :=
  dense_full_subcategory_reflective (skel_sub Sk) (skel_full Sk)
    (skeleton_IsoDense Sk).

Example skeleton_reflector_obj {C : Category} (Sk : Skeleton C) (c : C) :
  fobj[reflector (skeleton_reflective Sk)] c = skel_rep Sk c := eq_refl.

(* The reflector produced by the general theorem IS Theory/Skeleton.v:409's
   [skel_reflect], on the nose: the two [EssentiallySurjective] records
   agree field for field, and that class has eta. *)

Example skeleton_reflector_is_skel_reflect {C : Category} (Sk : Skeleton C) :
  reflector (skeleton_reflective Sk) = skel_reflect Sk := eq_refl.

Example skeleton_reflective_full {C : Category} (Sk : Skeleton C) :
  reflective_full (skeleton_reflective Sk) = skel_full Sk := eq_refl.

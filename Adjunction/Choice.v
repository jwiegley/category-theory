Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * Choosing right adjoints functorially *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/mate
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
     "Transformations of Adjoints", book p. 102 (PDF p. 111), Exercise 3.
     Item id [maclane:IV.7:ex3].

   THE EXERCISE, VERBATIM:

     3. In the functor category A^X let S be that full subcategory with
     objects those functors F : X → A which have a right adjoint
     RF : A → X.  Make R a functor S^op → X^A by choosing one RF for each
     F, with Rσ the conjugate of σ.

   LETTERS.  Mac Lane's F : X → A is a left adjoint, so his X is this
   file's D and his A is this file's C -- the convention Instance/Adj.v
   and Instance/Adj/Forgetful.v already fixed, where A^X is [D, C] (where
   left adjoints live) and X^A is [C, D] (where right adjoints live).  So
   S is a subcategory of [D, C] and R runs S^op ⟶ [C, D].  "Conjugate" is
   his §IV.7 Definition 2, formalized in Adjunction/Conjugate.v.

   WHAT IS DELIVERED.

   (A) [HasRightAdjoint F := ∃ U : C ⟶ D, F ⊣ U].  The `∃` of this
       library is [sigT], so a membership proof IS a chosen right adjoint
       together with a chosen adjunction: DATA, not a bare existential.
       That is the whole reason no choice principle is consumed anywhere
       below -- "choosing one RF for each F" is not a choice function
       applied to a proposition, it is the projection [adjobj_right] out
       of data the object already carries -- and it is what makes every
       [Print Assumptions] in this file report "Closed under the global
       context".  [LeftAdjSub C D : Subcategory ([D, C])] cuts [D, C] by
       that predicate with [shom := fun _ _ _ _ _ => True], the tree's
       full-subcategory idiom (Instance/Rng.v's [CRng_Sub],
       Instance/Ab/TorsionFree.v's [TorsionFree_Sub], and the two prior
       subcategories OF A FUNCTOR CATEGORY, Functor/Representable/
       Functorial.v:305's [ReprSubcat] and Instance/Ab/ModFunctor.v:206's
       [AbFunAdd_sub], the latter written in the same five-line
       [@Build_Subcategory] form as [LeftAdjSub]; measured, none is cut
       by a right-adjoint predicate, and [HasRightAdjoint] occurs in no
       other file), so it is FULL, and
       [LeftAdjCat C D := Sub ([D, C]) (LeftAdjSub C D)] is Mac Lane's S.

       THE PIVOT OF THE FILE IS ONE [eq_refl]: [leftadj_obj] records that
       [obj[LeftAdjCat C D] = AdjObj C D] on the nose.  Both are
       {F & {U & F ⊣ U}}, so an object of S IS an object of #395's
       category of adjunctions, and every accessor of Instance/Adj.v
       ([adjobj_left], [adjobj_right], [adjobj_adj]) applies to it with
       no coercion, no transport and no comparison map.

   (B) [RightAdjointFunctor C D : Opposite (LeftAdjCat C D) ⟶ [C, D]] --
       the issue's pinned name.  Object part [adjobj_right], the chosen
       right adjoint; arrow part [conj_mate], the conjugate of σ.  The
       contravariance is expressed by taking Construction/Opposite.v's
       opposite LITERALLY as the source, exactly as
       Instance/Adj/Forgetful.v does for [AdjForgetRight]; an arrow
       x ⟶ y of the opposite IS an arrow y ⟶ x of S, whose first
       projection is a σ : F_y ⟹ F_x, and [conj_mate] of that runs
       U_x ⟹ U_y, which is the direction the functor needs.

   (C) The comparison with #395: [SubToAdj], [AdjToSub], the two
       identifications ([RightAdjointFunctor] against [AdjForgetRight]
       transported, and [AdjForgetLeft ◯ SubToAdj] against the
       subcategory inclusion), fullness, faithfulness, essential
       surjectivity, the equivalence, and the STRICTCAT ISOMORPHISM
       [SubAdj_strict_iso].

   (D) Independence of the choice, in BOTH readings: (a) two membership
       proofs for one F give isomorphic OBJECTS of S, and
       [RightAdjointFunctor] carries that isomorphism to the mate of the
       identity; (b) a CHOICE FUNCTION as an explicit argument, with
       [choice_independence] saying any two choices give naturally
       isomorphic functors.

   (E) Non-vacuity at a named pair of categories: [LeftAdjCat _2 _2] is
       inhabited by an adjunction that is not the identity one, and
       [LeftAdjSub _2 _2] is PROPER -- some functor _2 ⟶ _2 has no right
       adjoint.

   WHY S AND NOT [Adj C D].  The two are isomorphic categories (C), so
   one might state the exercise over #395's [Adj C D] instead.  That
   would lose the exercise's sentence.  An arrow of S is a BARE σ (the
   [Sub] hom is {σ & True}), so "with Rσ the conjugate of σ" is a genuine
   CHOICE, made by [conj_mate] and justified by [conjugate_conj_mate];
   over [Adj C D] the conjugate is carried as a field of the arrow and
   there is nothing left to choose.  S is what the book asks for.

   THE ISSUE'S "Current state" IS STALE, SENTENCE BY SENTENCE.

   • "Absent." -- true of the FILE and of the subcategory only.  A
     whole-word sweep for [RightAdjointFunctor] over every `*.v` outside
     this one and its probe finds none, and no subcategory of a functor category
     cut by "has a right adjoint" exists.  But the arrow part, the
     object part and both functor laws were all in tree before this
     file.

   • "The closest in-tree analogue of the arrow part is the mate operator
     (Theory/Bicategory/Mates.v:486 ...)" -- both cited lines are
     accurate but the conclusion is not.  The closest analogue is not
     bicategorical at all: Adjunction/Conjugate.v:333's
     [conj_mate (A : F ⊣ U) (A' : F' ⊣ U') (σ : F' ⟹ F) : U ⟹ U'] IS the
     arrow part, over arbitrary C and D and with no bicategorical
     machinery.  Every [fmap] below is that constant.

   • "What is entirely missing is ... the choice of a right adjoint on
     objects, and the two functor laws." -- the first clause (the
     subcategory) is right; these two are not.
     Instance/Adj/Forgetful.v:106's [AdjForgetRight C D] already has
     [fobj := adjobj_right] -- the chosen right adjoint, objects of
     [Adj C D] carrying the choice as data -- with both functor laws
     beside it, and the two laws in the form this file consumes are
     Adjunction/Conjugate.v:491's [conj_mate_id] and :494's
     [conj_mate_compose].

   • Not in the issue at all, and the strongest prior art:
     Adjunction/Parameter.v (#396) already builds a functor of exactly
     this shape.  Its [pa_param_mate] (:452) IS [conj_mate],
     [pa_param_mate_id] (:541) ends in [conj_mate_id],
     [pa_param_mate_comp] (:549) in [conj_mate_compose], and
     [parametrized_right_adjoint_bifunctor] (:577) is the packaging.
     The only difference from this file is the source category.

   • "Theory/Bicategory/Mates.v:52-56 explicitly descopes mate
     functoriality (descope ledger entry 10), which is exactly the
     identity and composition laws this exercise needs." -- the citation
     is accurate, the conclusion is not, and the DoD box that hangs on it
     is answered NOT DISCHARGED below.

   THE MATES DESCOPE IS NOT DISCHARGED HERE, AND Theory/Bicategory/Mates.v
   WAS NOT EDITED BY THIS FILE.  Descope ledger entry 10
   (doc/plan/00-CONVENTIONS.md:579-581, "Mates beyond the bijection")
   descopes the double category of
   adjunctions and PASTING functoriality of mates in an ARBITRARY
   BICATEGORY.  What this exercise needs is VERTICAL composition at
   IDENTITY bounding cells in ordinary category theory, which #394
   already supplied; Adjunction/Conjugate.v:92-97 states in terms that
   [conjugate_id]/[conjugate_compose] "are the identity-bounding-cell
   shadow of the pasting functoriality that Mates.v deliberately leaves
   out of scope" and that "they do not discharge that entry".  So there
   was nothing for this file to update, and it updated nothing.
   (Instance/Adj/Bicategory.v (#399) later narrows Mates.v's note, on the
   strength of its own Cat-level bifunctoriality result, again without
   discharging the entry.)

   THE REVIEWER CHECKS.

   • No choice axiom.  Every constant of this file reports "Closed under
     the global context"; the [make print-assumptions] gate carries them
     all, fully qualified.  The mechanism is (A) above: membership is
     [sigT] data.

   • The composition law is proved FOR CONJUGATES, not inherited.
     [RightAdjointFunctor]'s three obligations are discharged by
     [conj_mate_respects], [conj_mate_id] and [conj_mate_compose] BY
     NAME, and those three are Conjugate.v's own results, proved there
     out of [conjugate_id]/[conjugate_compose] through [conj_mate_uniq]
     rather than out of any law of [D, C].  That this is non-vacuous was
     MEASURED on this very definition rather than assumed: recompiled in
     a scratch copy with the library's default obligation tactic
     (Lib/Tactics.v:225) in force and no obligation written,
     [Obligations.] reports "3 obligation(s) remaining", listing the
     [Proper] of [fmap], the identity law and the composition law, and
     the section close then breaks with "Unsolved obligations".  So
     automation closes NONE of the three.  Hence the [#[local]
     Obligation Tactic := intros] at the top of this file, which makes
     all three visible.

   STRENGTHS, MEASURED STRICT FIRST.  These [eq_refl] identifications
   HOLD and are shipped as [Example]s: the object pivot [leftadj_obj];
   the arrow action of [RightAdjointFunctor] and its value at an identity
   ([raf_fmap_variance], [raf_id_is_conj_mate_id]); BOTH actions of BOTH
   comparisons in (C) ([raf_obj_via], [raf_map_via], [incl_obj_via],
   [incl_map_via]); both OBJECT round trips of [SubToAdj]/[AdjToSub]
   ([rt_adj_obj], [rt_sub_obj]); both legs of the membership isomorphism
   read through [RightAdjointFunctor] ([raf_choice_iso_to],
   [raf_choice_iso_from]); the three projections of the canonical choice
   ([ch_canonical_left], [ch_canonical_right], [ch_canonical_adj]); and
   in (E) the value of [RightAdjointFunctor] at the concrete object.

   SEVEN identifications are REFUTED at [eq_refl] and are pinned from
   OUTSIDE this file, in Test/ProbeChoice397.v -- an in-file negative
   renames in lockstep with the constant it guards, and every negative
   here would additionally be a [make todo] hit, which the DoD box
   forbids.  All seven are CONVERSION (each error ends in an explicit
   "cannot unify" between two inhabitants of one type; none carries a
   universe clause and none is a bare has-type mismatch), and each was
   stripped and compiled ALONE with its whole error read:

     1. [RAF_via C D = RightAdjointFunctor C D] -- while BOTH data fields
        agree at [eq_refl], so the difference is confined to the three
        rebuilt [Functor] law fields.
     2. [LI_via C D = Incl ([D, C]) (LeftAdjSub C D)] -- likewise.
     3. [fmap[SubToAdj ◯ AdjToSub] f = f] -- the composite rebuilds
        [conj_right] as the mate of [conj_left], equal to the original
        only up to `≈` (Instance/Adj.v's [conj_pair_right_unique]).
     4. [fmap[AdjToSub ◯ SubToAdj] f = f] -- the composite returns
        (`1 f; I), and stdlib [sigT] has no definitional eta here
        (Lib/Foundation.v's [Set Primitive Projections] does not cover
        it), so this is not definitional even though [I : True] is the
        only inhabitant.
     5. [LeftAdjCat C D = Adj C D] -- the negative that keeps
        [SubAdj_strict_iso] from being vacuous: the isomorphism relates
        two genuinely DIFFERENT categories, S's hom being {σ & True} and
        [Adj]'s the record [ConjPair].
     6. [ch_obj (ch_canonical C D) x = x] -- [sigT] eta again: the three
        PROJECTIONS of the object return on the nose ([ch_canonical_left],
        [ch_canonical_right], [ch_canonical_adj]) while the sigma itself
        does not, and no constant compares the FUNCTOR
        [RightAdjointFunctor_ch] at the canonical choice with
        [RightAdjointFunctor] at any strength.
     7. The inverse law of the membership isomorphism,
        [raf_choice_inverse], which holds up to `≈` and not at
        [eq_refl]: the composite of the two mates of the identity is
        [nat_id] only after [conj_mate_compose], an identity
        cancellation and [conj_mate_id].

   The probe pins two further KINDS beside those seven: the covariant
   ascription [LeftAdjCat C D ⟶ [C, D] := RightAdjointFunctor C D] as a
   TYPING negative (a plain has-type mismatch, no "cannot unify", no
   universe clause, with the contravariant ascription accepted beside
   it), and the eight FORMABILITY rejections of the universe paragraph
   below -- seventeen pinned commands in all, one instrument check and
   sixteen negatives.  The probe also MEASURED that spelling the
   covariant ascription through [Program] is a false pass: [Program]
   accepts it and defers the variance mismatch into the obligation
   [(LeftAdjCat C D)^op = LeftAdjCat C D], a Leibniz equality of
   categories, so the variance is pinned by the two [eq_refl] readbacks
   above and by a plain ascription in the probe, never through
   [Program].

   [SubAdj_strict_iso] IS AN ISOMORPHISM OF CATEGORIES, NOT MERELY AN
   EQUIVALENCE, and the distinction is the tree's own: `≅[Cat]` in this
   library IS equivalence (Instance/Cat.v's hom-setoid is
   [Functor_Setoid]), whereas `≅[StrictCat]` compares functors by
   [Functor_StrictEq_Setoid] (Theory/Functor.v:606), which asks for
   Leibniz equality on OBJECTS and `≈` on MORPHISMS.  Refutations 3 and 4
   above therefore do not obstruct it: both object families are
   [fun x => eq_refl], the [Adj]-side morphism clause is
   [conj_mate_uniq] applied to [conj_pair_law], and the S-side clause is
   [reflexivity].  So the strict isomorphism is available even though
   neither arrow round trip is definitional, and [SubToAdj_Equivalence]
   is the weaker reading kept alongside because [SubToAdj_Full] is where
   [conj_mate_uniq] is spent.

   CONSTANTS.  79, under this criterion: [Print Module
   Category.Adjunction.Choice] with its output WHITESPACE-FLATTENED,
   counting the [Definition] and [Parameter] heads (44 + 35).  The
   [.glob] records 56 declaration heads (41 [def], 3 [inst], 12 [prf]);
   the difference, 23, is exactly the [Program] obligations, which no
   source sweep and no [.glob] sweep sees.  All 79 report "Closed under
   the global context" with zero [Axioms:] lines, each queried FULLY
   QUALIFIED, and all 79 are in the [make print-assumptions] gate, so
   the closure is permanent rather than a one-time measurement.  The
   file declares no [Record], [Class] or [Inductive], so there is no
   unlisted [Build_*].  Zero name collisions: every one of the 79 names
   was swept whole-word over every `*.v` outside this file and its
   probe, one at a time, and returns no file; the sweep was
   instrument-checked at [Full] (95 files) and [Monoid] (92).

   UNIVERSES, off BOTH binder and block, over all 79.  NOT ONE of the 79
   constraint blocks contains a universe EQUATION -- every entry is `<`
   or `<=` -- so reading the blocks alone reports no identification and
   is wrong.  The identification sits ENTIRELY IN THE BINDER: across all
   127 [Category@{o h p}] instances printed by [About] over the 79
   records, h and p are the SAME level variable without exception, and
   in every constant binding two categories ONE level variable fills all
   FOUR hom-and-proof slots -- C's hom, C's proof, D's hom, D's proof --
   with the two OBJECT universes free of it and of each other.  So the
   profile is [C : Category@{o1 h h}], [D : Category@{o2 h h}].  Nothing
   here introduces either identification: [conj_mate] and
   [AdjForgetRight] APPLIED AT REAL ARGUMENTS carry the identical
   profile.  hom = proof has FOUR independent donors -- [Opposite],
   [Subcategory], [Fun] and [Adjunction], each rejected alone at levels
   declared apart while [x ~> y], [id[x]], [Du ⟶ Cu] and [Cu ⟶ Du] are
   all accepted there, so [Functor] is NOT a donor -- and the collapse
   of C's hom level onto D's has TWO independent causes, [Fun] alone and
   the mere presence of functors in BOTH directions ([Au ⟶ Bu] accepted
   at levels declared apart, [Bu ⟶ Au] rejected).  [AdjObj], [Adj],
   [HasRightAdjoint], [LeftAdjSub] and [RightAdjointFunctor] are all
   rejected there too, but each of their bodies already contains one of
   the four, so none can be tested apart from them and none is claimed
   independent.  None is claimed unavoidable.  Word-bounded [Set] occurs
   in the constraint block of 13 of the 79 records and in the printed
   type of 7, and ALL of them are in section (E); sections (A)-(D) carry
   none anywhere.  It is inherited, not introduced: Instance/Two.v:111
   declares [TwoHom : TwoObj → TwoObj → Set], so [_2] is a
   [Category@{_ Set Set}] and [TwoConst] reads
   [Functor@{u1 Set Set u2 Set Set}] -- read that attribution at its
   measured width: nine of the 13 carry a genuine [Set < u] on one of
   their own levels, while the other four ([TwoConst], its second
   obligation, [two_arrows_agree], [two_const_functors_differ]) carry
   only the stdlib bounds [Set < Basics.flip.u*], which nothing
   measured ties to [TwoHom].

   COST.  Transitive in-project closure 29 modules excluding this file,
   measured over .Makefile.coq.d.  Marginals, by dropping one [Require]
   at a time: [Construction/Subcategory] 1, [Functor/Opposite] 1,
   [Instance/Adj/Forgetful] 1, [Instance/StrictCat] 1, [Instance/Two] 1,
   [Theory/Equivalence/FullFaithful] 1, and every other [Require] 0 --
   including [Instance/Sets], whose marginal is 0 and which is
   nevertheless REQUIRED: without that line the file stops at (E)'s
   [two_const_hom_iso] with "The reference Sets was not found", the
   category being named there by its bare identifier.  Consuming #395 costs
   exactly +2 modules (27 without it).  The concrete witness in (E) was
   chosen on that measurement: against the same base of 28,
   [Instance/Two] costs 1 where [Adjunction/Diagonal/Product] costs 6,
   [Construction/Slice/Adjunction] 10, [Instance/Monoid/Translation] 13
   and [Adjunction/Diagonal/Limit] 39; and requiring
   Instance/Two/Monoidal.v for its [two_thin] would cost 17, against the
   three lines [two_arrows_agree] takes.

   TRANSPARENCY.  Exactly ONE [Defined.] terminator in the file, against
   33 [Qed.] terminators (counted with their period, so that prose
   mentions of the two words are excluded): [two_const_adj], which is
   [Defined] because it produces DATA (an [Adjunction] record).  It is
   NOT load-bearing -- flipped alone to
   [Qed] in a scratch copy the whole file still compiles, because every
   [eq_refl] readback in (E) reduces through [adjobj_right] and
   [adjobj_left], which are projections of the sigma and never reach the
   third component.  Every [Program] obligation is [Qed] (the tree's
   [Unset Transparent Obligations]), and no readback below depends on
   one.

   THE [make todo] BOX IS MET BY THIS FILE.  That target greps every
   `*.v` case-insensitively for a handful of tokens, and two of them
   are relevant here: the vernacular that pins a rejected command, and
   the verb the issue's own prose uses where Mac Lane writes "which
   have a right adjoint".  A negative written here would therefore be a
   hit, which is the second reason (after renaming) the seven
   refutations are pinned from the probe instead; and the book's phrase
   is used throughout in place of the issue's.  This file contributes
   ZERO hits, verified by running that grep over it.

   NOT DELIVERED.  No 2-categorical reading, and nothing relates this to
   Theory/Bicategory/Mates.v's bicategorical [mate] beyond the ledger
   sentence above -- the identification of [conj_mate] with [mate] at
   identity bounding cells is Instance/Cat/Bicategory/Conjugate.v's and
   is not restated.  No naturality of the choice isomorphism in C or D,
   and no functoriality of [ch ↦ RightAdjointFunctor_ch].  No comparison
   of [choice_independence]'s isomorphism with
   Theory/Adjunction.v:367's [right_adjoint_iso] (which is [Qed], so its
   components do not reduce); [choice_right_adjoints_iso] merely records
   that donor at a membership pair.  No comparison, at any strength, of
   [RightAdjointFunctor_ch C D (ch_canonical C D)] with
   [RightAdjointFunctor C D]: the canonical choice returns the OBJECT's
   three projections at [eq_refl] and nothing more.  No dual (a
   [LeftAdjointFunctor] on the subcategory of functors that have a LEFT
   adjoint).  Nothing is
   registered as an exported [Instance] except [SubToAdj_Faithful] and
   [SubToAdj_Full] ([SubToAdj_ESO] is local), and no chosen right
   adjoint is made globally resolvable.
   No claim that [LeftAdjSub] is replete or wide, and no identification
   of S's image in [D, C].  In (E), the concrete adjunction is exhibited
   at one pair of categories only, no second pair is measured, and the
   two constant functors are separated on OBJECTS -- inequality of the
   two functor RECORDS follows in one step but is not stated.  The DoD
   box asking for the 8.19 and 8.20 nix targets is answered by the nix
   triple run on the landing commit: the 9.1, 8.19 and 8.20 derivations
   all built with rc=0 and zero errors, both new files compiled under
   each. *)

(* ------------------------------------------------------------------ *)
(** ** (A) The full subcategory of the functors that have a right adjoint *)

(* "Has a right adjoint", as DATA: a chosen U together with a chosen
   adjunction.  `∃` is [sigT] here, so this is Mac Lane's "choosing one
   RF for each F" already made constructive -- there is nothing left for
   a choice principle to do. *)
Definition HasRightAdjoint {C D : Category} (F : D ⟶ C) : Type :=
  ∃ U : C ⟶ D, F ⊣ U.

(* Mac Lane's S: the FULL subcategory of A^X = [D, C] on those objects.
   [shom] is the terminal predicate, so every ambient transformation
   between selected functors is retained. *)
Definition LeftAdjSub (C D : Category) : Subcategory ([D, C]) :=
  @Build_Subcategory ([D, C])
    (fun F : D ⟶ C => HasRightAdjoint F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition LeftAdjCat (C D : Category) : Category :=
  Sub ([D, C]) (LeftAdjSub C D).

(* THE PIVOT.  An object of S IS an object of #395's category of
   adjunctions, on the nose: both are {F & {U & F ⊣ U}}. *)
Example leftadj_obj (C D : Category) : obj[LeftAdjCat C D] = AdjObj C D
  := eq_refl.

Definition LeftAdjSub_Full (C D : Category) :
  Category.Construction.Subcategory.Full ([D, C]) (LeftAdjSub C D) :=
  fun _ _ _ _ _ => I.

(* ------------------------------------------------------------------ *)
(** ** (B) R : S^op ⟶ X^A *)

(* Object part: the chosen right adjoint.  Arrow part: the conjugate.
   The three obligations are the three conjugate laws BY NAME; none of
   them is closed by the library's default obligation tactic. *)
Program Definition RightAdjointFunctor (C D : Category) :
  Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (x : AdjObj C D);
  fmap := fun x y f =>
            conj_mate (adjobj_adj (x : AdjObj C D))
                      (adjobj_adj (y : AdjObj C D)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. now apply conj_mate_id. Qed.
Next Obligation. now apply conj_mate_compose. Qed.

(* Two readbacks, and they are not the same kind.  The first records the
   ORIENTATION of the arrow action -- which [conj_mate] argument is which
   -- so that a later edit swapping them is caught here; it is a
   projection out of the transparent record and reads back the written
   body.  The second is not a projection: it computes the identity of
   [Opposite (LeftAdjCat C D)] all the way down to [nat_id].  Neither
   direction may be left to elaboration, because [Program] does NOT
   reject a swapped arrow action -- measured on this very definition, it
   defers the resulting type error into an obligation, and the breakdown
   surfaces only at the section close. *)
Example raf_fmap_variance (C D : Category)
        (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor C D] f
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (y : AdjObj C D)) (`1 f) := eq_refl.

Example raf_id_is_conj_mate_id (C D : Category)
        (x : Opposite (LeftAdjCat C D)) :
  fmap[RightAdjointFunctor C D] (@id (Opposite (LeftAdjCat C D)) x)
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (x : AdjObj C D)) nat_id := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (C) S against #395's category of adjunctions *)

(* Identity on objects; on an arrow, the bare σ is paired with its mate.
   This is literally Instance/Adj/Forgetful.v's [AdjForgetLeft_Full]
   [prefmap], read as a functor. *)
Program Definition SubToAdj (C D : Category) : LeftAdjCat C D ⟶ Adj C D := {|
  fobj := fun x => (x : AdjObj C D);
  fmap := fun x y f =>
            {| conj_left  := `1 f
             ; conj_right := conj_mate (adjobj_adj (y : AdjObj C D))
                                       (adjobj_adj (x : AdjObj C D)) (`1 f) |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ _). Qed.
Next Obligation.
  intros f g Hfg; split; simpl; [ exact Hfg | now apply conj_mate_respects ].
Qed.
Next Obligation. split; simpl; [ reflexivity | now apply conj_mate_id ]. Qed.
Next Obligation.
  split; simpl; [ reflexivity | now apply conj_mate_compose ].
Qed.

(* R IS #395's second forgetful functor transported along that
   comparison: both actions agree on the nose. *)
Definition RAF_via (C D : Category) : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  AdjForgetRight C D ◯ Opposite_Functor (SubToAdj C D).

Example raf_obj_via (C D : Category) (x : Opposite (LeftAdjCat C D)) :
  fobj[RAF_via C D] x = fobj[RightAdjointFunctor C D] x := eq_refl.

Example raf_map_via (C D : Category) (x y : Opposite (LeftAdjCat C D))
        (f : x ~> y) :
  fmap[RAF_via C D] f = fmap[RightAdjointFunctor C D] f := eq_refl.

(* And the first forgetful functor, composed the same way, IS the
   inclusion of the subcategory -- again on both actions. *)
Definition LI_via (C D : Category) : LeftAdjCat C D ⟶ [D, C] :=
  AdjForgetLeft C D ◯ SubToAdj C D.

Example incl_obj_via (C D : Category) (x : LeftAdjCat C D) :
  fobj[LI_via C D] x = fobj[Incl ([D, C]) (LeftAdjSub C D)] x := eq_refl.

Example incl_map_via (C D : Category) (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[LI_via C D] f = fmap[Incl ([D, C]) (LeftAdjSub C D)] f := eq_refl.

#[export]
Program Instance SubToAdj_Faithful (C D : Category) :
  Category.Theory.Functor.Faithful (SubToAdj C D).
Next Obligation. destruct X as [Hl _]; exact Hl. Qed.

(* Fullness is where [conj_mate_uniq] is spent: the chosen preimage of a
   conjugate pair is its σ, and recovering the pair needs that the mate
   is THE conjugate of that σ. *)
#[export]
Program Instance SubToAdj_Full (C D : Category) :
  Category.Theory.Functor.Full (SubToAdj C D) := {|
  prefmap := fun x y g => (conj_left g; I)
|}.
Next Obligation.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law g).
Qed.

(* Essential surjectivity is free: the two categories have the same
   objects, and typeclass resolution fills [eso_iso] with [iso_id]
   (Theory/Isomorphism.v), leaving no obligation.  It is [#[local]], as
   the tree's two other concrete [EssentiallySurjective] witnesses are
   (Instance/FdVect.v:884, Construction/Reflective/Idempotent.v:457):
   the class carries a CHOSEN preimage and must not become globally
   resolvable; [SubToAdj_Equivalence] below still finds it. *)
#[local]
Program Instance SubToAdj_ESO (C D : Category) :
  EssentiallySurjective (SubToAdj C D) := {|
  eso_obj := fun d => (d : LeftAdjCat C D)
|}.

Definition SubToAdj_Equivalence (C D : Category) :
  EquivalenceOfCategories (SubToAdj C D) := FF_ESO_Equivalence (SubToAdj C D).

Program Definition AdjToSub (C D : Category) : Adj C D ⟶ LeftAdjCat C D := {|
  fobj := fun x => (x : LeftAdjCat C D);
  fmap := fun x y f => (conj_left f; I)
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. simpl; reflexivity. Qed.

Example rt_adj_obj (C D : Category) (x : Adj C D) :
  fobj[SubToAdj C D ◯ AdjToSub C D] x = x := eq_refl.

Example rt_sub_obj (C D : Category) (x : LeftAdjCat C D) :
  fobj[AdjToSub C D ◯ SubToAdj C D] x = x := eq_refl.

(* The strongest available identification.  `≅[StrictCat]` is an
   ISOMORPHISM OF CATEGORIES; `≅[Cat]` would be only an equivalence. *)
Program Definition SubAdj_strict_iso (C D : Category) :
  @Isomorphism StrictCat (LeftAdjCat C D) (Adj C D) := {|
  to := SubToAdj C D; from := AdjToSub C D
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** (D)(a) Two choices for one F *)

(* The subcategory is full, so the ambient identity of F lifts twice and
   the two memberships give ISOMORPHIC objects of S. *)
Definition choice_iso_in_Sub (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) :
  ((F; p) : LeftAdjCat C D) ≅[LeftAdjCat C D] (F; q) :=
  Full_membership_iso ([D, C]) (LeftAdjSub C D) (LeftAdjSub_Full C D) F p q.

(* R carries that isomorphism to the mate of the identity, on the nose,
   on BOTH legs. *)
Example raf_choice_iso_to (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (to (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; q) : AdjObj C D))
                (adjobj_adj ((F; p) : AdjObj C D)) nat_id := eq_refl.

Example raf_choice_iso_from (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (from (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id := eq_refl.

(* The two chosen right adjoints are naturally isomorphic.  This is the
   in-tree [right_adjoint_iso] recorded at a membership pair; it is
   [Qed], so its components do not reduce, and nothing below uses it. *)
Definition choice_right_adjoints_iso (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) : `1 p ≈ `1 q :=
  right_adjoint_iso F (`1 p) (`1 q) (`2 p) (`2 q).

(* The inverse law holds up to `≈` and not on the nose: it is
   [conj_mate_compose] followed by [conj_mate_id], with one
   identity-cancellation between them. *)
Lemma raf_choice_inverse (C D : Category) (F : D ⟶ C)
      (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  ≈ nat_id.
Proof.
  rewrite <- conj_mate_compose.
  transitivity (conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                          (adjobj_adj ((F; p) : AdjObj C D)) nat_id).
  - apply conj_mate_respects; intro a; simpl; cat.
  - now apply conj_mate_id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** (D)(b) A choice function as an explicit argument *)

(* The two conjugate laws restated with [D, C]'s and [C, D]'s own
   composition and identity in place of `∙` and [nat_id].  [rewrite],
   unlike [apply], will not cross those delta steps, and these are the
   forms the obligations of a functor INTO a functor category present. *)
Lemma cm_comp_fun {C D : Category} {F1 U1 F2 U2 F3 U3}
      (A1 : @Adjunction C D F1 U1) (A2 : @Adjunction C D F2 U2)
      (A3 : @Adjunction C D F3 U3)
      (s : F2 ⟹ F1) (s' : F3 ⟹ F2) :
  @compose ([C, D]) _ _ _ (conj_mate A2 A3 s') (conj_mate A1 A2 s)
    ≈ conj_mate A1 A3 (@compose ([D, C]) _ _ _ s s').
Proof. symmetry; now apply conj_mate_compose. Qed.

Lemma cm_id_fun {C D : Category} {F1 U1} (A1 : @Adjunction C D F1 U1) :
  conj_mate A1 A1 (@id ([D, C]) F1) ≈ @id ([C, D]) U1.
Proof. now apply conj_mate_id. Qed.

(* Mac Lane's "choosing one RF for each F", quantified: a function
   re-choosing a right adjoint for every member of S.  The name avoids
   the taken [Choice]. *)
Definition RightAdjChoice (C D : Category) : Type :=
  ∀ F : D ⟶ C, HasRightAdjoint F → HasRightAdjoint F.

Definition ch_obj {C D : Category} (ch : RightAdjChoice C D)
           (x : LeftAdjCat C D) : AdjObj C D := (`1 x; ch (`1 x) (`2 x)).

Program Definition RightAdjointFunctor_ch (C D : Category)
        (ch : RightAdjChoice C D) : Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (ch_obj ch x);
  fmap := fun x y f =>
    conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. apply cm_id_fun. Qed.
Next Obligation. symmetry; apply cm_comp_fun. Qed.

Lemma raf_ch_fmap (C D : Category) (ch : RightAdjChoice C D)
      (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor_ch C D ch] f
    = conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f).
Proof. reflexivity. Qed.

Definition ci_to (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch x) ~{[C, D]}~> adjobj_right (ch_obj ch' x) :=
  conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch' x))
            (@id ([D, C]) (`1 x)).

Definition ci_from (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch' x) ~{[C, D]}~> adjobj_right (ch_obj ch x) :=
  conj_mate (adjobj_adj (ch_obj ch' x)) (adjobj_adj (ch_obj ch x))
            (@id ([D, C]) (`1 x)).

Program Definition ci_iso (C D : Category) (ch ch' : RightAdjChoice C D)
        (x : LeftAdjCat C D) :
  @Isomorphism ([C, D]) (adjobj_right (ch_obj ch x))
                        (adjobj_right (ch_obj ch' x)) := {|
  to := ci_to C D ch ch' x; from := ci_from C D ch ch' x
|}.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch' x))
                          (adjobj_adj (ch_obj ch' x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch x))
                          (adjobj_adj (ch_obj ch x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.

(* These two readbacks exist because [rewrite] must get past [to] and
   [from] of a [Program]-built isomorphism; note also that [simpl] must
   NOT be run before the [cm_comp_fun] rewrites below, since it unfolds
   [conj_mate] and destroys the pattern. *)
Lemma ci_iso_to_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : to (ci_iso C D ch ch' x) = ci_to C D ch ch' x.
Proof. reflexivity. Qed.

Lemma ci_iso_from_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : from (ci_iso C D ch ch' x) = ci_from C D ch ch' x.
Proof. reflexivity. Qed.

(* INDEPENDENCE OF THE CHOICE.  Any two choice functions give naturally
   isomorphic functors -- `≈` at [C, D]'s functor setoid is exactly a
   natural isomorphism.  The components are mates of identities and the
   naturality square is [conj_mate_compose] read twice, once on each
   side; no property of either choice is used. *)
Theorem choice_independence (C D : Category) (ch ch' : RightAdjChoice C D) :
  RightAdjointFunctor_ch C D ch ≈ RightAdjointFunctor_ch C D ch'.
Proof.
  exists (ci_iso C D ch ch').
  intros x y f.
  rewrite ci_iso_to_eq, ci_iso_from_eq, !raf_ch_fmap.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  rewrite cm_comp_fun.
  apply conj_mate_respects.
  intro a; simpl; cat.
Qed.

(* (a) is (b) at the canonical choice: keep the adjoint the object
   already carries.  The three projections return on the nose. *)
Definition ch_canonical (C D : Category) : RightAdjChoice C D := fun _ h => h.

Example ch_canonical_left (C D : Category) (x : LeftAdjCat C D) :
  adjobj_left (ch_obj (ch_canonical C D) x) = adjobj_left (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_right (C D : Category) (x : LeftAdjCat C D) :
  adjobj_right (ch_obj (ch_canonical C D) x) = adjobj_right (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_adj (C D : Category) (x : LeftAdjCat C D) :
  adjobj_adj (ch_obj (ch_canonical C D) x) = adjobj_adj (x : AdjObj C D)
  := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (E) Non-vacuity: S is inhabited and proper at the walking arrow *)

(* [_2] is thin, so any two parallel arrows coincide; the three-line
   proof is from Instance/Two.v's own [TwoHom_inv] and
   [TwoHom_Y_X_absurd].  (Instance/Two/Monoidal.v:30 has the same lemma
   under the name [two_thin]; requiring that module would cost 17
   modules against the base of 28, that is, in place of Instance/Two --
   measured.) *)
Lemma two_arrows_agree {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof.
  destruct x, y;
    try (now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g)).
  exact (False_rect _ (TwoHom_Y_X_absurd f)).
Qed.

Program Definition TwoConst (a : TwoObj) : _2 ⟶ _2 := {|
  fobj := fun _ => a;
  fmap := fun _ _ _ => @id _2 a
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. apply two_arrows_agree. Qed.

Definition two_to_Y (x : TwoObj) : x ~{_2}~> TwoY :=
  match x with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_from_X (y : TwoObj) : TwoX ~{_2}~> y :=
  match y with TwoX => TwoIdX | TwoY => TwoXY end.

#[local] Obligation Tactic := repeat intro; apply two_arrows_agree.

(* Every hom-set in sight is a singleton: _2(TwoX, y) is inhabited for
   every y and _2(x, TwoY) for every x, and _2 is thin. *)
Program Definition two_const_hom_iso (x y : TwoObj) :
  @Isomorphism Sets
    {| carrier := @hom _2 (fobj[TwoConst TwoX] x) y
     ; is_setoid := @homset _2 (fobj[TwoConst TwoX] x) y |}
    {| carrier := @hom _2 x (fobj[TwoConst TwoY] y)
     ; is_setoid := @homset _2 x (fobj[TwoConst TwoY] y) |} := {|
  to   := {| morphism := fun _ => two_to_Y x |};
  from := {| morphism := fun _ => two_from_X y |}
|}.

#[local] Obligation Tactic := intros.

(* The constant functor at TwoX is left adjoint to the constant functor
   at TwoY -- an adjunction between two functors neither of which is the
   identity. *)
Definition two_const_adj : TwoConst TwoX ⊣ TwoConst TwoY.
Proof.
  apply (@Build_Adjunction' _2 _2 (TwoConst TwoX) (TwoConst TwoY)
                            two_const_hom_iso);
  intros; apply two_arrows_agree.
Defined.

Definition two_left_adjoint_object : LeftAdjCat _2 _2 :=
  (TwoConst TwoX; (TwoConst TwoY; two_const_adj)).

(* R at that object returns the chosen right adjoint, on the nose. *)
Example two_raf_value :
  fobj[RightAdjointFunctor _2 _2] two_left_adjoint_object = TwoConst TwoY
  := eq_refl.

(* Not a degenerate witness: the two constant functors differ, and the
   left adjoint of the object is not the identity functor. *)
Lemma two_const_functors_differ :
  fobj[TwoConst TwoX] TwoX = fobj[TwoConst TwoY] TwoX → False.
Proof. discriminate. Qed.

Lemma two_left_adjoint_not_identity :
  fobj[adjobj_left two_left_adjoint_object] TwoY = fobj[Id[_2]] TwoY → False.
Proof. discriminate. Qed.

(* PROPERNESS.  The constant functor at TwoY has no right adjoint: from
   an adjunction, the inverse transpose of the identity of R(TwoX) is an
   arrow TwoY ~> TwoX, and there is none. *)
Lemma two_const_Y_no_right_adjoint (R : _2 ⟶ _2)
      (A : TwoConst TwoY ⊣ R) : False.
Proof.
  exact (TwoHom_Y_X_absurd
           (from (@adj _2 _2 (TwoConst TwoY) R A (fobj[R] TwoX) TwoX)
                 (@id _2 (fobj[R] TwoX)))).
Qed.

Lemma two_left_adjoint_proper : HasRightAdjoint (TwoConst TwoY) → False.
Proof. intros [R A]; exact (two_const_Y_no_right_adjoint R A). Qed.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Open Scope category_scope.

(** * The category of setoids is an elementary topos *)

(* Book:      Mac Lane, Categories for the Working Mathematician, 2nd
              ed., §IV.10, printed p. 107 (PDF p. 116)
              ([maclane:IV.10:remark1]).  Verbatim, from the rendered
              page:

                "The category Sets of all (small) sets is a topos and so
                 is the category Sets^{C^op} of all set-valued
                 contravariant functors on a small category C."

   Book:      Mac Lane, ibid., Appendix "Foundations", §App.1, printed
              pp. 289-290 (PDF pp. 295-296) ([maclane:App.1:remark1]).
              Verbatim, from the rendered pages.  His axioms 8 and 9,
              printed p. 289:

                "An elementary topos is a category with a certain
                 additional structure: terminal object, pullbacks,
                 truth, a subobject classifier, and power objects (sets
                 of subsets)."

                "8. Truth.  There is an object Ω (the object of truth
                 values) and a monomorphism t : 1 → Ω called truth; to
                 any monomorphism m : a → b, there is a unique arrow
                 ψ : b → Ω such that the following square is a
                 pullback:"                                          (2)

                "9. Power objects.  To each object b, there is an
                 associated object P b and an arrow ε_b : b × P b → Ω
                 such that for every arrow f : b × a → Ω there is a
                 unique arrow g : a → P b for which the following
                 diagram commutes:"                                  (3)

              and the four witnesses, printed p. 290:

                "To understand these axioms, we observe how they apply
                 to the usual category of all sets.  There, any set with
                 just one element can serve as a terminal object 1,
                 because each set a has a unique function a → 1 to 1.
                 For two sets a and b, the pullback of two arrows
                 a → 1 ← b is then the usual set-theoretic product, with
                 its projections to the given factors a and b."

                "For truth values, take the object Ω to be any set 2
                 consisting of two objects, 1 and 0, while the
                 monomorphism t : 1 → 2 is just the usual inclusion of 1
                 in 2.  Then a monomorphism m : a → b, as in Axiom 8, is
                 a subset a of b.  This subset has a well-known
                 characteristic function ψ : b → 2 with ψ(y) = 1 or 0
                 according as the element of y of b is or is not in the
                 subset a.  This produces the pullback (2) above."

                "Axiom 9 describes P b, the set of all subsets s of b,
                 often called the "power set" P b.  Indeed, one can then
                 set ε_b(x, s) = 0 if the element x of b is in the
                 subset s and equal to 1 otherwise.  This does give a
                 pullback, as in (3) above."

                "These axioms for a topos then hold for the category of
                 sets."

   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   TWO NOTES ON THE PRINTED PAGE, BOTH LEFT AS THEY STAND.

   First, "according as the element of y of b is or is not in the subset
   a" is the book's own wording, transcribed verbatim; the sense is
   plainly "the element y of b".

   Second, and this one matters for the reading of clause (d): THE PAGE
   IS INTERNALLY INCONSISTENT ABOUT WHICH TRUTH VALUE MEANS MEMBERSHIP.
   Two sentences apart it says "ψ(y) = 1 or 0 according as the element
   of y of b is or is not in the subset a" and "ε_b(x, s) = 0 if the
   element x of b is in the subset s and equal to 1 otherwise" -- 1 for
   membership under ψ, 0 for membership under ε_b, on one page.  The
   issue's paraphrase silently corrects the second to "ε_b(x, s) = 1 iff
   x ∈ s".  BOTH SENTENCES ARE QUOTED ABOVE AND NEITHER IS RESOLVED
   HERE.  Nothing below depends on the choice: the naming of the truth
   value is a convention, and this tree's convention is recorded, with
   its own measurements, in Instance/Sets/Classifier/OneLevel.v and
   Instance/Fun/Classifier.v.  What IS delivered is the classifying
   rule in the form those two files prove it -- section (C)'s
   [app1_char_rule_U] and [app1_char_rule_dec], which say that the
   characteristic map takes the value [truth] exactly on the image.

   WHAT IS DELIVERED.  THREE inhabitants of
   [ElementaryTopos Sets@{o so}], each CONDITIONAL on one hypothesis.
   Read the three apart carefully: [Sets_Topos_IEM] IS [Sets_Topos] at
   [eq_refl] (the table below writes it as the [:=] it is), so it shares
   BOTH its truth object and its power object and differs only in the
   hypothesis it takes; [Sets_Topos_dec] is the one that differs in
   both, and in its reach:

     Sets_Topos     (U : Untruncate@{o})   Ω = Powerset_Omega
     Sets_Topos_dec (D : DecImage@{o so})  Ω = BoolSetoid   -- Mac Lane's 2
     Sets_Topos_IEM (E : IEM@{o})          := Sets_Topos (untruncate_of_IEM E)

   together with Mac Lane's four App.1 witnesses at each measured
   strength, in sections (B)-(E).  All three bundles are plain
   [Definition]s, all three are Closed under the global context, and
   there is no obligation and no tactic in any of them.

   THE ROUTE IS PURE ASSEMBLY: five fields, five pre-existing donors,
   NOTHING re-proved.

     topos_terminal    Instance/Sets.v:258's           [Sets_Terminal]
     topos_cartesian   Instance/Sets/Cartesian.v:32's  [Sets_Cartesian]
     topos_pullbacks   Instance/Sets/Pullback.v:393's  [Sets_HasPullbacks]
     topos_closed      Instance/Sets/Cartesian/Closed.v:38's [Sets_Closed]
     topos_classifier  Instance/Sets/Classifier/OneLevel.v:642's
                       [Sets_Classifier] (:814's [Sets_Classifier_dec]
                       on the decidable route)

   Instance/FinSet/Topos.v is NOT offered as a witness for anything
   here, and is not required by this file: the issue's reviewer check
   asks for exactly that, and its sibling Instance/Fun/Topos.v says the
   same on the presheaf side.

   WHY PLAIN [Definition]s AND NOT [Instance]s.  Instance/FinSet/Topos.v
   gives the reason and it is followed: the five [topos_*] projections
   are [#[export] Existing Instance]s, so registering a bundle would
   give typeclass search a second, convergent path to each component.
   MEASURED, at [Sets], in both directions: (i) the five projections ARE
   in the instance database, so FinSet's reason genuinely applies here
   -- [Print HintDb typeclass_instances] lists [simple apply
   @topos_terminal], [@topos_cartesian], [@topos_pullbacks],
   [@topos_closed] and [@topos_classifier]; and (ii) the harm is not
   observable today, because with the bundle registered globally all
   four unconditional components still resolve to the DIRECT instances
   and [@SubobjectClassifier Sets Sets_Terminal] still does not resolve,
   [Untruncate] being a [Definition] and not a [Class], so the
   [topos_classifier] path ends in an unresolvable metavariable.  Both
   readings are stated because either alone would mislead.  NOT
   MEASURED: whether the extra path costs search time.

   UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.

     Sets_Topos@{o so} :
       Untruncate@{o} → ElementaryTopos@{so so o} Sets@{o so}
       block: Set < o, o < so, plus stdlib bounds.

     Sets_Topos_IEM@{o so} : IEM@{o} → ElementaryTopos@{so so o} Sets@{o so}
       block: the same.

     Sets_Topos_dec@{o so} :
       DecImage@{o so} → ElementaryTopos@{so so o} Sets@{o so}
       block: o < so, plus stdlib bounds -- and NO [Set] at all.

     pullback_over_one_is_product@{o so} :
       ∀ a b : obj[Sets@{o so}], pbone@{o so} a b ≅ a × b
       block: o < so, plus stdlib bounds.

   Read four things off that.

   (1) NOT ONE CONSTRAINT IN ANY BLOCK OF THIS FILE IS AN EQUATION.
   Every entry is [<] or [<=].  That is worth stating because it was NOT
   free for section (B): written inside a [Section] with
   [Context (a b : Sets)], the same pullback development elaborates at
   [pullback_over_one_is_product@{u u0 u1 u2}] with TWO block equations
   ([u = u1] and [u0 = u2]) identifying the two objects' [Sets] with
   each other.  The annotated top-level form shipped below carries none.
   So here the annotation buys more than presentation -- it is what
   keeps the file equation-free -- unlike the bundles, where an
   unannotated body gives the same reading up to renaming.

   (2) NOTHING IS PINNED TO [Set].  [Set < o] is a strict LOWER bound
   and it is on the [Untruncate]/[IEM] route only, arriving from
   [Prop : Type@{Set+1}] through [Powerset_Omega].

   (3) THE TWO ROUTES DIFFER IN REACH, AND THAT IS THE POINT OF SHIPPING
   BOTH.  In a section declaring [Set < su], [Sets@{Set su}] is a
   category, its four unconditional donors are all accepted at
   [@{su Set}], and [Sets_Topos_dec@{Set su}] is ACCEPTED -- while
   [Sets_Classifier@{Set su}] and [Sets_Topos@{Set su}] are each refused
   with "Cannot enforce Set < Set because Set = Set".  So the decidable
   route reaches the [Sets] whose carrier universe is the literal [Set]
   and the truncation route does not.  Both refusals and the seven
   controls are pinned in Test/ProbeToposInstances404.v.  This
   corroborates at the TOPOS level what
   Instance/Sets/Classifier/OneLevel.v states at the classifier level.

   (4) THE CLASS'S OWN TWO COROLLARIES DO NOT BOTH REACH THIS TOPOS.
   [Pow] does; [relations_iso] does NOT, and neither does
   [classifier_classifies].  Both carry the bound [u <= u0] over
   [C : Category@{u u0 u0}] -- objects at or below homs -- while
   [Sets@{o so} : Category@{so o o}] has o < so, and
   [relations_iso] is built as [iso_compose exp_iso
   (classifier_classifies (a × b))], so it inherits the refusal.  Both
   are pinned in the probe, with [Pow] at this topos as the accepted
   control.  So this is a genuine [ElementaryTopos] at which one of
   Structure/Topos.v's own two derived constants is not statable, and
   docs/INHABITATION.md's row for those two constants keeps its
   FinSet-only witness column for exactly that reason.

   WHAT EACH CONSTANT CONSUMES.  Most of the file is assembly or
   conversion; only section (B) proves anything.

     Sets_Topos, _dec, _IEM   the five donors above; no tactic.
     app1_terminal_singleton  one [destruct] on [poly_unit].
     pbone_sq                 the terminal object's uniqueness, spent
                              NOT through [one_unique] but by a double
                              [destruct] -- see the gotcha below.
     pbone_from_prod          [ump_pullbacks] of [Sets_HasPullbacks],
                              nothing else.
     pullback_over_one_is_product
                              its FROM-TO law is the [unique_property]
                              of that same mediator, read at a point;
                              its TO-FROM law is [reflexivity] at a
                              point.  Neither inverse law is left to the
                              obligation tactic; both are written out.
     pbone_to_exl/_to_exr     [reflexivity] at a point -- the fork's two
                              projections reduce.
     pbone_from_fst/_from_snd the two halves of [unique_property].
     app1_truth_monic         [truth_monic] (Structure/SubobjectClassifier.v),
                              which is derived there, applied.
     app1_char_rule_U/_dec    [sets_classifier_char_iff] and
                              [sets_classifier_dec_char_iff]
                              (OneLevel.v:912/:920), applied verbatim at
                              the topos-level classifier; [:=] with no
                              tactic.
     app1_classifying_square  [char_pullback], re-exposed at the bundle.
     app1_classifying_unique  [char_unique], re-exposed at the bundle.
     every Example            conversion alone.

   ONE BUILDER GOTCHA, RECORDED BECAUSE IT COSTS TIME.  The square
   [pbone_sq : one ∘ exl ≈ one ∘ exr] cannot be supplied as
   [one_unique _ _]: the elaborator will not unify [@homset Sets]
   against [@SetoidMorphism_Setoid], and [apply one_unique] does not
   match the unfolded pointwise goal either.  What works is to go
   pointwise and [destruct] both composites, whose values inhabit
   [poly_unit].

   STRICT VERSUS [≈], MEASURED STRICT FIRST.

   TWENTY-TWO identifications hold at [eq_refl] and are shipped as
   [Example]s, and that is the whole count of [eq_refl] STATEMENTS
   below this header (the token occurs in this header several times
   more): the
   five field readbacks plus the decidable route's classifier; the
   terminal carrier and the terminal object itself; the chosen pullback
   of [a → 1 ← b] IS the section-(B) one; the mediator out of the
   product REDUCES to [sets_pb_med] (which is why
   Instance/Sets/Pullback.v's [Sets_IsPullback] being [Defined] matters
   here); Ω and [truth] on BOTH routes, with the decidable Ω's carrier
   [poly_bool]; the two [char] readbacks; the power object and its
   carrier on both routes; and membership as application on both routes.

   THE STRONGEST OF THOSE, and it is stronger than the brief expected:

     @Pow Sets (Sets_Topos U) b = Powerset_Prop_obj b   by [eq_refl]

   Mac Lane's "P b, the set of all subsets s of b" is DEFINITIONAL here,
   not an isomorphism.  The reason is that two files build the same
   record: Instance/Sets/Powerset.v:981's [Powerset_Prop_obj X] packages
   [SetoidMorphism X Powerset_Prop_truth] with [SetoidMorphism_Setoid],
   Instance/Sets/Cartesian/Closed.v:38's [exponent_obj x y] packages
   [SetoidMorphism x y] with the same, and
   Instance/Sets/Powerset/Universal.v:263 defines [Powerset_Omega] to BE
   [Powerset_Prop_truth].  So Ω^b and the power set are one term.

   ON THE DECIDABLE ROUTE THE POWER OBJECT IS THE **DECIDABLE** POWER
   SET, and that is measured both ways: its carrier IS
   [SetoidMorphism b BoolSetoid] at [eq_refl], and
   [@Pow Sets (Sets_Topos_dec D) b = Powerset_Prop_obj b] is REFUSED at
   [eq_refl] (a CONVERSION refusal, pinned in the probe).  NOT BUILT: no
   isomorphism between the two power objects, under [IEM] or otherwise,
   and no isomorphism between [BoolSetoid] and [Powerset_Omega].

   EVALUATION IS APPLICATION on both routes, at [eq_refl] -- with an
   ARGUMENT-ORDER DISCLOSURE, and with the reach of the two Examples
   stated exactly.  Mac Lane's ε_b : b × P b → Ω takes the ELEMENT
   first, ε_b(x, s); this tree's [eval : y^x × x ~> y] takes the SUBSET
   first, so the Examples read [eval (s, x) = s x].  That is a
   difference of convention, not of mathematics, and it is stated
   rather than silently normalised.  READ THEIR STRENGTH NARROWLY: the
   equation holds at an ARBITRARY second object of [Sets] -- it is a
   [Sets_Closed] fact, not a topos fact -- so the two Examples are one
   and the same fact at the two routes' Ω, and what their TYPES pin
   (that [carrier (Pow b)] reduces to the exponential's) is already
   pinned by [app1_pow_carrier] and [app1_pow_dec_carrier].  In
   particular the word MEMBERSHIP would be an over-read: nothing here
   relates [s x] to [sets_in_image], to [char] or to the classifying
   rule, and no such statement is made.

   FOUR IDENTIFICATIONS COME OUT AT [≈] AND NOT AT [eq_refl], all in
   section (B), and their cause is structural rather than incidental:
   Instance/Sets/Pullback.v:321 makes the apex a SIGMA carrying the
   agreement witness,

     sets_pb_carrier := { p : carrier x * carrier y
                        & equiv (f (fst p)) (g (snd p)) },

   so it is not the product carrier and its first projection is not
   [exl].  Hence Mac Lane's "the pullback of two arrows a → 1 ← b is
   then the usual set-theoretic product, with its projections to the
   given factors" is delivered as an ISOMORPHISM CARRYING ITS FOUR LEG
   EQUATIONS -- [pbone_to_exl], [pbone_to_exr], [pbone_from_fst],
   [pbone_from_snd] -- and not as a bare [≅].  FOUR strict forms are
   REFUSED and pinned in the probe: [pbone = a × b] and
   [carrier pbone = carrier (a × b)] and
   [exl ∘ pbone_to_prod = pbone_fst] are CONVERSION refusals, and
   [pbone_fst = exl] is a TYPING one -- a plain has-type mismatch with
   no "cannot unify" and no universe clause, because the two morphisms
   do not even share a source.

   THE OBSTRUCTION, ARGUED FOR THE RECORD, since the issue's Definition
   of Done asks for an instance OR an argued obstruction, its work item
   1 anticipates a verdict that no one-level instance exists, and the
   honest verdict is NEITHER of those two branches: a one-level instance
   DOES exist, conditionally.

     WHICH OF MAC LANE'S CLAUSES IS CONDITIONAL: exactly one, his Axiom
     8 "Truth" -- the subobject classifier -- and hence the §IV.9
     construction-1 clause.  Measured three ways: [Sets_Terminal],
     [Sets_Cartesian], [Sets_HasPullbacks] and [Sets_Closed] are
     argument-free [#[export]] instances, all four resolve by typeclass
     search, and all four are Closed; each of [Sets_Classifier],
     [Sets_Classifier_dec] and [Sets_Classifier_IEM] takes exactly one
     hypothesis.  So his Axioms 6 (terminal object), 7 (pullbacks, hence
     products) and 9 (power objects, here the exponential by Ω) are
     UNCONDITIONAL at [Sets]; only Axiom 8 is not.

     WHAT THE HYPOTHESES ARE, verbatim from
     Instance/Sets/Classifier/OneLevel.v:292, :297, :299 and
     Instance/Sets/Powerset.v:951:

       Definition Untruncate@{o} :=
         ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
       Definition DecImage@{o so} :=
         ∀ (u x : SetoidObject@{o o}) (m : u ~{Sets@{o so}}~> x),
           @Monic Sets@{o so} u x m →
           ∀ b : carrier x,
             sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).
       Definition IEM@{o} := ∀ P : Type@{o}, P + (P -> False).
       Definition Powerset_squash@{o} (A : Type@{o}) : Prop :=
         ∀ Q : Prop, (A → Q) → Q.

     WHERE THE HYPOTHESIS IS SPENT: exactly once.  In
     OneLevel.v:626-640's [small_of_untruncate] the argument [U] occurs
     on two lines, the binder at :626 and one use at :636
     ([exact (U P (proj2 Hp I))]), inside the obligation which by the
     field order of [Record SmallClassifierExt] (:324-:336) is
     [sce_elim].

     WHY IT IS NEEDED AT ALL: [≈] in this library is [Type@{o}]-valued,
     so the characteristic predicate [λ b, ∃ a, m a ≈ b] is
     [Type@{o}]-valued, and truncating it with the impredicative
     [Powerset_squash] is what puts it at the carrier's own level.
     Inverting that truncation is exactly [Untruncate].  The naive
     elimination [fun P h => h P (fun p => p)] is refused with "Cannot
     enforce o <= Prop", against the [Prop]-valued instantiation
     [powerset_squash_prop_inert] as the accepted control; that pair is
     already Test/ProbeClassifier402.v:176 and its control, and is CITED
     here rather than duplicated.

     NO IMPOSSIBILITY IS PROVED, AND THE PREMISE HAS NO IN-TREE
     INHABITANT, measured with TWO sweeps whose criteria are stated
     because the counts move with them.  (i) Declaration heads that
     MENTION one of the three at the first colon -- overwhelmingly
     binders -- number 36 outside this change's three files.  (ii)
     Declarations whose CONCLUSION is one of the three (the type
     preceded by an arrow, or followed by [:=] or a period) number FIVE:
     [untruncate_of_IEM], [DecImage_of_IEM], [IEM_of_DecImage] and
     [DecImage_iff_IEM]'s packaged pair, every one a PASSAGE between the
     hypotheses and not an inhabitant, and one refutation command,
     Test/ProbeFunClassifier403.v:425, which never enters the
     environment.
     Instance/Sets/Classifier/OneLevel.v's three-part disclosure applies
     verbatim here: (i) no unconditional axiom-free instance is built,
     (ii) no impossibility theorem is proved, (iii) an out-of-tree
     scratch development builds the classifier on exactly [classic] and
     [constructive_indefinite_description], so an in-tree impossibility
     theorem would refute a classically valid statement.  PART (iii) IS
     A HEADER CLAIM OF THAT FILE, quoted here and NOT re-run.
     Instance/Sets/Classifier.v:33-37 additionally records, as folklore
     and explicitly not as an in-tree theorem, that no small classifier
     can exist over predicative [Type].

   PRIOR ART, AND THE ISSUE'S "CURRENT STATE", EACH RE-MEASURED WITH ITS
   CRITERION AT THE BASE COMMIT.

     TRUE AT THE BASE COMMIT: "no [ElementaryTopos Sets]", and "the
     only [ElementaryTopos] inhabitant anywhere is
     Instance/FinSet/Topos.v:38".  CRITERION, stated so that it produces
     the numbers below: declaration heads whose type MENTIONS
     [ElementaryTopos] after a colon -- which therefore also catches the
     two that take one as a HYPOTHESIS -- swept comment-stripped ACROSS
     LINE BREAKS.  A line-anchored pattern such as
     [rg -n ':\s*ElementaryTopos' -g '*.v'] is NOT sound for this claim:
     it misses every head whose type wraps, which is all three bundles
     of THIS file.  Under the sound criterion the base commit returns
     three heads, two of them Structure/Topos.v:167's [Pow] and :184's
     [relations_iso] taking one as a hypothesis, so [FinSet_Topos] is
     the sole INHABITANT; the shipped tree returns ten.

     FALSE: "There is no [HasPullbacks Sets]" --
     Instance/Sets/Pullback.v:393's [#[export] Instance
     Sets_HasPullbacks], landed by #333, which the issue itself lists as
     a dependency.  FALSE: "no [SubobjectClassifier Sets]" -- three
     conditional ones at OneLevel.v:642, :814 and :836, plus the engine
     at :460.  FALSE FOR TWO OF THREE: "a tree-wide search finds exactly
     one instance of each of those three classes, all for FinSet" --
     true of [ElementaryTopos]; false of [SubobjectClassifier]
     (FinSet's, OneLevel.v's three, and four for functor categories at
     Instance/Fun/Classifier.v:794, :805, :810 and :1251) and false of
     [HasPullbacks] (FinSet's, [Sets_HasPullbacks],
     Instance/Cat/Pullback.v:496's [StrictCat_HasPullbacks],
     Instance/Fun/Pullback.v:316's [Fun_HasPullbacks], plus generic
     conditionals).

     STALE AS A CITATION: "The setoid half is blocked by a documented
     and deliberate universe obstruction (Instance/Sets/Classifier.v:29
     -:45)".  That file's :25-:38 now record the OPPOSITE -- that the
     conditional one-level instance exists -- and the obstruction
     paragraph proper is now the section headed "WHY ONE LEVEL DOES NOT
     SUFFICE UNCONDITIONALLY", beginning at :39.

     LINE DRIFT in four of the issue's citations: [Sets_Terminal] is
     Instance/Sets.v:258, not :248; [sets_char_pullback],
     [sets_char_unique] and [sets_char_subobject] are
     Instance/Sets/Classifier.v:243, :302 and :360, not :224, :283 and
     :341 -- all three off by 19 in the same direction.  CORRECT as
     cited: Instance/Sets/Cartesian.v:32, Instance/Sets/Cartesian/Closed.v:38
     and Instance/FinSet/Topos.v:38.

     A SECOND-INHABITANT NOTE, because it makes another file's header
     stale.  Through Structure/Topos/Colimits.v this bundle yields an
     initial object, a binary coproduct, coequalizers, pushouts and
     equalizers for [Sets]; unlike the presheaf side, where all five
     would be firsts, at [Sets] all five are SECOND inhabitants --
     Instance/Sets.v:275, Instance/Sets/Cocartesian.v:28,
     Instance/Sets/Coequalizer.v:293, Instance/Sets/Pushout.v:185 and
     Adjunction/GAFT/Sets.v:175 already have them.  That last file's
     header CALLED itself "the tree's only inhabitant of that class" and
     is corrected in this same change to "the only such LIBRARY-file
     inhabitant" -- which the derived one does NOT falsify, since it
     lives in Test/ProbeToposInstances404.v and is therefore not a
     library-file inhabitant, as that file's own appended note says.  The
     four colimit legs and the equalizer leg are ASCRIBED at the
     existing instances' own types in Test/ProbeToposInstances404.v, so
     the types are checked to line up;
     NO AGREEMENT PROOF IS BUILT, deliberately, and none is claimed.
     They live in the probe because requiring
     Structure/Topos/{Monadic,Colimits}.v takes this file's closure from
     74 to 101.

   WHAT IS NOT DELIVERED -- read this as the scope of the file.

     * No unconditional topos and no impossibility theorem (see the
       obstruction above).

     * No [classifier_classifies] and no [relations_iso] at any bundle
       here: both are refused, both refusals are pinned, and neither is
       repaired.  So this file adds NO witness to
       docs/INHABITATION.md's row for those two constants.

     * No comparison between the three bundles: no isomorphism of their
       truth objects, no isomorphism of their power objects, and no
       statement that they agree under [IEM].

     * No agreement proof between the derived colimits and the existing
       [Sets] instances (types only), and no [Complete]/[Cocomplete]
       statement derived from the topos structure.

     * No naturality anywhere, and no functoriality of any of the App.1
       witnesses in [a] or [b].

     * Nothing about slices, Lawvere-Tierney topologies, the internal
       logic or Giraud's theorem.

     * No relation to Instance/Fun/Topos.v's [Presheaf_Topos]: no
       functor between the two categories is built.

     * Nothing is registered as an [Instance]; all three bundles are
       plain [Definition]s, deliberately.

     * This file contributes NO lines to [make todo].  Its probe does,
       as every probe in this tree does, and that is disclosed rather
       than hidden. *)

(** ** (A) The three bundles *)

Definition Sets_Topos@{o so} (U : Untruncate@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier@{o so} U |}.

Definition Sets_Topos_dec@{o so} (D : DecImage@{o so}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier_dec@{o so} D |}.

Definition Sets_Topos_IEM@{o so} (E : IEM@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  Sets_Topos@{o so} (untruncate_of_IEM@{o} E).

Example sets_topos_terminal (U : Untruncate) :
  @topos_terminal Sets (Sets_Topos U) = Sets_Terminal := eq_refl.
Example sets_topos_cartesian (U : Untruncate) :
  @topos_cartesian Sets (Sets_Topos U) = Sets_Cartesian := eq_refl.
Example sets_topos_pullbacks (U : Untruncate) :
  @topos_pullbacks Sets (Sets_Topos U) = Sets_HasPullbacks := eq_refl.
Example sets_topos_closed (U : Untruncate) :
  @topos_closed Sets (Sets_Topos U) = Sets_Closed := eq_refl.
Example sets_topos_classifier (U : Untruncate) :
  @topos_classifier Sets (Sets_Topos U) = Sets_Classifier U := eq_refl.
Example sets_topos_dec_classifier (D : DecImage) :
  @topos_classifier Sets (Sets_Topos_dec D) = Sets_Classifier_dec D := eq_refl.

(** ** (B) App.1 clause (a): the terminal object is a one-element set,
       and clause (b): the pullback of [a → 1 ← b] is [a × b] *)

Example app1_terminal_carrier (U : Untruncate) :
  carrier (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U)))
  = poly_unit := eq_refl.

Example app1_terminal_is_donor (U : Untruncate) :
  @terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))
  = @terminal_obj Sets Sets_Terminal := eq_refl.

(* "any set with just one element can serve as a terminal object 1" *)
Lemma app1_terminal_singleton
  (t : carrier (@terminal_obj Sets Sets_Terminal)) : t = ttt.
Proof. destruct t; reflexivity. Qed.

(* The pullback of the unique arrows into 1.  Stated at top level with
   explicit binders rather than inside a Section: see universe reading
   (1) in the header. *)
Definition PBONE@{o so} (a b : obj[Sets@{o so}]) :=
  @pullback Sets@{o so} Sets_HasPullbacks@{so o} a b
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) one one.

Definition pbone@{o so} (a b : obj[Sets@{o so}]) : obj[Sets@{o so}] :=
  Pull _ _ (PBONE@{o so} a b).

Definition pbone_fst@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a := pullback_fst _ _ (PBONE@{o so} a b).

Definition pbone_snd@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> b := pullback_snd _ _ (PBONE@{o so} a b).

Definition pbone_to_prod@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a × b :=
  pbone_fst@{o so} a b △ pbone_snd@{o so} a b.

(* [one_unique] does not apply here; see the gotcha in the header. *)
Definition pbone_sq@{o so} (a b : obj[Sets@{o so}]) :
  one ∘ exl ≈ one ∘ (exr : a × b ~{Sets@{o so}}~> b).
Proof.
  intro p; destruct ((one[a] ∘ exl) p);
    destruct ((one[b] ∘ (exr : a × b ~{Sets@{o so}}~> b)) p); reflexivity.
Defined.

Definition pbone_from_prod@{o so} (a b : obj[Sets@{o so}]) :
  a × b ~{Sets@{o so}}~> pbone@{o so} a b :=
  unique_obj (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                (pbone_sq@{o so} a b)).

Definition pullback_over_one_is_product@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ≅ a × b.
Proof.
  unshelve refine {| to := pbone_to_prod@{o so} a b
                   ; from := pbone_from_prod@{o so} a b |}.
  - destruct (unique_property
                (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                   (pbone_sq@{o so} a b))) as [H1 H2].
    intro p; split; [ exact (H1 p) | exact (H2 p) ].
  - intro p; split; reflexivity.
Defined.

(* "with its projections to the given factors a and b": the four leg
   equations, at the setoid relation. *)
Lemma pbone_to_exl (a b : obj[Sets]) :
  exl ∘ pbone_to_prod a b ≈ pbone_fst a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_to_exr (a b : obj[Sets]) :
  exr ∘ pbone_to_prod a b ≈ pbone_snd a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_from_fst (a b : obj[Sets]) :
  pbone_fst a b ∘ pbone_from_prod a b ≈ exl.
Proof.
  exact (fst (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

Lemma pbone_from_snd (a b : obj[Sets]) :
  pbone_snd a b ∘ pbone_from_prod a b ≈ exr.
Proof.
  exact (snd (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

(* The mediator REDUCES: Instance/Sets/Pullback.v's [Sets_IsPullback] is
   [Defined], so the pullback's universal property computes. *)
Example pbone_from_computes (a b : obj[Sets]) :
  pbone_from_prod a b = sets_pb_med one one exl exr (pbone_sq a b) := eq_refl.

(* and the topos's own chosen pullback over 1 is that one *)
Example app1_pullback_is_topos_pullback (U : Untruncate) (a b : obj[Sets]) :
  @pullback Sets (@topos_pullbacks Sets (Sets_Topos U)) a b
    (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))) one one
  = PBONE a b := eq_refl.

(** ** (C) App.1 clause (c): Ω, truth, and the classifying rule *)

(* Mac Lane's "any set 2 consisting of two objects, 1 and 0", on the
   decidable route. *)
Example app1_omega_dec (D : DecImage) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) = BoolSetoid
  := eq_refl.
Example app1_omega_dec_carrier (D : DecImage) :
  carrier (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)))
  = poly_bool := eq_refl.
Example app1_truth_dec (D : DecImage) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) ttt = ptrue
  := eq_refl.

(* and the truncation route's own truth-value object *)
Example app1_omega_U (U : Untruncate) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos U)) = Powerset_Omega
  := eq_refl.
Example app1_truth_U (U : Untruncate) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos U)) ttt
  = Powerset_truth_point := eq_refl.

(* "the monomorphism t : 1 → 2": monic for free, from the derived
   [truth_monic] of Structure/SubobjectClassifier.v. *)
Definition app1_truth_monic (U : Untruncate) :
  @Monic Sets _ _ (@truth Sets _ (@topos_classifier Sets (Sets_Topos U)))
  := @truth_monic Sets _ _.

(* "This subset has a well-known characteristic function ψ : b → 2":
   the classifying rule, applied verbatim at the topos-level classifier
   on both routes. *)
Definition app1_char_rule_dec@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_dec_char_iff@{o so} D m M b.

Definition app1_char_rule_U@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_char_iff@{o so} U m M b.

Example app1_char_dec_strict@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M
  = char_of_dec@{o so} m M (D u x m M) := eq_refl.

Example app1_char_U_strict@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
  = Powerset_squash@{o} (sets_in_image@{o} m b) := eq_refl.

(* "such that the following square is a pullback" -- display (2) and its
   uniqueness clause are the class's own two fields, re-exposed at the
   bundle so that they can be quoted at a topos. *)
Definition app1_classifying_square@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_pullback Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

Definition app1_classifying_unique@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_unique Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

(** ** (D) App.1 clause (d): P b IS the power set of b *)

(* Mac Lane's "P b, the set of all subsets s of b" -- definitional, not
   an isomorphism.  See the header for why the two records coincide. *)
Example app1_pow_is_powerset (U : Untruncate) (b : obj[Sets]) :
  @Pow Sets (Sets_Topos U) b = Powerset_Prop_obj b := eq_refl.

Example app1_pow_carrier (U : Untruncate) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos U) b)
  = SetoidMorphism b Powerset_Prop_truth := eq_refl.

(* On the decidable route it is the DECIDABLE power set instead. *)
Example app1_pow_dec_carrier (D : DecImage) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos_dec D) b) = SetoidMorphism b BoolSetoid
  := eq_refl.

(* Membership: Mac Lane's ε_b is function application.  MIND THE
   ARGUMENT ORDER -- he writes ε_b(x, s) with the element first, and
   this tree's [eval : y^x × x ~> y] takes the subset first. *)
Example app1_eval_is_application (U : Untruncate) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos U) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos U))) (s, x) = s x
  := eq_refl.

Example app1_eval_dec_is_application (D : DecImage) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos_dec D) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D))) (s, x) = s x
  := eq_refl.

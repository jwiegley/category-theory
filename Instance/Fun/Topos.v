Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Classifier.

Open Scope category_scope.

(** * Presheaf categories are elementary toposes *)

(* Book:      Mac Lane, Categories for the Working Mathematician, 2nd
              ed., §IV.10, printed p. 107 (PDF p. 116)
              ([maclane:IV.10:remark1]).  Verbatim, from the rendered
              page:

                "The category Sets of all (small) sets is a topos and so
                 is the category Sets^{C^op} of all set-valued
                 contravariant functors on a small category C.  Such a
                 functor F : C^op → Sets is also called a presheaf."

   Book:      Awodey, Category Theory (1st ed., Carnegie Mellon
              pre-print, September 2005), §8.8 "Topoi", Definition 8.16
              and Proposition 8.17, printed pp. 210-211 (PDF pp.
              219-220) ([awodey:8.8:prop17]).  Verbatim:

                "Definition 8.16.  A topos is a category E such that:
                   1. E has all finite limits,
                   2. E has a subobject classifier,
                   3. E has all exponentials."

                "Proposition 8.17.  For any small category C, the
                 category of diagrams Sets^{C^op} is a topos."

                "Proof.  Since we already know that Sets^{C^op} has all
                 limits, and we know that it has exponentials by the
                 foregoing section, we just need to find a subobject
                 classifier.  To that end, for any category C we define
                 a sieve on an object C to be any set S of arrows
                 f : · → C (with arbitrary domain) that is closed under
                 precomposition, i.e. if f : D → C is in S then so is
                 f ∘ g : E → D → C for every g : E → D (think of a
                 sieve as a generalization of a "lower set" in a
                 poset)."

   Book:      Fong & Spivak, Seven Sketches in Compositionality, §7.3,
              printed pp. 231-232 (PDF pp. 243-244)
              ([7sketches:7.3:remark-presheaf-topos]).  Verbatim:

                "In general, we can think of any small category C as a
                 site; the corresponding topos is the category of
                 functors C^op → Set.^5  Such functors are called
                 presheaves on C."

                "Did you notice that we just introduced a huge class of
                 toposes?  For any category C, we said there is a topos
                 of presheaves on it."

              and, from the closing paragraph of the §7.2 "Review" on
              the facing page (printed p. 231), which is where this
              sentence actually sits:

                "Such toposes are called presheaf toposes and are
                 fundamental, but we will focus on sheaf toposes,
                 because our topos of behavior types will be a sheaf
                 topos."

              and its footnote 5, which is this issue's appended
              checkbox, verbatim:

                "5 The category of functors C → Set is also a topos: use
                 C^op as the defining site."

   nLab:      https://ncatlab.org/nlab/show/presheaf+topos
   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   WHAT IS DELIVERED.  [Presheaf_Topos C UT], an inhabitant of
   Structure/Topos.v's [ElementaryTopos ([C^op, Sets])] for an ARBITRARY
   category C -- at the universe levels measured below, which is where
   Awodey's word "small" lands -- CONDITIONAL on one hypothesis, #402's
   [Untruncate], which is the classifier field's and nothing else's.
   [Presheaf_Topos_IEM] is the same bundle under informative excluded
   middle.  Seven Sketches' footnote 5 is [Copresheaf_Topos], an
   [ElementaryTopos ([C, Sets])] supplied by [:=] at the opposite
   category with no tactic and no transport, since [(C^op)^op = C] holds
   by [eq_refl] in this tree -- recorded here as [psh_op_invol].

   THE ROUTE IS PURE ASSEMBLY: five fields, five pre-existing donors,
   NOTHING re-proved, no obligation raised and no tactic anywhere in the
   four bundles.

     topos_terminal    Instance/Fun/Terminal.v's [Functor_Category_Terminal]
     topos_cartesian   Instance/Fun/Cartesian.v's [Functor_Category_Cartesian]
     topos_pullbacks   Instance/Fun/Pullback.v's [Fun_HasPullbacks]
     topos_closed      Instance/Fun/Exponential.v's [Functor_Category_Closed]
     topos_classifier  Instance/Fun/Classifier.v's [Fun_Classifier]

   The three structural fields and the closed field fit WITHOUT a
   comparison because the record literal supplies the very terms the
   later fields were stated over: [Functor_Category_Closed]'s cartesian
   index IS the [topos_cartesian] written here, and [Fun_Classifier]'s
   terminal index IS the [topos_terminal] written here.  All five read
   back at [eq_refl] in section (B).

   THE ISSUE'S REVIEWER CHECK -- "the presheaf exponential is proved,
   not postulated" -- is met twice over: [psh_topos_exponent] records at
   [eq_refl] that the bundle's [exponent_obj] IS Awodey's display-(8.5)
   presheaf [PshExp], and [Print Assumptions] reports "Closed under the
   global context" for [Functor_Category_Closed] itself.  Its second
   check -- "the FinSet topos is not silently offered as the witness for
   either of Mac Lane's two claims" -- is met by construction:
   Instance/FinSet/Topos.v is neither required by this file nor cited as
   a witness for anything here, and the [Instance/Sets/Topos.v] sibling
   says the same on its own side.

   WHY A PLAIN [Definition] AND NOT AN [Instance].  Instance/FinSet/Topos.v
   gives the reason and it is followed here: the five [topos_*]
   projections are [#[export] Existing Instance]s, and the component
   structures are registered directly, so registering the bundle too
   would give typeclass search two convergent resolution paths for each
   component.  MEASURED, and the measurement differs from FinSet's
   situation: registering [Presheaf_Topos] is INERT today, because
   [Untruncate] is a plain [Definition] and not a [Class], so the
   bundle's premise can never be discharged by search and the second
   path is a dead end -- with the bundle registered, [@Terminal]
   still resolves to the direct instance and [@HasPullbacks] does not
   resolve at all.  The precedent is followed anyway, and it is
   future-proof against anyone registering an [Untruncate].  A separate
   measurement: THREE of the five components DO resolve on their own, to
   exactly the terms written here, so the record could carry three
   underscores; writing the terms out is what makes section (B)'s
   readbacks statable and stable.

   UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.

     Presheaf_Topos@{o h so} :
       ∀ C : Category@{o h h},
         Untruncate@{h} → ElementaryTopos@{so so h} ([C^op, Sets@{h so}])
       block: Set < h, h < so, o <= h, o <= so, plus stdlib bounds.

     Copresheaf_Topos@{o h so},  Presheaf_Topos_IEM@{o h so} and
     Copresheaf_Topos_IEM@{o h so}: character-for-character the same
     block, with [IEM@{h}] in place of [Untruncate@{h}] for the last two.

   Read five things off that.

   (1) NOT ONE CONSTRAINT BLOCK IN THIS FILE CONTAINS AN EQUATION --
   not in these four, and not in any of the twenty readbacks below.
   Every entry is [<] or [<=].  The readbacks reach that only because
   their [Section] [Context] is annotated; see the note at section (B).

   (2) C's hom and proof universes are identified IN THE BINDER
   ([Category@{o h h}], by reusing the level variable) with no equation
   in the block saying so -- the binder/block trap.  That identification
   is inherited from the donors, not introduced here.

   (3) C's OBJECT universe is BOUNDED above by its hom universe
   ([o <= h]), never identified.  That bound IS Awodey's "for any small
   category C", and it has EXACTLY TWO DONORS, EACH SUFFICIENT ALONE:
   [Functor_Category_Closed] and [Fun_Classifier].  Measured in a
   section declaring C's objects STRICTLY ABOVE its homs: the terminal,
   cartesian and pullback donors are all ACCEPTED there, and the
   exponential and the classifier are each refused alone.  Both refusals
   and the three controls are pinned in Test/ProbeToposInstances404.v.
   Instance/Fun/Exponential.v's own universes paragraph attributes the
   bound to [Transform]'s result type and declines to call it
   unavoidable; it is not claimed unavoidable here either.

   (4) [Set] appears ONLY as the strict LOWER bound [Set < h], which is
   [Prop : Type@{Set+1}] arriving through the truncation inside
   [Fun_Classifier].  NOTHING is pinned to [Set].  The bound is not
   inert: it excludes exactly the C whose hom universe is the literal
   [Set], and [_2] is such a C, which is why the probe's non-vacuity
   section (F) uses [_1], [Ordinal 2], [Parallel] and [Roof] and not
   [_2].  The probe
   pins that refusal with [Functor_Category_Closed _2] ACCEPTED as the
   discriminating control, so the exclusion is attributed to
   [Fun_Classifier] and not to the exponential.

   (5) THE ANNOTATION BUYS PRESENTATION, NOT STRENGTH, FOR THE BUNDLE,
   and that is measured rather than assumed.  The same four bodies with
   NO annotation at all elaborate at [∀ C : Category@{u1 u u}] with
   [u1 <= u] -- the same reading up to renaming, the annotated block's
   extra [o <= so] following from [o <= h < so] -- and no trailing [+]
   is needed.  Read that narrowly, because the #718 minimization lesson
   DOES fire one level down: an unannotated standalone alias of
   [Functor_Category_Closed] minimizes to [Category@{u0 u0 u0}], object,
   hom AND proof identified, strictly narrower than its donor.  No such
   alias is shipped here; the collapse is Instance/Fun/Exponential.v's
   own measurement, pinned in Test/ProbePresheafExp718.v, and is cited
   rather than duplicated.  The bundle escapes it because
   [Fun_Classifier] already fixes the reading -- which is also why the
   UNANNOTATED [Copresheaf_Topos] does not collapse: its body applies
   [Presheaf_Topos], whose binder has already fixed it.

   WHAT EACH CONSTANT CONSUMES.  Every constant in this file is either a
   record literal of five in-tree terms, a [:=] of another constant in
   this file, or an [Example ... := eq_refl].  There is no tactic, no
   [Program], no obligation and no [Qed] anywhere below.  So the ledger
   is short:

     Presheaf_Topos        the five donors named above, and nothing else.
     Presheaf_Topos_IEM    [Presheaf_Topos] and [untruncate_of_IEM].
     Copresheaf_Topos      [Presheaf_Topos] at [C^op]; the conversion
                           [(C^op)^op = C], which is definitional here.
     Copresheaf_Topos_IEM  [Copresheaf_Topos] and [untruncate_of_IEM].
     sections (B), (C)     conversion alone.

   STRICT VERSUS [≈], MEASURED STRICT FIRST.  Every identification in
   this file is [eq_refl], and NO equation is proved here at [≈] -- which
   is not a boast but a consequence of the file being an assembly: the
   morphism equations live in the five donors, and each was proved there
   with the [≈] discipline.  Read that exactly: a [≈] DOES occur inside
   one statement, the truncated proposition of [psh_char_is_awodey_sieve],
   but it is part of the sieve membership being read back and not an
   equation this file proves.  TWENTY [eq_refl] STATEMENTS are
   shipped, and that is their whole count below this header -- the
   token itself occurs once more down there, in a comment, and several
   times in this header:
   [psh_op_invol]; the five field readbacks; [exponent_obj] IS [PshExp];
   Ω IS [Sieve_Presheaf C]; [truth] IS [sieve_truth C]; [Pow] IS
   [PshExp P (Sieve_Presheaf C)] (the power object of a presheaf IS its
   exponential by Ω, which is Structure/Topos.v's [Pow] unfolded);
   [topos_terminal] IS Instance/Fun/Exponential.v's [presheaf_terminal];
   the chosen pullback IS [Fun_Pullback Sets_HasPullbacks]; the
   covariant bundle's closed and classifier fields ARE the tree's own
   [Functor_Category_Closed_cov] and [Fun_Classifier_cov], so the
   covariant reading is not a parallel construction; the THREE
   whole-bundle readbacks, which say something strictly stronger than
   those two field ones -- the covariant and contravariant bundles are
   the SAME TERM at opposite categories, in both directions, and the
   [IEM] pair with them; and section (C)'s three Awodey displays.

   ONE SPELLING NOTE, BECAUSE IT COST A REFUSAL.  Two readbacks need
   their types written out or elaboration stalls on an evar.  The
   pullback readback needs the CATEGORY ([a : F ~{[C^op, Sets]}~> H]);
   with a bare [F ~> H] the elaborator reports that F has type
   [C^op ⟶ Sets] where an [obj[?Category]] was expected.  And the
   restriction readback of section (C) needs its arrow ASCRIBED into
   [C^op] ([(h : c ~{C^op}~> d)]); written instead through the
   [morphism] coercion, as [morphism (fmap[Sieve_Presheaf C] h) S], the
   coercion is left an evar [?s] and [eq_refl] does not close.  Both the
   refusal and the accepted spelling are pinned in the probe, the
   accepted one as the discriminating control.

   THE SMALL READING IS BLOCKED, AND AT THE CLOSED FIELD -- NOT AT THE
   CLASSIFIER.  Instance/Fun/Classifier.v's [Section Small] lifts the
   presheaf category's hom universe above its object universe, giving
   [PShSmall Cs : Category@{OO HH HH}] with [Fun_Classifier_small] at
   that reading, which is what makes [classifier_classifies] apply there
   ([fun_classifier_classifies]).  FOUR of the five topos fields fit
   [PShSmall Cs] -- [PShSmall_Terminal], the pointwise cartesian
   structure, [Fun_HasPullbacks Sets_HasPullbacks] and
   [Fun_Classifier_small] are all accepted -- and the exponential does
   not:

     The term "Functor_Category_Closed Cs" has type
      "@Closed ([Cs^op, Sets])
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     while it is expected to have type
      "@Closed (PShSmall Cs)
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     (universe inconsistency: Cannot enforce o = small1.97 because
      o < so <= small1.96 <= small1.97).

   The obstruction sits at [presheaf_exp_iso], which is an isomorphism
   of hom-setoids in [Sets@{o so}]: at the lifted reading those
   hom-setoids are objects of a LARGER [Sets], so the exponential's
   category index -- unlike the functor category itself, whose hom
   universe is free to move up -- is invariant.  CONSEQUENCE: there is
   no [Presheaf_Topos_small], hence no topos here at which
   [classifier_classifies] applies.  What stands in for it is
   [fun_classifier_classifies], already in tree over
   [Fun_Classifier_small] and [Fun_HasPullbacks Sets_HasPullbacks]
   without a topos bundle; it is CITED and not re-derived.  NOTHING IS
   CLAIMED IMPOSSIBLE: only that the naive lift and the naive rebuild
   are both refused, with the error above.  Whether a [Setoid_Lift]-
   mediated exponential at the lifted [Sets] would work is NOT MEASURED,
   and repairing it would be work in Instance/Fun/Exponential.v rather
   than in a topos file.

   THE OBSTRUCTION, ARGUED FOR THE RECORD, since the issue's Definition
   of Done asks for an instance OR an argued obstruction and the honest
   verdict is neither of its two branches.

     WHICH CLAUSE IS CONDITIONAL: exactly one, the classifier -- Mac
     Lane's Axiom 8 "Truth" of §App.1 and his §IV.9 construction 1.  The
     terminal object, the pointwise products, the pointwise pullbacks
     and the exponentials are UNCONDITIONAL at [C^op, Sets]: all four
     donors are argument-free apart from C, and each is Closed under the
     global context.  So "presheaf categories are cartesian closed with
     finite limits" is unconditional in this tree; only the topos is
     conditional.

     WHAT THE HYPOTHESIS IS, verbatim from
     Instance/Sets/Classifier/OneLevel.v:297 and
     Instance/Sets/Powerset.v:951:

       Definition Untruncate@{o} :=
         ∀ P : Type@{o}, Powerset_squash@{o} P -> P.
       Definition Powerset_squash@{o} (A : Type@{o}) : Prop :=
         ∀ Q : Prop, (A → Q) → Q.

     WHERE IT IS SPENT: Instance/Fun/Classifier.v:173 records that
     [Untruncate] is spent EXACTLY ONCE in that file, in [med_img], and
     :178 that whether it is NECESSARY is not settled there.  It is not
     settled here either.

     WHY IT IS NEEDED AT ALL: [≈] in this library is [Type@{o}]-valued,
     so a sieve's membership predicate has to be truncated into [Prop]
     to sit at the carrier's own level, and inverting that truncation is
     exactly what [Untruncate] is.  The naive elimination
     [fun P h => h P (fun p => p)] is refused with "Cannot enforce
     o <= Prop"; that refusal is already
     Test/ProbeClassifier402.v:176 and is CITED, not duplicated here.

     NO IMPOSSIBILITY IS PROVED, and there is NO IN-TREE INHABITANT of
     the premise: a sweep of the declarations whose CONCLUSION is
     [Untruncate], [IEM] or [DecImage] returns five, of which four are
     PASSAGES between the hypotheses ([untruncate_of_IEM],
     [DecImage_of_IEM], [IEM_of_DecImage] and [DecImage_iff_IEM]) and
     one is a refutation command that never enters the environment
     (Test/ProbeFunClassifier403.v:425).
     Instance/Sets/Classifier/OneLevel.v's three-part
     disclosure applies verbatim, including its part (iii), that an
     out-of-tree scratch development builds the classifier on exactly
     [classic] and [constructive_indefinite_description] so an in-tree
     impossibility theorem would refute a classically valid statement.
     THAT PART IS A HEADER CLAIM OF THAT FILE, quoted here and NOT
     re-run.

     AND THERE IS NO [DecImage] VARIANT FOR PRESHEAVES.  At [Sets] there
     is one ([Sets_Classifier_dec]), which is why the sibling
     Instance/Sets/Topos.v ships three bundles and this file two;
     Instance/Fun/Classifier.v:184 and :397 record that no such
     presheaf variant is built.

   NON-VACUITY, and its limit.  A non-vacuity section is deliberately
   absent from this file: the four shape witnesses live in the probe, because
   naming them costs [Instance/One], [Instance/Ordinal],
   [Instance/Parallel] and [Instance/Roof] and none of the four is in
   this file's closure.  The probe carries [Presheaf_Topos] at [_1], at
   [Ordinal 2], at [Parallel] and at [Roof], with three [eq_refl]
   Examples over them.  NOTHING COMPUTES TO A NUMERAL, and that is
   structural rather than an omission: a sieve's membership is
   [Prop]-valued and truncated (Theory/Sieve.v:51-57 records that the
   [Prop] choice is forced, a [Type@{o}]-valued sieve type sitting one
   universe too high), so Ω carries no decidable code and there is no
   analogue of Instance/FinSet/Topos.v's [Pow 2 = 4].  What holds are
   the definitional readbacks of sections (B) and (C).

   NO CONFLICT WITH Instance/Fun/Closed.v.  That file's
   [fun_not_cartesian_closed] refutes cartesian closure of
   [[Omega, FinSet]] -- a FinSet-valued functor category, not a
   [Sets]-valued presheaf category -- and its Awodey counterexample
   concerns the OBJECTWISE formula, not the display-(8.5) one.  The two
   do not collide, and this file changes nothing there.

   PRIOR ART, AND THE ISSUE'S "CURRENT STATE", EACH RE-MEASURED WITH ITS
   CRITERION AT THE BASE COMMIT.

     TRUE STILL AT THE BASE COMMIT: "the only [ElementaryTopos]
     inhabitant anywhere is Instance/FinSet/Topos.v:38".  CRITERION, and
     it must be stated so that it produces the numbers beside it:
     declaration heads whose type MENTIONS [ElementaryTopos] after a
     colon -- so it also catches the two that take one as a HYPOTHESIS
     -- swept comment-stripped ACROSS LINE BREAKS, since a head whose
     type wraps is invisible to a line-anchored pattern:
     [rg -n ':\s*ElementaryTopos' -g '*.v'] is exactly such a pattern and
     misses all three bundles of Instance/Sets/Topos.v, whose [:] and
     class name sit on different lines.  Under the sound criterion the
     base commit returns three heads, two of them Structure/Topos.v:167's
     [Pow] and :184's [relations_iso] taking one as a hypothesis, leaving
     [FinSet_Topos] as the sole INHABITANT; the shipped tree returns ten,
     the seven new bundles included.  ALSO TRUE: "[ElementaryTopos]
     carries pullbacks explicitly ... the assembly must supply pullbacks
     directly" -- Structure/Topos.v:153 does, and this file supplies
     them.

     STALE, in six places.  "For presheaves ... no terminal object, no
     exponentials, no pullbacks, no classifier" -- all four now exist,
     at Instance/Fun/Terminal.v:362, Instance/Fun/Exponential.v:639,
     Instance/Fun/Pullback.v:316 and Instance/Fun/Classifier.v:794, and
     all four are consumed here.  "Instance/Fun/Cartesian.v:111 is the
     only structural instance on any functor category" -- it is not.
     "[ls Instance/Fun/] contains Cartesian.v and nothing else" --
     [ls Instance/Fun/*.v | wc -l] returns 10 before this file.  "sieve
     occurs only twice in the tree, both prose" -- [rg -li 'sieve'
     -g '*.v'] returns 6 files, one of which, Theory/Sieve.v, is a
     258-line module DECLARING the notion.  "no [HasPullbacks] for a
     functor category (the only instance in the tree is
     Instance/FinSet/Classifier.v:264)" -- [Fun_HasPullbacks] is
     Instance/Fun/Pullback.v:316.  And the Awodey section's "the
     classifier by #403, and the cartesian-closure component by the
     Awodey §8.7 issue" -- both have landed, and are what this file
     assembles.

     A FIRST, MEASURED BY THREE SWEEPS RATHER THAN BY NAME.  Through
     Structure/Topos/Colimits.v, this bundle yields an initial object, a
     binary coproduct, coequalizers, pushouts and equalizers for
     [C^op, Sets], and each would be the FIRST inhabitant of its class
     at any functor category in this tree.  Criterion, all three run at
     the base commit: (i) a name sweep for [Fun_Initial],
     [Fun_Cocartesian], [Fun_HasCoequalizers], [Fun_HasPushouts],
     [Fun_HasEqualizers], [Functor_Category_Initial] and
     [Functor_Category_Cocartesian] returns nothing; (ii) a shape sweep
     for any of [Initial], [Cocartesian], [HasCoequalizers],
     [HasPushouts], [HasEqualizers] applied to a bracketed functor
     category returns nothing, with [@Cartesian ([] returning five CODE
     lines as the instrument (a sixth hit is prose); (iii) every
     declaration head of those five classes tree-wide was read, and not
     one is at a functor category.
     The five are exhibited in the probe rather than here, because
     requiring Structure/Topos/{Monadic,Colimits}.v takes this file's
     closure from 108 to 133.  They are CONDITIONAL on [Untruncate],
     like the bundle, and no construction of their own is offered.

   WHAT IS NOT DELIVERED -- read this as the scope of the file.

     * No unconditional presheaf topos, and no impossibility theorem
       (see the obstruction above).  [Untruncate] has no axiom-free
       in-tree inhabitant.

     * No [Presheaf_Topos_small], hence no [classifier_classifies],
       [relations_iso] or [Sub_classifier_natural] AT a topos here: all
       three are refused at [Presheaf_Topos], and the probe pins the
       three refusals.  [fun_classifier_classifies] is the standalone
       result that stands in for the first.

     * No comparison of [Presheaf_Topos] with Instance/Sets/Topos.v's
       [Sets_Topos]: no functor between the two categories is built and
       nothing relates their truth objects or their power objects.

     * No sheaf reading.  Theory/Sheaf.v is not touched; the trivial
       coverage and the equivalence with sheaves on a trivial site
       belong to the Seven Sketches §7.4 item and are not attempted.

     * No slice topos, no Lawvere-Tierney topology, no internal logic,
       and nothing about Giraud's theorem.

     * Nothing about the Yoneda embedding, representables, or density,
       and no naturality of any identification in C.

     * Nothing computes: see the non-vacuity paragraph.

     * Nothing is registered as an [Instance]; all four bundles are
       plain [Definition]s, deliberately.

     * This file contributes NO lines to [make todo].  Its probe does,
       as every probe in this tree does, and that is disclosed rather
       than hidden. *)

(** ** (A) The four bundles *)

(* [(C^op)^op = C] by conversion: what makes the covariant reading a
   [:=] rather than a transport. *)
Example psh_op_invol (C : Category) : (C^op)^op = C := eq_refl.

Definition Presheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) := {|
  topos_terminal   := Functor_Category_Terminal Sets_Terminal;
  topos_cartesian  := Functor_Category_Cartesian (C^op) Sets Sets_Cartesian;
  topos_pullbacks  := Fun_HasPullbacks Sets_HasPullbacks;
  topos_closed     := Functor_Category_Closed C;
  topos_classifier := Fun_Classifier UT
|}.

Definition Presheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(* Seven Sketches §7.3 footnote 5: "The category of functors C → Set is
   also a topos: use C^op as the defining site." *)
Definition Copresheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} (C^op) UT.

Definition Copresheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Copresheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(** ** (B) The five fields, and the two derived objects, read back *)

Section Readback.

(* ANNOTATED DELIBERATELY.  Left bare, this [Context] fixes its own
   universes at discharge and every readback that USES it acquires the
   block equation [u0 = u1] -- sixteen of the nineteen below, the three
   exceptions being the whole-bundle readbacks, which bind their own [C]
   and [UT] and so never see this [Context] (measured on the bare
   variant).  The equation is the [Untruncate] universe identified with
   C's hom universe, which the bundles carry in their BINDER instead.
   The
   equation is sound but it would make reading (1) below true only of
   the four bundles' blocks; annotating moves it back into the binder
   and makes the file equation-free throughout.  Measured both ways. *)
Universes ro rh rso.
Context (C : Category@{ro rh rh}) (UT : Untruncate@{rh}).

Example psh_topos_terminal :
  @topos_terminal _ (Presheaf_Topos C UT)
  = @Functor_Category_Terminal (C^op) Sets Sets_Terminal := eq_refl.

Example psh_topos_cartesian :
  @topos_cartesian _ (Presheaf_Topos C UT)
  = @Functor_Category_Cartesian (C^op) Sets Sets_Cartesian := eq_refl.

Example psh_topos_pullbacks :
  @topos_pullbacks _ (Presheaf_Topos C UT)
  = @Fun_HasPullbacks (C^op) Sets Sets_HasPullbacks := eq_refl.

Example psh_topos_closed :
  @topos_closed _ (Presheaf_Topos C UT) = Functor_Category_Closed C
  := eq_refl.

Example psh_topos_classifier :
  @topos_classifier _ (Presheaf_Topos C UT) = Fun_Classifier UT := eq_refl.

(* The exponential IS Awodey's display-(8.5) presheaf.  This is the
   issue's reviewer check that it is proved rather than postulated. *)
Example psh_topos_exponent (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (@topos_closed _ (Presheaf_Topos C UT)) P Q
  = PshExp P Q := eq_refl.

(* Ω is Awodey's presheaf of sieves, and truth his total sieve. *)
Example psh_topos_omega :
  @Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = Sieve_Presheaf C := eq_refl.

Example psh_topos_truth :
  @truth ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = sieve_truth C := eq_refl.

(* Mac Lane's Axiom 9 object, unfolded: the power object of a presheaf
   is its exponential by Ω. *)
Example psh_topos_pow (P : C^op ⟶ Sets) :
  @Pow ([C^op, Sets]) (Presheaf_Topos C UT) P
  = PshExp P (Sieve_Presheaf C) := eq_refl.

(* The terminal presheaf is the one Instance/Fun/Exponential.v names. *)
Example psh_terminal_is_donor :
  @topos_terminal _ (Presheaf_Topos C UT) = presheaf_terminal C := eq_refl.

(* The chosen pullback is the pointwise one.  The category must be
   written out in the two arrows, or elaboration stalls. *)
Example psh_pullback_is_donor (F G H : C^op ⟶ Sets)
  (a : F ~{[C^op, Sets]}~> H) (b : G ~{[C^op, Sets]}~> H) :
  @pullback ([C^op, Sets]) (@topos_pullbacks _ (Presheaf_Topos C UT))
    F G H a b
  = Fun_Pullback Sets_HasPullbacks a b := eq_refl.

(* The covariant reading is not a parallel construction: its closed and
   classifier fields ARE the tree's own covariant donors. *)
Example copsh_topos_closed :
  @topos_closed _ (Copresheaf_Topos C UT) = Functor_Category_Closed_cov C
  := eq_refl.

Example copsh_topos_classifier :
  @topos_classifier _ (Copresheaf_Topos C UT) = Fun_Classifier_cov UT
  := eq_refl.

(* STRONGER THAN THE TWO FIELD READBACKS ABOVE: the covariant reading and
   the contravariant one are the SAME TERM at opposite categories, as
   WHOLE bundles and in both directions, and the [IEM] pair with them.
   [(C^op)^op = C] by conversion is what makes all three [eq_refl]. *)
Example copsh_is_psh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos C UT = Presheaf_Topos (C^op) UT := eq_refl.

Example psh_is_copsh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos (C^op) UT = Presheaf_Topos C UT := eq_refl.

Example copsh_iem_is_psh_iem_at_op (C : Category) (Em : IEM) :
  Copresheaf_Topos_IEM C Em = Presheaf_Topos_IEM (C^op) Em := eq_refl.

(** ** (C) Awodey's three displays *)

(* "t : 1 → Ω, namely, at each C, the 'total sieve': t_C = {f : · → C}." *)
Example psh_truth_is_total_sieve (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (@topos_terminal _ (Presheaf_Topos C UT))] c)) :
  transform[@truth ([C^op, Sets]) _
              (@topos_classifier _ (Presheaf_Topos C UT))] c u
  = @total_sieve C c := eq_refl.

(* "u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}", with the membership
   truncated by [Powerset_squash] -- which is what [Untruncate] inverts.
   The bound variables must be typed as Instance/Fun/Classifier.v types
   its own Example, or the [morphism] coercion is left an evar. *)
Example psh_char_is_awodey_sieve (E U : C^op ⟶ Sets) (theta : U ⟹ E)
  (M : @Monic ([C^op, Sets]) U E theta) (c d : C)
  (e : carrier (fobj[E] c)) (f : d ~{C}~> c) :
  sieve_mem (transform[@char ([C^op, Sets]) _
                         (@topos_classifier _ (Presheaf_Topos C UT))
                         U E theta M] c e) f
  = Powerset_squash (∃ x : carrier (fobj[U] d),
                       transform[theta] d x ≈ fmap[E] f e) := eq_refl.

(* "and given h : D → C let h* : Ω(C) → Ω(D) be defined by:
    h*(S) = {g : · → D | h ∘ g ∈ S}."  The arrow must be ascribed into
   [C^op]; see the spelling note in the header. *)
Example psh_omega_is_restriction (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  fmap[@Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))]
      (h : c ~{C^op}~> d) S
  = sieve_restrict h S := eq_refl.

End Readback.

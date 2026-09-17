Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** * The free ring functors, read through the adjoint functor theorem *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab: https://ncatlab.org/nlab/show/free+ring
   nLab: https://ncatlab.org/nlab/show/created+limit
   Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §V.6 Exercise 2, book p. 125 (PDF p. 134); the theorem it
             invokes is §V.6 Theorem 2, book p. 123, as Adjunction/GAFT.v
             :332 reads it
   Awodey:   Category Theory, 1st ed., §9.9 Exercise 9, printed p. 264
             (PDF p. 273)
   Fong & Spivak: Seven Sketches in Compositionality (CUP, 2019),
             §3.4.2 Example 3.74 clause 1, printed p. 104 (PDF p. 116)

   Mac Lane's Exercise 2 asks that Freyd's theorem be run at the forgetful
   functors of rings -- [Rng ⟶ Sets] and [Rng ⟶ Ab] -- and that its output
   be compared with the free ring and the tensor/monoid ring built by hand.
   Both halves are here, and so is the disclosure of what each one is worth.

   ** READ THIS BEFORE READING ANYTHING ELSE: NOTHING HERE IS CIRCULAR ANY
      MORE, AND THE CIRCULAR READINGS ARE KEPT BESIDE THE NEW ONES

   [Rng_Forget_Ab_continuous] IS NOT CIRCULAR.  It is derived from
   [Rng_Forget_continuous] (Instance/Rng/Limit.v:932) and
   [Ab_Forget_reflects_limits] (Instance/Ab/Limit.v:705) through the
   factorization below, and neither of those mentions an adjunction: the
   first comes from strict creation over [Sets_Complete], the second from
   strict creation of limits of abelian groups.  Nothing in its term
   mentions [FreeRngAb], [FreeAb] or any free object.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17).  This block
   used to read "ONE RESULT HERE IS NEW, TWO ARE CIRCULAR" and continued:

     "THE TWO GAFT APPLICATIONS ARE CIRCULAR, AND SAYING SO IS THE POINT.
      Freyd's third hypothesis is a solution set, and the two fed to it
      below -- [Rng_Forget_Ab_solution_set_from_adjunction] and
      [Rng_Forget_solution_set_from_adjunction] -- are
      [solution_set_of_adjunction] (Adjunction/GAFT.v:366) applied to
      [free_rng_ab_adjunction] (Instance/Rng/Free.v:676) and to the
      retyping of [free_ring_via_ab_adjunction] (:874): the singleton
      family at the unit of THE VERY ADJUNCTION EACH APPLICATION IS MEANT
      TO PRODUCE.  So [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] are
      genuine applications of a genuine theorem and are worthless as
      existence proofs -- strip Instance/Rng/Free.v and nothing in those
      two lines survives."

   That description is now TRUE OF TWO DIFFERENT CONSTANTS and FALSE of
   [free_rng_ab_via_GAFT] and [free_ring_via_GAFT].  The two circular
   solution sets are kept, under the names they always had, and the two
   circular GAFT applications built from them are kept under the new names
   [free_rng_ab_via_GAFT_from_adjunction] and
   [free_ring_via_GAFT_from_adjunction].  Every sentence of the quoted
   paragraph applies to those four and to nothing else.

   WHAT THE TWO HEADLINE CONSTANTS NOW CONSUME is
   [Rng_Forget_Ab_solution_set_prop] and [Rng_Forget_solution_set_prop]:
   the quotients of the FREE-RING TERM MODEL ([FRTerm],
   Instance/Rng/Free.v:301) by [Prop]-valued congruences, covered by the
   kernel congruence of an evaluation.  Strip Instance/Rng/Free.v's
   ADJUNCTIONS and both still stand.  Strip its TERM MODEL and they do not
   -- which is a dependence on a CONSTRUCTION, not on the conclusion, and
   is the same dependence every solution-set argument has.

   THE EXCEPTION, STATED HERE SO IT IS NOT DISCOVERED LATER.  The five
   [_mon] clauses -- the comparison with the monoid-ring route -- are
   stated about [free_ring_via_GAFT_from_adjunction], the CIRCULAR
   constant, and not about the new one.  [free_ring_via_mon] is itself
   pinned at [Set] and the non-circular application carries
   [Set < carrier], so the two cannot be compared; the measurement and the
   refusal are recorded at the clause itself.  The [_ab] comparisons are
   about the new constant and are unaffected.

   The disclosure this file used to make is still made by
   Adjunction/GAFT/Sets.v about its own instance; Instance/Grp/FreeAFT.v
   moved with this one.

   ** WHY THE CONTINUITY RESULT IS THE ONE WORTH HAVING

   Instance/Rng/Limit.v's NOT-DELIVERED block (:210-223) explains why no
   CREATION result for [Rng_Forget_Ab] is proved there, and the reason is
   structural rather than a matter of effort.  The cone-mediator method
   that works over [Sets] does not transpose to [Ab]: multiplication would
   need a cone whose apex is a direct sum with leg [(a, b) ↦ leg a · leg b],
   and that map is BILINEAR, not additive, so it is not a morphism of [Ab]
   and there is no cone to take a mediator of; the multiplicative unit is
   worse, since [Ab]'s initial object is a ZERO object (Instance/Ab.v:262,
   :276) and the only canonical maps out of it send everything to zero, so
   none of them selects [1].  NOTHING BELOW REPAIRS THAT.  No creation
   result for [Rng_Forget_Ab] is proved here either, and the bilinearity
   obstruction stands exactly where that block leaves it.

   What the composite route gets is the CONTINUITY anyway, by going around
   the obstruction rather than through it.  Given a limiting cone [N] over
   a diagram [K] in [Rng]:

     - [Rng_Forget_continuous] makes [FCone Rng_Forget N] limiting in
       [Sets] -- that is creation over [Sets], where the mediator method
       does work, because a set carries no additivity constraint at all;
     - by the factorization, that cone IS [FCone Ab_Forget (FCone
       Rng_Forget_Ab N)] -- same apex, same legs, same coherence proof,
       only a different diagram record (see the next paragraph);
     - [Ab_Forget_reflects_limits], which is
       [ReflectsLimitCone K Ab_Forget], then makes [FCone Rng_Forget_Ab N]
       limiting in [Ab].

   So the multiplicative structure never has to be built over [Ab]: it is
   built over [Sets], where it is legal, and the conclusion is imported
   back into [Ab] by reflection.  Creation is strictly more than this and
   is still missing.

   AND THE CONTRAST WITH RAPL IS THE WHOLE REASON THE ROUTE MATTERS HERE.
   Adjunction/Continuity.v:209's [right_adjoint_Continuous] would give
   [ContinuousFunctor Rng_Forget_Ab] in one line from
   [free_rng_ab_adjunction], since [FreeRngAb ⊣ Rng_Forget_Ab].  That term
   would be CIRCULAR in exactly the sense above: fed to GAFT it would
   presuppose the adjunction GAFT is being asked to produce, and the
   application would establish nothing.  Instance/Ab/Limit.v:45-67 states
   the same contrast for its own two continuity constants -- the RAPL-built
   [Ab_Forget_Continuous] (Instance/Ab/FreeNotContinuous.v:475) against the
   creation-built [Ab_Forget_creates_continuous] -- and this file is the
   first consumer for which the distinction actually bites.

   ** THE FACTORIZATION IS DEFINITIONAL ON DATA AND NOT ON RECORDS

   [rng_forget_factors_obj] and [rng_forget_factors_map] are [eq_refl]:
   [fobj[Rng_Forget] R] and [fmap[Rng_Forget] f] are convertible with
   [fobj[Ab_Forget ◯ Rng_Forget_Ab] R] and [fmap[Ab_Forget ◯
   Rng_Forget_Ab] f].  Both sides reduce to [rig_setoid R] and [rig_map f]
   (Instance/Rng.v:117-135 is where those two functors are written, and
   :613 and :615 already record the two object readbacks).

   THE FUNCTOR RECORDS ARE NOT CONVERTIBLE, and pretending otherwise would
   have made this file two lines shorter and wrong.  [Rng_Forget] is a
   [Program Definition] whose three functor laws are discharged by [Qed]
   obligations; [Ab_Forget ◯ Rng_Forget_Ab] is a [Compose] record whose
   laws are [Compose]'s generic proofs.  Those proof fields do not reduce
   to each other, so [Cone (Rng_Forget ◯ K)] and
   [Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))] are DIFFERENT TYPES and no
   [exact] crosses between them.  What IS convertible is every component a
   cone is built from -- apex, legs, and the coherence statement, which
   mentions the diagram only through [fmap] -- so [rng_ab_recone] and
   [rng_sets_recone] rebuild the record field for field, reusing the SAME
   coherence proof term.  Each is four lines and neither needs a tactic.

   ** THE TYPE TRAP GAFT SETS, MEASURED HERE AND NOT INHERITED AS A RUMOUR

   [ContinuousFunctor] does not ascribe where GAFT asks for
   [PreservesImageLimit].  Measured in this worktree, Rocq 9.1.1, feeding
   [GAFT Rng_Forget Rng_Complete Rng_Forget_continuous sols] is refused,
   with this STABLE head:

     The term "Rng_Forget_continuous" has type "ContinuousFunctor
     Rng_Forget" while it is expected to have type
     "Limit.PreservesImageLimit"

   The trailing [cannot unify ...] clause is deliberately NOT quoted here,
   because it is IMPORT-SENSITIVE: it is rendered with whatever module
   short-names are in scope, so the same refusal prints
   [cannot unify "Limit.Limit K" and "Cone.Cone K"] under one import list
   and [cannot unify "Cone.Cone (F ◯ K)" and "IsLimitCone N"] under
   another (measured at [Ab], four import lists, in
   Test/ProbeAlgLimit443.v's section E).  An earlier revision of this
   paragraph quoted one of them as though it were the text; two independent
   measurements of this same refusal then appeared to contradict each other
   when neither was wrong.  Only the head is quoted now.

   The refusal itself is the same one Instance/Ab/Limit.v:70-79 records at
   [Ab_Forget] and Test/ProbeGrpFreeAFT442.v's N6 records at [Grp_Forget],
   here at [Rng].  The bridge [Continuous_PreservesImageLimit]
   (Construction/Comma/Creation.v:232) is load-bearing and stands in both
   GAFT terms below.

   ** THE ISSUE'S "CURRENT STATE" IS STALE IN SIX PLACES

   It says: "The ring cases are entirely absent: [Rng] and [Ab] do not
   exist (#257, #256), so neither the ring-side forgetful functors nor
   their free objects exist, and no [SolutionSet] instance is ever built
   for a forgetful functor of this kind."  Each clause, checked against a
   green build on 2026-09-13:

   1. "[Rng] ... [does] not exist" -- [Rng], Instance/Rng.v:102.
   2. "[Ab] [does] not exist" -- [Ab], Instance/Ab.v.
   3. "neither the ring-side forgetful functors ... exist" --
      [Rng_Forget_Ab], Instance/Rng.v:117; [Rng_Forget], :129.
   4. "nor their free objects exist" -- [FreeRngAb],
      Instance/Rng/Free.v:672; [free_ring_via_ab], :872;
      [free_ring_via_mon], :880; with the adjunctions
      [free_rng_ab_adjunction] (:676), [free_ring_via_ab_adjunction]
      (:874) and [free_ring_via_mon_adjunction] (:883).
   5. "no [SolutionSet] instance is ever built for a forgetful functor of
      this kind" -- [Grp_Forget_solution_set_from_adjunction],
      Instance/Grp/FreeAFT.v:417, at [Grp_Forget : Grp ⟶ Sets], which is
      a forgetful functor of exactly this kind.
   6. The Awodey section's "the adjoint functor theorem's only in-tree
      application is a diagonal/product toy example" -- [free_group_via_GAFT],
      Instance/Grp/FreeAFT.v:423, and [GAFT_at_Sets_Id],
      Adjunction/GAFT/Sets.v:158, which feeds GAFT [Sets_Id_SolutionSet]
      (:140).  Sweeping [grep -rnw GAFT] over all [.v] files outside
      [Adjunction/GAFT*], those two are the only applications of the theorem
      in tree; everything else is prose or a probe.

   None of the six is established here -- each was in tree before this file
   was started, which is the whole difficulty, exactly as at [Grp].  What
   is NOT stale is the issue's requirement.

   ** THE ONE ABSENCE THAT WAS REAL, AND THE FINDING THAT IT WAS ONLY
      NOMINAL

   Before this file, [grep -rnP '⊣\s*Rng_Forget(?![A-Za-z0-9_])'] over all
   [.v] files returned NOTHING: no adjunction in tree had the literal
   [Rng_Forget : Rng ⟶ Sets] as its right adjoint.  Instance/Rng/Limit.v
   :151-154 records the same measurement and draws the correct conclusion
   for its own purposes, that [right_adjoint_Continuous] does not reach
   [Rng_Forget].

   THAT ABSENCE IS NOMINAL, NOT STRUCTURAL, and the measurement above is
   what made it look otherwise.  Instance/Rng/Free.v:874's
   [free_ring_via_ab_adjunction] has right adjoint [RngUnderlyingAb], which
   is DEFINED as [Ab_Forget ◯ Rng_Forget_Ab] (:861) -- the very composite
   the factorization identifies with [Rng_Forget] on data.  Every field of
   [Adjunction] (Theory/Adjunction.v:133-157) mentions the right adjoint
   only through [U y] and [fmap[U] f], so the five field TYPES are
   convertible and the record can be copied across field by field.  That
   is [free_ring_via_ab_adjunction_set] below, and the trick is not
   invented here: Instance/Rng/Free.v:892's
   [free_ring_via_mon_adjunction_ab] is the same copy, between the same two
   presentations of the same underlying-set functor, with the reason
   spelled out at :887-891.

   So the second GAFT application IS buildable, and an earlier reading of
   this issue that concluded it was not -- on the strength of the [grep]
   alone -- was wrong.  The [grep] is a measurement of NAMES; the question
   is one of TYPES.

   ** THE TWO HIDDEN CHECKBOXES IN THE ISSUE BODY

   (A) Awodey §9.9 Exercise 9 asks to "Build a solution set for a forgetful
   functor out of an algebraic category and derive the free construction
   from the adjoint functor theorem, so the theorem has a genuine
   application in the tree."  ADDRESSED, at two functors, IN BOTH READINGS.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): this clause
   read "ADDRESSED, at two functors, and with the circularity disclosed:
   the solution sets below are not Mac Lane's, and the derivation is
   therefore an application of the theorem and not an independent
   construction.  Awodey's exercise is satisfied in its literal reading --
   the theorem has a genuine application -- and NOT in the reading a reader
   might want, where the free ring is OBTAINED from the theorem."  The
   reading the reader wanted is now delivered: the solution sets are STILL
   not Mac Lane's (they are congruence quotients of a term model, not
   subrings cut down by a cardinality bound), but they are built without
   the adjunction, so the free ring IS obtained from the theorem.
   Instance/Grp/FreeAFT.v moved with this file.

   (B) Fong & Spivak §3.4.2 Example 3.74 clause 1 asks to "Deliver the
   conclusion as [Adjunction] witnesses rather than only as universal
   arrows, so the 'free is left adjoint to forgetful' slogan is a statement
   in the library".  Its supporting sentence, "Today Instance/CMon.v:169
   supplies a forgetful functor with no free functor and no adjunction
   beside it, and no other algebraic category exists in tree", is EXACT in
   its first half and stale in its second.  [CMon_Forget] is still at
   Instance/CMon.v:169 with no [FreeCMon] and, measured,
   [grep -rnP '⊣\s*CMon_Forget(?![A-Za-z0-9_])'] over all [.v] files returns
   nothing.  But five other algebraic categories carry the slogan already:
   [free_group_adjunction] (Instance/Grp/Free.v:438),
   [free_ab_adjunction] (Instance/Ab/Free.v:564),
   [free_mon_sets_adjunction] (Instance/Mon/Free.v:518),
   [free_module_adjunction] (Instance/Mod/Free.v:517) and
   [free_rng_ab_adjunction] (Instance/Rng/Free.v:676).  What this file adds
   that was genuinely missing is the slogan AT THE LITERAL UNDERLYING-SET
   FUNCTOR OF RINGS:
   [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget]
   is the first inhabitant in tree of a type of that shape, by the
   measurement two paragraphs up.  [Instance/CMon.v]'s own gap is NOT
   closed here; no free commutative monoid is built.

   ** THE COMPARISON CLAUSES ARE AT [≈] AND CANNOT BE ANYTHING ELSE

   The issue asks that each "compare with the usual construction" clause be
   "a proved isomorphism of the AFT-produced adjoint with the explicit free
   object".  [GAFT] (Adjunction/GAFT.v:241) ends in [Qed], so its output
   does not reduce and no component of it can be named.  Measured:

     Example nr1 : `1 free_ring_via_GAFT = free_ring_via_ab := eq_refl.

   is refused with "The term "eq_refl" has type "`1 (free_ring_via_GAFT) =
   `1 (free_ring_via_GAFT)" while it is expected to have type "`1
   (free_ring_via_GAFT) = free_ring_via_ab" (cannot unify "`1
   (free_ring_via_GAFT)" and "free_ring_via_ab")".  So NO [eq_refl] is
   claimed anywhere about a GAFT output, and the three comparisons below
   are at [≈], by [left_adjoints_agree] (Instance/Rng/Free.v:844) -- left
   adjoints to a fixed functor are isomorphic.  That donor is [Defined],
   so the comparison morphism has a name ([adj_left_compare], :769) and the
   unit clause ([adj_left_compare_unit], :779) is available; Mac Lane's
   exercise asks for both.  Theory/Adjunction.v:407's [left_adjoint_iso]
   inhabits the same types and is recorded beside each comparison so the
   claim is machine-checked twice.

   ** WHAT IS DELIVERED

   1. The factorization, at [eq_refl] on objects and on morphisms.
   2. [Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab], and its
      apex-only consequence [Rng_Forget_Ab_PreservesAllLimits] -- the
      genuinely new, non-circular result, derived without an ADJUNCTION and
      without RAPL — though emphatically not without creation, since both of
      its inputs are creation results (Instance/Rng/Limit.v:933's
      [creates_limits_continuous ...] and Instance/Ab/Limit.v:707's
      [creates_reflects_limits ...]); what it avoids is a creation argument
      FOR [Rng_Forget_Ab] ITSELF, which is the one that stops.  Without
      an adjunction and without RAPL.
   3. [Rng_Forget_Ab_reflects_limits : ReflectsLimitCone K Rng_Forget_Ab],
      the same composite read in the other direction, also adjunction-free.
   4. [free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget],
      the retyping, which is the Seven Sketches clause and the third GAFT
      hypothesis at [Rng_Forget] in one.
   5. FOUR solution sets (an earlier revision said two): the two
      NON-CIRCULAR ones built from [Prop] congruences on the free-ring term
      model, [Rng_Forget_Ab_solution_set_prop] and
      [Rng_Forget_solution_set_prop], which the two headline GAFT
      applications [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] consume;
      and the two circular ones, kept under the names that say so, which
      [free_rng_ab_via_GAFT_from_adjunction] and
      [free_ring_via_GAFT_from_adjunction] consume.
   6. Three comparison clauses at [≈], each with its named comparison
      morphism and its unit equation: against [FreeRngAb], against
      [free_ring_via_ab] and against [free_ring_via_mon].  THE FIRST TWO
      are about the non-circular constants; the THIRD is about
      [free_ring_via_GAFT_from_adjunction], for the measured universe
      reason recorded at the clause.

   Items 1-4 do not depend on the AFT applications at all, and none of them
   is circular.

   ** NOT DELIVERED

   (1) NO CREATION RESULT FOR [Rng_Forget_Ab], and no repair of the
   bilinearity obstruction Instance/Rng/Limit.v:210-223 records.
   Continuity is strictly less than creation and nothing here compares the
   two as propositions.  (2) NO [Complete Ab]-based route: [Ab_Complete]
   (Instance/Ab/Limit.v:749) exists and is not used, because GAFT is run at
   [Rng_Forget_Ab] and so wants [Complete Rng], not [Complete Ab].
   (3) NO SOLUTION SET OF MAC LANE'S OWN SHAPE.  CORRECTION, PR "algebraic
   carriers are sets" (2026-09-17): this clause read "NO NON-CIRCULAR
   SOLUTION SET", and that is false -- there are two, above.  What is still
   true, and is what the clause went on to say, is that MAC LANE'S OWN
   family is not built: the subrings generated by the image of a set, cut
   down by a cardinality bound, need a generated-subring API that does not
   exist over [RingObject].  The analogous gap at [Grp] is filed as #1309
   together with the universe-minimization artifact of
   Instance/Discrete.v:59's [DiscreteCat_Functor] -- the second of which
   has since been repaired -- and the [Rng] case would still meet the
   first.  Nothing here attempts it.  What is delivered instead is a
   congruence-quotient family, which is a different argument for the same
   conclusion.  (Instance/Mod/TensorAFT.v section 10 shows the two
   arguments meet at [RMod R], Mac Lane's family being SMALL UP TO
   ISOMORPHISM with the congruences as its small index; no such bridge is
   built here.)  (4) THE GRAPH HALF OF THE ISSUE IS NOT TOUCHED.  Producing the left adjoint to the categories-to-graphs
   forgetful functor via GAFT and comparing it with
   Construction/Free/Quiver.v:561's [FreeForgetfulAdjunction] -- the issue
   body's ":550" for that constant is stale by eleven lines, measured -- would
   need [Complete StrictCat] and continuity of that forgetful functor; the only
   completeness in tree is Instance/Cat/Limit.v:532's [StrictCat_Complete],
   which is CONDITIONAL on [∀ C, ObjUIP C] and [DepFunext] and so would
   carry those hypotheses into every constant downstream, and
   [grep -rnE 'ContinuousFunctor (Forgetful|Quiver)'] returns nothing.
   (5) NO MONADICITY and no comparison functor, so nothing here says [Rng]
   is an Eilenberg-Moore category; Riehl §5.6 Example 5.6.8 remains an
   observation, as Instance/Rng/Limit.v:228-231 already records.
   (6) NO [Test/Probe] FILE accompanies this one.  The [eq_refl] readbacks
   below are guarded only by being [Example]s in this file, and the two
   refusals quoted in the header -- the [ContinuousFunctor]/
   [PreservesImageLimit] ascription and the non-reducing GAFT output -- are
   measured here but pinned nowhere.  That is a gap, not a claim.
   (7) NOTHING is registered as an [Instance]; the file declares none.

   ** STATUS: axiom-free

   Counting [def]+[prf] heads in the [.glob] file, this file declares
   THIRTY-FOUR constants and NO [Program] obligations -- it uses no
   [Program] at all, so the trap of obligations that no source-level
   reading sees does not arise here.  [Print Assumptions] reports "Closed
   under the global context" for all thirty-four, read back by name:
   [rng_forget_factors_obj], [rng_forget_factors_map],
   [rng_underlying_ab_is_forget_obj], [rng_underlying_ab_is_forget_map],
   [rng_ab_recone], [rng_sets_recone], [rng_ab_image_limit],
   [rng_ab_limit_cone], [rng_ab_reflect], [Rng_Forget_Ab_continuous],
   [Rng_Forget_Ab_PreservesAllLimits], [Rng_Forget_Ab_reflects_limits],
   [free_ring_via_ab_adjunction_set], [free_ring_via_mon_adjunction_set],
   [free_ring_via_ab_adjunction_set_transpose],
   [Rng_Forget_Ab_solution_set_from_adjunction],
   [Rng_Forget_solution_set_from_adjunction], [free_rng_ab_via_GAFT],
   [free_ring_via_GAFT], the three [_agrees] comparisons, their three
   [_via_left_adjoint_iso] cross-checks, the three [_comparison]
   morphisms, the three [_comparison_is_component] readbacks and the three
   [_unit] clauses.  That is a readback of this file's own constants, not
   a directory-wide certification, and nothing here is registered with
   [make print-assumptions].

   EIGHT of the thirty-four are [eq_refl] Examples: the four factorization
   readbacks, the transpose readback and the three
   [_comparison_is_component] readbacks.  No [eq_refl] is claimed about a
   GAFT output anywhere.

   This file contributes ZERO hits to [make todo]. *)

(** * The factorization of [Rng_Forget] through [Ab] *)

(* On data these two functors are the same term.  The records are not
   convertible -- see the header -- which is why the two recones below
   exist at all. *)

Example rng_forget_factors_obj (R : Rng) :
  fobj[Rng_Forget] R = fobj[Ab_Forget ◯ Rng_Forget_Ab] R := eq_refl.

Example rng_forget_factors_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[Rng_Forget] f = fmap[Ab_Forget ◯ Rng_Forget_Ab] f := eq_refl.

(* [RngUnderlyingAb] (Instance/Rng/Free.v:861) IS that composite, so the
   same two readbacks hold against it.  These are what make the retyping of
   [free_ring_via_ab_adjunction] typecheck. *)

Example rng_underlying_ab_is_forget_obj (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[Rng_Forget] R := eq_refl.

Example rng_underlying_ab_is_forget_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[Rng_Forget] f := eq_refl.

(** * Continuity of [Rng_Forget_Ab], without a creation argument FOR IT,
      and without RAPL *)

Section RngAbContinuity.

Context {J : Category}.
Context (K : J ⟶ Rng).

(* A cone over [Ab_Forget ◯ (Rng_Forget_Ab ◯ K)] rebuilt as a cone over
   [Rng_Forget ◯ K].  Apex, legs and coherence proof are reused verbatim;
   only the diagram record changes, and every type the fields inhabit is
   convertible by the factorization above. *)
Definition rng_ab_recone (M : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)))
  : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Rng_Forget ◯ K)
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* The other direction, needed for the reflection clause. *)
Definition rng_sets_recone (M : Cone (Rng_Forget ◯ K))
  : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) :=
  @Build_Cone J Sets (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* Step one: the image of a limiting cone of rings under [Ab_Forget ◯
   Rng_Forget_Ab] is limiting, because that composite's image cone IS
   [Rng_Forget]'s, and [Rng_Forget] is continuous.  Every cone the goal
   quantifies over is re-presented by [rng_ab_recone]; no tactic is
   involved. *)
Definition rng_ab_image_limit (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Ab_Forget (FCone Rng_Forget_Ab N)) :=
  fun M => Rng_Forget_continuous J K N HN (rng_ab_recone M).

(* Step two: [Ab_Forget] reflects limit cones, so the [Ab]-level cone is
   limiting.  This is where the bilinearity obstruction is bypassed -- the
   ring multiplication on the apex is never built over [Ab]. *)
Definition rng_ab_limit_cone (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Rng_Forget_Ab N) :=
  Ab_Forget_reflects_limits (Rng_Forget_Ab ◯ K) (FCone Rng_Forget_Ab N)
    (rng_ab_image_limit N HN).

(* The same composite read backwards: [Ab_Forget] is continuous by
   creation ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v:764, which
   presupposes no adjunction either), and [Rng_Forget] reflects. *)
Definition rng_ab_reflect (N : Cone K)
  (HN : IsLimitCone (FCone Rng_Forget_Ab N)) : IsLimitCone N :=
  Rng_Forget_reflects_limits K N
    (fun M =>
       Ab_Forget_creates_continuous J (Rng_Forget_Ab ◯ K)
         (FCone Rng_Forget_Ab N) HN (rng_sets_recone M)).

End RngAbContinuity.

(** The headline non-circular result. *)
Definition Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab :=
  fun J K N HN => rng_ab_limit_cone K N HN.

Definition Rng_Forget_Ab_PreservesAllLimits :
  PreservesAllLimits Rng_Forget_Ab :=
  Continuous_PreservesAllLimits Rng_Forget_Ab_continuous.

Definition Rng_Forget_Ab_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget_Ab :=
  fun N HN => rng_ab_reflect K N HN.

(** * The underlying-set adjunction, retyped onto [Rng_Forget] *)

(* Instance/Rng/Free.v:874 states the composite adjunction against
   [RngUnderlyingAb].  Every field of [Adjunction] mentions the right
   adjoint only through [U y] and [fmap[U] f], and the two readbacks above
   say those agree definitionally, so the five field types are convertible
   and the record copies across.  This is Instance/Rng/Free.v:892's own
   manoeuvre at the other pair of presentations.

   This is the first inhabitant in tree of [_ ⊣ Rng_Forget]: see the header
   for the measurement, and for why its absence was nominal. *)

Definition free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_ab Rng_Forget
    (@adj _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction).

(* The monoid route retyped the same way, so that the comparison below can
   be made against BOTH explicit constructions rather than only one. *)
Definition free_ring_via_mon_adjunction_set : free_ring_via_mon ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_mon Rng_Forget
    (@adj _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab).

(* The retyping is inert on the transpose, hence on the unit. *)
Example free_ring_via_ab_adjunction_set_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction_set X R) f
    = to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f := eq_refl.

(** * [Prop] congruences on the free-ring terms *)

(* THE NON-CIRCULAR SOLUTION SETS.

   A solution set for [Rng_Forget_Ab] at [A] must be a family of rings, at
   the universe the theorem demands, through which every homomorphism out
   of [A] factors.  The family used here is the QUOTIENTS OF THE FREE-RING
   TERM MODEL by [Prop]-valued congruences: [FRTerm A]
   (Instance/Rng/Free.v:301) with its relation [fr_eq], which is already a
   [Prop] inductive since the PR "algebraic carriers are sets"
   (2026-09-17).

   WHY THE INDEX IS THE RIGHT SIZE.  Every field of [IsRngCongruence] is a
   [Prop], so the record is a [Prop] and the sigma over it lands at the
   carrier universe rather than one above it.  Structure/Complete.v's SIZE
   NOTE, item 1, is the authority and is not restated; item 2(b) is why the
   index universe has to be the carrier universe in the first place.  The
   same device serves Instance/Mod/TensorAFT.v (section 3A) and
   Instance/Grp/FreeAFT.v.

   NO [PropEquiv] HYPOTHESIS ANYWHERE BELOW: [rig_prop] is a field of
   [RigObject] and [cmon_prop] a field of [CMonObject], both with
   [#[export] Existing Instance], so the kernel congruence of an evaluation
   is available at every ring with no side condition. *)

Section RngCongruence.

Context (A : AbObject).

Record IsRngCongruence (Rq : FRTerm A → FRTerm A → Prop) : Prop := {
  rc_refl  : ∀ s, Rq s s;
  rc_sym   : ∀ s t, Rq s t → Rq t s;
  rc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  rc_gen   : ∀ s t, fr_eq s t → Rq s t;
  rc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_plus A s t) (@fr_plus A s' t');
  rc_neg   : ∀ s s', Rq s s' → Rq (@fr_neg A s) (@fr_neg A s');
  rc_mul   : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_mul A s t) (@fr_mul A s' t')
}.

Definition RngCongIdx : Type :=
  { Rq : FRTerm A → FRTerm A → Prop & IsRngCongruence Rq }.

(* NAMED for [PropEquiv_of_relation]'s sake: written inline, its setoid
   argument is found by resolution, which picks the AMBIENT term setoid
   rather than the quotient's, and both implications are then refused. *)
Definition QRng_Setoid (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : Setoid (FRTerm A) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := rc_refl  Rq H
        ; Equivalence_Symmetric  := rc_sym   Rq H
        ; Equivalence_Transitive := rc_trans Rq H |} |}.

(* The quotient ring, at the SAME [Rng] instance.  Every law is the term
   model's own law passed through [rc_gen]. *)
Definition QRng (Rq : FRTerm A → FRTerm A → Prop) (H : IsRngCongruence Rq)
  : RingObject :=
  {| ring_rig := {|
       rig_setoid :=
         {| carrier := FRTerm A
          ; is_setoid := QRng_Setoid Rq H |};
       rig_zero := @fr_zero A;
       rig_add  := @fr_plus A;
       rig_one  := @fr_one A;
       rig_mul  := @fr_mul A;
       rig_add_respects := fun _ _ Hs _ _ Ht => rc_plus Rq H _ _ _ _ Hs Ht;
       rig_mul_respects := fun _ _ Hs _ _ Ht => rc_mul Rq H _ _ _ _ Hs Ht;
       rig_add_assoc := fun s t u => rc_gen Rq H _ _ (fre_add_assoc s t u);
       rig_add_comm := fun s t => rc_gen Rq H _ _ (fre_add_comm s t);
       rig_add_zero_l := fun s => rc_gen Rq H _ _ (fre_add_zero_l s);
       rig_mul_assoc := fun s t u => rc_gen Rq H _ _ (fre_mul_assoc s t u);
       rig_mul_one_l := fun s => rc_gen Rq H _ _ (fre_mul_one_l s);
       rig_mul_one_r := fun s => rc_gen Rq H _ _ (fre_mul_one_r s);
       rig_distr_l := fun s t u => rc_gen Rq H _ _ (fre_distr_l s t u);
       rig_distr_r := fun s t u => rc_gen Rq H _ _ (fre_distr_r s t u);
       rig_mul_zero_l := fun s => rc_gen Rq H _ _ (fr_mul_zero_l A s);
       rig_mul_zero_r := fun s => rc_gen Rq H _ _ (fr_mul_zero_r A s);
       rig_prop := @PropEquiv_of_relation _ (QRng_Setoid Rq H) Rq
                     (fun _ _ h => h) (fun _ _ h => h)
     |};
     ring_neg := @fr_neg A;
     ring_neg_respects := fun _ _ Hs => rc_neg Rq H _ _ Hs;
     ring_neg_l := fun s => rc_gen Rq H _ _ (fre_neg_l s)
  |}.

(* The canonical insertion of [A] into the quotient. *)
Definition QRng_insert (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : A ~{Ab}~> Rng_Forget_Ab (QRng Rq H).
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := @fr_gen A |}.
    intros a b Hab; exact (rc_gen Rq H _ _ (fre_gen Hab)).
  - exact (rc_gen Rq H _ _ (@fre_gen_zero A)).
  - intros a b; exact (rc_gen Rq H _ _ (fre_gen_plus a b)).
Defined.

End RngCongruence.

Arguments IsRngCongruence {A} Rq.
Arguments RngCongIdx A.
Arguments QRng_Setoid {A} Rq H.
Arguments QRng {A} Rq H.
Arguments QRng_insert {A} Rq H.

(* THE KERNEL CONGRUENCE of a ring-valued extension, and the covering. *)

Section RngKernel.

Context (A : AbObject).
Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Definition rng_ker : FRTerm A → FRTerm A → Prop :=
  fun s t => @pequiv _ _ (rig_prop R) (fr_eval h s) (fr_eval h t).

Lemma rng_ker_is_cong : IsRngCongruence rng_ker.
Proof.
  unfold rng_ker.
  constructor.
  - intro s; apply (@pequiv_from _ _ (rig_prop R)); reflexivity.
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R)); symmetry;
      exact (@pequiv_to _ _ (rig_prop R) _ _ Hst).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (rig_prop R)).
    transitivity (fr_eval h t);
      [ exact (@pequiv_to _ _ (rig_prop R) _ _ H1)
      | exact (@pequiv_to _ _ (rig_prop R) _ _ H2) ].
  (* [fr_eval_respects] takes [R] EXPLICITLY (Instance/Rng/Free.v:691)
     while [fr_eval] takes both implicitly (:689). *)
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R));
      exact (fr_eval_respects R h s t Hst).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_add_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
  - intros s s' H1; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (ring_neg_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_mul_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
Qed.

Definition rng_ker_idx : RngCongIdx A := existT _ rng_ker rng_ker_is_cong.

(* The mediator out of the quotient: respectfulness IS [pequiv_to]. *)
Program Definition rng_ker_med : QRng rng_ker rng_ker_is_cong ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval h |}
|}.
Solve All Obligations with
  (first [ (intros s t Hst; exact (@pequiv_to _ _ (rig_prop R) _ _ Hst))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. *)
Example rng_ker_factors (a : carrier (cmon_setoid A)) :
  rig_map rng_ker_med (cmon_map (QRng_insert rng_ker rng_ker_is_cong) a)
  = cmon_map h a
  := eq_refl.

End RngKernel.

Arguments rng_ker {A R} h.
Arguments rng_ker_is_cong {A R} h.
Arguments rng_ker_idx {A R} h.
Arguments rng_ker_med {A R} h.

(* NAMED so that both record fields elaborate [QRng] at ONE universe
   instance; written inline they mint two and the record is refused. *)
Definition QRngOf {A : Ab} (i : RngCongIdx A) : obj[Rng] :=
  QRng (`1 i) (`2 i).

Definition QRngInsertOf {A : Ab} (i : RngCongIdx A)
  : A ~{Ab}~> Rng_Forget_Ab (QRngOf i) := QRng_insert (`1 i) (`2 i).

Definition Rng_Forget_Ab_solution_set_prop (A : Ab) :
  SolutionSet Rng_Forget_Ab A.
Proof.
  unshelve refine (@Build_SolutionSet Rng Ab Rng_Forget_Ab A
                     (RngCongIdx A) QRngOf QRngInsertOf _).
  intros c h.
  exists (rng_ker_idx h), (rng_ker_med h).
  intro a; simpl; reflexivity.
Defined.

(* THE [Rng_Forget] HALF, TAKEN DIRECTLY AND NOT AS A COMPOSITE.

   The free ring on a SET is the free ring on the free abelian group on it
   ([free_ring_via_ab := FreeRngAb ◯ FreeAb], Instance/Rng/Free.v:915), so
   the SAME congruence index over [FreeAbObject X] and the SAME quotients
   serve; only the covering changes, by one transposition through
   [free_ab_extend].  Cost over the [Ab] case: three lines and no new
   vocabulary.

   THE COMPOSITE ROUTE WAS MEASURED AND NOT TAKEN.  Composing through
   Adjunction/Compose.v would need a GAFT application for [Ab_Forget] as
   well -- a fourth term model and a fourth congruence class -- or else
   would lean on the already-in-tree [free_ab_adjunction], which would make
   the result an adjunction-COMPOSITION rather than a GAFT application and
   leave [free_ring_via_GAFT] naming a theorem it did not prove.

   ONE TRAP: [free_ab_extend h] will not elaborate against an open [?A0]
   ([h : X ~> Rng_Forget c] and [X ~> Ab_Forget ?A0] are convertible but
   not unifiable), so the target is given explicitly. *)

Definition Rng_Forget_solution_set_prop (X : Sets) :
  SolutionSet Rng_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Rng Sets Rng_Forget X
                     (RngCongIdx (FreeAbObject X)) QRngOf
                     (fun i => fmap[Ab_Forget] (QRngInsertOf i)
                                 ∘ free_ab_unit X) _).
  intros c h.
  exists (rng_ker_idx (@free_ab_extend X (Rng_Forget_Ab c) h)),
         (rng_ker_med (@free_ab_extend X (Rng_Forget_Ab c) h)).
  intro a; simpl.
  reflexivity.
Defined.

(** * The two solution sets, and the two GAFT applications *)

(* THE CIRCULAR DISCHARGES, KEPT FOR COMPARISON; REMOVAL CANDIDATES FOR
   JOHN.  Each is named so that the circularity is visible at every use
   site rather than buried in a term: the family is the singleton at the
   unit of the adjunction the theorem is being asked to produce.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): these two are
   no longer what the GAFT applications below consume.  They are kept
   because removing working code is John's call, because the naming
   convention they establish is what makes the circularity legible, and
   because they are the honest comparison -- two different solution sets
   for one functor, one read off the answer and one not. *)

Definition Rng_Forget_Ab_solution_set_from_adjunction (A : Ab) :
  SolutionSet Rng_Forget_Ab A :=
  solution_set_of_adjunction free_rng_ab_adjunction A.

Definition Rng_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Rng_Forget X :=
  solution_set_of_adjunction free_ring_via_ab_adjunction_set X.

(* Mac Lane §V.6 Exercise 2, first half: the tensor/monoid ring on an
   abelian group.  [Continuous_PreservesImageLimit] is load-bearing -- see
   the header's measurement of what happens without it.

   NON-CIRCULAR since the PR "algebraic carriers are sets": the solution
   set is [Rng_Forget_Ab_solution_set_prop], built from the free-ring term
   model and its [Prop] congruences.  Strip Instance/Rng/Free.v's
   ADJUNCTIONS and this still stands; strip its TERM MODEL and it does
   not, which is the honest statement of what it depends on. *)
Definition free_rng_ab_via_GAFT : ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_prop.

(* Second half: the free ring on a set, likewise non-circular. *)
Definition free_ring_via_GAFT : ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_prop.

(* The circular readings, kept under names that say so. *)
Definition free_rng_ab_via_GAFT_from_adjunction :
  ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_from_adjunction.

Definition free_ring_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_from_adjunction.

(** * The comparison clauses, at [≈] *)

(* [GAFT] is [Qed], so its output does not reduce and no [eq_refl] is
   available; the header quotes the refusal.  What IS available is the
   uniqueness of left adjoints, and [left_adjoints_agree]
   (Instance/Rng/Free.v:844) is [Defined], so the comparison morphism has a
   name and the unit clause can be stated. *)

Definition free_rng_ab_via_GAFT_agrees : `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoints_agree (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction.

Definition free_ring_via_GAFT_agrees :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoints_agree (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set.

(* RECORDED STATEMENT CHANGE, PR "algebraic carriers are sets"
   (2026-09-17), AND THE MEASURED REASON.  This clause and the four other
   [_mon] ones below used to be stated about [free_ring_via_GAFT] and are
   now stated about [free_ring_via_GAFT_from_adjunction], the circular
   reading.  Nothing is lost -- the same theorem, "left adjoints to
   [Rng_Forget] agree", is still in tree against the monoid-ring route --
   but the WITNESS is a different constant and that must be said.

   THE OBSTRUCTION IS [free_ring_via_mon]'S OWN [Set] PIN, not the new
   solution set's fault and not repairable from this file.  Measured,
   [About] under [Set Printing Universes]:

     free_ring_via_mon@{u u0 … u7} : Functor@{u Set Set u …}
     free_ring_via_ab@{u u0 … u8}  : Functor@{u u1 u1 u0 …}

   -- the monoid route pins the hom AND proof universes of [Sets] to
   [Set], where the abelian-group route leaves them free.  The
   non-circular [free_ring_via_GAFT] carries the [Set < carrier] side
   condition of the [Prop] index (see the solution-set section above), so
   the two cannot be compared, and the attempt is refused with

     The term "free_ring_via_mon" has type "Sets@{Set u} ⟶ Rng@{u Set}"
     while it is expected to have type "Sets@{u0 u1} ⟶ Rng@{u1 u0}"
     (universe inconsistency: Cannot enforce Set = u0 because Set < u0)

   (generated universe names replaced positionally; everything else
   verbatim).  [free_ring_via_GAFT_agrees] above, against
   [free_ring_via_ab], is unaffected and IS about the non-circular
   constant.  Widening [free_ring_via_mon] would be a change to
   Instance/Rng/Free.v and belongs to its own commit, exactly as the
   widening of Adjunction/SpanningArrow.v did. *)
Definition free_ring_via_GAFT_agrees_mon :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoints_agree (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(* Theory/Adjunction.v:407's [left_adjoint_iso] inhabits the same three
   types.  The two terms are NOT identified -- that theorem is [Qed], so no
   component of it reduces and none can be named, which is exactly why the
   transparent donor is used above. *)

Example free_rng_ab_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoint_iso Rng_Forget_Ab _ FreeRngAb (`2 free_rng_ab_via_GAFT)
    free_rng_ab_adjunction.

Example free_ring_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoint_iso Rng_Forget _ free_ring_via_ab (`2 free_ring_via_GAFT)
    free_ring_via_ab_adjunction_set.

Example free_ring_via_GAFT_agrees_mon_via_left_adjoint_iso :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoint_iso Rng_Forget _ free_ring_via_mon
    (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(** ** The comparison morphisms, named *)

Definition free_rng_ab_via_GAFT_comparison (A : Ab)
  : `1 free_rng_ab_via_GAFT A ~{Rng}~> FreeRngAb A :=
  adj_left_compare (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction A.

Definition free_ring_via_GAFT_comparison (X : Sets)
  : `1 free_ring_via_GAFT X ~{Rng}~> free_ring_via_ab X :=
  adj_left_compare (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set X.

Definition free_ring_via_GAFT_comparison_mon (X : Sets)
  : `1 free_ring_via_GAFT_from_adjunction X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set X.

(* [left_adjoints_agree] is [Defined], so each comparison IS the component
   of the corresponding natural isomorphism, by [eq_refl] and not by an
   argument. *)

Example free_rng_ab_via_GAFT_comparison_is_component (A : Ab) :
  to (projT1 free_rng_ab_via_GAFT_agrees A)
    = free_rng_ab_via_GAFT_comparison A := eq_refl.

Example free_ring_via_GAFT_comparison_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees X)
    = free_ring_via_GAFT_comparison X := eq_refl.

Example free_ring_via_GAFT_comparison_mon_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees_mon X)
    = free_ring_via_GAFT_comparison_mon X := eq_refl.

(** ** The unit clauses

    Mac Lane's exercise asks for the comparison to be compatible with the
    universal arrows, not merely for an isomorphism to exist.  Composing
    the comparison with the AFT-produced unit gives the explicit
    construction's own unit -- the ring-expression insertion on one side,
    the word insertion on the other. *)

Theorem free_rng_ab_via_GAFT_unit (A : Ab) :
  fmap[Rng_Forget_Ab] (free_rng_ab_via_GAFT_comparison A)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_rng_ab_via_GAFT) A
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.
Proof.
  exact (adj_left_compare_unit (`2 free_rng_ab_via_GAFT)
           free_rng_ab_adjunction A).
Qed.

Theorem free_ring_via_GAFT_unit (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_ring_via_GAFT) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT)
           free_ring_via_ab_adjunction_set X).
Qed.

Theorem free_ring_via_GAFT_unit_mon (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison_mon X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        (`2 free_ring_via_GAFT_from_adjunction) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT_from_adjunction)
           free_ring_via_mon_adjunction_set X).
Qed.

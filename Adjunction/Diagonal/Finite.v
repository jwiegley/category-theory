(** * The finite-shape rows of the diagonal-adjoint table *)

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   nLab:      https://ncatlab.org/nlab/show/coequalizer
   nLab:      https://ncatlab.org/nlab/show/pullback
   nLab:      https://ncatlab.org/nlab/show/pushout
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Mac Lane, "Categories for the Working Mathematician", Springer GTM 5,
   2nd ed., §IV.2 (p. 90) tabulates a long list of adjunctions together
   with their units and counits, and Exercise 6 of that section asks for
   the entries of four of its rows: the equalizer, the coequalizer, the
   pullback and the pushout.  Each is an instance of the sandwich
   colim ⊣ Δ ⊣ lim at a FIXED finite shape --

     - the walking parallel pair (Instance/Parallel.v's [Parallel]): a
       limit over it is an equalizer, a colimit a coequalizer;
     - the walking cospan ([Roof^op], Structure/Span.v's [Cospan]): a
       limit over it is a pullback;
     - the walking span ([Roof], [Span]): a colimit over it is a pushout

   -- so the FUNCTORS come by instantiation.  The content of the exercise
   is the other column of the table: what the unit and the counit ARE,
   read as the elementary data those four words name.  Riehl, "Category
   Theory in Context", Dover 2016, states the general form as Proposition
   4.6.1 with Exercise 4.6.ii asking for exactly this identification (the
   counit is the universal cone, the unit the universal cocone); Awodey,
   "Category Theory", Oxford 2nd ed. 2010, runs the same argument for the
   special shapes in §9.3, and treats the four elementary universal
   properties themselves in §5.2 and §3.4.

   Read the four rows in the two variances and the pattern is visible:

     Δ[Parallel] ⊣ Eq      counit = the equalizing arrow (at ParX)
                           unit   = an isomorphism (see below)
     Coeq ⊣ Δ[Parallel]    unit   = the coequalizing arrow (at ParY)
                           counit = an isomorphism
     Δ[Roof^op] ⊣ Pb       counit = the two projections (at RNeg, RPos)
                           unit   = an isomorphism
     Po ⊣ Δ[Roof]          unit   = the two injections (at RNeg, RPos)
                           counit = an isomorphism

   THE "IDENTITY" ENTRIES ARE NOT IDENTITIES, AND THIS FILE DOES NOT
   CLAIM THEY ARE.  For Δ ⊣ lim the unit at x is a morphism
   x ~> lim(Δ[J](x)) -- an arrow between two DIFFERENT objects -- so
   [dia_unit L x = id[x]] is not merely false but ill-typed, which is
   measured below as a rejection of TYPING kind.  What is true, and is
   what the table's entry means, is that the unit is INVERTIBLE, with the
   limiting leg at a distinguished shape object as its inverse; that is
   [dia_unit_iso], and dually [dia_counit_iso].  Both hold over any shape
   satisfying the sufficient condition [ShapeLinked] introduced here, and
   all three finite shapes satisfy it. *)

(* What is consumed here, and what is built

   CONSUMED, not rebuilt:

     - Adjunction/Diagonal/Limit.v, in full: [HasLimitsOfShape],
       [HasColimitsOfShape], [LimitFunctor], [ColimitFunctor],
       [Diagonal_Limit_Adjunction], [Colimit_Diagonal_Adjunction],
       [lim_counit], [colim_unit], [lim_counit_is_limit_leg],
       [colim_unit_is_colimit_inj], [lim_transpose_to],
       [lim_transpose_to_commutes], [colim_transpose_from],
       [colim_transpose_from_commutes], [Cocone_of], [lim_leg],
       [lim_med_eq], [colim_inj], [colim_med_eq], [colim_med_commutes],
       [colim_med_unique], [lim_leg_coherence], [colim_inj_coherence],
       [limits_iff_diagonal_right_adjoint],
       [colimits_iff_diagonal_left_adjoint], [Sets_HasLimitsOfShape],
       [Sets_HasColimitsOfShape], and its witness object [DiagBoolSet].
       Not one general limit or colimit result is re-proved; every row
       below is that file applied at a fixed shape.  The issue's
       Current-state section says "Adjunction/Diagonal/Product.v only
       covers the binary-product shape"; that is STALE, since
       Adjunction/Diagonal/Limit.v covers every shape.  A second entry of
       that section is stale differently: it lists Structure/Cocone.v
       among the in-tree donors, and NO SUCH FILE EXISTS -- [Cocone] and
       [ACocone] are declared in Structure/Cone.v, which is the donor
       actually consumed here.
     - Instance/Parallel.v: [Parallel], [ParObj], [ParX], [ParY],
       [ParOne], [APair].
     - Instance/Roof.v: [Roof], [RoofObj], [RNeg], [RZero], [RPos],
       [ZeroNeg], [ZeroPos], [IdZero], and the [roof_laws] hint database.
     - Structure/Span.v: [ASpan], [Span], [Cospan].
     - Structure/Equalizer.v: [Equalizer], [Coequalizer].
     - Structure/Equalizer/Fork.v: [IsEqualizer], [HasEqualizers],
       [fork_eq], [eq_desc], [equalizer_monic],
       [equalizer_is_equalizer].
     - Structure/Coequalizer.v: [IsCoequalizer], [HasCoequalizers],
       [cofork], [coeq_desc], [coequalizer_epic],
       [coequalizer_is_coequalizer].
     - Theory/Morphisms/Stability.v: [IsPullback], [is_pullback_commutes],
       [is_pullback_ump], [is_pullback_pullback], [pullback_is_pullback].
     - Structure/Pullback.v: [Pullback], [Pull], [HasPullbacks].
     - Structure/Pullback/Limit.v: [Pullback_to_Universal],
       [Pullback_Limit], [Pushout_Limit].
     - Structure/Pushout.v: [IsPushout], [pushout_apex], [HasPushouts].
     - Theory/Morphisms/CokernelPair.v: [IsPushoutSquare],
       [Build_IsPushoutSquare], [is_pushout_square_commutes],
       [is_pushout_square_ump], [is_pushout_square_pushout].
     - Theory/Morphisms.v: [Monic], [Epic], [monic], [epic].

   BUILT here:

     - The four rows: [EqualizerFunctor], [CoequalizerFunctor],
       [PullbackFunctor], [PushoutFunctor], each with its adjunction
       ([Diagonal_Equalizer_Adjunction], [Coequalizer_Diagonal_Adjunction],
       [Diagonal_Pullback_Adjunction], [Pushout_Diagonal_Adjunction]) and
       its named unit or counit.  Every statement is COVARIANT: no [^op]
       occurs in the type of the coequalizer or pushout row, and the
       [Roof^op] that occurs in the pullback row is the SHAPE, not a
       dualized ambient category.
     - The identifications the exercise asks for, against the ELEMENTARY
       APIs rather than the cone machinery: [eq_counit_IsEqualizer],
       [coeq_unit_IsCoequalizer], [pb_counit_IsPullback] and
       [po_unit_IsPushoutSquare].
     - Their packagings [HasLimitsOfShape_HasEqualizers],
       [HasColimitsOfShape_HasCoequalizers],
       [HasLimitsOfShape_HasPullbacks] and
       [HasColimitsOfShape_HasPushouts], so a consumer who has limits of
       one of these shapes gets the elementary class whose chosen arrow IS
       the counit (dually the unit) component.
     - [ShapeLinked] with [dia_unit_iso] and [dia_counit_iso]: the
       "identity" entries of the table, at their true strength.  Those
       three head a general constant-diagram development of ELEVEN
       constants over an arbitrary [J] and [C], the other eight being
       [lim_const_legs], [colim_const_injs], [dia_unit],
       [dia_unit_strict], [dia_unit_leg], [dia_counit],
       [dia_counit_strict] and [dia_counit_inj].  [ShapeLinked] itself
       carries only BOUNDS ([u0 <= u], [u1 <= u]) and no equation; the
       other ten, with the four obligations of the two [_iso] constants,
       are exactly the fourteen constants carrying [u0 = u2], as the
       universes section below records.
     - Four transports, [IsEqualizer_respects], [IsCoequalizer_respects],
       [IsPullback_respects] and [IsPushoutSquare_respects].  None of the
       three elementary records is stated up to [≈] in its distinguished
       arrow, and each is needed here at an arrow that differs by a unit
       residue from the one the tree's own conversions produce, so the
       transports are not optional.  The last of the four is the primal
       one read at [C^op] -- a [:=] with no tactic.
     - The pushout half of the shape/elementary bridge:
       [po_inj_commutes], [po_legs], [po_legs_coherence], [po_cocone],
       [po_inj_ump] and [po_inj_IsPushoutSquare].  THE TREE HAS THE
       PULLBACK BRIDGE AND NOT THE PUSHOUT ONE, measured:
       Structure/Pullback/Limit.v gives [Pullback_to_Universal], but its
       [Pushout_Limit] (:60) is a bare alias for [Colimit] with no
       conversion to any pushout universal property, and outside this file
       [IsPushoutSquare] occurs only in Theory/Morphisms/CokernelPair.v,
       its probe, and Instance/Sets/CokernelPair.v, none of which builds
       one from a colimit.  So the pullback row is REUSE and the pushout
       row is CONSTRUCTION, and the two are not symmetric in cost.
     - Four degenerate readings used by the witnesses:
       [equalizer_of_equal_pair], [coequalizer_of_equal_pair],
       [pullback_of_identity], [pushout_of_identity].
     - [ACospan], the cospan of a pair of morphisms as a diagram of shape
       [Roof^op].  It is [ASpan] in [C^op], opposed -- not a new functor:
       Structure/Pullback/Limit.v already writes that composite inline,
       and it is given a name here because three results need it.
     - The four biconditionals by instantiation, and the readbacks tying
       the two Roof rows to Structure/Span.v's [Span] and [Cospan] and the
       two Parallel rows to Structure/Equalizer.v's [Equalizer] and
       [Coequalizer], all at [eq_refl].

   NO EQUALIZER, COEQUALIZER, PULLBACK OR PUSHOUT FUNCTOR EXISTED IN THE
   TREE.  That absence was measured by the issue's author with a
   multi-line-aware sweep over the TYPES of every constant in the tree's
   802 [.v] files (803 with this one), finding seven constants whose name
   mentions one of those words and whose type contains [⟶], in all seven
   of which the [⟶] is in an ARGUMENT
   (a diagram [Parallel ⟶ C]) rather than in the constant's own type.  A
   first run of that sweep reported SIX: it keyed on
   [Definition|Theorem|Lemma|Instance] and so missed
   [Structure/Coequalizer/Split.v:132]'s [split_coequalizer_preserved],
   which is declared with [Corollary].  Widening the keyword list is what
   yields seven, and the characterization is unchanged by it -- that
   constant's own type is an [IsCoequalizer], its [F : C ⟶ D] being an
   argument.  The
   check re-run here is weaker and only corroborating: a name sweep for a
   [Definition] or [Program Definition] called [EqualizerFunctor],
   [CoequalizerFunctor], [PullbackFunctor] or [PushoutFunctor] returns
   nothing outside this file. *)

(* Strengths, measured strict-first

   THIRTY-THREE identifications hold at Leibniz [eq] and are shipped as
   [eq_refl] Examples -- every [Example] in the file is one.  The ones
   worth knowing:

     - the unit of Δ ⊣ lim IS the transpose of the identity
       ([dia_unit_strict]), and dually the counit of colim ⊣ Δ IS the
       transpose of the identity ([dia_counit_strict]);
     - each row's unit or counit IS the general one
       ([eq_row_counit], [coeq_row_unit], [pb_row_counit],
       [po_row_unit]);
     - each row functor's object action IS the (co)limit object
       ([EqualizerFunctor_obj] and its three siblings);
     - the chosen apex of each derived elementary class IS the (co)limit
       object ([HasEqualizers_apex] and its three siblings);
     - the six counit/unit components of the four rows (1+1+2+2) are
       the six legs with a unit residue ([eq_arrow_strict],
       [coeq_arrow_strict], [pb_fst_strict], [pb_snd_strict],
       [po_in1_strict], [po_in2_strict]);
     - the legs of [ACospan f g] and [ASpan f g] ARE f and g
       ([acospan_left], [acospan_right], [aspan_left], [aspan_right]);
     - the two Roof-indexed functor categories' objects ARE [Cospan C]
       and [Span C], and all four shape hypotheses ARE the tree's own
       aliases ([pullback_shape_hypothesis] and its three siblings).

   [pb_leg_IsPullback] is not an [eq_refl] but is the same kind of fact:
   it is Structure/Pullback/Limit.v's [Pullback_to_Universal] read through
   the apex-pinned predicate, supplied by [:=] WITH NO TACTIC, so the
   limit apex and both limiting legs land on the pullback's apex and
   projections by conversion alone.

   SEVEN strict attempts were made and REJECTED.  Every one was verified
   by STRIPPING the guard and reading the whole error; [Fail]'s own
   message is INVISIBLE under this repository's [coqc] invocation (a
   [Fail] command that succeeds prints nothing at all), so reading the
   stripped error is the only way to learn the failure kind here.  Six are
   CONVERSION failures ("cannot unify") and one is a TYPING failure; each
   is stated so it can be pinned as a probe.

     R1. [eq_arrow L F = lim_leg L F ParX] -- the counit component carries
         a residual [∘ id]; the control at [lim_leg L F ParX ∘ id]
         succeeds.  This is Adjunction/Diagonal/Limit.v's own rejection R1
         instantiated at [Parallel], not a new phenomenon.
     R2. [coeq_arrow M F = colim_inj M F ParY] -- dually, an [id ∘]
         residue; control at [id ∘ colim_inj M F ParY].
     R3. [pb_fst P F = lim_leg P F RNeg] -- as R1 at [Roof^op].
     R4. [pushout_inj1 Q F = colim_inj Q F RNeg] -- as R2 at [Roof].
     R5. [dia_unit L x = id[x]] -- a TYPING failure, and the sharpest
         measurement in the file: the two sides have codomains
         [lim_obj L (Δ[J](x))] and [x], so the table's "unit = identity"
         entry is not a proposition one can even state at [eq].  What
         replaces it is [dia_unit_iso].
     R6. [Opposite Roof = Roof] -- the walking span is not its own
         opposite on the nose, which is why the pullback and pushout rows
         are two separate sections over two different shapes rather than
         one section read twice.
     R7. [Opposite Parallel = Parallel] -- likewise for the walking
         parallel pair; the equalizer and coequalizer rows share a SHAPE
         but not a variance, and it is [Colimit F := Limit (F^op)] that
         dualizes, not the shape.

   A NOTATION HAZARD BIT WHILE MEASURING R6 AND R7, AND IT PRODUCED A
   FALSE PASS.  Written [Roof^op = Roof], the negative fails with "The
   term Roof has type Category while it is expected to have type ?C ⟶ ?D"
   -- Functor/Opposite.v opens [functor_scope], and in the argument of an
   [eq] there is no expected type for [Bind Scope category_scope with
   Category] to rescue, so [^op] parses as the FUNCTOR opposite and the
   command fails on notation rather than on the mathematics.  Both
   negatives must be spelled [Opposite Roof] and [Opposite Parallel].
   Inside the file the same [Roof^op] is harmless, every occurrence
   sitting in an argument or ascription position whose expected type is
   [Category]. *)

(* Universes, measured off BOTH the binder and the constraint block

   Every [Category@{...}] occurrence in the file -- 119 of them, swept
   over the printed signatures of all 140 constants -- identifies the hom
   universe with the proof universe.  That is entirely the donors' doing,
   and the attribution is probed rather than assumed: in a section
   declaring [Universes uo uh up] with [Constraint uh < up], NINE donors
   are each rejected ALONE with "Cannot enforce up = uh" --
   [HasLimitsOfShape], [Limit], [Diagonal], [Fun] (as [[Parallel, D]]),
   [Opposite], [IsEqualizer], [IsCoequalizer], [IsPullback] and
   [IsPushoutSquare].  At most EIGHT of the nine are independent:
   [HasLimitsOfShape] is defined as [∀ F, Limit F], so its rejection does
   not discriminate against [Limit]'s.  Meanwhile the hom type
   [x ~{D}~> y], the identity
   [id[x]] AND [Cone] are all ACCEPTED at those very levels.  The [Cone]
   control is what makes the attribution discriminate: the cone RECORD is
   innocent, so "the cone vocabulary" would be the wrong cause.  Nothing
   in this file adds to the identification, and none of it is claimed
   unavoidable.

   FOURTEEN constants carry a universe EQUATION, all of them [u0 = u2],
   and they are exactly the two GENERIC constant-diagram sections:
   [lim_const_legs], [colim_const_injs], [dia_unit], [dia_unit_strict],
   [dia_unit_leg], [dia_unit_iso] with its two obligations, and the five
   [dia_counit] counterparts.  The equation identifies the shape's
   hom-and-proof universe with the ambient category's; it is INHERITED
   from Adjunction/Diagonal/Limit.v, whose header records exactly [u0 = u2]
   for [LimitFunctor] and its neighbours, and whose binder-versus-block
   disagreement is inherited too -- [dia_unit]'s binder reads
   [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}], which looks as
   though the two hom levels are independent, while the block carries
   [u0 = u2].

   THE FOUR ROW SECTIONS CARRY NO UNIVERSE EQUATION AT ALL.  Their blocks
   are bounds only.  Read that at its true strength, which is smaller than
   it looks: nothing is thereby made more general.  The identification the
   general theorem records as an equation is DISCHARGED BY INSTANTIATION
   -- the row constants read [Parallel@{u3 u0}] and [Roof@{u3 u0}], taking
   C's hom universe as the shape's own -- which they may do because both
   shapes are universe-polymorphic with an EMPTY constraint block
   ([Parallel@{u u0} : Category@{u u0 u0}] and likewise [Roof], measured).
   What a consumer gains is only that no equation between two categories
   THEY declared ever appears.

   Neither finite shape carries [Set].  This is worth saying because the
   degenerate rows of the same table do: Adjunction/Diagonal/Limit.v
   records that [_0]'s own signature is [Category@{u Set Set}], so its
   empty-shape corollaries inherit a [Set] pin.  [Parallel] and [Roof] do
   not, and so neither does any general result below.

   TWENTY constants carry the literal [Set], and they are exactly the
   concrete [Sets] witness block, from [SetsConstTrue] onwards.  The token
   appears in universe INSTANCES in the signature ([Sets@{Set u}],
   [DiagBoolSet@{u Set}]); the only [Set] in any constraint BLOCK is the
   bound [Set < u].  The cause is the two-element carrier: [DiagBoolSet]
   is itself polymorphic ([DiagBoolSet@{u u0} : obj[Sets@{u0 u}]], no
   [Set] in its binder), and it is universe MINIMIZATION at the use site
   that instantiates its relation universe at [Set].  The obvious
   alternative explanation is ruled out by a control: this tree records a
   hazard by which a [Sets]-morphism whose [proper_morphism] is left to
   instance resolution pins the carrier universe, with the repair being to
   supply the certificate as an explicit pointwise term -- BOTH forms were
   compiled here and BOTH give the identical [Sets@{Set u}], so the
   resolution hazard is not what is happening.  A third variant, the same
   morphism inside a section declaring [Constraint Set < o], elaborates at
   [Sets@{o so}] with [Set] appearing only as a strict lower bound, so the
   pin is liftable.  It is NOT lifted here: the witness block is a
   witness, and Adjunction/Diagonal/Limit.v's own [Sets] witness carries
   the same [Set < u].  Not claimed unavoidable.

   The four [Sets_*] adjunctions and the four [Sets_Has*] classes are
   [Set]-FREE -- the pin begins only where [bool] does. *)

(* Non-vacuity

   All four rows are inhabited at [Sets], which is both complete and
   cocomplete in tree: [Sets_Diagonal_Equalizer_Adjunction],
   [Sets_Coequalizer_Diagonal_Adjunction],
   [Sets_Diagonal_Pullback_Adjunction] and
   [Sets_Pushout_Diagonal_Adjunction], with the four elementary classes
   [DiagSets_HasEqualizers], [DiagSets_HasCoequalizers],
   [Sets_HasPullbacks_of_shape] and [Sets_HasPushouts_of_shape] falling
   out of the rows.

   That the witnesses are not degenerate is PROVED, in two senses and for
   all four rows.  First, the diagrams are not constant: each is built
   from [SetsConstTrue], the constant map at [true] on the two-element
   discrete setoid, and [SetsPairDiagram_not_constant],
   [SetsCospanDiagram_not_constant] and [SetsSpanDiagram_not_constant]
   show that the arrow the diagram carries is not an identity (each is
   [sets_const_true_not_id] by conversion, the conversion itself pinned by
   [sets_pair_arrow_strict] and its two siblings).  A constant diagram
   sends every arrow to an identity, so none of the three is one.  Second,
   the four objects produced are not subsingletons:
   [sets_equalizer_two_elements], [sets_coequalizer_two_elements],
   [sets_pullback_two_elements] and [sets_pushout_two_elements] each
   exhibit two elements that are provably not [≈]-equal.  The two elements
   are obtained by transporting [true] and [false] backwards along the
   four isomorphisms [sets_equalizer_iso], [sets_coequalizer_iso],
   [sets_pullback_iso] and [sets_pushout_iso], and the separation is
   discharged by [discriminate] on the underlying [bool]; no induction on
   a (co)limit construction could yield a negative.  Those four
   isomorphisms are not assumed either -- each is an instance of one of
   the four degenerate readings, so what is computed is the equalizer of a
   pair whose legs agree, the pullback of a cospan one of whose legs is an
   identity, and their duals.

   The route the witnesses do NOT take is worth naming: they use the
   UNIVERSAL PROPERTY, not the construction, so nothing here computes the
   compatible-family setoid of Instance/Sets/Complete.v or the inductive
   quotient of Instance/Sets/Cocomplete.v.  No [eq_refl] below evaluates a
   (co)limit element. *)

(* What is NOT delivered

     - THE FOUR [Sets]-LEVEL CLASSES ARE SECOND INHABITANTS, AND NO
       AGREEMENT WITH THE FIRST IS CLAIMED.  Each of
       [DiagSets_HasEqualizers], [DiagSets_HasCoequalizers],
       [Sets_HasPullbacks_of_shape] and [Sets_HasPushouts_of_shape]
       duplicates a pre-existing inhabitant of its class --
       [Adjunction/GAFT/Sets.v:175]'s [Sets_HasEqualizers],
       [Instance/Sets/Coequalizer.v:293]'s [Sets_HasCoequalizers],
       [Instance/Sets/Pullback.v:393]'s [Sets_HasPullbacks] and
       [Instance/Sets/Pushout.v:185]'s [Sets_HasPushouts].  The four
       built here come from the general theorem applied to
       [Sets_HasLimitsOfShape]; the four pre-existing ones are direct
       constructions.  NOTHING relates the two -- no isomorphism, no
       [≈], not even a comparison of chosen apexes -- so these are a
       second route to the same classes and not an identification of
       the tree's own objects.  The names differ deliberately, and the
       four here are plain [Definition]s rather than [Instance]s, so
       the pre-existing exported instances still win every resolution.
     - NO CONVERSE for any of the four packagings.  Nothing builds
       [HasLimitsOfShape Parallel C] from [HasEqualizers C], nor any of
       the other three directions.  The obstruction is real rather than
       neglect: the elementary classes quantify over PAIRS and SPANS,
       whose diagrams are [APair f g], [ASpan f g] and [ACospan f g], and
       a general [F : Parallel ⟶ C] is not one of those records on the
       nose; transporting a limit along an isomorphism of diagrams is not
       attempted and no such transport is used.  So each [Has*] result
       here runs one way only.
     - No uniqueness for any of the four functors.  [left_adjoint_iso] and
       [right_adjoint_iso] are not instantiated, so nothing says
       [EqualizerFunctor] is THE right adjoint of [Δ[Parallel]] up to
       natural isomorphism, and the four biconditionals assert only the
       EXISTENCE of an adjoint, not that it is the one named.
     - No naturality for any identification.  [eq_counit_IsEqualizer] and
       its three siblings are statements about one diagram at a time;
       nothing exhibits the assignment as natural in the diagram, and
       there is no comparison of the four elementary APIs as functors.
     - Nothing about preservation, reflection or creation of these four
       shapes, and no instantiation of RAPL or LAPC at these rows.
     - The pushout row is NOT derived from the pullback row.  It could
       have been: [fun H F => H (Opposite_Functor F)] inhabits
       [HasLimitsOfShape (Opposite Roof) (Opposite C) →
       HasColimitsOfShape Roof C], and that was compiled to check.  It is
       not used, because every statement downstream would then be about
       [C^op] and the covariance the issue asks for would be lost.
     - [ShapeLinked] is a SUFFICIENT condition and is not claimed to be
       connectedness.  No general theory of connected shapes is developed,
       nothing relates it to Structure/Groupoid/Connected.v's [Connected],
       and no shape is exhibited that fails it.
     - The four row functors and the four [Has*] results are plain
       [Definition]s, NOT registered [Instance]s: each takes a
       [HasLimitsOfShape] or [HasColimitsOfShape] parameter, which is not
       a class, so resolution could never produce it.  This follows
       Adjunction/Diagonal/Limit.v, which gives the same reason for
       [LimitFunctor].
     - No wide equalizers or wide pullbacks: Structure/Equalizer/Wide.v
       and Structure/Pullback/Wide.v are untouched, and nothing here says
       anything about the shapes they use.
     - No relation to Structure/Pullback/Reduction.v's interdefinability
       results, so nothing connects these four rows to each other.
     - No concrete computation of any of the four objects: the witnesses
       are up to isomorphism only, and no element of any (co)limit is
       evaluated.
     - Nothing at a shape other than these three, and no finite-shape
       row for the terminal or initial object -- those are the degenerate
       rows Adjunction/Diagonal/Limit.v already delivers. *)

(* Axiom status and counts

   140/140 constants report "Closed under the global context".  Method:
   [Print Module Category.Adjunction.Diagonal.Finite] with whitespace
   FLATTENED before matching (it wraps long entries onto their own lines)
   enumerates 140 names; the file declares no [Record], [Class] or
   [Inductive], so there is no unlisted [Build_*] constructor, and the
   count decomposes as 136 source-declared names plus the 4 [Program]
   obligations of [dia_unit_iso] and [dia_counit_iso], which a [.glob]
   sweep does not record.  The file's third [Program], [SetsConstTrue],
   generates no obligation at all -- its [proper_morphism] is discharged
   during elaboration.  Each name was queried by its FULLY QUALIFIED name,
   in seven chunks of twenty, and the same chunking was used to pair every
   [About] output with its constant (an unchunked run cannot be parsed
   reliably: [About]'s record boundaries are ambiguous, and interleaving
   [Print Assumptions] gives a separator that is). *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * Transport of the elementary predicates along [≈] *)

(* None of the three elementary records is stated up to [≈] in its
   distinguished arrow, and each is needed here at an arrow that differs
   from the one the tree's conversions produce by a unit residue.  These
   four transports supply exactly that. *)

Section Respects.

Context {C : Category}.

Lemma IsEqualizer_respects {x y q : C} {f g : x ~> y} {e e' : q ~> x} :
  IsEqualizer f g q e → e ≈ e' → IsEqualizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (eq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsCoequalizer_respects {x y q : C} {f g : x ~> y} {e e' : y ~> q} :
  IsCoequalizer f g q e → e ≈ e' → IsCoequalizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (coeq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsPullback_respects {x y z P : C} {f : x ~> z} {g : y ~> z}
  {p1 p1' : P ~> x} {p2 p2' : P ~> y} :
  IsPullback f g P p1 p2 → p1 ≈ p1' → p2 ≈ p2' →
  IsPullback f g P p1' p2'.
Proof.
  intros H H1 H2.
  unshelve econstructor.
  - rewrite <- H1, <- H2; exact (is_pullback_commutes H).
  - intros Q q1 q2 Hc.
    unshelve eapply Build_Unique.
    + exact (unique_obj (is_pullback_ump H Q q1 q2 Hc)).
    + split.
      * rewrite <- H1.
        exact (fst (unique_property (is_pullback_ump H Q q1 q2 Hc))).
      * rewrite <- H2.
        exact (snd (unique_property (is_pullback_ump H Q q1 q2 Hc))).
    + intros v [Hv1 Hv2].
      apply (uniqueness (is_pullback_ump H Q q1 q2 Hc)).
      split.
      * rewrite H1; exact Hv1.
      * rewrite H2; exact Hv2.
Defined.

End Respects.

(* The pushout square is [IsPullback] in the opposite category, and the
   two hom-setoids agree there, so its transport is the primal one read at
   [C^op]: a [:=] with no tactic. *)
Definition IsPushoutSquare_respects {C : Category} {x y z P : C}
  {f : x ~> y} {g : x ~> z} {i1 i1' : y ~> P} {i2 i2' : z ~> P} :
  IsPushoutSquare f g P i1 i2 → i1 ≈ i1' → i2 ≈ i2' →
  IsPushoutSquare f g P i1' i2' :=
  @IsPullback_respects (C^op) y z x P f g i1 i1' i2 i2'.

(** * Constant diagrams: the unit and the counit at a linked shape *)

(* [j0] links the shape [J] when every object of [J] is joined to it by a
   single arrow, in one direction or the other.  Over a CONSTANT diagram
   any such arrow becomes an equation between two legs, because the
   constant diagram sends every arrow to an identity; so over a linked
   shape all the legs of a cone (dually, all the injections of a cocone)
   over a constant diagram agree.  This is a sufficient condition for
   connectedness of the shape, not the general one, and it is all three
   finite shapes below need. *)
Definition ShapeLinked {J : Category} (j0 : J) : Type :=
  ∀ j : J, (j0 ~{J}~> j) + (j ~{J}~> j0).

Section ConstantLimit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Lemma lim_const_legs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  lim_leg L (Δ[J](x)) j ≈ lim_leg L (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j0).
    + symmetry; exact (lim_leg_coherence L (Δ[J](x)) k).
    + apply id_left.
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j).
    + symmetry; apply id_left.
    + exact (lim_leg_coherence L (Δ[J](x)) k).
Qed.

(* The unit of Δ ⊣ lim, named. *)
Definition dia_unit (x : C) : x ~{C}~> lim_obj L (Δ[J](x)) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) x.

(* The unit IS the transpose of the identity, on the nose. *)
Example dia_unit_strict (x : C) :
  dia_unit x = lim_transpose_to L (@id ([J, C]) (Δ[J](x))) := eq_refl.

Lemma dia_unit_leg (x : C) (j : J) :
  lim_leg L (Δ[J](x)) j ∘ dia_unit x ≈ id[x].
Proof.
  exact (lim_transpose_to_commutes L
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

(* Over a linked shape the unit is invertible, its inverse being the
   limiting leg at the linking object.  This is the precise sense in
   which the unit of the equalizer and pullback rows "is the identity". *)
Program Definition dia_unit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  x ≅ lim_obj L (Δ[J](x)) := {|
  to   := dia_unit x;
  from := lim_leg L (Δ[J](x)) j0
|}.
Next Obligation.
  refine (lim_med_eq L (@limit_cone J C (Δ[J](x)) (L (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite comp_assoc, dia_unit_leg, id_left.
    symmetry; exact (lim_const_legs x j0 Hl j).
  - apply id_right.
Qed.
Next Obligation. apply dia_unit_leg. Qed.

End ConstantLimit.

Section ConstantColimit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).

Lemma colim_const_injs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  colim_inj M (Δ[J](x)) j ≈ colim_inj M (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (colim_inj M (Δ[J](x)) j ∘ fmap[Δ[J](x)] k).
    + symmetry; apply id_right.
    + exact (colim_inj_coherence M (Δ[J](x)) k).
  - transitivity (colim_inj M (Δ[J](x)) j0 ∘ fmap[Δ[J](x)] k).
    + symmetry; exact (colim_inj_coherence M (Δ[J](x)) k).
    + apply id_right.
Qed.

(* The counit of colim ⊣ Δ, named. *)
Definition dia_counit (x : C) : colim_obj M (Δ[J](x)) ~{C}~> x :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) x.

Example dia_counit_strict (x : C) :
  dia_counit x = colim_transpose_from M (@id ([J, C]) (Δ[J](x)))
  := eq_refl.

Lemma dia_counit_inj (x : C) (j : J) :
  dia_counit x ∘ colim_inj M (Δ[J](x)) j ≈ id[x].
Proof.
  exact (colim_transpose_from_commutes M
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

Program Definition dia_counit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  colim_obj M (Δ[J](x)) ≅ x := {|
  to   := dia_counit x;
  from := colim_inj M (Δ[J](x)) j0
|}.
Next Obligation. apply dia_counit_inj. Qed.
Next Obligation.
  refine (colim_med_eq M (@limit_cone (J^op) (C^op) ((Δ[J](x))^op)
                            (M (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite <- comp_assoc, dia_counit_inj, id_right.
    symmetry; exact (colim_const_injs x j0 Hl j).
  - apply id_left.
Qed.

End ConstantColimit.

(** * The three finite shapes are linked *)

Definition Parallel_linked : @ShapeLinked Parallel ParX.
Proof.
  intro j; destruct j.
  - left; exact ((true; ParIdX) : ParX ~{Parallel}~> ParX).
  - left; exact ((true; ParOne) : ParX ~{Parallel}~> ParY).
Defined.

Definition Roof_linked : @ShapeLinked Roof RZero.
Proof.
  intro j; destruct j.
  - left; exact ZeroNeg.
  - left; exact IdZero.
  - left; exact ZeroPos.
Defined.

Definition Roofop_linked : @ShapeLinked (Roof^op) RZero.
Proof.
  intro j; destruct j.
  - right; exact ZeroNeg.
  - left; exact IdZero.
  - right; exact ZeroPos.
Defined.

(** * Row 1: equalizers as the right adjoint of Δ[Parallel] *)

Section EqualizerRow.

Context {C : Category}.
Context (L : HasLimitsOfShape Parallel C).

Definition EqualizerFunctor : [Parallel, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Equalizer_Adjunction :
  @Diagonal C Parallel ⊣ EqualizerFunctor := Diagonal_Limit_Adjunction L.

Definition eq_counit (F : Parallel ⟶ C) : Δ[Parallel](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* Mac Lane's counit entry for the equalizer row: the equalizing arrow. *)
Definition eq_arrow (F : Parallel ⟶ C) : lim_obj L F ~{C}~> F ParX :=
  transform[eq_counit F] ParX.

Example eq_arrow_strict (F : Parallel ⟶ C) :
  eq_arrow F = lim_leg L F ParX ∘ id := eq_refl.

Lemma eq_leg_is_arrow (F : Parallel ⟶ C) :
  lim_leg L F ParX ≈ eq_arrow F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F ParX). Qed.

(* The identification against the ELEMENTARY equalizer API. *)
Definition eq_counit_IsEqualizer {x y : C} (f g : x ~> y) :
  IsEqualizer f g (lim_obj L (APair f g)) (eq_arrow (APair f g)) :=
  IsEqualizer_respects (equalizer_is_equalizer f g (L (APair f g)))
    (eq_leg_is_arrow (APair f g)).

Definition HasLimitsOfShape_HasEqualizers : HasEqualizers C :=
  {| equalizer := fun x y f g =>
       (lim_obj L (APair f g);
         (eq_arrow (APair f g); eq_counit_IsEqualizer f g)) |}.

(* Mac Lane's unit entry: the identity, in the precise sense that the
   unit is invertible with the limiting leg as its inverse. *)
Definition eq_unit_iso (x : C) : x ≅ lim_obj L (Δ[Parallel](x)) :=
  dia_unit_iso L ParX Parallel_linked x.

End EqualizerRow.

(** * Row 2: coequalizers as the left adjoint of Δ[Parallel] *)

Section CoequalizerRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Parallel C).

Definition CoequalizerFunctor : [Parallel, C] ⟶ C := ColimitFunctor M.

Definition Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor ⊣ @Diagonal C Parallel := Colimit_Diagonal_Adjunction M.

Definition coeq_unit (F : Parallel ⟶ C) : F ⟹ Δ[Parallel](colim_obj M F) :=
  colim_unit M F.

(* Mac Lane's unit entry for the coequalizer row: the coequalizing arrow. *)
Definition coeq_arrow (F : Parallel ⟶ C) : F ParY ~{C}~> colim_obj M F :=
  transform[coeq_unit F] ParY.

Example coeq_arrow_strict (F : Parallel ⟶ C) :
  coeq_arrow F = id ∘ colim_inj M F ParY := eq_refl.

Lemma coeq_inj_is_arrow (F : Parallel ⟶ C) :
  colim_inj M F ParY ≈ coeq_arrow F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F ParY). Qed.

Definition coeq_unit_IsCoequalizer {x y : C} (f g : x ~> y) :
  IsCoequalizer f g (colim_obj M (APair f g)) (coeq_arrow (APair f g)) :=
  IsCoequalizer_respects (coequalizer_is_coequalizer f g (M (APair f g)))
    (coeq_inj_is_arrow (APair f g)).

Definition HasColimitsOfShape_HasCoequalizers : HasCoequalizers C :=
  {| coeq := fun x y f g =>
       (colim_obj M (APair f g);
         (coeq_arrow (APair f g); coeq_unit_IsCoequalizer f g)) |}.

Definition coeq_counit_iso (x : C) : colim_obj M (Δ[Parallel](x)) ≅ x :=
  dia_counit_iso M ParX Parallel_linked x.

End CoequalizerRow.

(** * Row 3: pullbacks as the right adjoint of Δ[Roof^op] *)

Section PullbackRow.

Context {C : Category}.
Context (L : HasLimitsOfShape (Roof^op) C).

(* The two legs of a cospan, read covariantly in C. *)
Definition cospan_left (F : Roof^op ⟶ C) : F RNeg ~{C}~> F RZero :=
  fmap[F] (ZeroNeg : RNeg ~{Roof^op}~> RZero).

Definition cospan_right (F : Roof^op ⟶ C) : F RPos ~{C}~> F RZero :=
  fmap[F] (ZeroPos : RPos ~{Roof^op}~> RZero).

Definition PullbackFunctor : [Roof^op, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Pullback_Adjunction :
  @Diagonal C (Roof^op) ⊣ PullbackFunctor := Diagonal_Limit_Adjunction L.

Definition pb_counit (F : Roof^op ⟶ C) : Δ[Roof^op](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* Mac Lane's counit entry for the pullback row: the two projections. *)
Definition pb_fst (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RNeg :=
  transform[pb_counit F] RNeg.

Definition pb_snd (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RPos :=
  transform[pb_counit F] RPos.

Example pb_fst_strict (F : Roof^op ⟶ C) :
  pb_fst F = lim_leg L F RNeg ∘ id := eq_refl.

Example pb_snd_strict (F : Roof^op ⟶ C) :
  pb_snd F = lim_leg L F RPos ∘ id := eq_refl.

Lemma pb_leg_is_fst (F : Roof^op ⟶ C) : lim_leg L F RNeg ≈ pb_fst F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RNeg). Qed.

Lemma pb_leg_is_snd (F : Roof^op ⟶ C) : lim_leg L F RPos ≈ pb_snd F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RPos). Qed.

(* The limiting legs of a cospan ARE its pullback projections.  This is
   Structure/Pullback/Limit.v's [Pullback_to_Universal] read through the
   apex-pinned predicate: a [:=] with no tactic, the apex and both
   projections landing on the nose. *)
Definition pb_leg_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (lim_leg L F RNeg) (lim_leg L F RPos) :=
  pullback_is_pullback _ _ (Pullback_to_Universal F (L F)).

(* The identification against the ELEMENTARY pullback API. *)
Definition pb_counit_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (pb_fst F) (pb_snd F) :=
  IsPullback_respects (pb_leg_IsPullback F)
    (pb_leg_is_fst F) (pb_leg_is_snd F).

(* A cospan in C, as a diagram of shape Roof^op. *)
Definition ACospan {x y z : C} (f : x ~> z) (g : y ~> z) : Roof^op ⟶ C :=
  (@ASpan (C^op) z x y f g)^op.

Example acospan_left {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_left (ACospan f g) = f := eq_refl.

Example acospan_right {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_right (ACospan f g) = g := eq_refl.

Definition HasLimitsOfShape_HasPullbacks : HasPullbacks C :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback (pb_counit_IsPullback (ACospan f g)) |}.

Definition pb_unit_iso (x : C) : x ≅ lim_obj L (Δ[Roof^op](x)) :=
  dia_unit_iso L RZero Roofop_linked x.

End PullbackRow.

(** * Row 4: pushouts as the left adjoint of Δ[Roof] *)

Section PushoutRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Roof C).

Definition span_left (F : Roof ⟶ C) : F RZero ~{C}~> F RNeg :=
  fmap[F] ZeroNeg.

Definition span_right (F : Roof ⟶ C) : F RZero ~{C}~> F RPos :=
  fmap[F] ZeroPos.

Definition PushoutFunctor : [Roof, C] ⟶ C := ColimitFunctor M.

Definition Pushout_Diagonal_Adjunction :
  PushoutFunctor ⊣ @Diagonal C Roof := Colimit_Diagonal_Adjunction M.

Definition po_unit (F : Roof ⟶ C) : F ⟹ Δ[Roof](colim_obj M F) :=
  colim_unit M F.

(* Mac Lane's unit entry for the pushout row: the two injections. *)
Definition pushout_inj1 (F : Roof ⟶ C) : F RNeg ~{C}~> colim_obj M F :=
  transform[po_unit F] RNeg.

Definition pushout_inj2 (F : Roof ⟶ C) : F RPos ~{C}~> colim_obj M F :=
  transform[po_unit F] RPos.

Example po_in1_strict (F : Roof ⟶ C) :
  pushout_inj1 F = id ∘ colim_inj M F RNeg := eq_refl.

Example po_in2_strict (F : Roof ⟶ C) :
  pushout_inj2 F = id ∘ colim_inj M F RPos := eq_refl.

Lemma po_inj_is_in1 (F : Roof ⟶ C) : colim_inj M F RNeg ≈ pushout_inj1 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RNeg). Qed.

Lemma po_inj_is_in2 (F : Roof ⟶ C) : colim_inj M F RPos ≈ pushout_inj2 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RPos). Qed.

(* The colimiting square of a span commutes. *)
Lemma po_inj_commutes (F : Roof ⟶ C) :
  colim_inj M F RNeg ∘ span_left F ≈ colim_inj M F RPos ∘ span_right F.
Proof.
  transitivity (colim_inj M F RZero).
  - exact (colim_inj_coherence M F (ZeroNeg : RZero ~{Roof}~> RNeg)).
  - symmetry.
    exact (colim_inj_coherence M F (ZeroPos : RZero ~{Roof}~> RPos)).
Qed.

(* Every hom-setoid of [Roof] is trivially true, so a functor out of it
   carries any two parallel arrows to [≈]-equal morphisms; the identity
   arrows go to identities.  These two facts discharge every case of the
   cocone coherence below. *)
Lemma roof_fmap_any (F : Roof ⟶ C) {a b : Roof} (k k' : a ~{Roof}~> b) :
  fmap[F] k ≈ fmap[F] k'.
Proof. apply fmap_respects; exact I. Qed.

Lemma roof_fmap_id (F : Roof ⟶ C) (a : Roof) (k : a ~{Roof}~> a) :
  fmap[F] k ≈ id.
Proof.
  rewrite (roof_fmap_any F k (id[a])).
  apply fmap_id.
Qed.

(* The cocone under a span determined by a competing commuting square:
   the leg at the apex RZero is forced to be the common composite. *)
Definition po_legs (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q) (j : Roof) : F j ~{C}~> Q :=
  match j return F j ~{C}~> Q with
  | RNeg  => q1
  | RZero => q1 ∘ span_left F
  | RPos  => q2
  end.

Lemma po_legs_coherence (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∀ (a b : Roof) (k : a ~{Roof}~> b),
    po_legs F Q q1 q2 b ∘ fmap[F] k ≈ po_legs F Q q1 q2 a.
Proof.
  intros a b k.
  destruct a, b; simpl in k; auto with roof_laws; simpl.
  - rewrite (roof_fmap_id F RNeg k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroNeg : RZero ~{Roof}~> RNeg)).
    reflexivity.
  - rewrite (roof_fmap_id F RZero k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroPos : RZero ~{Roof}~> RPos)).
    symmetry; exact Hc.
  - rewrite (roof_fmap_id F RPos k); apply id_right.
Qed.

Definition po_cocone (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) : Cocone F :=
  @Cocone_of Roof C F Q (po_legs F Q q1 q2) (po_legs_coherence F Q q1 q2 Hc).

Lemma po_inj_ump (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∃! u : colim_obj M F ~> Q,
    u ∘ colim_inj M F RNeg ≈ q1 ∧ u ∘ colim_inj M F RPos ≈ q2.
Proof.
  unshelve eapply Build_Unique.
  - exact (colim_med M (po_cocone F Q q1 q2 Hc)).
  - split.
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RNeg).
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RPos).
  - intros v [Hv1 Hv2].
    apply (colim_med_unique M (po_cocone F Q q1 q2 Hc)).
    intro j; destruct j.
    + exact Hv1.
    + rewrite <- (colim_inj_coherence M F
                    (ZeroNeg : RZero ~{Roof}~> RNeg)).
      now rewrite comp_assoc, Hv1.
    + exact Hv2.
Qed.

(* The colimiting injections of a span form a pushout square, in the
   apex-pinned sense of Theory/Morphisms/CokernelPair.v. *)
Definition po_inj_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (colim_inj M F RNeg) (colim_inj M F RPos) :=
  Build_IsPushoutSquare (po_inj_commutes F) (po_inj_ump F).

(* The identification against the ELEMENTARY pushout API. *)
Definition po_unit_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (pushout_inj1 F) (pushout_inj2 F) :=
  IsPushoutSquare_respects (po_inj_IsPushoutSquare F)
    (po_inj_is_in1 F) (po_inj_is_in2 F).

Example aspan_left {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_left (ASpan f g) = f := eq_refl.

Example aspan_right {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_right (ASpan f g) = g := eq_refl.

Definition HasColimitsOfShape_HasPushouts : HasPushouts C :=
  {| pushout := fun x y z f g =>
       is_pushout_square_pushout (po_unit_IsPushoutSquare (ASpan f g)) |}.

Definition po_counit_iso (x : C) : colim_obj M (Δ[Roof](x)) ≅ x :=
  dia_counit_iso M RZero Roof_linked x.

End PushoutRow.

(** * Degenerate rows of the elementary data *)

(* Four small readings of the elementary predicates, used below to compute
   the four (co)limit objects at a concrete witness.  Each is proved from
   the descent property alone, with no reference to the shape categories. *)

Section Degenerate.

Context {C : Category}.

(* A pair whose two legs agree is equalized by an isomorphism onto the
   common domain: the identity forks such a pair, and the equalizing
   arrow is monic. *)
Definition equalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : q ~> x} (E : IsEqualizer f f q e) : q ≅ x.
Proof.
  assert (Hf : f ∘ id[x] ≈ f ∘ id[x]) by reflexivity.
  pose proof (eq_desc E (id[x]) Hf) as D.
  unshelve refine {| to := e; from := unique_obj D |}.
  - exact (unique_property D).
  - apply (@monic _ _ _ e (equalizer_monic f f E)).
    rewrite comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(* Dually, a pair whose two legs agree is coequalized by an isomorphism
   onto the common codomain. *)
Definition coequalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : y ~> q} (E : IsCoequalizer f f q e) : q ≅ y.
Proof.
  assert (Hf : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  pose proof (coeq_desc E (id[y]) Hf) as D.
  unshelve refine {| to := unique_obj D; from := e |}.
  - exact (unique_property D).
  - apply (@epic _ _ _ e (coequalizer_epic f f E)).
    rewrite <- comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(* The pullback of a cospan one of whose legs is an identity is the
   domain of the other leg, projected by the second projection. *)
Definition pullback_of_identity {y z P : C} (g : y ~> z)
  {p1 : P ~> z} {p2 : P ~> y} (H : IsPullback (id[z]) g P p1 p2) : P ≅ y.
Proof.
  assert (Hc : id[z] ∘ g ≈ g ∘ id[y]).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pullback_ump H y g (id[y]) Hc) as D.
  pose proof (is_pullback_ump H P p1 p2 (is_pullback_commutes H)) as DP.
  unshelve refine {| to := p2; from := unique_obj D |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pullback_commutes H).
        apply id_left.
      * rewrite comp_assoc, (snd (unique_property D)).
        apply id_left.
    + apply (uniqueness DP); split; apply id_right.
Defined.

(* Dually, the pushout of a span one of whose legs is an identity is the
   codomain of the other leg, injected by the second injection. *)
Definition pushout_of_identity {x z P : C} (g : x ~> z)
  {i1 : x ~> P} {i2 : z ~> P} (H : IsPushoutSquare (id[x]) g P i1 i2) :
  P ≅ z.
Proof.
  assert (Hc : g ∘ id[x] ≈ id[z] ∘ g).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pushout_square_ump H z g (id[z]) Hc) as D.
  pose proof (is_pushout_square_ump H P i1 i2
                (is_pushout_square_commutes H)) as DP.
  unshelve refine {| to := unique_obj D; from := i2 |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite <- comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pushout_square_commutes H).
        apply id_right.
      * rewrite <- comp_assoc, (snd (unique_property D)).
        apply id_right.
    + apply (uniqueness DP); split; apply id_left.
Defined.

End Degenerate.

(** * Non-vacuity: the four rows at Sets *)

Definition SetsEq : HasLimitsOfShape Parallel Sets :=
  Sets_HasLimitsOfShape Parallel.

Definition SetsParallelColim : HasColimitsOfShape Parallel Sets :=
  Sets_HasColimitsOfShape Parallel.

Definition SetsPb : HasLimitsOfShape (Roof^op) Sets :=
  Sets_HasLimitsOfShape (Roof^op).

Definition SetsPo : HasColimitsOfShape Roof Sets :=
  Sets_HasColimitsOfShape Roof.

Definition Sets_Diagonal_Equalizer_Adjunction :
  @Diagonal Sets Parallel ⊣ EqualizerFunctor SetsEq :=
  Diagonal_Equalizer_Adjunction SetsEq.

Definition Sets_Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor SetsParallelColim ⊣ @Diagonal Sets Parallel :=
  Coequalizer_Diagonal_Adjunction SetsParallelColim.

Definition Sets_Diagonal_Pullback_Adjunction :
  @Diagonal Sets (Roof^op) ⊣ PullbackFunctor SetsPb :=
  Diagonal_Pullback_Adjunction SetsPb.

Definition Sets_Pushout_Diagonal_Adjunction :
  PushoutFunctor SetsPo ⊣ @Diagonal Sets Roof :=
  Pushout_Diagonal_Adjunction SetsPo.

(* All four elementary classes are inhabited at Sets by the rows above. *)

Definition DiagSets_HasEqualizers : HasEqualizers Sets :=
  HasLimitsOfShape_HasEqualizers SetsEq.

Definition DiagSets_HasCoequalizers : HasCoequalizers Sets :=
  HasColimitsOfShape_HasCoequalizers SetsParallelColim.

Definition Sets_HasPullbacks_of_shape : HasPullbacks Sets :=
  HasLimitsOfShape_HasPullbacks SetsPb.

Definition Sets_HasPushouts_of_shape : HasPushouts Sets :=
  HasColimitsOfShape_HasPushouts SetsPo.

(** ** A concrete, non-constant diagram *)

(* The constant map at [true] on the two-element discrete setoid.  Nothing
   below is a constant DIAGRAM: [SetsConstTrue] is not an identity, which
   is what [sets_const_true_not_id] records. *)
Program Definition SetsConstTrue : DiagBoolSet ~{Sets}~> DiagBoolSet := {|
  morphism := fun _ => true
|}.

Lemma sets_const_true_not_id : SetsConstTrue ≈ id[DiagBoolSet] → False.
Proof. intro H; discriminate (H false). Qed.

Definition SetsPairDiagram : Parallel ⟶ Sets :=
  APair SetsConstTrue SetsConstTrue.

Lemma SetsPairDiagram_not_constant :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsCospanDiagram : Roof^op ⟶ Sets :=
  ACospan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsCospanDiagram_not_constant :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsSpanDiagram : Roof ⟶ Sets :=
  ASpan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsSpanDiagram_not_constant :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

(** ** The four objects computed, and each proved not a subsingleton *)

Lemma sets_two_elements_of_iso {X : Sets} (i : X ≅ DiagBoolSet) :
  { a : carrier X & { b : carrier X & a ≈ b → False } }.
Proof.
  exists (from i true).
  exists (from i false).
  intro H.
  pose proof (iso_to_from i true) as H1.
  pose proof (iso_to_from i false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to i (from i true)).
    - symmetry; exact H1.
    - transitivity (to i (from i false)).
      + apply (proper_morphism (to i)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.

Definition sets_equalizer_iso :
  lim_obj SetsEq SetsPairDiagram ≅ DiagBoolSet :=
  equalizer_of_equal_pair SetsConstTrue
    (eq_counit_IsEqualizer SetsEq SetsConstTrue SetsConstTrue).

Definition sets_coequalizer_iso :
  colim_obj SetsParallelColim SetsPairDiagram ≅ DiagBoolSet :=
  coequalizer_of_equal_pair SetsConstTrue
    (coeq_unit_IsCoequalizer SetsParallelColim SetsConstTrue SetsConstTrue).

Definition sets_pullback_iso :
  lim_obj SetsPb SetsCospanDiagram ≅ DiagBoolSet :=
  pullback_of_identity SetsConstTrue
    (pb_counit_IsPullback SetsPb SetsCospanDiagram).

Definition sets_pushout_iso :
  colim_obj SetsPo SetsSpanDiagram ≅ DiagBoolSet :=
  pushout_of_identity SetsConstTrue
    (po_unit_IsPushoutSquare SetsPo SetsSpanDiagram).

Definition sets_equalizer_two_elements :
  { a : carrier (lim_obj SetsEq SetsPairDiagram)
  & { b : carrier (lim_obj SetsEq SetsPairDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_equalizer_iso.

Definition sets_coequalizer_two_elements :
  { a : carrier (colim_obj SetsParallelColim SetsPairDiagram)
  & { b : carrier (colim_obj SetsParallelColim SetsPairDiagram)
    & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_coequalizer_iso.

Definition sets_pullback_two_elements :
  { a : carrier (lim_obj SetsPb SetsCospanDiagram)
  & { b : carrier (lim_obj SetsPb SetsCospanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pullback_iso.

Definition sets_pushout_two_elements :
  { a : carrier (colim_obj SetsPo SetsSpanDiagram)
  & { b : carrier (colim_obj SetsPo SetsSpanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pushout_iso.

(** ** Readbacks pinning the concrete diagrams *)

Example sets_pair_arrow_strict :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    = SetsConstTrue := eq_refl.

Example sets_cospan_arrow_strict :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    = SetsConstTrue := eq_refl.

Example sets_span_arrow_strict :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    = SetsConstTrue := eq_refl.

(** * Readbacks of the four rows against their adjunctions *)

Section Readbacks.

Context {C : Category}.

Example eq_row_counit (L : HasLimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @counit ([Parallel, C]) C (@Diagonal C Parallel) (EqualizerFunctor L)
          (Diagonal_Equalizer_Adjunction L) F = eq_counit L F := eq_refl.

Example coeq_row_unit (M : HasColimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @unit C ([Parallel, C]) (CoequalizerFunctor M) (@Diagonal C Parallel)
        (Coequalizer_Diagonal_Adjunction M) F = coeq_unit M F := eq_refl.

Example pb_row_counit (L : HasLimitsOfShape (Roof^op) C)
  (F : Roof^op ⟶ C) :
  @counit ([Roof^op, C]) C (@Diagonal C (Roof^op)) (PullbackFunctor L)
          (Diagonal_Pullback_Adjunction L) F = pb_counit L F := eq_refl.

Example po_row_unit (M : HasColimitsOfShape Roof C) (F : Roof ⟶ C) :
  @unit C ([Roof, C]) (PushoutFunctor M) (@Diagonal C Roof)
        (Pushout_Diagonal_Adjunction M) F = po_unit M F := eq_refl.

(* The four functors' object actions are the four (co)limit objects. *)

Example EqualizerFunctor_obj (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[EqualizerFunctor L] (APair f g) = lim_obj L (APair f g) := eq_refl.

Example CoequalizerFunctor_obj (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[CoequalizerFunctor M] (APair f g) = colim_obj M (APair f g) := eq_refl.

Example PullbackFunctor_obj (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  fobj[PullbackFunctor L] (ACospan f g) = lim_obj L (ACospan f g) := eq_refl.

Example PushoutFunctor_obj (M : HasColimitsOfShape Roof C)
  {S x y : C} (f : S ~> x) (g : S ~> y) :
  fobj[PushoutFunctor M] (ASpan f g) = colim_obj M (ASpan f g) := eq_refl.

(* The chosen (co)limit of the elementary classes built above is the
   (co)limit object of the corresponding diagram, on the nose. *)

Example HasEqualizers_apex (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@equalizer C (HasLimitsOfShape_HasEqualizers L) x y f g)
    = lim_obj L (APair f g) := eq_refl.

Example HasCoequalizers_apex (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@coeq C (HasColimitsOfShape_HasCoequalizers M) x y f g)
    = colim_obj M (APair f g) := eq_refl.

Example HasPullbacks_apex (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback C (HasLimitsOfShape_HasPullbacks L) x y z f g)
    = lim_obj L (ACospan f g) := eq_refl.

Example HasPushouts_apex (M : HasColimitsOfShape Roof C)
  {x y z : C} (f : x ~> y) (g : x ~> z) :
  pushout_apex (@pushout C (HasColimitsOfShape_HasPushouts M) x y z f g)
    = colim_obj M (ASpan f g) := eq_refl.

End Readbacks.

(** * The four rows as biconditionals, and the tree's shape vocabulary *)

Section Biconditionals.

Context (C : Category).

(* Riehl's Proposition 4.6.1 at the three finite shapes, by instantiation.
   Read the right-hand sides exactly: they assert the EXISTENCE of an
   adjoint functor, not that it is the one named above. *)

Definition equalizers_iff_diagonal_right_adjoint :
  HasLimitsOfShape Parallel C
    ↔ { R : [Parallel, C] ⟶ C & @Diagonal C Parallel ⊣ R } :=
  limits_iff_diagonal_right_adjoint Parallel C.

Definition coequalizers_iff_diagonal_left_adjoint :
  HasColimitsOfShape Parallel C
    ↔ { K : [Parallel, C] ⟶ C & K ⊣ @Diagonal C Parallel } :=
  colimits_iff_diagonal_left_adjoint Parallel C.

Definition pullbacks_iff_diagonal_right_adjoint :
  HasLimitsOfShape (Roof^op) C
    ↔ { R : [Roof^op, C] ⟶ C & @Diagonal C (Roof^op) ⊣ R } :=
  limits_iff_diagonal_right_adjoint (Roof^op) C.

Definition pushouts_iff_diagonal_left_adjoint :
  HasColimitsOfShape Roof C
    ↔ { K : [Roof, C] ⟶ C & K ⊣ @Diagonal C Roof } :=
  colimits_iff_diagonal_left_adjoint Roof C.

(* The objects of the two Roof-indexed functor categories ARE the tree's
   spans and cospans, and the two shape hypotheses ARE "every cospan has
   a pullback-limit" and "every span has a pushout-colimit", in the
   vocabulary of Structure/Span.v and Structure/Pullback/Limit.v. *)

Example cospan_is_pullback_shape : obj[[Roof^op, C]] = Cospan C := eq_refl.

Example span_is_pushout_shape : obj[[Roof, C]] = Span C := eq_refl.

Example pullback_shape_hypothesis :
  HasLimitsOfShape (Roof^op) C = (∀ F : Cospan C, Pullback_Limit F)
  := eq_refl.

Example pushout_shape_hypothesis :
  HasColimitsOfShape Roof C = (∀ F : Span C, Pushout_Limit F) := eq_refl.

(* The two Parallel rows likewise land on Structure/Equalizer.v's own
   aliases. *)

Example equalizer_shape_hypothesis :
  HasLimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Equalizer F) := eq_refl.

Example coequalizer_shape_hypothesis :
  HasColimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Coequalizer F)
  := eq_refl.

End Biconditionals.

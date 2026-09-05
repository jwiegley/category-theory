Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(** * The copower is left adjoint to the power *)

(* nLab:      https://ncatlab.org/nlab/show/copower
   nLab:      https://ncatlab.org/nlab/show/power
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor

   Sources, cited BY LOCATION, both read off the RENDERED page (the printed
   page number and the PDF page number differ by a constant +9, verified):

     - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
       (Springer GTM 5), section IV.2, exercise 12, printed p. 90
       (PDF p. 99), item [maclane:IV.2:ex12], VERBATIM:

         "12. If X is a set and C a category with powers and copowers,
          prove that the copower  c ↦ X · c  is left adjoint to the power
          c ↦ c^X."

       That is the theorem this file exists for, and
       [Copower_Power_Adjunction] is its name.

     - Mac Lane, same book, section IV.7, exercise 1, printed p. 102
       (PDF p. 111), item [maclane:IV.7:ex1], VERBATIM AS PRINTED:

         "1. Interpret the definition  C(X · a, c) ≅ Set(X, C(c, a))  of
          copowers X · a in C as an adjunction with parameter a."

       See the misprint disclosure below.  Nothing in THIS section of the
       file discharges Ex 1; the quote is carried because the variance
       argument settles what the parameter half must say.

   ★ THE PRINTED FORM OF §IV.7 Ex 1 HAS THE VARIANCE WRONG.  It is a
   MISPRINT, not an OCR artifact: the page was read at 400 dpi and the
   [pdftotext] layer agrees, printing "Set (X, C(c, a))".  The reason it
   cannot be what is meant is a variance count and not a matter of taste:

     LHS  C(X·a, c)        is COVARIANT     in c
     RHS  Set(X, C(a,c))   is COVARIANT     in c   <- consistent
     RHS  Set(X, C(c,a))   is CONTRAVARIANT in c   <- as printed

   A covariant and a contravariant functor of [c] cannot be naturally
   isomorphic in [c].  Mathematically a map OUT of the X-fold copower of [a]
   is an X-indexed FAMILY of maps [a → c], which is [Set(X, C(a,c))].  The
   correct form is therefore [C(X · a, c) ≅ Set(X, C(a,c))], and that is
   what Structure/Limit/Power/Hom.v's [copower_hom_iso] already proves --
   [copower_hom_functor J b] is [c ↦ ∏_J C(b,c)], covariant, exactly as the
   variance count requires.  The printed form is disclosed here rather than
   reproduced, and rather than silently "fixed".

   ★ THE ISSUE AND THE BOOK PARAMETRIZE DIFFERENT VARIABLES.  Ex 12 above
   fixes the SET X and varies the object; Ex 1 fixes nothing and asks for the
   bifunctor [(X, a) ↦ X · a] read as an adjunction with parameter [a], whose
   assembled right adjoint is the HOM-FUNCTOR.  The issue's own item 4 asks
   instead for the INDEX SET as the parameter -- the variable its item 3
   (= Ex 12) holds FIXED.  Both readings are true and neither implies the
   other; this section delivers Ex 12, at a fixed [J].

   PRIOR ART -- THE ISSUE'S "Current state" IS STALE, AND HERE IS THE
   CRITERION.

   THE CRITERION, stated once and used for every count below: "any
   whole-word occurrence in any [.v] file OTHER THAN THIS ONE, comments
   included", reproduced by

     rg -l -w -e '<token>' -g '*.v' \
        -g '!Structure/Limit/Power/Adjunction.v' .

   Issue #366 says: "Absent.  Searches for [copower], [cotensor] and
   [tensoring] return nothing."  That is FALSE for [copower], which AT THE
   BASE COMMIT (every count in this paragraph is taken there, before this
   file and its probe existed) occurs in
   THREE files -- Structure/Limit/Power.v (361 lines),
   Structure/Limit/Power/Hom.v (548) and Test/ProbePower.v -- all delivered
   by issue #321, and the module path the issue "suggests",
   Structure/Limit/Power.v, is ALREADY TAKEN by it.  What IS absent is the
   FUNCTOR: [Power_Functor], [Copower_Functor], [power_fmap] and
   [copower_fmap] each return ZERO files, so functoriality in the object
   variable is genuinely new.  The instrument discriminates: [power] itself
   returns 42 files and [Monoid] 91.  (At HEAD, excluding only this file,
   the probe adds one to each of [copower] and [power] and one to three of
   the four functor names; the collision sweep below therefore excludes the
   probe as well.)

   Accordingly a QA correction on the issue supersedes its first three work
   items with "consume, do not rebuild", and this file consumes: #321's
   [power], [copower], [power_ev], [copower_inj], [power_ump], [copower_ump],
   [power_desc], [copower_desc], and -- for the adjunction proper -- its two
   already-proved characterizing bijections [power_hom_iso_at] and
   [copower_hom_iso_at].  Nothing below re-derives a universal property.

   WHY THIS IS A NEW FILE AND NOT AN EXTENSION -- MEASURED, NOT PREFERRED

   Structure/Limit/Power.v CANNOT host the adjunction: it would be a
   DEPENDENCY CYCLE, not merely a cost.  Structure/Limit/Power/Hom.v Requires
   Structure/Limit/Power.vo (visible in .Makefile.coq.d at the
   [Structure/Limit/Power/Hom.vo :] rule), so Power.v cannot Require Power/Hom.v
   back, and the two [_at] bijections this file composes live in Power/Hom.v.

   Structure/Limit/Power/Hom.v COULD have hosted it -- Theory/Adjunction is a
   MARGINAL cost of exactly ONE module there -- but that would place
   Theory/Adjunction behind that file's one existing consumer,
   Test/ProbePower.v (measured: it is the only [.v] file in the tree that
   Requires Power/Hom), and would mix the characterizing-isomorphism layer
   with the adjunction layer.  The margin is also not stable for the rest of
   #366: Adjunction/Parameter.v, which the parameter half wants, is a marginal
   FORTY-SIX on that same base.  A sibling costs no existing file anything,
   since nothing Requires it.

   Closures, measured as transitive in-project [.vo] dependencies EXCLUDING
   the file itself, over .Makefile.coq.d: Structure/Limit/Power/Hom.v is 36
   and this file is 38, the two added modules being Power/Hom.v itself and
   Theory/Adjunction.v.  Adjunction/GAFT.v is 42 and is untouched.

   WHAT IS DELIVERED HERE

   [Power_Functor J : C ⟶ C], the endofunctor [b ↦ J ⋔ b], with all three
   functor laws PROVED from [power_desc]'s uniqueness clause -- the issue's
   item 2, which had no prior art of any kind.

   [Copower_Functor J : C ⟶ C] costs NOTHING, and that is the one place the
   op-trick in #321's design pays in full.  [copower] is DEFINITIONALLY
   [@power (C^op)], so [Copower_Functor J := Opposite_Functor
   (@Power_Functor (C^op) HC J)] needs no obligation, no tactic and no proof
   text: Functor/Opposite.v's [Opposite_Functor] is a plain [Definition] that
   passes all three law fields through unchanged.  Four [eq_refl] readbacks
   pin what that buys -- the object action IS [copower J b], the arrow action
   IS the op-power's [power_fmap], the double opposite returns the op-power
   functor ON THE NOSE, and the arrow action IS the mediator [copower_desc]
   produces.

   TWO REFUTATIONS, MEASURED STRICT-FIRST, WITH THEIR VERBATIM ERRORS, SO A
   PROBE CAN PIN THEM.  Both were compiled alone with the other stripped.

   (1) CONVERSION.  A hand-built DIRECT copower functor -- object action
   [b ↦ copower J b], arrow action the [copower_desc] mediator, three
   obligations -- agrees with [Copower_Functor J] on BOTH data fields at
   [eq_refl], and the WHOLE RECORD is refused:

     The term "eq_refl" has type
      "Copower_Functor_direct = Copower_Functor_direct"
     while it is expected to have type
      "Copower_Functor_direct = Copower_Functor J"
     (cannot unify "Copower_Functor_direct" and "Copower_Functor J").

   The two data fields agreeing is what says nothing is LOST by taking the
   cheap route; the record differing is the three [Program]-rebuilt law
   fields, as everywhere else in this tree.

   (2) TYPING, and it is a DIFFERENT KIND, told apart by the error text
   rather than by a label.  Stated with BOTH sides' implicits written out,
   [@Copower_Functor C HC J = @Power_Functor (C^op) HC J := eq_refl] is
   refused at the STATEMENT, before any [eq_refl] is examined, the two
   constants not sharing a type ([C ⟶ C] against [C^op ⟶ C^op]); the
   error carries no "cannot unify" clause:

     The term "Power_Functor J" has type "C^op ⟶ C^op"
     while it is expected to have type "C ⟶ C".

   That spelling matters.  Written [Copower_Functor J = @Power_Functor
   (C^op) HC J], with the left side's category IMPLICIT, the statement
   ELABORATES -- the elaborator re-solves that category as [C^op], leaving
   the coproduct instance an unresolved evar -- and the error fires at
   [eq_refl] instead, which is negative 3's fact at [C^op] and not a type
   mismatch at all; a first draft of this paragraph quoted exactly that
   error, and the probe's negative 2 records the episode.  The same
   equation at [C] ([Copower_Functor J = Power_Functor J]) is negative 3,
   and it is CONVERSION: both sides share [C ⟶ C] and the error ends in
   [cannot unify "Copower_Functor J" and "Power_Functor J"].

   So [Copower_Functor J] is [Opposite_Functor] OF the op-power functor and
   is NOT that functor; what holds on the nose is the double opposite,
   [copower_functor_double_op] below.

   [Copower_Power_Adjunction J : Copower_Functor J ⊣ Power_Functor J] is
   Ex 12.  Its hom-set isomorphism is the COMPOSITE of #321's two bijections
   rather than a fresh derivation from the universal properties, which is
   what "consume, do not rebuild" means here and is the issue's stated
   reviewer check that the file does not fork the API.  The composite is
   well-founded because the two bijections share their right-hand side ON THE
   NOSE: [copower_hom_iso_at (copower_ump J b) c] and
   [power_hom_iso_at (power_ump J c) b] both land at the [Sets]-power
   [J ⋔ C(b,c)], written [cp_middle b c] below, so they compose with no
   comparison map inserted and [cp_adj_iso] is a [:=] with no tactic.  Only
   the two naturality clauses of [Build_Adjunction'] are proved, each in a
   handful of lines through [cp_to_uniq].

   That shared landing is not asserted: [cp_copower_at_middle] and
   [cp_power_at_middle] supply the two DONORS AS TERMS at a type naming
   [cp_middle b c], so each typechecks only if that donor's target is
   [cp_middle b c] up to delta.  An [X = X] tautology would have said nothing
   here and is deliberately not what is written.  The ascriptions are also
   not vacuous through a coercion: at the SWAPPED middle [cp_middle c b] the
   copower one is refused, and the error prints the donor's real target,

     The term "copower_hom_iso_at (copower_ump J b) c" has type
      "… ≅ (J ⋔ {| carrier := b ~{ C }~> c; is_setoid := homset b c |})%power"
     while it is expected to have type "… ≅ cp_middle J c b".

   which is a plain typing mismatch -- no "cannot unify", no universe clause.

   UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE BLOCK

   Reproduce with [Set Printing Universes.] and [About]; reading either alone
   gets this wrong, in both directions, and it does so here.

   Every constant is over [C : Category@{u u0 u0}] -- hom identified with
   proof by REUSING the level variable in the BINDER, with no equation in any
   block saying so.  That identification is inherited: it is [Category]'s own
   shape at every donor, and nothing here adds to it.

     [Power_Functor@{u u0 u1 u2 u3 u4 u5}] and
     [Copower_Functor@{u u0 u1 u2 u3 u4 u5 u6}] have blocks of BOUNDS ONLY --
     NO equation anywhere -- and the INDEX stays free of [C]'s hom universe:
     [Power_Functor]'s index [Type@{u3}] carries only [u3 <= u1] and
     [u3 <= u2], both against the class's own levels.  So §A is universe-free
     in the sense that matters.

     [cp_adj_iso] and [Copower_Power_Adjunction] carry FOUR equations,
     [u0 = u1], [u0 = u2], [u0 = u4] and [u0 = u5], identifying [C]'s
     hom-and-proof level with all four index slots of [HasIndexedProducts]
     and [HasIndexedCoproducts], plus the bound [u6 <= u0] on the index.
     Read as a boundary a consumer meets: at an index universe strictly
     ABOVE [C]'s hom-and-proof level, [Power_Functor], [Copower_Functor]
     and [power_fmap] are ACCEPTED while [Copower_Power_Adjunction] is
     REFUSED ("Cannot enforce ji <= ..."), pinned as probe negative 14 with
     those three as its controls.

   ★ THOSE FOUR ARE NOT CREATED BY COMPOSING, AND THE ISOLATING EXPERIMENT
   SAYS SO.  Applying [copower_hom_iso_at] to [copower_ump J b] ALONE already
   carries [u0 = u4] and [u0 = u5]; applying [power_hom_iso_at] to
   [power_ump J c] ALONE already carries [u0 = u1] and [u0 = u2]; the
   composite carries exactly their union and nothing further.  Measured by
   defining four constants -- one per donor applied alone, one pairing them
   without composing, one composing them -- and reading all four blocks.

   The CAUSE is a binder, not a block, which is why the naive measurement
   misses it: the bare donor reads
   [copower_hom_iso_at@{u u0 u1 u2 u3} : ∀ {C : Category@{u3 u u}}
   {J : Type@{u}} …] -- hom, proof AND INDEX all at the ONE level [u] -- while
   its block contains no equation at all.  Applying it at a [copower_ump]
   drawn from the CLASS, whose index slots are separate levels, turns that
   binder identification into the block equations above.  This is #321's own
   recorded [iprod_hom_iso] propagation, now localized: it is per-donor, and
   it is already present before any composition.  It is NOT claimed
   unavoidable.

   NO word-bounded [Set] occurs in the binder or the block of ANY of the
   seven constants measured ([power_fmap], [Power_Functor], [Copower_Functor],
   [power_functor_ev], [copower_functor_inj], [cp_adj_iso],
   [Copower_Power_Adjunction]).  That is strictly better than the limit-shaped
   route: [power_of_limit@{u u0 u1}] reads
   [∀ {C : Category@{u1 Set Set}} …], pinning [C]'s hom AND proof to the
   literal [Set] in its binder.  Going through the CLASS
   ([power]/[power_ev]/[power_ump]) rather than through
   [Limit (DiscreteCat_Functor …)] avoids that pin entirely.

   AN ENGINEERING FINDING, RECORDED BECAUSE IT COST A COMPILE

   [rewrite] does not match a goal that DISPLAYS the pattern it is given.
   The second naturality clause of [Build_Adjunction'] presents the composite
   [fmap[Copower_Functor J] g ∘ copower_inj J x j], and under
   [Set Printing All] its implicit object arguments are MIXED: the middle
   object elaborates as [copower J x] while the codomain elaborates as
   [fobj[Copower_Functor J] y].  A lemma stated naively gets [copower J y] in
   both positions and a lemma stated with the injection ascribed to
   [b ~> fobj[Copower_Functor J] b] gets [fobj[…] x] in both, so BOTH are
   rejected with "Found no subterm matching", the second one printing an
   ascription the elaborator had already erased.  The repair is not a third
   spelling but to stop rewriting: [apply compose_respects] followed by
   [symmetry; exact (copower_functor_inj J g j)] closes it by CONVERSION,
   which does not care how the objects are spelled.  Same family as the
   [star_fmap_mor] finding recorded for Construction/Slice/Pullback.v.

   THE ONE [Defined] IS LOAD-BEARING, MEASURED BY FLIPPING IT.
   [Copower_Power_Adjunction] closed with [Qed] instead breaks
   [cp_adj_readback] outright:

     The term "eq_refl" has type
      "adj[Copower_Power_Adjunction] = adj[Copower_Power_Adjunction]"
     while it is expected to have type
      "adj[Copower_Power_Adjunction] = cp_adj_iso b c"
     (cannot unify "adj[Copower_Power_Adjunction]" and "cp_adj_iso b c").

   AS THE FILE NOW STANDS THERE ARE SEVEN [Defined]s AND SIXTY-ONE [Qed]s,
   counted over proof terminators in the code body, and EXACTLY THREE of the
   seven are load-bearing -- measured by flipping each ALONE to [Qed] and
   recompiling: [Copower_Power_Adjunction] (above), [cp_pa_adj] and
   [ex1_pa_adj], each of which an [eq_refl] readback or a mate computation
   reduces through.  The other four -- [power_of_weighted],
   [copower_of_weighted], [One_iprod_ump] and [One_icoprod_ump] -- compile as
   [Qed] with everything else intact and are [Defined] by the convention that
   a constant producing DATA stays transparent.  All THREE load-bearing ones
   are PINNED in the probe by an opaque [Qed]-closed clone whose readback is
   refuted (negatives 5, 12 and 13), so the flipping measurement is guarded;
   the four that are not load-bearing stay measured only, "flipping this
   changes nothing" being a counterfactual no refutation command can
   express.

   STATUS OF §A-§B ALONE, AS FIRST LANDED: axiom-free, 25/25 constants
   reporting "Closed under the global context", each queried by fully
   qualified name.  (The whole-file figure is 147/147; see the COST section
   below.)  The criterion for 25 is
   every [Definition] and [Parameter] head of
   [Print Module Category.Structure.Limit.Power.Adjunction] on its
   whitespace-flattened output -- that command wraps its module head across
   three lines, so a line-anchored sweep of it needs flattening first -- which
   is 22 source-declared heads plus the THREE [Program] obligations of
   [Power_Functor], invisible to a [.glob] sweep (the [.glob] carries exactly
   22 [def]/[prf] entries).  The file declares no [Record], [Class] or
   [Inductive], so there is no unlisted [Build_*].  ([Print Module] renders an
   opaque constant as [Parameter]; the eight so shown here are the three
   obligations and five ordinary [Qed] lemmas, not axioms, which is what the
   audit above checks.)  All 25 names are free under the criterion stated in
   the prior-art paragraph -- ZERO collisions across all 25, swept one name
   at a time.  All 25 are registered in the Makefile's
   [print-assumptions] gate, FULLY QUALIFIED: the three [Program] obligations
   are NOT reachable by their bare names in that target's single shared scope
   (measured -- the gate stops with "The reference
   Power_Functor_obligation_1 was not found in the current environment"), so
   the whole block is qualified rather than only the three, following the
   [Powerset.Universal] precedent already in that file.

   [make todo] grew, FOR §A-§B AS FIRST LANDED, by exactly ONE line, and it
   was PROSE: the engineering paragraph above used an ordinary English verb
   that the target's case-insensitive pattern matches on its first
   alternative.  That verb has since been replaced, so this file now
   contributes ZERO hits: it carries no probe command and no ticket marker
   of any kind, and the paragraph you are reading is written so as not to
   add one.
   ────────────────────────────────────────────────────────────────────────

   C. THE WEIGHTED-LIMIT COMPARISON, AND THAT IT IS AN AGREEMENT

   Structure/Limit/Weighted.v presents a limit by a WEIGHT.  The power is the
   weighted limit over the TERMINAL SHAPE [_1] whose WEIGHT picks out the
   index SET and whose DIAGRAM is constant at [b].  [conical_weighted]
   (Weighted.v:354) is NOT this theorem and is not cited as though it were:
   it is the CONSTANT weight over an ARBITRARY shape, i.e. weighted ⇒
   ordinary limit, which is the conical case and says nothing about powers.

   BOTH DIRECTIONS ARE PROVED, which is what makes this an agreement of the
   two presentations rather than one inhabitant of a class.
   [power_WeightedLimit] puts the CHOSEN power in the class, and
   [power_of_weighted] runs the other way: for an ARBITRARY weighted limit of
   that weight and that diagram, [wlim_obj] IS a power, with [wpow_ev] --
   the identity transported back across [wlim_iso] -- as its evaluations.
   The converse assumes NOTHING about the ambient category, not even that it
   has powers.  [copower_of_weighted] is the dual, and [WeightedColimit] is
   the class it consumes.  The whole of [wlim_natural] is spent in exactly
   one lemma per side ([wpow_from_is_precompose], [wcop_from_is_postcompose]).

   THE COPOWER HALF IS BUILT DIRECTLY OVER [1^op] AND IS NOT AN
   OP-INSTANTIATION, AND BOTH REASONS ARE PINNED.  A colimit weight is
   contravariant on the shape, so [WeightedColimit W F] puts [W] over [J^op];
   [Opposite _1 = _1] is refuted at [eq_refl] (CONVERSION), and
   [Opposite_Functor (copower_diagram b) = @power_diagram (C^op) b] is
   refuted too (TYPING -- the error reports the SHAPES, [1 ⟶ C^op] against
   [1^op ⟶ C^op]).  So the power half cannot simply be read at [C^op]: this
   is where #321's op-trick, which makes §A's copower functor entirely free,
   does not carry.

   THE WEIGHT IS DISCRETE, AND THAT IS FORCED RATHER THAN CONVENIENT: the
   evaluations of a power are indexed by ELEMENTS, so the backward leg's
   respectfulness would have to derive [ev j ≈ ev j'] from [j ≈ j'].
   [index_setoid J] therefore uses [eq_Setoid], and both [wpow_cone] and
   [wcop_cocone] get respectfulness for free from that.

   THE ROUND TRIP RETURNS THE CHOSEN DATA WITH ONE IDENTITY RESIDUE PER SIDE,
   EXHIBITED RATHER THAN DESCRIBED.  [wrt_ev_residue] and [wrt_inj_residue]
   close at [eq_refl] on [power_ev J b j ∘ id] and [id ∘ copower_inj J b j];
   the strict forms are refuted and pinned, and [wrt_ev_equiv]/[wrt_inj_equiv]
   are the [≈] statements, one [id_right] and one [id_left].

   ★ AND THE TWO DIRECTIONS COST DIFFERENT UNIVERSES, WHICH IS THE
   INTERESTING MEASUREMENT HERE.  [power_WeightedLimit] carries the block
   equation [u0 = u3] -- [C]'s hom-and-proof level IDENTIFIED with the INDEX
   universe -- and [copower_WeightedColimit] carries [u0 = u4]; but
   [power_of_weighted] and [copower_of_weighted] carry NO EQUATION AT ALL,
   their index universe merely BOUNDED.  Where the identification enters is
   LOCALIZED by probe rather than attributed: under [Constraint ch < ji],
   [power], [power_ev], [Power_Functor], [index_setoid], [power_weight],
   [power_diagram] and even [HomDiagram cu (power_diagram bu)] are ALL
   accepted, and [WeightedLimit (power_weight Ju) (power_diagram bu)] is
   refused -- so it is putting the weight and the hom-diagram into ONE [Sets]
   that forces it, not the weight and not the diagram.  It is NOT claimed
   unavoidable, and it is inherent to a [Sets]-weighted formulation with a
   bare-[Type] weight rather than to anything #321 does.

   ────────────────────────────────────────────────────────────────────────

   D0. THE COPOWER BIFUNCTOR, WHICH BOTH PARAMETER READINGS SHARE

   [Copower_Bifunctor : C ∏ Coq ⟶ C] makes [(b, J) ↦ J · b] functorial in
   both arguments at once.  §D fixes the OBJECT and varies the index; §E
   fixes the INDEX and varies the object.  They are two parametrizations of
   this ONE bifunctor, differing only in which slot of
   [ParametrizedAdjunction]'s [X ∏ P ⟶ A] the parameter occupies, and §D
   reaches its own by [Copower_Bifunctor ◯ Swap] rather than by building a
   second bifunctor.

   ★ THE INDEX CATEGORY IS [Coq], AND THAT IS FORCED, NOT PREFERRED.  The
   copower injections are indexed by ELEMENTS, so [fmap_respects] must derive
   [copower_inj (f j) ≈ copower_inj (f' j)] from [f ≈ f'], which needs
   [f j = f' j] at LEIBNIZ equality.  [Coq]'s hom-setoid is pointwise
   Leibniz and supplies it.  [Sets]' does not, and the probe carries an
   AXIOM-FREE COUNTERMODEL -- [sets_index_respects_absurd], over a
   two-element setoid whose [≈] is the total relation -- refuting
   [SetsIndexRespects], the [fmap_respects] obligation of the CANONICAL
   arrow action (the copower mediator of the injections, which is what any
   arrow action commuting with the injections must be).  Read it at that
   scope: THAT action over [Sets] is refuted outright rather than merely
   recorded as a proof that does not go through; no other arrow action with
   the same object action is investigated, and none is claimed refuted.
   #321's own Power/Hom.v:104-107 anticipates the same
   fact for its bijections -- ":105  the index of [HasIndexedCoproducts] is a
   bare [Type]", ":106  No claim is made about a coarser setoid on the
   index" -- and this is that fact, refuted.

   ────────────────────────────────────────────────────────────────────────

   D1. MAC LANE §IV.7 EXERCISE 1, UNRESTRICTED

   [Copower_Bifunctor_Iso J : CopLeft J ≅ CopRight J] in
   [[C^op ∏ C, Sets]] is the exercise's displayed isomorphism -- in its
   CORRECTED form [C(J · a, c) ≅ Set(J, C(a,c))], per the variance argument
   above -- upgraded from a family of bijections to an isomorphism of
   BIFUNCTORS, which is what "natural in the parameter a" asks for.  It takes
   no hypothesis beyond [HasIndexedCoproducts].

   The right-hand side is pleasing and is not a coincidence:
   [CopRight J] is [@Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C],
   so Mac Lane's [Set(J, −)] is §A's OWN power functor read at [Sets], and
   the whole right-hand side is that functor applied to the hom-bifunctor.
   Both object actions read back at [eq_refl].

   The pointwise-invertible transformation is upgraded through #369's
   [componentwise_iso] rather than by building the inverse transformation and
   its naturality by hand.  That donor costs a MARGINAL 10 modules (measured
   by dropping the [Require]: 111 → 101); it is taken because building the
   inverse by hand would fork exactly the general lemma that file exists to
   supply.

   ────────────────────────────────────────────────────────────────────────

   D2. THE SAME EXERCISE PACKAGED, AND THE PUNCHLINE

   [Copower_Object_ParametrizedAdjunction : ParametrizedAdjunction
   Ex1_Bifunctor] is #396's record at the object parameter, and #396's
   Theorem 3 then assembles the right adjoints into
   [MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq] -- WHICH IS THE HOM-FUNCTOR,
   which is the point of the exercise.  That identification is delivered at
   two strengths and neither is asserted: [ex1_hom_bifunctor_obj] closes at
   [eq_refl] on the OBJECT action, [fobj (a,c) = (a ~{C}~> c)], and
   [ex1_hom_bifunctor_fmap] gives the ARROW action POINTWISE as
   [g ↦ k ∘ g ∘ unop h], through [ex1_param_mate_precomp], which reads the
   parameter mate off [conj_mate]'s own component formula rather than
   recomputing conjugacy.

   THE PACKAGING NEEDS A HYPOTHESIS AND IT IS AN EXPLICIT ARGUMENT.  The
   right adjoint [C(a,−)] must land in the SAME index category the copower
   is indexed by, and there the two demands pull against each other: the
   copower wants LEIBNIZ equality on the index (D0), the hom-functor wants
   [C]'s own [≈].  [HomAllStrict C] is exactly where they coincide.

   ★ IT IS NOT A NEW HYPOTHESIS AND IS NOT REDECLARED.
   Construction/Comma/Special.v:395 already carries [HomStrict], at a FIXED
   pair of objects, for its own [Full] criterion; that name is CONSUMED here
   and quantified over all objects ([HomAllStrict C := ∀ x y, HomStrict x y])
   at a marginal cost of 4 modules.  The collision was found by sweeping this
   file's own declared names, and consuming the donor is what resolves it:
   redeclaring [HomStrict] would have put two different predicates under one
   name in the [print-assumptions] target's single shared scope.  That donor
   also supplies [Blur_HomStrict_absurd], a compiled category where the
   per-hom-set form is refutable, which is the boundary of the hypothesis.

   ★ AND THE HYPOTHESIS IS INHABITED IN TREE, WHICH IS BETTER THAN THE
   OBVIOUS GUESS.  [_1]'s hom-setoid IS [Morphism_equality] (Instance/One.v:32),
   so [One_HomAllStrict] is the identity implication, and [_1] has all
   indexed products and coproducts trivially ([One_HasIndexedProducts] and
   [One_HasIndexedCoproducts] are three-line record literals over an
   eight-line universal property apiece, every step [one_hom_eq]) -- so
   [One_Ex1_ParametrizedAdjunction] is a genuine in-tree model.  Read it at
   its strength: it exercises the HYPOTHESES and the assembly, not the
   conclusion, everything in [1] collapsing to [ttt].  No non-degenerate
   model is exhibited and none is claimed.

   ────────────────────────────────────────────────────────────────────────

   E. THE ISSUE'S OWN ITEM 4: THE INDEX SET AS THE PARAMETER

   Here the parameter slot holds the INDEX and the varying argument is the
   object.  The right adjoints ARE §A's power functors ON THE NOSE --
   [pa_right Copower_ParametrizedAdjunction J = Power_Functor J] by
   [eq_refl] -- while the partial functors agree with §A's copower functors
   on BOTH ACTIONS at [eq_refl] ([copower_bifunctor_partial_obj],
   [copower_bifunctor_partial_fmap]) but not as RECORDS, which is the next
   paragraph.  Also [pa_adj]'s own hom-set isomorphism IS §B's [cp_adj_iso] by
   [eq_refl] ([pa_adj_iso_is_cp_adj_iso]) -- so §E does not fork §B's
   bijection.  #396's Theorem 3 then assembles
   [Power_Bifunctor : Coq^op ∏ C ⟶ C], contravariant in the index, with
   [fobj (J, b) = power J b] at [eq_refl].

   ★ THE §B ISOMORPHISM ASCRIBES AT THE PARTIAL FUNCTOR; THE §B ADJUNCTION
   DOES NOT, AND THE ERROR SAYS WHY.  [fobj[Partial_l Copower_Bifunctor J] b]
   and [fobj[Copower_Functor J] b] agree at [eq_refl], so [cp_adj_iso J b c]
   ascribes at the partial functor's type with nothing inserted; but
   [Adjunction] is indexed by the functor RECORD rather than by its two
   actions, so [Copower_Power_Adjunction J] is REFUSED there, the error
   naming the offending field:

     (cannot unify "λ (x y : obj[C^op^op]) (f g : x ~{ C^op^op }~> y),
                    fmap_respects y x f g"
      and "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J").

   Both facts are pinned.  [cp_pa_adj] therefore rebuilds the record -- but
   over the SAME isomorphism and the same two uniqueness lemmas, so no
   universal property is re-derived.

   THE CONJUGACY IS CONSUMED, NOT RECOMPUTED.  [copower_reindex h] is #396's
   [param_transform] and [power_reindex h] is its [pa_param_mate], which
   [power_reindex_is_conj_mate] records at [eq_refl] as #394's [conj_mate];
   [power_reindex_conjugate] is [pa_natural_p] ascribed at #394's
   [Conjugate], the ascription being the whole proof because
   [pa_square_is_Conjugate] identifies the two on the nose; and
   [power_reindex_universal] is [pa_param_mate_universal], so the mate is the
   UNIQUE conjugate and not merely one.  Functoriality in the index is
   [pa_param_mate_id]/[pa_param_mate_comp] and [param_transform_id]/[_comp],
   cited by name.  What is proved here rather than cited is the elementary
   reading of each: [copower_reindex_inj] and [power_reindex_ev]
   ([ev_{j'} ∘ τ_b ≈ ev_{h j'}]), the second from the mate's component
   formula plus [cp_pa_counit_inj].

   ★ §D AND §E ARE DIFFERENT STATEMENTS AND NEITHER DISCHARGES THE OTHER.
   Mac Lane's Ex 1 varies the OBJECT; the issue's item 4 varies the INDEX,
   which is the variable its own item 3 (= §IV.2 Ex 12, §B above) holds
   FIXED.  Both are true and both are here, labelled.

   ────────────────────────────────────────────────────────────────────────

   UNIVERSES OF §C-§E, MEASURED OFF BOTH BINDER AND BLOCK

   All eighteen measured constants are over [C : Category@{u u0 u0}] -- hom
   identified with proof by REUSING the level variable in the BINDER, with no
   block equation saying so -- and NO word-bounded [Set] occurs in the binder
   or the block of ANY of them.  The block equations are:

     [power_WeightedLimit]                    u0 = u3        (index)
     [copower_WeightedColimit]                u0 = u4        (index)
     [power_of_weighted]                      none
     [copower_of_weighted]                    none
     [Copower_Bifunctor], [CopLeft], [CopRight], [HomCoq],
       [copower_reindex]                      none
     [Copower_Bifunctor_Iso]                  u0 = u2, u0 = u3
     [Copower_Object_ParametrizedAdjunction], [ex1_pa_adj],
       [MacLane_Ex1_hom_bifunctor]            none
     [Copower_ParametrizedAdjunction], [Power_Bifunctor], [cp_pa_adj],
       [power_reindex], [power_reindex_conjugate]
                                              u0 = u1, u0 = u2,
                                              u0 = u4, u0 = u5

   ★ SO THE OBJECT-PARAMETRIZED READING IS UNIVERSE-FREER THAN THE
   INDEX-PARAMETRIZED ONE, AND THE REASON IS WHICH BIJECTION EACH USES.  §D2
   builds its hom-set bijection DIRECTLY from the copower's universal
   property, in [Coq], and carries no equation at all; §E composes #321's two
   [_at] bijections and inherits exactly the four equations localized in the
   §B paragraph above.  §D1 sits between them at two, which is CONSISTENT
   with only the COPRODUCT class being involved there -- but that is an
   attribution, not an isolation: no experiment removes one donor and shows
   one equation vanish.  None of this is claimed unavoidable.

   ────────────────────────────────────────────────────────────────────────

   COST, AND WHAT IT BUYS

   Closure 111 modules (transitive in-project [.vo] dependencies over
   [.Makefile.coq.d], EXCLUDING the file itself), up from the 38 of §A-§B.
   Measured by DROPPING each [Require] one at a time: of the twelve added
   for §C-§E, [Adjunction/Parameter] 28, [Instance/Coq] 13,
   [Instance/Fun/Morphisms] 10, [Construction/Comma/Special] 4,
   [Structure/Limit/Weighted] 1, and the other SEVEN ZERO apiece; of the
   §A-§B [Require]s, [Structure/Limit/Power/Hom] costs 2.  Those marginals
   do not add to 111 - 38 and are not meant to: a drop-one marginal ignores
   what the survivors share.  Nothing in the tree Requires this file, so
   none of that lands on an existing consumer.

   147/147 CONSTANTS CLOSED UNDER THE GLOBAL CONTEXT, each queried by fully
   qualified name, ZERO [Axioms:] lines.  The criterion for 147 is every
   [Definition] and [Parameter] head of
   [Print Module Category.Structure.Limit.Power.Adjunction] on its
   WHITESPACE-FLATTENED output (the command wraps its module head): 86
   [Definition] plus 61 [Parameter].  The [.glob] carries 110 (86 [def] + 24
   [prf]), so THIRTY-SEVEN of the 61 opaque constants are [Program]
   obligations that no source or [.glob] sweep sees, and 147 - 110 = 37
   checks that.  The file declares no [Record], [Class] or [Inductive], so
   there is no unlisted [Build_*].  All 147 are in the [print-assumptions]
   gate, FULLY QUALIFIED, which took block 5 of that target from 25.5 to
   38.9 KiB, measured on the raw text with its [@{]/[}] delimiters (the
   largest block in the file is 73.6).

   ZERO COLLISIONS across all 147 names, swept ONE NAME AT A TIME under the
   criterion of the prior-art paragraph WIDENED to exclude this file's own
   probe as well (which names 27 of them as controls, by design):

     rg -l -w -e '<token>' -g '*.v' \
        -g '!Structure/Limit/Power/Adjunction.v' \
        -g '!Test/ProbeCopower366.v' .

   instrument-checked at [power] = 42 files and [Monoid] = 91, both under
   that same exclusion (unexcluded, [Monoid] is 92, this file mentioning
   it).  TWO REAL
   COLLISIONS were found before landing and BOTH were resolved by consuming
   the donor rather than by renaming: [HomStrict] and [One_HomStrict] are
   Construction/Comma/Special.v:395/:617.

   Test/ProbeCopower366.v mirrors this file's full [Require] list and carries
   FIFTEEN refutation commands = 1 instrument check + 14 negatives of THREE
   KINDS told apart by the error TEXT: 9 CONVERSION (each ends "cannot unify"
   between two terms of one type), 3 TYPING (a plain "has type ... expected",
   with NO "cannot unify" and no universe clause), 2 FORMABILITY (each ends
   in a universe clause).  Each was stripped ONE AT A TIME, compiled ALONE,
   and produced exactly one [Error] whose whole text was read.  NEGATIVES 2
   AND 3 ARE THE SAME EQUATION AT TWO SPELLINGS AND COME OUT AS DIFFERENT
   KINDS -- with BOTH sides' implicits written out, [@Copower_Functor C HC J]
   against [@Power_Functor (C^op) HC J] is refused at the STATEMENT, the
   two constants not sharing a type and the error carrying no "cannot
   unify";
   against [Power_Functor J] at [C] they do share one and there is -- which
   is why a negative's kind is read off its error and never guessed from its
   statement.  A FALSE GUARD WAS CAUGHT THERE AND IS RECORDED IN THE PROBE:
   negative 2 as first written, [Copower_Functor J = @Power_Functor (C^op)
   HC J], left the left side's category IMPLICIT, and the elaborator
   re-solved it as [C^op] (leaving its coproduct instance an unresolved
   evar) so that the two sides DID share a type; the error then fired at
   [eq_refl], refuting negative 3's fact restated at [C^op] and not the type
   mismatch the comment claimed.  The tell is general: a negative whose
   claimed reason is "the two sides do not share a type" but whose error
   fires at [eq_refl] elaborated its statement and is measuring something
   else -- the [obj[?C]] family Test/ProbeFiniteProducts335.v records.
   Negatives 12 and 13 pin the two further load-bearing [Defined]s
   ([cp_pa_adj], [ex1_pa_adj]) by the opaque-clone technique negative 5 uses
   for [Copower_Power_Adjunction]; negative 14 pins the index-universe
   boundary recorded in the §B universe paragraph.  Every constant a
   negative names also appears outside every refutation; the only tokens
   confined to one are the refuted commands' own names, which never enter
   the environment, and the instrument's deliberately absent one.
   Rename-simulated 15/15 -- the thirteen target constants the negatives
   name plus the two reached only through their clones -- with each rename
   applied to THIS FILE ONLY (a whole-tree rename is a no-op by
   construction), every break landing on a [Check] control line and none
   inside a refutation.

   [make todo] grows by 29, ALL of them in the probe (its 15 refutation
   commands and 14 prose lines matching that target's pattern); this file
   contributes NOTHING, the one prose line §A-§B first carried having been
   reworded.

   ────────────────────────────────────────────────────────────────────────

   NOT DELIVERED

   - No [Set]-indexed reading of anything: the index category is [Coq]
     throughout, and the CANONICAL arrow action over [Sets] is REFUTED
     (probe §H) rather than deferred; no other arrow action over [Sets] is
     investigated.  Whether some full subcategory of [Sets] on discrete
     setoids would serve is not investigated either; no such subcategory
     exists in tree.
   - No NON-DEGENERATE model of [HomAllStrict].  [_1] is the only witness and
     it collapses everything; in particular nothing here exhibits a category
     with genuinely many arrows satisfying it, and no impossibility is
     claimed either.
   - §D1 and §D2 are NOT RELATED to each other.  Nothing states that
     [Copower_Bifunctor_Iso] is the [Sets]-valued shadow of
     [MacLane_Ex1_hom_bifunctor], and the two land in different categories
     ([Sets] against [Coq]), so a comparison would need a functor between
     them that is not built.
   - No naturality of the §C comparison in [J] or in [b], and no uniqueness
     for [wlim_obj] (the class has none), so §C is an agreement of the two
     presentations at fixed data and not an equivalence of structures.
   - No [WeightedLimit] statement for the general indexed product, only for
     the constant family that a power is.
   - No 2-categorical reading, nothing about [Adjunction/Map.v]'s maps of
     adjunctions, and no relation between §E's conjugate pairs and
     [Instance/Adj.v]'s category of adjunctions.
   - Nothing is registered as an [Instance]: [One_HasIndexedProducts] and
     [One_HasIndexedCoproducts] are plain [Definition]s deliberately, so that
     resolution is not offered a degenerate model of either class.
   - No concrete witness at a named category for §B, §D1 or §E; the only
     concrete instantiation anywhere in the file is [_1] for §D2. *)

#[local] Obligation Tactic := idtac.

(** ** The power as an endofunctor of [C]

    The arrow action is the mediator [power_desc] produces for the family
    [j ↦ g ∘ ev j], and every functor law is one appeal to that mediator's
    uniqueness clause followed by a computation with [power_fmap_ev]. *)

Section PowerFunctor.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).

Definition power_fmap {b b' : C} (g : b ~> b') : power J b ~> power J b' :=
  unique_obj (power_desc (power_ump J b')
                (fun j : J => g ∘ power_ev J b j)).

(* The characterizing equation of the arrow action: it commutes with the
   evaluations.  This is the mediator's [unique_property], nothing more. *)
Lemma power_fmap_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ power_fmap g ≈ g ∘ power_ev J b j.
Proof. exact (unique_property (power_desc (power_ump J b') _) j). Qed.

Program Definition Power_Functor : C ⟶ C := {|
  fobj := fun b => power J b;
  fmap := fun b b' g => power_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply (uniqueness (power_desc (power_ump J b') _)).
  intros j; rewrite power_fmap_ev; now rewrite Hg.
Qed.
Next Obligation.
  intros b.
  apply (uniqueness (power_desc (power_ump J b) _)).
  intros j; rewrite id_left; apply id_right.
Qed.
Next Obligation.
  intros x y z f g.
  apply (uniqueness (power_desc (power_ump J z) _)).
  intros j.
  rewrite comp_assoc, power_fmap_ev.
  rewrite <- !comp_assoc; now rewrite power_fmap_ev.
Qed.

Example power_functor_obj (b : C) :
  fobj[Power_Functor] b = power J b := eq_refl.

Example power_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Power_Functor] g = power_fmap g := eq_refl.

(* [power_fmap_ev] restated through [fmap], which is the spelling the
   adjunction's naturality goals present. *)
Lemma power_functor_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ fmap[Power_Functor] g ≈ g ∘ power_ev J b j.
Proof. exact (power_fmap_ev g j). Qed.

End PowerFunctor.

Arguments power_fmap {C HP} J {b b'} g.
Arguments Power_Functor {C HP} J.
Arguments power_functor_ev {C HP} J {b b'} g j.

(** ** The copower as an endofunctor, for free

    [copower J b] is [@power (C^op) HC J b] DEFINITIONALLY (#321), so the
    copower functor is the op-power functor read back through
    [Opposite_Functor].  That is a plain [Definition] with no obligation and
    no tactic; the four [Example]s below record by [eq_refl] exactly what it
    costs, namely nothing. *)

Section CopowerFunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition Copower_Functor : C ⟶ C :=
  Opposite_Functor (@Power_Functor (C^op) HC J).

Example copower_functor_obj (b : C) :
  fobj[Copower_Functor] b = copower J b := eq_refl.

Example copower_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g = @power_fmap (C^op) HC J b' b g := eq_refl.

(* The double opposite returns the op-power functor ON THE NOSE, which is
   what makes [C ⟶ C] the right type rather than [(C^op)^op ⟶ (C^op)^op]. *)
Example copower_functor_double_op :
  Opposite_Functor Copower_Functor = @Power_Functor (C^op) HC J := eq_refl.

(* And the arrow action IS the mediator [copower_desc] produces, read
   covariantly: no [^op] appears in this statement. *)
Example copower_functor_desc {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => copower_inj J b' j ∘ g)) := eq_refl.

Lemma copower_functor_inj {b b' : C} (g : b ~> b') (j : J) :
  fmap[Copower_Functor] g ∘ copower_inj J b j
  ≈ copower_inj J b' j ∘ g.
Proof. exact (@power_fmap_ev (C^op) HC J b' b g j). Qed.

End CopowerFunctor.

Arguments Copower_Functor {C HC} J.
Arguments copower_functor_inj {C HC} J {b b'} g j.

(** ** Mac Lane §IV.2 Exercise 12

    The hom-set isomorphism is the composite of #321's two bijections.  The
    two land at the SAME [Sets]-power -- [copower_hom_iso_at] at
    [J ⋔ C(b,c)] read from the copower side, [power_hom_iso_at] at the same
    object read from the power side -- so no comparison map is needed and
    [cp_adj_iso] is supplied by [:=]. *)

Section CopowerPowerAdjunction.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* The shared right-hand side of the two bijections: the [Sets]-power of the
   hom-setoid [C(b,c)] by [J].  Naming it lets each donor be ASCRIBED at a
   type mentioning it, which is what says they meet ON THE NOSE. *)
Definition cp_middle (b c : C) : Sets :=
  @power Sets Sets_HasIndexedProducts J
    {| carrier := @hom C b c ; is_setoid := @homset C b c |}.

(* Each donor lands at [cp_middle b c] with no comparison map inserted --
   these are the two donors supplied AS TERMS at that ascribed type, so a
   change to either target breaks them.  A tautology [X = X] would say
   nothing here, and is deliberately not what is written. *)
Example cp_copower_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle b c) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

Example cp_power_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C b (power J c)
     ; is_setoid := @homset C b (power J c) |} (cp_middle b c) :=
  power_hom_iso_at (@power_ump C HP J c) b.

Definition cp_adj_iso (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Copower_Functor J] b) c
     ; is_setoid := @homset C (fobj[Copower_Functor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  iso_compose (iso_sym (power_hom_iso_at (@power_ump C HP J c) b))
              (copower_hom_iso_at (@copower_ump C HC J b) c).

(* The forward transpose of [u] is the unique arrow whose [j]-th evaluation
   is [u] precomposed with the [j]-th injection -- Mac Lane's correct
   [C(X · a, c) ≅ Set(X, C(a,c))], read at one pair of objects. *)
Lemma cp_to_char (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_adj_iso b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (unique_property (power_desc (power_ump J c) _) j). Qed.

Lemma cp_to_uniq {b c : C} (u : copower J b ~> c) (v : b ~> power J c) :
  (∀ j : J, power_ev J c j ∘ v ≈ u ∘ copower_inj J b j) →
  to (cp_adj_iso b c) u ≈ v.
Proof.
  intros H.
  exact (uniqueness (power_desc (power_ump J c)
           (fun j : J => u ∘ copower_inj J b j)) v H).
Qed.

(* Mac Lane §IV.2 Ex 12: the copower is left adjoint to the power. *)
Definition Copower_Power_Adjunction : Copower_Functor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' cp_adj_iso).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_to_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (copower_functor_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_to_char x y g j).
Defined.

(* The adjunction's own hom-set isomorphism IS the composite, and both its
   legs are the mediators of the two universal properties, on the nose. *)
Example cp_adj_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J) Copower_Power_Adjunction b c
  = cp_adj_iso b c := eq_refl.

Example cp_to_readback (b c : C) (u : copower J b ~> c) :
  to (cp_adj_iso b c) u
  = unique_obj (power_desc (power_ump J c)
                  (fun j : J => u ∘ copower_inj J b j)) := eq_refl.

Example cp_from_readback (b c : C) (v : b ~> power J c) :
  from (cp_adj_iso b c) v
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => power_ev J c j ∘ v)) := eq_refl.

End CopowerPowerAdjunction.

Arguments cp_adj_iso {C HP HC} J b c.
Arguments Copower_Power_Adjunction {C HP HC} J.

(** ** C. The weighted-limit presentation, and that it agrees

    Mac Lane's §III.4 power is an indexed product; Structure/Limit/Weighted.v
    presents limits by a WEIGHT.  The power is the weighted limit over the
    TERMINAL SHAPE [1] whose weight picks out the index SET and whose diagram
    is constant at [b].  Both directions are proved: [power_WeightedLimit]
    inhabits the class at the chosen power, and [power_of_weighted] shows
    that ANY weighted limit for that weight and diagram IS a power.  Dually
    for the copower and [WeightedColimit]. *)

Section WeightedPower.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).
Context (b : C).

(* The weight picks out [J] as a DISCRETE setoid.  Discreteness is what the
   backward leg's respectfulness needs: evaluations are indexed by ELEMENTS,
   so a coarser index setoid would demand [ev j ≈ ev j'] from [j ≈ j']. *)
Definition index_setoid : Sets :=
  {| carrier := J ; is_setoid := eq_Setoid J |}.

Definition power_weight : _1 ⟶ Sets := Δ[_1]( index_setoid ).

Definition power_diagram : _1 ⟶ C := Δ[_1]( b ).

Definition wpow_to_fn (c : C)
  (a : power_weight ⟹ HomDiagram c power_diagram) : c ~> power J b :=
  unique_obj (power_desc (power_ump J b) (fun j : J => a ttt j)).

Program Definition wpow_to (c : C) :
  SetoidMorphism ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| morphism := wpow_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (power_desc (power_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wpow_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |}
    ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram)) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => power_ev J b j ∘ u |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wpow_iso (c : C) :
  @Isomorphism Sets ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| to := wpow_to c ; from := wpow_from c |}.
Next Obligation.
  intros c u; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
                       (fun j : J => power_ev J b j ∘ u))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wpow_to_fn.
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition power_WeightedLimit :
  WeightedLimit power_weight power_diagram := {|
  wlim_obj := power J b ;
  wlim_iso := wpow_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
            (fun j : J => (a ttt j) ∘ h))).
  intro j.
  rewrite comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example power_weighted_obj : wlim_obj power_WeightedLimit = power J b
  := eq_refl.

End WeightedPower.

Arguments power_diagram {C} b.

Section WeightedCopower.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

(* The colimit weight is contravariant on the shape, so it lives over
   [1^op].  That shape is NOT [1] -- refuted at [eq_refl] and pinned -- which
   is why this half is built directly rather than instantiated at [C^op]. *)
Definition copower_weight : (Opposite _1) ⟶ Sets :=
  @Diagonal Sets (Opposite _1) (index_setoid J).

Definition copower_diagram : _1 ⟶ C := @Diagonal C _1 b.

Definition wcop_to_fn (c : C)
  (a : copower_weight
         ⟹ HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)) :
  copower J b ~{C}~> c :=
  unique_obj (copower_desc (copower_ump J b) (fun j : J => a ttt j)).

Program Definition wcop_to (c : C) :
  SetoidMorphism
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| morphism := wcop_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (copower_desc (copower_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wcop_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |}
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram))) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => u ∘[C] copower_inj J b j |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wcop_iso (c : C) :
  @Isomorphism Sets
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| to := wcop_to c ; from := wcop_from c |}.
Next Obligation.
  intros c u; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
                       (fun j : J => u ∘[C] copower_inj J b j))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wcop_to_fn.
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition copower_WeightedColimit :
  WeightedColimit copower_weight copower_diagram := {|
  wlim_obj := copower J b ;
  wlim_iso := wcop_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
            (fun j : J => h ∘[C] (a ttt j)))).
  intro j.
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity |].
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example copower_weighted_obj :
  wlim_obj copower_WeightedColimit = copower J b := eq_refl.

End WeightedCopower.

Arguments copower_diagram {C} b.

(** ** C'. The converses: a weighted limit for that data IS a power

    This is what turns §C from "the chosen power inhabits the class" into an
    agreement of the two presentations, which is the issue's stated reviewer
    check.  Nothing here assumes the ambient category has powers at all. *)

Section WeightedPowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedLimit (power_weight J) (power_diagram b)).

(* A family read as a weighted cone.  Respectfulness is free because
   [index_setoid J] is DISCRETE; naturality is [id_left] twice. *)
Program Definition wpow_cone (c : C) (pi : ∀ _ : J, c ~> b) :
  power_weight J ⟹ HomDiagram c (power_diagram b) := {|
  transform := fun _ => {| morphism := pi |}
|}.
Next Obligation. intros c pi i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.

(* The generic element: transport the identity back across [wlim_iso]. *)
Definition wpow_ev (j : J) : wlim_obj WL ~> b :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

(* The only place [wlim_natural] is spent: the inverse transpose of [u] is
   the generic element precomposed with [u]. *)
Lemma wpow_from_is_precompose (c : C) (u : c ~> wlim_obj WL) (j : J) :
  from (wlim_iso WL c) u ttt j ≈ wpow_ev j ∘ u.
Proof.
  unfold wpow_ev.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose (HomDiagram_precompose u (power_diagram b)) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; apply id_left. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition power_of_weighted : IsPower b (wlim_obj WL) wpow_ev.
Proof.
  apply Build_IsPower; intros c pi.
  exists (to (wlim_iso WL c) (wpow_cone c pi)).
  - intro j.
    rewrite <- (wpow_from_is_precompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wpow_cone c pi) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wpow_from_is_precompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedPowerConverse.

Section WeightedCopowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedColimit (copower_weight J) (copower_diagram b)).

Program Definition wcop_cocone (c : C) (iota : ∀ _ : J, b ~{C}~> c) :
  copower_weight J
    ⟹ HomDiagram (C:=C^op) c (Opposite_Functor (copower_diagram b)) := {|
  transform := fun _ => {| morphism := iota |}
|}.
Next Obligation.
  intros c iota i x y Hxy; simpl in Hxy; subst; reflexivity.
Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.

Definition wcop_inj (j : J) : b ~{C}~> wlim_obj WL :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

Lemma wcop_from_is_postcompose (c : C) (u : wlim_obj WL ~{C}~> c)
  (j : J) : from (wlim_iso WL c) u ttt j ≈ u ∘[C] wcop_inj j.
Proof.
  unfold wcop_inj.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose
               (HomDiagram_precompose (C:=C^op) u
                  (Opposite_Functor (copower_diagram b))) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; cat. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition copower_of_weighted : IsCopower b (wlim_obj WL) wcop_inj.
Proof.
  apply Build_IsCopower; intros c iota.
  exists (to (wlim_iso WL c) (wcop_cocone c iota)).
  - intro j.
    rewrite <- (wcop_from_is_postcompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wcop_cocone c iota) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wcop_from_is_postcompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedCopowerConverse.

(* The round trip returns the chosen data with ONE identity residue on each
   side, exhibited here rather than described. *)

Section WeightedRoundTrip.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

Definition wrt_ev (j : J) : power J b ~{C}~> b :=
  wpow_ev J b (power_WeightedLimit J b) j.

Example wrt_ev_residue (j : J) : wrt_ev j = power_ev J b j ∘[C] id
  := eq_refl.

Lemma wrt_ev_equiv (j : J) : wrt_ev j ≈ power_ev J b j.
Proof. exact (@id_right C _ _ (power_ev J b j)). Qed.

Definition wrt_inj (j : J) : b ~{C}~> copower J b :=
  wcop_inj J b (copower_WeightedColimit J b) j.

Example wrt_inj_residue (j : J) : wrt_inj j = id ∘[C] copower_inj J b j
  := eq_refl.

Lemma wrt_inj_equiv (j : J) : wrt_inj j ≈ copower_inj J b j.
Proof. exact (@id_left C _ _ (copower_inj J b j)). Qed.

End WeightedRoundTrip.

(** ** D0. The copower BIFUNCTOR, which BOTH parameter readings share

    [(b, J) ↦ J · b] is functorial in both arguments at once.  §D fixes the
    OBJECT and varies the index (Mac Lane's Ex 1 reads the object as the
    parameter); §E fixes the index and varies the object.  They are two
    parametrizations of this ONE bifunctor, and neither implies the other.

    The index category is [Coq], not [Sets], and that is FORCED: the copower
    injections are indexed by ELEMENTS, so [fmap_respects] demands
    [f j = f' j] at LEIBNIZ equality from [f ≈ f'].  [Coq]'s hom-setoid is
    pointwise Leibniz and supplies it; [Sets]' does not, and the probe
    carries an axiom-free countermodel refuting the CANONICAL arrow action
    over [Sets] -- the copower mediator of the injections -- outright rather
    than merely recording that the obvious proof does not go through.  No
    other arrow action over [Sets] is claimed refuted. *)

Section CopowerBifunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.

Definition cop_bifun_fmap (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) :
  copower (snd p) (fst p) ~> copower (snd q) (fst q) :=
  unique_obj (copower_desc (copower_ump (snd p) (fst p))
    (fun j : snd p =>
       copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf)).

Lemma cop_bifun_inj (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) (j : snd p) :
  cop_bifun_fmap p q gf ∘ copower_inj (snd p) (fst p) j
    ≈ copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf.
Proof.
  exact (unique_property (copower_desc (copower_ump (snd p) (fst p)) _) j).
Qed.

Program Definition Copower_Bifunctor : C ∏ Coq ⟶ C := {|
  fobj := fun p => copower (snd p) (fst p) ;
  fmap := fun p q gf => cop_bifun_fmap p q gf
|}.
Next Obligation.
  intros p q gf gf' [Hg Hf].
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; rewrite cop_bifun_inj.
  destruct gf as [g f], gf' as [g' f']; simpl in *.
  rewrite Hg; now rewrite (Hf j).
Qed.
Next Obligation.
  intros p.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; simpl; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros p q r gf hk.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j.
  rewrite <- comp_assoc, cop_bifun_inj.
  rewrite comp_assoc, cop_bifun_inj.
  now rewrite <- !comp_assoc.
Qed.

Example copower_bifunctor_obj (J : Type) (b : C) :
  fobj[Copower_Bifunctor] (b, J) = copower J b := eq_refl.

Example copower_bifunctor_partial_obj (J : Type) (b : C) :
  fobj[Partial_l Copower_Bifunctor J] b = fobj[Copower_Functor J] b
  := eq_refl.

Example copower_bifunctor_partial_fmap (J : Type) {b b' : C} (g : b ~> b') :
  fmap[Partial_l Copower_Bifunctor J] g = fmap[Copower_Functor J] g
  := eq_refl.

End CopowerBifunctor.

Arguments Copower_Bifunctor {C HC}.

(** ** D1. Mac Lane §IV.7 Exercise 1, UNRESTRICTED

    The displayed isomorphism of the exercise, in its CORRECTED form
    [C(J · a, c) ≅ Set(J, C(a,c))], upgraded from a family of bijections to
    an isomorphism of BIFUNCTORS on [C^op ∏ C] -- which is what "natural in
    the parameter a" asks for.  No hypothesis beyond [HasIndexedCoproducts].

    The right-hand side is [Power_Functor] AT [Sets] composed with the
    hom-bifunctor: Mac Lane's [Set(J, −)] is §A's own power functor. *)

Section ObjectParameterUnrestricted.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition CopLeft : C^op ∏ C ⟶ Sets :=
  Hom C ◯ ((Opposite_Functor (Copower_Functor J)) ∏⟶ Id[C]).

Definition CopRight : C^op ∏ C ⟶ Sets :=
  @Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C.

Example copleft_obj (a c : C) :
  fobj[CopLeft] (a, c)
  = {| carrier := @hom C (copower J a) c
     ; is_setoid := @homset C (copower J a) c |} := eq_refl.

Example copright_obj (a c : C) :
  fobj[CopRight] (a, c)
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C a c ; is_setoid := @homset C a c |} := eq_refl.

Program Definition cop_nat : CopLeft ⟹ CopRight := {|
  transform := fun p =>
    to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))
|}.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.

Definition cop_nat_pointwise (p : C^op ∏ C) :
  IsIsomorphism (transform[cop_nat] p) :=
  @Build_IsIsomorphism Sets _ _ _
    (from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_to_from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_from_to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))).

Definition Copower_Bifunctor_Iso :
  @Isomorphism ([C^op ∏ C, Sets]) CopLeft CopRight :=
  @IsIsoToIso ([C^op ∏ C, Sets]) _ _ cop_nat
    (componentwise_iso cop_nat cop_nat_pointwise).

End ObjectParameterUnrestricted.

Arguments CopLeft {C HC} J.
Arguments CopRight {C} J.
Arguments Copower_Bifunctor_Iso {C HC} J.

(** ** D2. Mac Lane §IV.7 Exercise 1, PACKAGED as an adjunction with a
    parameter -- and the punchline, that the assembled right adjoint IS the
    hom-functor

    The packaging needs the right adjoint [C(a,−)] to land in the SAME index
    category the copower is indexed by, and there the two demands pull
    against each other: the copower wants LEIBNIZ equality on the index, the
    hom-functor wants [C]'s own [≈].  [HomAllStrict C] is exactly the
    hypothesis under which they coincide, and it is disclosed as an explicit
    argument rather than hidden.  It is inhabited in tree -- degenerately,
    by the terminal category, whose hom-setoid IS [Morphism_equality]. *)

(* [Construction/Comma/Special.v:395] already declares this hypothesis at a
   FIXED pair of objects, for exactly this reason (its [Full] criterion for
   the discrete-hom comparison), so it is CONSUMED here and quantified over
   all objects rather than redeclared.  Its [Blur_HomStrict_absurd] is a
   compiled witness of a category where the per-hom-set form is refutable. *)
Definition HomAllStrict (C : Category) : Type :=
  ∀ x y : C, @HomStrict C x y.

Section ObjectParameterPackaged.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (HS : HomAllStrict C).

Program Definition HomCoq (a : C) : C ⟶ Coq := {|
  fobj := fun c => @hom C a c ;
  fmap := fun c c' (k : c ~> c') => fun h : a ~> c => k ∘ h
|}.
Next Obligation. intros a c c' k k' Hk h; now rewrite (HS _ _ _ _ Hk). Qed.
Next Obligation. intros a c h; apply HS; apply id_left. Qed.
Next Obligation.
  intros a x y z k k' h; apply HS; simpl; symmetry; apply comp_assoc.
Qed.

(* The SAME bifunctor as §D0, with its two arguments exchanged so that the
   OBJECT sits in the parameter slot [P] of [ParametrizedAdjunction]. *)
Definition Ex1_Bifunctor : Coq ∏ C ⟶ C := Copower_Bifunctor ◯ Swap.

Example ex1_bifunctor_obj (J : Type) (a : C) :
  fobj[Ex1_Bifunctor] (J, a) = copower J a := eq_refl.

Example ex1_partial_obj (a : C) (J : Type) :
  fobj[Partial_l Ex1_Bifunctor a] J = copower J a := eq_refl.

Lemma ex1_partial_inj (a : C) {J J' : Type} (h : J ~{Coq}~> J') (j : J) :
  fmap[Partial_l Ex1_Bifunctor a] h ∘ copower_inj J a j
    ≈ copower_inj J' a (h j) ∘ id.
Proof.
  unfold Partial_l, Ex1_Bifunctor; simpl; unfold bimap; simpl.
  exact (cop_bifun_inj (a, J) (a, J') (id, h) j).
Qed.

Program Definition ex1_adj_iso (a : C) (J : Type) (c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Ex1_Bifunctor a] J) c
     ; is_setoid := @homset C (fobj[Partial_l Ex1_Bifunctor a] J) c |}
    {| carrier := @hom Coq J (fobj[HomCoq a] c)
     ; is_setoid := @homset Coq J (fobj[HomCoq a] c) |} :=
  {| to   := {| morphism := fun u => fun j : J => u ∘ copower_inj J a j |}
   ; from := {| morphism := fun fam : J → (a ~> c) =>
                  unique_obj (copower_desc (copower_ump J a) fam) |} |}.
Next Obligation. intros a J c u u' Hu j; apply HS; now rewrite Hu. Qed.
Next Obligation.
  intros a J c fam fam' Hfam.
  apply (uniqueness (copower_desc (copower_ump J a) fam)).
  intros j.
  rewrite (unique_property (copower_desc (copower_ump J a) fam') j).
  now rewrite (Hfam j).
Qed.
Next Obligation.
  intros a J c fam j; simpl.
  apply HS.
  exact (unique_property (copower_desc (copower_ump J a) fam) j).
Qed.
Next Obligation.
  intros a J c u; simpl.
  apply (uniqueness (copower_desc (copower_ump J a)
                       (fun j : J => u ∘ copower_inj J a j))).
  intros j; reflexivity.
Qed.

Example ex1_to_char (a : C) (J : Type) (c : C)
  (u : copower J a ~> c) (j : J) :
  to (ex1_adj_iso a J c) u j = u ∘ copower_inj J a j := eq_refl.

Definition ex1_pa_adj (a : C) : Partial_l Ex1_Bifunctor a ⊣ HomCoq a.
Proof.
  unshelve eapply (@Build_Adjunction' C Coq (Partial_l Ex1_Bifunctor a)
                     (HomCoq a) (ex1_adj_iso a)).
  - intros x y z f g j; simpl.
    apply HS.
    rewrite <- comp_assoc.
    rewrite (ex1_partial_inj a g j).
    now rewrite id_right.
  - intros x y z f g j; simpl.
    apply HS; symmetry; apply comp_assoc.
Defined.

Definition Copower_Object_ParametrizedAdjunction :
  ParametrizedAdjunction Ex1_Bifunctor := {|
  pa_right := HomCoq ;
  pa_adj   := ex1_pa_adj
|}.

(* ★ THE PUNCHLINE.  #396's Theorem 3 assembles the right adjoints into a
   bifunctor contravariant in the parameter, and that bifunctor IS the
   hom-functor of [C] -- on objects definitionally, on arrows pointwise. *)
Definition MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq :=
  @parametrized_right_adjoint_bifunctor Coq C C Ex1_Bifunctor
    Copower_Object_ParametrizedAdjunction.

Example ex1_hom_bifunctor_obj (a c : C) :
  fobj[MacLane_Ex1_hom_bifunctor] (a, c) = (a ~{C}~> c) := eq_refl.

Example ex1_pa_right_is_HomCoq (a : C) :
  pa_right Copower_Object_ParametrizedAdjunction a = HomCoq a := eq_refl.

Lemma ex1_counit_inj (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq a) (ex1_pa_adj a) c
    ∘ copower_inj (a ~> c) a g ≈ g.
Proof.
  exact (unique_property
           (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g).
Qed.

(* The parameter mate is PRECOMPOSITION -- read off [conj_mate]'s own
   component formula, not recomputed. *)
Lemma ex1_param_mate_precomp {a a' : C} (h : a' ~> a) (c : C)
  (g : a ~> c) :
  pa_param_mate Copower_Object_ParametrizedAdjunction h c g = g ∘ h.
Proof.
  unfold pa_param_mate, conj_mate; simpl.
  apply HS.
  rewrite <- comp_assoc.
  rewrite (cop_bifun_inj (a', (a ~> c)) (a, (a ~> c)) (h, id) g).
  simpl.
  rewrite comp_assoc.
  apply compose_respects; [ apply ex1_counit_inj | reflexivity ].
Qed.

Lemma ex1_hom_bifunctor_fmap {a a' c c' : C}
  (h : a ~{C^op}~> a') (k : c ~> c') (g : a ~> c) :
  fmap[MacLane_Ex1_hom_bifunctor] ((h, k) : (a, c) ~{C^op ∏ C}~> (a', c'))
    g = k ∘ g ∘ unop h.
Proof.
  etransitivity.
  { apply (f_equal (fun x : a' ~> c => k ∘ x)).
    exact (ex1_param_mate_precomp (unop h) c g). }
  apply HS; apply comp_assoc.
Qed.

End ObjectParameterPackaged.

Arguments HomCoq {C} HS a.
Arguments Ex1_Bifunctor {C HC}.

(* ** [HomAllStrict] is inhabited in tree, degenerately

   [_1]'s hom-setoid IS [Morphism_equality] (Instance/One.v:32), so
   [HomAllStrict _1] is the identity implication -- which is also the donor's
   own [One_HomStrict] (Construction/Comma/Special.v:617), there at the
   single object pair.  The witness exercises the
   HYPOTHESES and the assembly, not the conclusion: everything in [1]
   collapses to [ttt]. *)

Definition One_HomAllStrict : HomAllStrict _1 := fun _ _ _ _ H => H.

Lemma one_hom_eq {x y : _1} (f g : x ~{_1}~> y) : f = g.
Proof. destruct f, g; reflexivity. Qed.

Definition One_iprod_ump {A : Type} (f : A → _1) :
  IsIndexedProduct f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_icoprod_ump {A : Type} (f : A → _1) :
  @IsIndexedCoproduct _1 A f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_HasIndexedProducts : @HasIndexedProducts _1 :=
  @Build_HasIndexedProducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_iprod_ump).

Definition One_HasIndexedCoproducts : @HasIndexedCoproducts _1 :=
  @Build_HasIndexedCoproducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_icoprod_ump).

Definition One_Ex1_ParametrizedAdjunction :
  ParametrizedAdjunction (@Ex1_Bifunctor _1 One_HasIndexedCoproducts) :=
  @Copower_Object_ParametrizedAdjunction _1 One_HasIndexedCoproducts
    One_HomAllStrict.

(** ** E. The issue's own item 4: the INDEX SET as the parameter

    Here the parameter slot of [ParametrizedAdjunction] holds the index and
    the varying argument is the object, so the partial functors ARE §A's
    copower functors and the right adjoints ARE §A's power functors.  A
    function between index sets induces a transformation of copower functors
    whose CONJUGATE is the induced transformation of power functors, and
    that conjugacy is #396's [pa_natural_p] consumed, not recomputed. *)

Section IndexParameter.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

(* The §B isomorphism ASCRIBES at the partial functor (both [fobj]s reduce
   to [copower J b]); the §B ADJUNCTION does not, because [Adjunction] is
   indexed by the functor RECORD.  Both facts are pinned in the probe. *)
Definition cp_pa_iso (J : Type) (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Copower_Bifunctor J] b) c
     ; is_setoid := @homset C (fobj[Partial_l Copower_Bifunctor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  cp_adj_iso J b c.

Lemma cp_partial_inj (J : Type) {b b' : C} (g : b ~> b') (j : J) :
  fmap[Partial_l Copower_Bifunctor J] g ∘ copower_inj J b j
    ≈ copower_inj J b' j ∘ g.
Proof.
  unfold Partial_l; simpl; unfold bimap; simpl.
  now rewrite (cop_bifun_inj (b, J) (b', J) (g, id) j).
Qed.

(* [cp_to_char] restated in the spelling these goals present: [rewrite] is
   syntactic and will not see through the [cp_pa_iso] delta. *)
Lemma cp_pa_char (J : Type) (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_pa_iso J b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (cp_to_char J b c u j). Qed.

Definition cp_pa_adj (J : Type) :
  Partial_l Copower_Bifunctor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' (cp_pa_iso J)).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_pa_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (cp_partial_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_pa_char J x y g j).
Defined.

Definition Copower_ParametrizedAdjunction :
  ParametrizedAdjunction Copower_Bifunctor := {|
  pa_right := fun J : Coq => Power_Functor J;
  pa_adj   := cp_pa_adj
|}.

Definition Power_Bifunctor : Coq^op ∏ C ⟶ C :=
  @parametrized_right_adjoint_bifunctor C Coq C Copower_Bifunctor
    Copower_ParametrizedAdjunction.

Example power_bifunctor_obj (J : Type) (b : C) :
  fobj[Power_Bifunctor] (J, b) = power J b := eq_refl.

Example pa_right_is_power_functor (J : Type) :
  pa_right Copower_ParametrizedAdjunction J = Power_Functor J := eq_refl.

(* The parametrized adjunction's own hom-set isomorphism at each index IS
   §B's, on the nose -- so §E does not fork §B's bijection. *)
Example pa_adj_iso_is_cp_adj_iso (J : Type) (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    (pa_adj Copower_ParametrizedAdjunction J) b c
  = cp_adj_iso J b c := eq_refl.

End IndexParameter.

Arguments cp_pa_adj {C HP HC} J.
Arguments Copower_ParametrizedAdjunction {C HP HC}.
Arguments Power_Bifunctor {C HP HC}.

Section IndexReindexing.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

Notation PA := (@Copower_ParametrizedAdjunction C HP HC).
Notation CB := (@Copower_Bifunctor C HC).

(* Reindexing the COPOWER, covariantly in the index set. *)
Definition copower_reindex {J J' : Type} (h : J ~{Coq}~> J') :
  Partial_l CB J ⟹ Partial_l CB J' := param_transform CB h.

Lemma copower_reindex_inj {J J' : Type} (h : J ~{Coq}~> J') (b : C) (j : J) :
  copower_reindex h b ∘ copower_inj J b j ≈ copower_inj J' b (h j) ∘ id.
Proof. exact (cop_bifun_inj (b, J) (b, J') (id, h) j). Qed.

(* Reindexing the POWER, CONTRAVARIANTLY: #396's conjugate mate, consumed. *)
Definition power_reindex {J J' : Type} (h : J' ~{Coq}~> J) :
  Power_Functor J ⟹ Power_Functor J' := pa_param_mate PA h.

Example power_reindex_is_conj_mate {J J' : Type} (h : J' ~{Coq}~> J) :
  power_reindex h
    = conj_mate (pa_adj PA J) (pa_adj PA J') (param_transform CB h) := eq_refl.

(* The counit of the parametrized adjunction at the index [J], read through
   the copower injections: it IS the evaluation, with one identity residue. *)
Lemma cp_pa_counit_inj (J : Type) (b : C) (j : J) :
  @counit C C (Partial_l CB J) (Power_Functor J) (pa_adj PA J) b
    ∘ copower_inj J (power J b) j ≈ power_ev J b j.
Proof.
  etransitivity.
  - exact (unique_property
             (copower_desc (copower_ump J (power J b))
                (fun i : J => power_ev J b i ∘ id)) j).
  - apply id_right.
Qed.

(* The contravariant reindexing of powers is evaluation at [h j']. *)
Lemma power_reindex_ev {J J' : Type} (h : J' ~{Coq}~> J) (b : C) (j' : J') :
  power_ev J' b j' ∘ power_reindex h b ≈ power_ev J b (h j').
Proof.
  unfold power_reindex, pa_param_mate, conj_mate; simpl.
  etransitivity.
  { exact (unique_property (power_desc (power_ump J' b) _) j'). }
  rewrite <- comp_assoc.
  rewrite (copower_reindex_inj h (power J b) j').
  rewrite id_right.
  apply cp_pa_counit_inj.
Qed.

(* ★ THE CONJUGACY, CONSUMED.  [pa_natural_p] is #396's theorem and
   [pa_square_is_Conjugate] says the square IS #394's [Conjugate] on the
   nose, so the ascription below is the whole proof. *)
Definition power_reindex_conjugate {J J' : Type} (h : J' ~{Coq}~> J) :
  Conjugate (pa_adj PA J) (pa_adj PA J')
            (copower_reindex h) (power_reindex h) :=
  pa_natural_p PA h.

(* And it is the UNIQUE such transformation. *)
Definition power_reindex_universal {J J' : Type} (h : J' ~{Coq}~> J) :
  ∃! tau : Power_Functor J ⟹ Power_Functor J',
    Conjugate (pa_adj PA J) (pa_adj PA J') (copower_reindex h) tau :=
  pa_param_mate_universal PA h.

Corollary power_reindex_id (J : Type) : power_reindex (@id Coq J) ≈ nat_id.
Proof. exact (pa_param_mate_id PA). Qed.

Corollary power_reindex_comp {J J' J'' : Type}
  (h : J' ~{Coq}~> J) (h' : J'' ~{Coq}~> J') :
  power_reindex (h ∘ h') ≈ power_reindex h' ∙ power_reindex h.
Proof. exact (pa_param_mate_comp PA h h'). Qed.

Corollary copower_reindex_id (J : Type) :
  copower_reindex (@id Coq J) ≈ nat_id.
Proof. exact (param_transform_id CB). Qed.

Corollary copower_reindex_comp {J J' J'' : Type}
  (h : J ~{Coq}~> J') (h' : J' ~{Coq}~> J'') :
  copower_reindex (h' ∘ h) ≈ copower_reindex h' ∙ copower_reindex h.
Proof. exact (param_transform_comp CB h h'). Qed.

End IndexReindexing.

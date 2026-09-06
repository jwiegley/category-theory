Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Two.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

Set Default Proof Using "All".

(** * The subobject classifier of a set-valued functor category *)

(* Mac Lane, CWM 2nd ed., §IV.9 construction 2 and remark 1, book
   pp. 105-106 ([maclane:IV.9:construction2], [maclane:IV.9:remark1]).
   Verbatim, from the rendered pages:

     "For example, take C to be the category of functions f : X → Y.
      Here, a monomorphism g ↣ f is a function g : S → T between a pair
      of subsets S ⊂ X and T ⊂ Y such that g(s) = f(s) for all s ∈ S.
      ...  In this case, there are three types of elements of X: those x
      in S, those x not in S but with g x in T, and, finally, those x not
      in S with g x not in T.  We may then define a characteristic
      function with three values by setting

          ψ_S x = 0  if x ∈ S ,
          ψ_S x = 1  if x ∉ S but f x ∈ T ,
          ψ_S x = 2  if f x ∉ T (and hence, x ∉ S) .

      Again this prescription provides a pullback ... of objects X → Y
      and j : {0,1,2} → {0, 1} in the category of functions, where the
      function j on the right is given by j0 = 0, j1 = 0, j2 = 2.  Thus,
      in this case, the inclusion j on the right is a subobject
      classifier for the category of functions."

     "There are many other examples of subobject classifiers.  First,
      recall that the arrow category 2 is the category with only two
      objects 0 and 1 and only one non-identity arrow a : 0 → 1.  Thus,
      an ordinary function f is the same thing as a functor 2 → Sets.
      Hence, we have constructed above the subobject classifier for the
      functor category Sets^2.  For any category C, there is a subobject
      classifier (find it!) for the functor category Sets^C."

   THE PRINTED PAGE CARRIES A MISPRINT, and it is recorded rather than
   silently corrected: the text says "j : {0,1,2} → {0, 1}" while the
   diagram's lower-right corner is "{0,2}" and the formula in the same
   sentence is "j0 = 0, j1 = 0, j2 = 2".  The diagram and the formula
   agree with each other, so the codomain of j is the two-element set
   {0, 2} and the text's "{0, 1}" is the misprint.  The mathematics
   below follows the diagram and the formula.

   Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print,
   September 2005), §8.8, printed pp. 210-211, inside the proof of
   Proposition 8.17 ([awodey:8.8:def-sieve],
   [awodey:8.8:construction-omega-sieves]).  Verbatim:

     "To that end, for any category C we define a sieve on an object C
      to be any set S of arrows f : · → C (with arbitrary domain) that
      is closed under precomposition ...  Then let:

          Ω(C) = {S ⊆ C_1 | S is a sieve on C}

      and given h : D → C let:  h* : Ω(C) → Ω(D)  be defined by:
          h*(S) = {g : · → D | h ∘ g ∈ S}.

      This clearly defines a presheaf Ω : C^op → Sets, with a
      distinguished point, t : 1 → Ω, namely, at each C, the "total
      sieve": t_C = {f : · → C}."

     "We claim that t : 1 → Ω so defined is a subobject classifier for
      Sets^{C^op}.  Indeed, given any object E and subobject U ↣ E,
      define u : E → Ω at any object C ∈ C by:

          u_C(e) = {f : D → C | f*(e) ∈ U(D) ↣ E(D)}

      for any e ∈ E(C).  That is, u_C(e) is the sieve of arrows into C
      that take e ∈ E(C) back into the subobject U.

      The reader should verify that this specification does indeed
      determine a unique classifying morphism for U ↣ E.  □"

   Mac Lane's Sets^C is the COVARIANT functor category [C, Sets] and
   Awodey's Ω is for PRESHEAVES [C^op, Sets].  The two are one family
   with C replaced by C^op, and here that replacement costs nothing:
   [(D^op)^op = D] holds by [eq_refl] in this tree, so the covariant
   reading [Fun_Classifier_cov] is [Fun_Classifier] at [D^op] supplied
   by [:=] with no tactic and no transport.

   WHAT IS DELIVERED, AND AT WHICH STRENGTH.  A genuine
   [@SubobjectClassifier ([C^op, Sets]) (Functor_Category_Terminal
   Sets_Terminal)] for an ARBITRARY category C — at the universe levels
   the presheaf category itself forces, see UNIVERSES below —
   CONDITIONALLY on #402's [Untruncate@{o}], in two universe readings:

     [Fun_Classifier      : Untruncate -> SubobjectClassifier] at the
        minimized reading of the presheaf category, with
        Ω := [Sieve_Presheaf C] (Theory/Sieve.v) and
        truth := [sieve_truth C], both read back by [eq_refl], and the
        characteristic map read back as [char_nat] likewise;

     [Fun_Classifier_small : ... -> SubobjectClassifier] at a reading
        that places the presheaf category's OBJECTS at or below its
        HOMS, which is what Structure/SubobjectClassifier.v's
        [classifier_classifies] demands — see WORK ITEM 2 below.

   [Fun_Classifier_IEM] is the first at #402's [untruncate_of_IEM], and
   [Fun_Classifier_cov] the covariant reading.  Neither is registered as
   an [Instance]: the hypothesis must not become globally resolvable,
   and neither must a chosen classifier.

   THE PER-CONSTANT HYPOTHESIS LEDGER, MEASURED AT THE SIGNATURES.  The
   three class obligations cost three different things, and this is the
   file's sharpest fact.

     [char_nat], [char_square]   NO hypothesis at all.  They are section
        constants of Section Char, whose Context is C, E, U and theta and
        nothing else, so no [Monic] and no [Untruncate] occurs in either
        type.  The classifying square commutes for an ARBITRARY natural
        transformation, monic or not.

     [presheaf_char_unique]      NO hypothesis either — neither [Monic]
        nor [Untruncate].  Section Unique's Context is C, E, U, theta, h and the
        [IsPullback] the caller supplies.  Awodey's "the reader should verify
        ... a UNIQUE classifying morphism", which the issue flags as real work,
        is the CHEAP half here.  What pays for it is the sieve read as a
        SUBPRESHEAF: [h_sub_char] feeds the pullback's own universal property
        [sieve_subpresheaf d S], the presheaf of the arrows into d that lie in
        the sieve, together with its cone [sieve_cone] into E, and the witness
        comes OUT of the mediator as a genuine element, so no truncation is
        eliminated anywhere in it.  The Awodey §8.8 "standalone, exported Sieve
        as a subobject of the representable" checkbox is the further step
        [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject], that subpresheaf
        embedded in [Curried_CoHom C d]; the three form a chain ending in
        [sieve_subobject], and NOTHING outside the chain consumes any of them —
        measured by deleting all three and recompiling the file, which succeeds
        — so the checkbox is delivered as a standalone reading of Awodey's
        clause, and the uniqueness clause consumes only the subpresheaf and its
        cone.

     [presheaf_char_pullback]    needs BOTH.  [Monic theta] is turned
        into pointwise injectivity by #369's
        [presheaf_monic_iff_injective] (Instance/Fun/Morphisms.v) — this
        is the issue's reviewer check, "the monos used are the pointwise
        ones, which requires the pointwise mono characterisation" — and
        that injectivity, named [theta_inj] here, is spent at THREE
        SITES on the way to [presheaf_char_pullback] — the mediator
        [char_med]'s respectfulness obligation, its naturality (two
        obligations, [Transform] carrying both [naturality] and
        [naturality_sym]), and the uniqueness clause of
        [presheaf_char_pullback] itself — which is FOUR uses; a fifth
        is section (I)'s [small_pb], which rebuilds only that last
        clause.  [Untruncate] is spent EXACTLY ONCE, in [med_img],
        where the commuting hypothesis at f := id gives a squashed image
        membership and the mediator must produce an ELEMENT — the token
        [UT] is eliminated at exactly one line of the file.

   WHETHER [Untruncate] IS NECESSARY IS NOT SETTLED.  It SUFFICES; no
   impossibility is proved, and no weaker hypothesis was searched for.
   What IS measured is that the naive elimination
   [fun P h => h P (fun p => p)] is refused with "Cannot enforce
   o <= Prop" — #402's wall, at the same level o — with
   [powerset_squash_prop_inert] as the accepted control, both pinned in
   Test/ProbeFunClassifier403.v.  No [DecImage]-shaped variant is built.

   THE DISCLOSURE, IN THREE PARTS, following #402's.  (i) NO
   unconditional axiom-free instance is built here.  (ii) NO
   impossibility theorem is proved here.  (iii) An in-tree impossibility
   proof is out of reach in a precise sense: a scratch development
   compiled against this worktree builds [Fun_Classifier
   (untruncate_of_IEM IEM_classical)] out of Coq's own classical axioms
   and [Print Assumptions] reports EXACTLY [constructive_indefinite_
   description] and [classic] (Coq.Logic.ClassicalEpsilon), so an
   in-tree impossibility theorem would refute a classically valid
   statement.  That is an ARGUMENT, not a theorem: nothing below proves
   it, and the classical instance is deliberately not shipped.

   THE TRUTH-VALUE CONVENTION, AND THE DICTIONARY.  Every subobject
   classifier puts ITS truth value on the subobject — that is what the
   classifying pullback square says — so a "convention" here can only be
   the NAME the truth value carries.  Mac Lane names his 0 (§IV.9
   construction 1, book p. 105: ψ_S x = 0 if x ∈ S, with 0 the value
   "truth"); Seven Sketches names it [true]; Instance/FinSet/Classifier.v
   names it [fin_true], which is [Fin.F1], the FIRST element of [Fin.t 2] —
   so read as a numeral it is Mac Lane's 0, and the "swap 0 ↔ 1" that
   Instance/Sets/Classifier/OneLevel.v records is between the two books'
   NAMES, not between elements of any in-tree Ω; and OneLevel.v's two
   instances name theirs [Powerset_truth_point] and [ptrue], with no
   numeral at all.  Here Ω(c) is a set of SIEVES and the truth point is the
   total sieve: an element of the subobject has the total characteristic
   sieve ([char_square], no hypothesis), and the converse is the pullback
   clause, where [Untruncate] is spent.  There is no numeral in Ω(c) and
   nothing to swap.

   The numeral enters only at the arrow shape, through section (G)'s
   codes [twoX_code : Sieve TwoX → Fin.t 3] and
   [twoY_code : Sieve TwoY → Fin.t 2], and there the dictionary

       total sieve on TwoX  ↔  0        {TwoXY}  ↔  1        ∅  ↔  2
       total sieve on TwoY  ↔  0                            ∅  ↔  2

   is FORCED rather than chosen, by two facts.  The page puts 0 ON the
   subset and an element of the subobject has the total characteristic
   sieve, so the total sieve is 0 — the same [Fin.F1] that [fin_true] is,
   so numeral for numeral this file, Instance/FinSet/Classifier.v and the
   page agree.  Then [jmap := fmap[Sieve_Presheaf (_2^op)] TwoXY] carries
   total ↦ total, mid ↦ total, empty ↦ empty ([j_total], [j_mid],
   [j_empty]), so it IDENTIFIES the first two and SEPARATES the first from
   the third ([j_identifies], [j_separates]) — Mac Lane's j0 = 0, j1 = 0,
   j2 = 2 with codomain {0, 2}, whose fibres are {0, 1} and {2}; with total
   already at 0 that leaves {TwoXY} at 1 and ∅ at 2 on TwoX, and total at 0
   and ∅ at 2 on TwoY.  The three sieves on TwoX are pairwise ≉-distinct
   ([twoX_total_neq_mid], [twoX_mid_neq_empty], [twoX_total_neq_empty]),
   the two on TwoY likewise.  The identification with his EXPLICIT
   three-element object is [mac_dictionary]: under #402's [IEM] the codes
   satisfy [twoY_code (jmap S) = macj (twoX_code S)] for EVERY sieve S,
   where [macj] is Mac Lane's j written out and computing at all three
   arguments.  So the arrow-shape specialisation is PROVED, not asserted,
   which is the issue's other reviewer check.  The counts themselves —
   "exactly three sieves on TwoX" — are constructively unavailable (a sieve
   on TwoX is a pair of [Prop]s under mutual implication, so counting them
   is as strong as two-valuedness of [Prop]), and are delivered under [IEM]
   as [twoX_three_sieves] and [twoY_two_sieves].  This is the SAME
   conditionality as the general instance, for the same reason.

   WORK ITEM 2 ("subfunctors correspond to natural families of sieves,
   which is the content of the classification"), and the exact status of
   [classifier_classifies].  The sentence "classifier_classifies is not
   statable for presheaf categories" would be FALSE; the precise one is
   this.  The theorem carries the BOUND [u <= u0] over
   [C : Category@{u u0 u0}] — objects at or below homs — which is what
   #402 records as unsatisfiable at [Sets].  At a presheaf category it IS
   satisfiable, and three things are measured.  (a) The theorem is
   FORMABLE at an ABSTRACT classifier of [[C^op, Sets]] (a probe
   control).  (b) It is NOT applicable to [Fun_Classifier], whose own
   elaboration minimizes the presheaf category's hom universe below its
   object universe: the refusal is of the shape "Cannot enforce o = …
   because o < … <= … <= …", pinned.  (c) A HAND-ANNOTATED redefinition DOES
   escape it, and that is section (I): under declared universes with
   [so <= OO] and [OO <= HH], [PShSmall := [Cs^op, Sets@{o so}] :
   Category@{OO HH HH}] carries [Fun_Classifier_small], and
   [fun_classifier_classifies] is [classifier_classifies] applied to it
   over [Fun_HasPullbacks Sets_HasPullbacks] — an isomorphism in [Sets]
   between the subobjects of a presheaf and the maps into Ω.  That IS
   work item 2, in the form the issue calls "the content of the
   classification"; and its NATURAL upgrade comes with it, since
   Structure/SubobjectClassifier/Natural.v's [Sub_classifier_natural]
   carries the same bound — [fun_sub_classifier_natural] and
   [fun_Sub_Representable] are that theorem and its representability
   corollary applied.  The re-annotation is NOT free: [small_pb] reuses the
   already-built pieces, but the uniqueness clause has to be RESTATED
   ([small_char_sub_h], [small_h_sub_char], [small_unique]), because
   [presheaf_char_unique] takes an [IsPullback] and the two universe
   readings of that argument are not interconvertible — measured:
   supplying section (I)'s [IsPullback] to [presheaf_char_unique] is
   refused with a universe inconsistency at that argument, the field where
   the two readings visibly differ being [ump], which quantifies over the
   ambient category's objects and hom-types.  The two
   ROUND TRIPS of Structure/SubobjectClassifier.v are delivered for the
   minimized reading as well ([fun_char_roundtrip],
   [fun_pullback_roundtrip]), both [:=] of that file's own constants,
   both NAMING [Fun_HasPullbacks Sets_HasPullbacks] explicitly in their
   statements — it is a plain [Definition], not an [Instance], so nothing
   resolves it silently.

   WHY THREE FILES.  Theory/Sieve.v is LEAN (closure 16, a subset of
   both Theory/Sheaf.v's 18 and Construction/Localization.v's 23, so
   either could reuse it later at zero module cost; neither is rewired
   here).  Instance/Fun/Pullback.v is a general [C, D] result with no
   [Sets] in it at all.  This file is the [Sets]-valued assembly, and it
   is where [Functor/Hom.v]'s [Curried_CoHom] and
   Instance/Fun/Morphisms.v's mono characterisation enter, neither of
   which is in the lean closure.

   UNIVERSES, measured off BOTH binder and block over all 115 constants.
   [Fun_Classifier@{u u0 u1}] is over [C : Category@{u1 u u}] with
   [Untruncate@{u}] — C's hom universe, C's proof universe and [Sets]' CARRIER
   universe are all the single level [u], and that identification sits ENTIRELY
   IN THE BINDER: its constraint block carries NO equation at all, only bounds
   ([Set < u], [u < u0], [u1 <= u] and stdlib bounds), and
   [Fun_Classifier_small@{co o so OO HH u u0}] carries none either (its block
   adds no equation to the four declared constraints of section (I), [Set < o],
   [o < so], [so <= OO] and [OO <= HH]; the rest are bounds — eight relating the
   declared levels to each other and to the constant's own [u], and the stdlib
   ones).  Reading the block alone reports no identification and is wrong.
   TWENTY of the 115 do carry a block equation, and it is a different one.
   FOURTEEN — Section Char's [Efmap_resp], [Efmap_comp], [Efmap_id],
   [theta_natural], [in_image], [char_sieve], [char_at], [char_nat],
   [char_square] and their five [Program] obligations — carry [u1 = u2],
   identifying the [Sets] universes of the two presheaves E and U: that section
   binds E and U on SEPARATE Context lines, so each gets its own [Sets]
   instance, and [Context (theta : U ⟹ E)] — a transformation lives between
   functors into ONE [Sets] — equates them, an equation handed to every constant
   of the section by discharge, [Efmap_resp] included though its own type never
   mentions U or theta; the same body in a section binding E and U on separate
   lines but no theta carries no equation (measured out of tree, not pinned).
   WHERE the identification lands is decided by the binding shape and not by
   theta: Section Pullback has the same [theta] in its Context but binds
   [{E U : C^op ⟶ Sets}] on ONE line, so its constants share the level in the
   BINDER and carry no block equation at all, [presheaf_char_pullback] included.
   THREE — Section Unique's [char_sub_h], [h_sub_char] and
   [presheaf_char_unique] — also bind [{E U}] on one line, and their [u1 = u2]
   is a DIFFERENT identification under the same spelling: [u2] there is a
   universe [Sieve_Presheaf] brings in through
   [Context (h : E ⟹ Sieve_Presheaf C)], which BOUNDS it ([u0 < u2]) without
   identifying it, and the equation is the [IsPullback] Context [HP]'s — the
   same Context without [HP] carries no equation and with it carries this one
   (measured out of tree, not pinned; that [HP] places E, U and
   [Sieve_Presheaf C] as objects of ONE functor category is an explanation, not
   the measurement).  The other THREE are section (I)'s [small_char_sub_h],
   [small_h_sub_char] and [small_unique], which carry [so = u0] (and [so = u])
   from the declared constraints.  [Sieve_Presheaf] and [SieveObj] carry none,
   and neither does anything in Instance/Fun/Pullback.v except [Fun]'s own
   [u0 = u2], which SEVENTEEN of that file's 24 do carry.  SIXTY-THREE of the
   115 carry a word-bounded [Set], always as the strict LOWER bound [Set < _]
   and never as an equation.  The two BINDER identifications are the presheaf
   category's, not this file's, and each is guarded by a probe negative with
   controls accepted at the very same levels: [ch = cp] has TWO INDEPENDENT
   donors, [Opposite] and [Fun] (the second refused with no [^op] in the command
   at all), while [@Functor Cu Cu] and [@Functor Cu Sets] are ACCEPTED, so
   [Functor] is not a donor; and [ch = o] is [Fun]'s in BOTH variances, with
   [Cv^op], [Cv^op ⟶ Sets] and [Cv ⟶ Sets] accepted as controls.  C's OBJECT
   universe is only BOUNDED ([u1 <= u]), which is Awodey's "for any SMALL
   category C" and is where smallness lands.  The strict lower bound [Set < u]
   enters with the [Prop]-valued membership itself ([Prop : Type@{Set+1}]) — it
   is already [SieveObj]'s in Theory/Sieve.v, upstream of any [Powerset_squash]
   — and is a BOUND, never a pin, but it excludes exactly the C whose hom
   universe is the literal [Set].  TWENTY-ONE constants carry [Set] in a BINDER
   and every one of them is section (G)'s — most as [Sieve@{_ Set}], the rest
   through [_2] or [FinSet] — inherited from Instance/Two.v's
   [TwoHom : TwoObj → TwoObj → Set] and not introduced here; the other thirty of
   section (G)'s fifty-one heads carry [Set] only as the block bound above.

   THE ISSUE'S "Current state" IS STALE ON FOUR COUNTS, each measured.  It says
   [ls Instance/Fun/] "contains only [Cartesian.v]"; at the base commit that
   directory has SEVEN satellites (Cartesian, Terminal, Closed, Morphisms,
   Discrete, Group, Action).  It says there is "not even a [Terminal] instance
   for a functor category"; that is #339's [Functor_Category_Terminal], and
   Instance/Fun/Terminal.v even carries the specialised [Two_Sets_Terminal].  It
   says the pointwise mono characterisation is missing; that is #369's
   [presheaf_monic_iff_injective].  And it says the only [SubobjectClassifier]
   instance in the tree is Instance/FinSet/Classifier.v's; #402 added two
   conditional ones for [Sets].  What IS genuinely absent, and is what these
   three files supply, is any sieve at all (at the base commit
   [rg -in 'sieve' -g '*.v'] returns two prose lines, one in Theory/Sheaf.v and
   one in Construction/Localization.v; without the [-g] the doc/plan coverage
   records add 143 more), any classifier for a functor category, and any
   pullback instance for a functor category.

   COUNTS, WITH THEIR CRITERIA.  Constants closed under the global
   context: 115/115 with zero [Axioms:] lines, counted as the entries
   [Print Module] emits at five-space indent (which include the
   [Program] obligations, invisible to the [.glob]); this file declares
   no record, so there is no unlisted [Build_*].  Every one is queried
   FULLY QUALIFIED, and all 115 are in the [print-assumptions] gate,
   which carries 161 names for the three files together.  [Defined]
   tokens: 7, of which FOUR are load-bearing — measured by flipping each
   ALONE to [Qed] and compiling the result alone: [sieve_sub_map],
   [sieve_subpresheaf], [sieve_incl] and [sieve_cone] all stop the file,
   while [med_img], [presheaf_char_pullback] and [small_pb] compile as
   [Qed] and are kept [Defined] only because they produce data.
   Statements closed by [:= eq_refl]: 14.  Transitive
   in-project closure excluding this file: 105 modules, with drop-one
   marginals Instance/Fun/Terminal 29, Instance/Sets/Classifier/OneLevel
   14, and Theory/Sieve, Structure/SubobjectClassifier/Natural,
   Instance/Fun/Morphisms and Instance/Fun/Pullback 1 each; EVERY other
   Require costs 0, Instance/FinSet included, which is why [MacOmega] can
   live here rather than in the probe.  The 14 for
   OneLevel is what identity with #402's hypothesis costs, and it is paid
   deliberately: restating
   [Untruncate] locally would fork the hypothesis, which is the whole
   point of consuming it.  This file contributes ZERO [make todo] hits;
   its probe carries the refutation commands.

   NOT DELIVERED.  No unconditional axiom-free instance and no impossibility
   theorem (the three-part disclosure above).  No proof that [Untruncate] is
   necessary, and no [DecImage] variant.  No
   [@SubobjectClassifier ([_2, FinSet]) _] instance: [MacOmega] is built and
   computes, but the instance would need the shape-[_2] converse of the mono
   characterisation and a three-way characteristic map, neither of which is
   built.  No bijection between the sieves on TwoX and [Fin.t 3] without [IEM] —
   [twoX_code] is defined only from it.  No converse for [Fun_IsPullback]
   (Instance/Fun/Pullback.v's own NOT DELIVERED).  No pushouts, equalizers or
   completeness for [C, D].  No [ElementaryTopos] for any presheaf category and
   no exponentials: Instance/Fun/Closed.v refutes the inheritance of cartesian
   closure in general, and its positive half is not attempted here.  NATURALITY
   IS DELIVERED, but only at the second reading: [Sub_classifier_natural] is
   MEASURED to be formable at an abstract classifier of [[C^op, Sets]] and
   refused at [Fun_Classifier] — the same pair as [classifier_classifies] —
   while at [Fun_Classifier_small] it applies, and is shipped as
   [fun_sub_classifier_natural] with [fun_Sub_Representable] beside it.  So
   there is NO naturality statement for [Fun_Classifier] itself.  No
   Grothendieck topology, no coverage and no sheaf reading; Theory/Sheaf.v and
   Construction/Localization.v are NOT rewired, only pointed at this file in
   prose.  No comparison of [Sieve_Presheaf] at a poset with a lower-set
   construction.  No passage from a subobject of the representable BACK to a
   sieve: [sieve_subobject] runs one way only, so Awodey's "as a subobject of
   the representable" is delivered as an embedding of sieves and not as an
   identification of the two notions — and nothing outside the chain
   [sieve_incl] / [sieve_incl_Monic] / [sieve_subobject] consumes it, the
   uniqueness clause taking the subpresheaf and its cone instead (the ledger
   above).  No comparison of [Fun_Classifier] with [Fun_Classifier_small] at any
   strength: they are two universe readings of one construction, and no equation
   relates them.  Nothing at all is registered as an [Instance] in this file:
   the setoid [sieve_sub_obj] needs is an inline record literal, and the only
   registered instance of the three files is Theory/Sieve.v's [Sieve_Setoid]. *)

#[local] Obligation Tactic := idtac.

(* ---------------- (A) the truth transformation ---------------- *)

Program Definition sieve_truth (C : Category) :
  @terminal_obj ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    ⟹ Sieve_Presheaf C := {|
  transform := fun c => {| morphism := fun _ => @total_sieve C c |}
|}.
Next Obligation.
  intros C c; unfold Proper, respectful; intros u v _ d g; simpl.
  split; auto.
Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.

Example sieve_truth_at (C : Category) (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (Functor_Category_Terminal Sets_Terminal)] c)) :
  transform[sieve_truth C] c u = @total_sieve C c := eq_refl.

(* ---------------- (B) the characteristic transformation ------- *)

Section Char.

Context {C : Category}.
Context {E : C^op ⟶ Sets}.
Context {U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).

Definition Efmap_resp {c d : C} (f g : d ~{C}~> c) (Hfg : f ≈ g)
      (e : carrier (fobj[E] c)) : fmap[E] f e ≈ fmap[E] g e
  := @fmap_respects (C^op) Sets E c d f g Hfg e.

Definition Efmap_comp {c d d' : C} (f : d ~{C}~> c) (g : d' ~{C}~> d)
      (x : carrier (fobj[E] c)) :
  fmap[E] (f ∘ g) x ≈ fmap[E] g (fmap[E] f x)
  := @fmap_comp (C^op) Sets E c d d' g f x.

Definition Efmap_id {c : C} (x : carrier (fobj[E] c)) :
  fmap[E] (@id C c) x ≈ x
  := @fmap_id (C^op) Sets E c x.

Definition theta_natural {c d : C} (f : d ~{C}~> c)
    (x : carrier (fobj[U] c)) :
  fmap[E] f (transform[theta] c x) ≈ transform[theta] d (fmap[U] f x)
  := @naturality (C^op) Sets U E theta c d f x.

Definition in_image (d : C) (y : carrier (fobj[E] d)) : Type :=
  ∃ x : carrier (fobj[U] d), transform[theta] d x ≈ y.

Program Definition char_sieve (c : C) (e : carrier (fobj[E] c)) :
  @Sieve C c := {|
  sieve_mem := fun d (f : d ~{C}~> c) =>
                 Powerset_squash (in_image d (fmap[E] f e))
|}.
Next Obligation.
  intros c e d f g Hfg Hmem Q k.
  apply Hmem; intros [x Hx]; apply k; exists x.
  transitivity (fmap[E] f e); [ exact Hx | exact (Efmap_resp f g Hfg e) ].
Qed.
Next Obligation.
  intros c e d d' f g Hmem Q k.
  apply Hmem; intros [x Hx]; apply k.
  exists (fmap[U] g x).
  transitivity (fmap[E] g (transform[theta] d x)).
  - symmetry; exact (theta_natural g x).
  - transitivity (fmap[E] g (fmap[E] f e)).
    + exact (proper_morphism (fmap[E] g) _ _ Hx).
    + symmetry; exact (Efmap_comp f g e).
Qed.

Program Definition char_at (c : C) :
  fobj[E] c ~{Sets}~> @SieveObj C c := {|
  morphism := char_sieve c
|}.
Next Obligation.
  intros c.
  unfold Proper, respectful; intros e e' Hee' d f; simpl.
  split; intros Hmem Q k; apply Hmem; intros [x Hx]; apply k; exists x.
  - transitivity (fmap[E] f e); [ exact Hx | ].
    exact (proper_morphism (fmap[E] f) _ _ Hee').
  - transitivity (fmap[E] f e'); [ exact Hx | ].
    symmetry; exact (proper_morphism (fmap[E] f) _ _ Hee').
Qed.

Program Definition char_nat : E ⟹ Sieve_Presheaf C := {|
  transform := char_at
|}.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ exact Hc | symmetry; exact Hc ].
Qed.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ symmetry; exact Hc | exact Hc ].
Qed.

(* the square commutes, with no hypothesis at all *)
Theorem char_square :
  char_nat ∘[[C^op, Sets]] theta
    ≈ sieve_truth C ∘[[C^op, Sets]]
        @one ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal) U.
Proof.
  intros c x d f; simpl.
  split; intro Hm; [ exact I | ].
  intros Q k; apply k.
  exists (fmap[U] f x).
  symmetry; exact (theta_natural f x).
Qed.

End Char.

(* ---------------- (C) a sieve as a subobject of y(c) ---------- *)

Section SieveSub.

Context {C : Category}.

Lemma sieve_sub_eq (c : C) (S : Sieve c) (k : C) :
  Equivalence (fun u v : { g : k ~{C}~> c & sieve_mem S g } =>
                 projT1 u ≈ projT1 v).
Proof.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - etransitivity; eassumption.
Qed.

Definition sieve_sub_obj (c : C) (S : Sieve c) (k : C) : SetoidObject :=
  {| carrier := { g : k ~{C}~> c & sieve_mem S g }
   ; is_setoid := {| equiv := fun u v => projT1 u ≈ projT1 v
                   ; setoid_equiv := sieve_sub_eq c S k |} |}.

Definition sieve_sub_map (c : C) (S : Sieve c) (k j : C) (h : j ~{C}~> k) :
  sieve_sub_obj c S k ~{Sets}~> sieve_sub_obj c S j.
Proof.
  unshelve refine {| morphism := fun u => existT _ (projT1 u ∘ h) _ |}.
  - exact (sieve_closed S (projT1 u) h (projT2 u)).
  - intros u v Huv; simpl in *. now rewrite Huv.
Defined.

Definition sieve_subpresheaf (c : C) (S : Sieve c) : C^op ⟶ Sets.
Proof.
  unshelve refine (@Build_Functor (C^op) Sets (sieve_sub_obj c S)
                     (fun k j (h : k ~{C^op}~> j) => sieve_sub_map c S k j h)
                     _ _ _).
  - intros k j h1 h2 Hh u; simpl. now rewrite Hh.
  - intros k u; simpl. apply id_right.
  - intros k j l h1 h2 u; simpl. apply comp_assoc.
Defined.

Definition sieve_incl (c : C) (S : Sieve c) :
  sieve_subpresheaf c S ~{[C^op, Sets]}~> Curried_CoHom C c.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S)
                     (Curried_CoHom C c) (fun k => _) _).
  - unshelve refine {| morphism := fun u => projT1 u |}.
    intros u v Huv; exact Huv.
  - intros k j h u; simpl. reflexivity.
Defined.

Definition sieve_incl_Monic (c : C) (S : Sieve c) :
  @Monic ([C^op, Sets]) _ _ (sieve_incl c S) :=
  snd (presheaf_monic_iff_injective (sieve_incl c S))
      (fun k a b Hab => Hab).

Definition sieve_subobject (c : C) (S : Sieve c) :
  @SubObj ([C^op, Sets]) (Curried_CoHom C c) :=
  @Build_SubObj ([C^op, Sets]) (Curried_CoHom C c)
    (sieve_subpresheaf c S) (sieve_incl c S) (sieve_incl_Monic c S).

(* the cone into E determined by an element of E c *)
Definition sieve_cone {E : C^op ⟶ Sets} (c : C) (e : carrier (fobj[E] c))
  (S : Sieve c) : sieve_subpresheaf c S ~{[C^op, Sets]}~> E.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S) E
                     (fun k => _) _).
  - unshelve refine {| morphism := fun u => fmap[E] (projT1 u) e |}.
    intros u v Huv; simpl in *.
    exact (@fmap_respects _ _ E c k (projT1 u) (projT1 v) Huv e).
  - intros k j h u; simpl. symmetry.
    exact (@fmap_comp _ _ E c k j h (projT1 u) e).
Defined.

End SieveSub.

(* ---------------- (D) uniqueness of the classifying map ------- *)

Section Unique.

Context {C : Category}.
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (h : E ⟹ Sieve_Presheaf C).
Context (HP : @IsPullback ([C^op, Sets]) E
                (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
                (Sieve_Presheaf C) h (sieve_truth C) U theta
                (@one _ (Functor_Category_Terminal Sets_Terminal) U)).

Lemma char_sub_h (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id C d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id C d))).
    exact (proj2 (Hc d (@id C d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id C d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma h_sub_char (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id C d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id C d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone C E d ed S).
  assert (Hcone : ∀ (k : C) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[[C^op, Sets]] q1
                  ≈ sieve_truth C ∘[[C^op, Sets]]
                      @one ([C^op, Sets])
                        (Functor_Category_Terminal Sets_Terminal)
                        (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one _ (Functor_Category_Terminal Sets_Terminal) _) Hsq)
    as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id C d) HidS)).
  pose proof (Hu1 d (existT _ (@id C d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem presheaf_char_unique : h ≈ char_nat theta.
Proof.
  intros c e d f; split; [ apply h_sub_char | apply char_sub_h ].
Qed.

End Unique.

(* ---------------- (E) the classifying square is a pullback ---- *)

Section Pullback.

Context {C : Category}.
Context (UT : Untruncate).
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (M : @Monic ([C^op, Sets]) U E theta).

Definition theta_inj : ∀ (c : C^op) (a b : carrier (fobj[U] c)),
    transform[theta] c a ≈ transform[theta] c b -> a ≈ b
  := fst (presheaf_monic_iff_injective theta) M.

Definition med_img {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : in_image theta c (transform[q1] c z).
Proof.
  pose proof (UT _ (Hq c z)) as Hx.
  destruct Hx as [x Hx].
  exists x.
  transitivity (fmap[E] (@id C c) (transform[q1] c z)); [ exact Hx | ].
  exact (Efmap_id (E:=E) (transform[q1] c z)).
Defined.

Definition med_elt {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : carrier (fobj[U] c) :=
  projT1 (med_img q1 Hq c z).

Definition med_spec {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) :
  transform[theta] c (med_elt q1 Hq c z) ≈ transform[q1] c z :=
  projT2 (med_img q1 Hq c z).

Program Definition char_med {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)) :
  Q ⟹ U := {|
  transform := fun c => {| morphism := fun z => med_elt q1 Hq c z |}
|}.
Next Obligation.
  intros Q q1 Hq c.
  unfold Proper, respectful; intros z z' Hzz'.
  apply (theta_inj c).
  transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
  transitivity (transform[q1] c z').
  - exact (proper_morphism (transform[q1] c) _ _ Hzz').
  - symmetry; exact (med_spec q1 Hq c z').
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  symmetry.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.

Definition presheaf_char_pullback :
  @IsPullback ([C^op, Sets]) E
    (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
    (Sieve_Presheaf C) (char_nat theta) (sieve_truth C) U theta
    (@one _ (Functor_Category_Terminal Sets_Terminal) U).
Proof.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id C c)) I). }
    unshelve refine {| unique_obj := char_med q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj c).
      transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

End Pullback.

(* ---------------- (F) the classifier ---------------- *)

Definition Fun_Classifier {C : Category} (UT : Untruncate) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Build_SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal)
    (Sieve_Presheaf C)
    (sieve_truth C)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => presheaf_char_pullback UT theta M)
    (fun U E theta M h HP => presheaf_char_unique theta h HP).

Definition Fun_Classifier_IEM {C : Category} (Em : IEM) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  Fun_Classifier (untruncate_of_IEM Em).

Definition Fun_Classifier_cov {D : Category} (UT : Untruncate) :
  @SubobjectClassifier ([D, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Fun_Classifier (D^op) UT.

Example fun_classifier_omega {C : Category} (UT : Untruncate) :
  @Ω ([C^op, Sets]) _ (Fun_Classifier UT) = Sieve_Presheaf C := eq_refl.
Example fun_classifier_truth {C : Category} (UT : Untruncate) :
  @truth ([C^op, Sets]) _ (Fun_Classifier UT) = sieve_truth C := eq_refl.
Example fun_classifier_char {C : Category} (UT : Untruncate)
  {U E : C^op ⟶ Sets} (theta : U ⟹ E) (M : @Monic ([C^op, Sets]) U E theta) :
  @char ([C^op, Sets]) _ (Fun_Classifier UT) U E theta M = char_nat theta
  := eq_refl.

(* ---------------- (G) the arrow shape ---------------- *)

Example op_op_two : (_2^op)^op = _2 := eq_refl.
Check (Sieve_Presheaf (_2^op) : _2 ⟶ Sets).

Definition twoX_pred (P Q : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoX) → Prop :=
  fun d => match d with TwoX => fun _ => P | TwoY => fun _ => Q end.

Program Definition twoX_sieve (P Q : Prop) (H : P -> Q) :
  @Sieve (_2^op) TwoX := {| sieve_mem := twoX_pred P Q |}.
Next Obligation. intros P Q H d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros P Q H d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoX_total : @Sieve (_2^op) TwoX :=
  twoX_sieve True True (fun x => x).
Definition twoX_mid : @Sieve (_2^op) TwoX :=
  twoX_sieve False True (fun x => match x return True with end).
Definition twoX_empty : @Sieve (_2^op) TwoX :=
  twoX_sieve False False (fun x => x).

Definition twoY_pred (R : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoY) → Prop :=
  fun d => match d with TwoY => fun _ => R | TwoX => fun _ => True end.

Program Definition twoY_sieve (R : Prop) : @Sieve (_2^op) TwoY :=
  {| sieve_mem := twoY_pred R |}.
Next Obligation. intros R d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros R d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoY_total : @Sieve (_2^op) TwoY := twoY_sieve True.
Definition twoY_empty : @Sieve (_2^op) TwoY := twoY_sieve False.

Theorem twoX_total_neq_mid : twoX_total ≈ twoX_mid -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoX_mid_neq_empty : twoX_mid ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoXY) I). Qed.
Theorem twoX_total_neq_empty : twoX_total ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoY_total_neq_empty : twoY_total ≈ twoY_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoIdY) I). Qed.

Theorem twoX_sieve_normal (S : @Sieve (_2^op) TwoX) :
  S ≈ twoX_sieve (sieve_mem S TwoIdX) (sieve_mem S TwoXY)
        (fun p => sieve_closed S TwoIdX TwoXY p).
Proof.
  intros d f; destruct d;
    [ pose proof (TwoHom_inv TwoX TwoX f) as Hf
    | pose proof (TwoHom_inv TwoX TwoY f) as Hf ];
    simpl in Hf; subst; simpl; split; auto.
Qed.

Theorem twoY_sieve_normal (S : @Sieve (_2^op) TwoY) :
  S ≈ twoY_sieve (sieve_mem S TwoIdY).
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f)
    | pose proof (TwoHom_inv TwoY TwoY f) as Hf ];
    simpl in *; subst; simpl; split; auto.
Qed.

Definition jmap :
  @SieveObj (_2^op) TwoX ~{Sets}~> @SieveObj (_2^op) TwoY :=
  @fmap (_2^op^op) Sets (Sieve_Presheaf (_2^op)) TwoX TwoY TwoXY.

Theorem j_total : jmap twoX_total ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_mid : jmap twoX_mid ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_empty : jmap twoX_empty ≈ twoY_empty.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.

Theorem j_identifies : jmap twoX_total ≈ jmap twoX_mid.
Proof. transitivity twoY_total; [ apply j_total | symmetry; apply j_mid ]. Qed.

Theorem j_separates : jmap twoX_total ≈ jmap twoX_empty -> False.
Proof.
  intro H. apply twoY_total_neq_empty.
  transitivity (jmap twoX_total); [ symmetry; apply j_total | ].
  transitivity (jmap twoX_empty); [ exact H | apply j_empty ].
Qed.

Theorem twoX_sieve_ext (P Q : Prop) (H : P -> Q) (P' Q' : Prop) (H' : P' -> Q')
        (HP : P <-> P') (HQ : Q <-> Q') :
  twoX_sieve P Q H ≈ twoX_sieve P' Q' H'.
Proof. intros d f; destruct d; simpl; assumption. Qed.

Theorem twoY_sieve_ext (R R' : Prop) (HR : R <-> R') :
  twoY_sieve R ≈ twoY_sieve R'.
Proof. intros d f; destruct d; simpl; [ split; auto | assumption ]. Qed.

Theorem twoX_three_sieves (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  (S ≈ twoX_total) + (S ≈ twoX_mid) + (S ≈ twoX_empty).
Proof.
  pose proof (twoX_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdX)) as [Hp | Hp].
  - left; left. rewrite HN. apply twoX_sieve_ext.
    + split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
    + split; [ exact (fun _ => I)
             | exact (fun _ => sieve_closed S TwoIdX TwoXY Hp) ].
  - destruct (Em (sieve_mem S TwoXY)) as [Hq | Hq].
    + left; right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact (fun _ => I) | exact (fun _ => Hq) ].
    + right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact Hq | intro C0; destruct C0 ].
Qed.

Theorem twoY_two_sieves (Em : IEM) (S : @Sieve (_2^op) TwoY) :
  (S ≈ twoY_total) + (S ≈ twoY_empty).
Proof.
  pose proof (twoY_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdY)) as [Hp | Hp].
  - left. rewrite HN. apply twoY_sieve_ext.
    split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
  - right. rewrite HN. apply twoY_sieve_ext.
    split; [ exact Hp | intro C0; destruct C0 ].
Qed.

Theorem total_is_twoX_total : @total_sieve (_2^op) TwoX ≈ twoX_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

Theorem total_is_twoY_total : @total_sieve (_2^op) TwoY ≈ twoY_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

(* --- Mac Lane's explicit j : {0,1,2} -> {0,2} --- *)

Definition macj : Fin.t 3 -> Fin.t 2 :=
  fun k => match k with
           | Fin.F1 => Fin.F1
           | Fin.FS k' => match k' with
                          | Fin.F1 => Fin.F1
                          | Fin.FS _ => Fin.FS Fin.F1
                          end
           end.

Example macj_0 : macj Fin.F1 = Fin.F1 := eq_refl.
Example macj_1 : macj (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example macj_2 : macj (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

Definition twoX_code (Em : IEM) (S : @Sieve (_2^op) TwoX) : Fin.t 3 :=
  match Em (sieve_mem S TwoIdX) with
  | inl _ => Fin.F1
  | inr _ => match Em (sieve_mem S TwoXY) with
             | inl _ => Fin.FS Fin.F1
             | inr _ => Fin.FS (Fin.FS Fin.F1)
             end
  end.

Definition twoY_code (Em : IEM) (S : @Sieve (_2^op) TwoY) : Fin.t 2 :=
  match Em (sieve_mem S TwoIdY) with
  | inl _ => Fin.F1
  | inr _ => Fin.FS Fin.F1
  end.

Lemma twoX_code_total (Em : IEM) : twoX_code Em twoX_total = Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_total TwoIdX)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoX_code_mid (Em : IEM) : twoX_code Em twoX_mid = Fin.FS Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_mid TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_mid TwoXY)) as [|N2];
    [ reflexivity | destruct (N2 I) ].
Qed.

Lemma twoX_code_empty (Em : IEM) :
  twoX_code Em twoX_empty = Fin.FS (Fin.FS Fin.F1).
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_empty TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_empty TwoXY)) as [Hq|];
    [ destruct Hq | reflexivity ].
Qed.

Lemma twoY_code_total (Em : IEM) : twoY_code Em twoY_total = Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_total TwoIdY)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoY_code_empty (Em : IEM) : twoY_code Em twoY_empty = Fin.FS Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_empty TwoIdY)) as [Hp|];
    [ destruct Hp | reflexivity ].
Qed.

Example two_op_XY_IdY : (TwoXY ∘[_2^op] TwoIdY) = TwoXY := eq_refl.

Lemma jmap_mem_IdY (S : @Sieve (_2^op) TwoX) :
  sieve_mem (jmap S) TwoIdY <-> sieve_mem S TwoXY.
Proof. unfold jmap; simpl; split; intro H; exact H. Qed.

(* Mac Lane's j AS AN OBJECT of [_2, FinSet]: the three-element object
   {0,1,2} at TwoX, the two-element object {0,2} at TwoY, and [macj]
   between them.  [Instance/FinSet] costs this file ZERO extra modules
   (measured), so the explicit construction lives here beside the sieve
   one it is being identified with. *)

Definition macO (o : TwoObj) : nat := match o with TwoX => 3 | TwoY => 2 end.

Definition macF (x y : TwoObj) (f : TwoHom x y) :
  Fin.t (macO x) -> Fin.t (macO y) :=
  match f with
  | TwoIdX => fun k => k
  | TwoIdY => fun k => k
  | TwoXY  => macj
  end.

Lemma macF_respects (a b : TwoObj) :
  Proper (@equiv _ (@homset _2 a b)
            ==> @equiv _ (@homset FinSet (macO a) (macO b))) (macF a b).
Proof.
  intros f g Hfg; simpl in Hfg.
  assert (Heq : f = g) by exact Hfg.
  rewrite Heq; intro k; reflexivity.
Qed.

Lemma macF_id (a : TwoObj) : macF a a (@id _2 a) ≈ @id FinSet (macO a).
Proof. destruct a; intro k; reflexivity. Qed.

Lemma macF_comp (a b c : TwoObj) (f : b ~{_2}~> c) (g : a ~{_2}~> b) :
  macF a c (f ∘[_2] g) ≈ macF b c f ∘[FinSet] macF a b g.
Proof.
  destruct a, b, c;
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    pose proof (TwoHom_inv _ _ f) as Hf;
    pose proof (TwoHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; intro k; reflexivity.
Qed.

Definition MacOmega : _2 ⟶ FinSet :=
  @Build_Functor _2 FinSet macO macF macF_respects macF_id macF_comp.

Example macOmega_X : fobj[MacOmega] TwoX = 3%nat := eq_refl.
Example macOmega_Y : fobj[MacOmega] TwoY = 2%nat := eq_refl.
Example macOmega_fmap : fmap[MacOmega] TwoXY = macj := eq_refl.

(* THE IDENTIFICATION.  Under informative excluded middle the sieves on
   TwoX are coded by [Fin.t 3] and those on TwoY by [Fin.t 2], and the
   sieve presheaf's action along the one non-identity arrow IS Mac
   Lane's j — that is, [MacOmega]'s own arrow action, by the [eq_refl]
   above.  So his explicit three-element construction is the general
   sieve answer read through the dictionary, proved rather than
   asserted. *)
Theorem mac_dictionary (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  twoY_code Em (jmap S) = macj (twoX_code Em S).
Proof.
  unfold twoY_code, twoX_code.
  destruct (Em (sieve_mem (jmap S) TwoIdY)) as [Hj | Nj];
  destruct (Em (sieve_mem S TwoIdX)) as [Hx | Nx].
  - reflexivity.
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny]; [ reflexivity | ].
    destruct (Ny (proj1 (jmap_mem_IdY S) Hj)).
  - destruct (Nj (proj2 (jmap_mem_IdY S)
                   (sieve_closed S TwoIdX TwoXY Hx))).
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny].
    + destruct (Nj (proj2 (jmap_mem_IdY S) Hy)).
    + reflexivity.
Qed.

(* ---------------- (H) the two round trips ---------------- *)

Definition fun_truth_subobject {C : Category} (UT : Untruncate) :
  @SubObj ([C^op, Sets])
    (@Ω ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT)) :=
  @truth_subobject ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT).

Definition fun_char_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets}
  (h : x ~{[C^op, Sets]}~> @Ω ([C^op, Sets])
                              (Functor_Category_Terminal Sets_Terminal)
                              (Fun_Classifier UT)) :
  @char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT) _ _
    (sub_mono (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    (sub_is_monic (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    ≈ h
  := @classifier_char_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x h.

Definition fun_pullback_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets} (s : @SubObj ([C^op, Sets]) x) :
  @sub_reindex ([C^op, Sets]) (Fun_HasPullbacks Sets_HasPullbacks) _ x
    (@char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT) _ _ (sub_mono s) (sub_is_monic s))
    (fun_truth_subobject UT)
    ≈ s
  := @classifier_pullback_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x s.

(* ------------------------------------------------------------------ *)
(** ** (I) The classification theorem, at objects <= homs *)

Section Small.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}).
Context (UTs : Untruncate@{o}).
Definition PShSmall : Category@{OO HH HH} := [Cs^op, Sets@{o so}].
Definition PShSmall_Terminal : @Terminal PShSmall :=
  @Functor_Category_Terminal (Cs^op) Sets@{o so} Sets_Terminal.

Definition small_pb (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E)
  (M : @Monic PShSmall U E theta) :
  @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
    (Sieve_Presheaf Cs) (char_nat theta) (sieve_truth Cs) U theta
    (@one PShSmall PShSmall_Terminal U).
Proof using Cs UTs.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : Cs) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id Cs c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id Cs c)) I). }
    unshelve refine {| unique_obj := char_med UTs theta M q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec UTs theta M q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj theta M c).
      transitivity (transform[q1] c z);
        [ exact (med_spec UTs theta M q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

Section SmallUnique.
Context (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E).
Context (h : E ~{PShSmall}~> Sieve_Presheaf Cs).
Context (HP : @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
                (Sieve_Presheaf Cs) h (sieve_truth Cs) U theta
                (@one PShSmall PShSmall_Terminal U)).

Lemma small_char_sub_h (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof using All.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id Cs d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id Cs d))).
    exact (proj2 (Hc d (@id Cs d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id Cs d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma small_h_sub_char (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof using All.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id Cs d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id Cs d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone Cs E d ed S).
  assert (Hcone : ∀ (k : Cs) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[PShSmall] q1
                  ≈ sieve_truth Cs ∘[PShSmall]
                      @one PShSmall PShSmall_Terminal (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one PShSmall PShSmall_Terminal _) Hsq) as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id Cs d) HidS)).
  pose proof (Hu1 d (existT _ (@id Cs d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem small_unique : h ≈ char_nat theta.
Proof using All.
  intros c e d f; split; [ apply small_h_sub_char | apply small_char_sub_h ].
Qed.

End SmallUnique.

Definition Fun_Classifier_small :
  @SubobjectClassifier PShSmall PShSmall_Terminal :=
  @Build_SubobjectClassifier PShSmall PShSmall_Terminal
    (Sieve_Presheaf Cs)
    (sieve_truth Cs)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => small_pb U E theta M)
    (fun U E theta M h HP => small_unique U E theta h HP).

Example fun_classifier_small_omega :
  @Ω PShSmall PShSmall_Terminal Fun_Classifier_small = Sieve_Presheaf Cs
  := eq_refl.
Example fun_classifier_small_truth :
  @truth PShSmall PShSmall_Terminal Fun_Classifier_small = sieve_truth Cs
  := eq_refl.

(* WORK ITEM 2, in the form the issue calls "the content of the
   classification": the subobjects of a presheaf x correspond to the
   maps x ⟹ Ω, as an isomorphism of setoids in [Sets].  This is
   Structure/SubobjectClassifier.v's own theorem applied, over
   Instance/Fun/Pullback.v's [Fun_HasPullbacks Sets_HasPullbacks], which
   is a plain [Definition] and so is named here rather than resolved. *)
Definition fun_classifier_classifies (x : obj[PShSmall]) :
  @Isomorphism Sets
    {| carrier := @SubObj PShSmall x |}
    {| carrier := x ~{PShSmall}~> @Ω PShSmall PShSmall_Terminal
                                    Fun_Classifier_small |} :=
  @classifier_classifies PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small x.

(* Awodey's naturality clause, which is strictly stronger than the
   object-wise bijection: the subobject presheaf of the presheaf category
   IS the presheaf represented by Ω.  Structure/SubobjectClassifier/
   Natural.v's theorem applied; it too carries the [u <= u0] bound, so it
   is available here and refused at [Fun_Classifier], the same pair as
   [classifier_classifies]. *)
Definition fun_sub_classifier_natural :
  @Isomorphism ([(PShSmall^op), Sets])
    (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks))
    (@Curried_CoHom PShSmall
       (@Ω PShSmall PShSmall_Terminal Fun_Classifier_small)) :=
  @Sub_classifier_natural PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

Definition fun_Sub_Representable :
  Representable (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks)) :=
  @Sub_Representable PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

End Small.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Adjunction.GAFT.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* The Stone–Čech compactification over the tree's [Top]

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5):
   §V.6, book p. 125 (PDF p. 134), the compactification of a discrete set by
   the general adjoint functor theorem
   (maclane:V.6:construction-stone-cech-discrete); §V.8, Construction 1,
   book pp. 131–132 (PDF pp. 140–141), the compactification of an arbitrary
   space by the special adjoint functor theorem with the unit interval as
   cogenerator (maclane:V.8:construction1); and §V.8 Exercise 4, the
   injectivity of the unit on completely regular spaces (maclane:V.8:ex4).
   Riehl, "Category Theory in Context", 2nd ed., Example 4.7.12, printed
   p. 178 (PDF p. 198; riehl:4.7:example12).
   nLab:  https://ncatlab.org/nlab/show/Stone-Cech+compactification
   nLab:  https://ncatlab.org/nlab/show/Tychonoff+theorem
   Paper: M. H. Stone, "Applications of the theory of Boolean rings to
          general topology", Trans. Amer. Math. Soc. 41 (1937), 375–481
   Paper: E. Čech, "On bicompact spaces", Ann. of Math. 38 (1937), 823–844

   BACKGROUND.  Stone and Čech found, independently and in the same year,
   that a space X sits inside a compact Hausdorff space βX through which
   every continuous map from X to a compact Hausdorff space extends
   uniquely.  The nLab page reads this categorically: the inclusion of
   compact Hausdorff spaces into all spaces has a left adjoint β, so the
   compact Hausdorff spaces form a reflective subcategory, and the unit
   X → βX is an embedding precisely when X is a Tychonoff space.  It is
   one of the universal mapping problems Samuel collected in 1948
   (Theory/Universal/Arrow.v's header).  Mac Lane uses it twice as the
   showcase of the adjoint functor theorems: through GAFT at the
   underlying-set functor, where the compactification of a discrete set
   has a solution set bounded by the double power set, and through SAFT
   at the inclusion, where Urysohn's lemma makes [0,1] a cogenerator.
   Riehl names what the SAFT construction produces, the closure of the
   image of X in a power of the interval.  The classical direct
   construction is the space of ultrafilters on X; Tychonoff's theorem
   for Hausdorff spaces needs the ultrafilter theorem, "and possibly
   excluded middle", while for locales "no choice whatsoever is needed"
   (nLab, Tychonoff theorem), which is why the constructive home of these
   constructions is locale theory (Johnstone, "Stone Spaces", CUP 1982).

   THE ISSUE'S TWO HEADLINE NAMES ARE NOT CONSTANTS HERE, FOR TWO
   DIFFERENT REASONS.  Stated as the issue pins them, [StoneCech_discrete]
   is a left adjoint to the underlying-set functor [CompHaus_Forget]
   obtained from GAFT, and [StoneCech] a left adjoint to the inclusion
   [CompHaus_Incl] obtained from SAFT with the interval as cogenerator.
     - The §V.6 statement, the adjunction at [CompHaus_Forget], is refuted
       under informative excluded middle at the universe instance that
       [GAFT_CompHaus_only_complete] produces, the one with the objects of
       [CompHaus] at its hom universe ([StoneCech_adjunction_refuted_IEM]).
       [IEM] (Instance/Sets/Classifier/OneLevel.v) is a hypothesis there,
       never an axiom, and it holds classically, so at that instance the
       statement is false in every classical model: for this name the
       obstacle is not a missing proof.  It is refuted as well with the
       objects above the hom universe
       ([StoneCech_adjunction_refuted_IEM_above]); below it the statement
       is not formable.  Both refutations reach the instances
       Refutations.v's COVERAGE records: the [Top] slot at the hom
       universe, the proof that a space is compact Hausdorff at the
       object universe, and the separating opens of its Hausdorff proof
       at the points' universe.  #455's review measured what a draft of
       this bullet denied, that the refutation goes through at an
       instance whose object universe lies above the hom universe: an
       arrow index of [Top], which [IEM] supplies, indexes the arrows of
       [CompHaus] at every object universe at or above the hom universe
       (Refutations.v's [CompHaus_ArrowIndex_of_Top]).
     - The §V.8 statement, the adjunction at [CompHaus_Incl], is NOT
       refuted, and classically it holds.  Refutations.v's argument needs,
       in the left adjoint's domain, an object as large as the arrow
       collection of [CompHaus]; the domain [Top@{h o}] has its points at
       [o], strictly below [h], so the argument does not apply, and the
       book's βX of a space whose points lie in a universe has at most
       2^2^|X| points and lies in that universe (a meta-argument about the
       set-theoretic model with choice, not a theorem here).  What is
       vacuous in this encoding is the adjoint-functor-theorem ROUTE to
       it: SAFT at the inclusion consumes a completeness hypothesis that
       is refuted under [IEM] at every shape universe SAFT accepts there,
       at the instances Refutations.v's COVERAGE records
       ([CompHaus_not_complete_IEM_below], paired with SAFT on one
       hypothesis in [SAFT_Incl_IEM_vacuous_below]; at the shapes at or
       above the objects also [CompHaus_not_complete_IEM] and
       [SAFT_Incl_IEM_vacuous]).  Refutations.v's [SAFT_CompHaus_Incl] is
       a conditional at more instances than those, and there its premise
       stays classically false, a meta-argument (Refutations.v's (3)).
       For this name the obstacle IS a missing proof: a direct
       construction, such as the space of ultrafilters, or an encoding
       under which the route is not vacuous.
   The arguments are in the satellite Instance/Top/StoneCech/Refutations.v.
   The repair is filed as two follow-up issues: #1328 re-encodes [Top] and
   [CompHaus] with Prop-valued opens, putting continuous maps at the
   universe of the points, and #1329 is Stone–Čech proper, over #1328's
   encoding for the adjoint-functor-theorem routes or by a direct
   construction in this one.

   WHY: THE UNIVERSE OF TOP'S HOMS.  Instance/Top.v's header (its point 2)
   places the hom-sets of [Top@{h o}] strictly above the points, o < h,
   because continuity quantifies over the opens of the codomain.  An object
   is a [TopSpace@{o}], of type [Type@{o+1}], so the objects AND the arrows
   of [Top], and of its full subcategory [CompHaus], all fit in [Type@{h}]:
   the category is small relative to its own hom universe.  The adjoint
   functor theorems as the tree states them consume completeness at shapes
   no smaller than the homs: Adjunction/GAFT.v's [GAFT] takes
   [Complete@{h h h cobj}], and Adjunction/SAFT/Characterization.v's
   [SAFT_wellpowered] takes [Complete@{so so h o}] under [h <= so].  At
   those shapes a product indexed by every arrow of [CompHaus] is formable,
   and Freyd's argument (Structure/Complete/Freyd.v) applies: [CompHaus]
   has two parallel arrows from the point to the two-point space that
   evaluation at the point tells apart constructively, so it has no such
   products once its arrows carry an index, and decidable equality of
   objects, which [IEM] supplies, is such an index ([canonical_ArrowIndex]).
   This is the reverse of Structure/Complete.v's size note for [Sets] and
   the algebraic categories, where homs sit at the level of the carriers
   and objects one level up: there the solution sets are the wall; here
   they are free ([taut_sols] below) and completeness is.
   A Prop-valued topology moves the homs down.  Over
   Test/ProbeStoneCech455.v's [p455_TopP], a minimal record of Prop-valued
   opens, that file's [p455_ContHom X Y : Type@{o}], a setoid map with
   Prop-valued preservation of Prop-valued opens, is accepted under a
   closed binder [@{o}], so with an empty constraint block, while
   [ContinuousMorphism X Y] ascribed at [Type@{o}] for [X Y : TopSpace@{o}]
   is refused: "universe inconsistency: Cannot enforce <1> <= o because o <
   <1>" (the generated universe written <1>).  That probe pins both (its
   N6).  With homs at the points' universe the objects sit one level above
   them, as in [Sets].  The expectation, which nothing in this file tests,
   is that Freyd's argument then no longer reaches the universes the
   theorems use and that completeness becomes the classical question
   (Tychonoff) it is in the book.  That re-encoding is #1328, and
   Stone–Čech over it is #1329; neither is attempted here.

   WHAT IS CONSUMED AND BUILT, in this file.
   (1) Discrete spaces.  [Discrete_Hausdorff]: every discrete space
       (Instance/Top.v's [Discrete_Top]) is Hausdorff, at every universe,
       separating two points by the opens [z ≈ x] and [z ≈ y].  It is used
       here in place of Instance/Top.v's [Point_Hausdorff], which is
       monomorphised at a [Set] carrier (About: [IsHausdorff@{u Set Set
       Set} Point_Top@{Set}]; that file's comment carries the correction).
       [FinEnum A] is a list meeting every [≈]-class of [A], and
       [Discrete_Compact_of_FinEnum] with [FinEnum_of_Discrete_Compact]
       prove THE DISCRETE SPACE ON [A] IS COMPACT IF AND ONLY IF [A] IS
       FINITELY ENUMERABLE, compactness in [IsCompact]'s strong sense (the
       finite subcover handed over as a list, with a covering index for
       each point).  [Discrete_nat_not_compact] shows the condition is a
       real restriction.  [Bool_CH], [Point_CH] and [Discrete_CH X FX] are
       the objects of [CompHaus] built from these.
   (2) The finite case of §V.6.  [StoneCech_finite X FX] is a
       [UniversalArrow] from [Setoid_Lift X] to [CompHaus_Forget] for every
       finitely enumerable setoid [X]: βX is [X] with the discrete topology,
       the unit is the identity, and a map extends as itself, continuous by
       Instance/Top.v's [out_of_discrete_continuous].  The arrow starts at
       a LIFTED setoid because [CompHaus_Forget] lands in the [Sets] one
       universe up, [Sets@{h s}] (Instance/Top/Forgetful.v's header), so the
       universal arrow is from [Setoid_Lift@{o h} X] for [X] at the points'
       universe [o].
   (3) GAFT at [CompHaus_Forget], reduced to completeness alone.
       [CompHaus_Forget_PreservesImageLimit]: the forgetful functor
       preserves every limit that exists, because it is represented by the
       one-point space; a point of the limit is read off the cone from the
       point that an element of a competing cone determines ([sc_pt_cone]),
       and uniqueness is the limit's.  No decidability and no hypothesis is
       used.  [taut_sols]: the tautological solution set, every object with
       every arrow, fits at the hom universe, because the whole object type
       of [CompHaus] does.  So [GAFT_CompHaus_only_complete] is GAFT with
       one hypothesis left, [Complete@{h h h h} CompHaus], and Mac Lane's
       double-power-set bound is not needed.  That hypothesis is refuted
       under [IEM] in Refutations.v, which pairs the two on a single [comp]
       ([GAFT_CompHaus_IEM_vacuous]): GAFT's own instance is the refuted
       one.  With the objects above the homs [taut_sols] no longer fits
       GAFT, and Refutations.v's [GAFT_CompHaus_IEM_vacuous_above] pairs
       GAFT, with any family of solution sets, against the refutation of
       its completeness hypothesis at that instance.
   (4) Exercise 4 at the level of universal arrows, assuming of the
       compactification nothing beyond the universal arrow itself.  Over
       the underlying-set functor: [unit_injective_of_separated] (points
       separated by maps into compact Hausdorff spaces make the unit
       injective), its converse [separated_of_unit_injective], so the two
       are equivalent, and [unit_injective_of_dec] (decidable equality
       suffices, the separating map being the characteristic map [sc_chi]
       into [Bool_CH]).  At a space, over the inclusion:
       [StoneCech_unit_injective_completely_regular], the issue's pinned
       name, stated PARAMETRICALLY: for any compact Hausdorff [K] whose maps
       separate the points of [X] ([KSeparated K X]), the unit of any
       universal arrow at [X] is injective.  Its converse comes in two
       strengths.  [KSeparated_of_unit_injective_local] asks only that [K]
       separate the points of the universal object, and that premise is
       met: [KSeparated_of_unit_injective_local_at_CompHaus] applies it at
       [CompHaus_Incl_universal K].  [KSeparated_of_unit_injective] asks
       [K] to separate the points of EVERY compact Hausdorff space.  No
       [K] in the tree is shown to meet that premise, and any [K] that
       meets it with ¬¬-stable equality of points yields double-negation
       elimination (Refutations.v's
       [CompHaus_point_separator_stable_DNE]).  At [K] = [0,1],
       [KSeparated] is the point-separating half of complete regularity
       (classically, being functionally Hausdorff), which is what the
       book's hypothesis is used for; the interval itself is not an object
       of [CompHaus] in the tree (NOT DELIVERED).  The only universal arrow
       at [CompHaus_Incl] in the tree is [CompHaus_Incl_universal], at a
       space that is already compact Hausdorff, so the one in-tree
       application of the pinned name is at an identity unit, not at the
       interval.  The issue's note that the restriction to completely
       regular spaces is unnecessary at the level of universal arrows is
       read here, as an interpretation that no constant of this file
       shows, as: classically the universal arrow exists at every space
       whatever its separation, and separation is exactly what makes its
       unit injective (the theorem and its local converse above).
   Instance/Top/StoneCech/Refutations.v then states the metatheorems:
   completeness of [CompHaus] and of [Top] at the theorems' universes
   refuted under an arrow index and under [IEM], at every shape universe at
   or above the hom universe with the limits its COVERAGE records; the
   adjunction at [CompHaus_Forget] refuted under [IEM] at every object
   universe at or above the hom universe, the only ones at which it is
   formable, at the instances its COVERAGE records; the vacuity pairs for
   GAFT and SAFT; SAFT at the inclusion
   reduced to three hypotheses; an injection, from completeness alone, of
   [obj[CompHaus] → bool] into the points of one space; and the cost
   (double-negation elimination) of any cogenerating family of [CompHaus]
   with ¬¬-stable members, and of any single ¬¬-stable [K] that separates
   the points of every compact Hausdorff space.

   STRENGTHS, strict first.
     - [eq_refl]: [StoneCech_finite_obj] (the universal object IS
       [Discrete_CH X FX]), [StoneCech_finite_unit] (the unit IS
       [sc_fin_unit X FX], by definition the identity of [Sets] at
       [Setoid_Lift X]), and [CompHaus_Incl_universal_obj] (the universal
       object at a compact Hausdorff space is the space itself).  A wrong-value
       control for [StoneCech_finite_obj] has to name a genuinely different
       object.  At [X] := [bool_setoid_object] the equation with [Bool_CH] on
       the right is ACCEPTED, [Bool_CH] being [Discrete_CH] at [bool_FinEnum] up
       to conversion ([Bool_Discrete] is [Discrete_Top bool_setoid_object]), so
       a control written that way would pass vacuously.  The wrong-value control
       is the equation with the one-point space [Point_CH] on the right: it is
       refused at the carrier ("cannot unify" [arrow_obj] and [Point_CH]), and
       its value is wrong as a theorem (Test/ProbeStoneCech455.v's N1, whose
       [p455_n1_wrong_value] derives [False] from it).  The same equation
       against [Discrete_CH] at a second enumeration of bool, listing [false]
       first, is refused as well ("cannot unify" [arrow_obj] and [Discrete_CH]
       at that enumeration), but it pins only that the universal object carries
       the enumeration it was built from: the two objects have one space and
       differ in their [Qed] compactness proofs, so that their values differ is
       meta-level (the probe's N2).
     - [UniversalArrow] records: [StoneCech_finite] and
       [CompHaus_Incl_universal], each built by Theory/Universal/Arrow.v's
       [universal_arrow_from_UMP] from unique existence whose uniqueness is
       [≈] of continuous maps, pointwise.
     - [∃!] up to [≈]: [CompHaus_Forget_PreservesImageLimit].
     - [≈] on points, never [=], in all of Exercise 4; data both ways in
       the compactness characterization ([FinEnum] and [IsCompact] are
       [Type]-valued).
     - [False]: [nat_not_FinEnum], [Discrete_nat_not_compact].

   UNIVERSES, measured with [Set Printing Universes. About …], stdlib
   bounds left out.  Every binder is explicit: [o] the points, [h] the hom
   universe of [Top] (and of [CompHaus] where the two coincide), [s] the
   objects of the [Sets] that [CompHaus_Forget] lands in, [j] a shape.

     Discrete_Hausdorff@{h o} : ∀ A : SetoidObject@{o o},
       IsHausdorff@{h o o o} (Discrete_Top@{o o} A)      (* o < h *)
     FinEnum@{o} : SetoidObject@{o o} → Type@{o}
     StoneCech_finite@{o h …} : ∀ X : SetoidObject@{o o}, FinEnum@{o} X →
       UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget
       (* o < h, h < the Sets level *)
     GAFT_CompHaus_only_complete@{h s …} : Complete@{h h h h} →
       ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget  (* h < s *)
     StoneCech_unit_injective_completely_regular@{h o …} :
       ∀ K X, KSeparated K X → ∀ UA : UniversalArrow X CompHaus_Incl, …
       (* o < h, X : Top@{h o} *)

   All four universes of GAFT's completeness hypothesis are [h]: the
   objects of [CompHaus] are placed at its hom universe, which is exactly
   what makes the tautological solution set legal and what Freyd's
   argument exploits.  A word-bounded [Set] occurs in none of the 41
   readbacks of this file.  One binder was measured to matter: without
   one, [bool_FinEnum] elaborates at [FinEnum@{Set} bool_setoid_object@{Set
   Set}] (About, on the same lemma stated without a binder;
   Test/ProbeStoneCech455.v pins its consequences), which would force
   [Bool_CH], built from it, and so the refutations that use [Bool_CH], to
   a [Set] carrier.  Every constant takes its hypotheses as top-level
   binders; no [Section] is used.

   NON-VACUITY.  [FinEnum] is inhabited ([bool_FinEnum]; the one-point
   space through Instance/Top.v's [Point_Compact]) and not universal
   ([Discrete_nat_not_compact]).  [StoneCech_finite_bool_injective] applies
   [unit_injective_of_dec] to [StoneCech_finite] at the two-point set with
   the decider [sc_bool_dec], and [StoneCech_unit_injective_at_CompHaus]
   applies [StoneCech_unit_injective_completely_regular] at every compact
   Hausdorff [K] to [CompHaus_Incl_universal K] with [KSeparated_self K]:
   the premises of both forms of Exercise 4 are jointly met, at compatible
   universes, by universal arrows built here.  Their conclusions carry no
   new content (at both, the unit is the identity).
   [KSeparated_of_unit_injective_local_at_CompHaus] closes the round trip
   at [CompHaus_Incl_universal K]: all three premises of the local
   converse are met there, the injectivity of the unit by
   [StoneCech_unit_injective_at_CompHaus].  The strong converse
   [KSeparated_of_unit_injective] has no witness: no [K] in the tree is
   shown to meet its premise, and a [K] with ¬¬-stable equality of points
   meets it only at the price of double-negation elimination (see (4)).
   The hypothesis of [GAFT_CompHaus_only_complete] IS refuted under
   [IEM]: that constant is a conditional with a classically false premise,
   kept as the measured reduction, not as a result.

   STALE PREMISES OF THE ISSUE, RE-MEASURED.
     - "No topological categories exist — no [Top], no [CompHaus]": both
       exist, Instance/Top.v (#259) and Instance/Top/CompHaus.v (#413).
     - "SAFT itself is never applied to any concrete category"
       (docs/INHABITATION.md): its [SAFT_wellpowered] row records
       applications at the powerset lattice [Subsets Y] and at
       [Indiscrete], conditionally on [Untruncate] at [Sets], and at
       [(RMod R)^op] (#454).
     - "#413 supplies [CompHaus] and the creation of limits by its
       underlying-set functor, which creates limits, so [CompHaus] is
       complete": #413 formed [CreatesLimit K CompHaus_Forget] but did not
       prove it (Instance/Top/CompHaus.v, NOT DELIVERED (c)), and
       completeness at the universes the theorems use here is refuted
       under [IEM], with the objects of [CompHaus] at its hom universe and
       above it (Refutations.v, COVERAGE).
     - The issue's search for Stone, Čech, Tychonoff, Urysohn and complete
       regularity, narrowed to the terms themselves, finds nothing but
       comment prose outside this development.  Method: grep -E, case-sensitive,
       over the files of _CoqProject other than this development's own
       (these two and Test/ProbeStoneCech455.v), with the pattern
   "Čech|Stone-Cech|[Cc]ompactif|Tychonoff|Urysohn|[Cc]ompletely regular"
       (the issue's case-insensitive pattern also matches words such as
       "ConstOne" and "milestone").  It finds four files:
       Theory/Universal/Arrow.v, Structure/Limit.v (Čech cohomology),
       Instance/Roster.v and Instance/Top/CompHaus.v, every hit inside a
       comment.

   NOT DELIVERED.
     - A constant named [StoneCech_discrete].  Its statement, the §V.6
       adjunction at [CompHaus_Forget], is refuted under [IEM] at the
       instance GAFT produces and at every object universe above it, at
       the instances Refutations.v's COVERAGE records (above).
     - A constant named [StoneCech].  Its statement, the §V.8 adjunction
       at [CompHaus_Incl], is not refuted and holds classically, but
       neither a direct construction nor a non-vacuous route to it is
       built here.
     - #1329 carries both constructions, over #1328's encoding or, where
       the statement is not refuted, by a direct construction in this
       one.
     - Stone–Čech at an infinite set or at a non-discrete space, the
       ultrafilter construction of βX, Tychonoff at any arity and Urysohn's
       lemma; Mac Lane's double-power-set solution set (not needed at these
       universes, see (3)); Riehl's closure-of-the-image description.
     - The interval as an object of [CompHaus], hence the SAFT route with
       the interval cogenerator (the issue's Reviewer line) even as a
       conditional, and the interval form of Exercise 4.
       Instance/Top/Interval.v's [I_Top] is shown neither compact nor
       Hausdorff there, and every constant naming it inherits the stdlib
       axioms [ClassicalDedekindReals.sig_forall_dec] and
       [functional_extensionality_dep] (Print Assumptions [I_Top]; that file
       is among docs/AXIOMS.md's reals-importing files), so none is here.
       The route would be vacuous classically in any case: its completeness
       hypothesis is the refuted one, and Refutations.v's
       [CompHaus_cogenerator_stable_DNE] shows that any cogenerating family
       of [CompHaus] with ¬¬-stable members, the interval's among them,
       costs double-negation elimination.
     - The discrete case as a composite with a packaged [Discrete ⊣
       Forget] on [Top]: Instance/Top/Forgetful.v shows that adjunction
       cannot be packaged as one [Adjunction] record, its two functors
       living on different [Sets].
     - Nothing is registered as an [Instance].

   COUNTS.  41 constants here (22 [Definition], 8 [Lemma], 8 [Theorem],
   3 [Example]), all closed under the global context by their fully
   qualified names, [Print Module] listing exactly these 41, so no
   auxiliary constant is generated.  Seven proofs end [Defined] (by token);
   four are load-bearing, each measured by flipping it alone to [Qed] and
   recompiling this file and its satellite: [sc_pt_cone] (its vertex must
   unfold to the point for [sc_pres_pt]), [sc_pres_map] (unfolded by
   [CompHaus_Forget_PreservesImageLimit]), [sc_chi] (computed by the
   [discriminate] in [unit_injective_of_dec]) and [CompHaus_Incl_universal]
   (its readback [CompHaus_Incl_universal_obj]); the other three,
   [sc_fin_ump], [taut_sols] and [sc_bool_dec], flip with everything green
   and are kept [Defined] as data.  Closure 67 modules excluding self:
   Instance/Top/CompHaus.v costs 11 at the margin, Adjunction/GAFT.v 8,
   each of the other thirteen [Category.*] [Require]s 0 (each dropped
   alone). *)

(** * Discrete spaces: separation, and compactness as finite enumerability *)

Lemma Discrete_Hausdorff@{h o +| o < h +} (A : SetoidObject@{o o}) :
  IsHausdorff@{h o o o} (Discrete_Top@{o o} A).
Proof.
  intros x y nxy.
  exists (fun z => z ≈ x). exists (fun z => z ≈ y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. exact (transitivity (symmetry Hx) Hy).
Qed.

(* A finite enumeration of a setoid: a list meeting every class. *)
Definition FinEnum@{o +} (A : SetoidObject@{o o}) : Type@{o} :=
  ∃ l : list A, ∀ x : A, ∃ y : A, (In y l ∧ x ≈ y)%type.

(* Every open cover of a finitely enumerable discrete space has a finite
   subcover: one covering index per listed point. *)
Lemma Discrete_Compact_of_FinEnum@{o +} (A : SetoidObject@{o o})
  (F : FinEnum A) : IsCompact (Discrete_Top@{o o} A).
Proof.
  intros I U HU.
  destruct F as [l Hl].
  exists (map (fun y => `1 (fst (snd HU y) ttt)) l).
  intro x. destruct (Hl x) as [y [Hin Hxy]].
  exists (`1 (fst (snd HU y) ttt)). split.
  - exact (in_map (fun y => `1 (fst (snd HU y) ttt)) l y Hin).
  - exact (fst HU _ y x (symmetry Hxy) (`2 (fst (snd HU y) ttt))).
Qed.

(* Conversely, the cover by the singleton classes has a finite subcover,
   which is a finite enumeration. *)
Lemma FinEnum_of_Discrete_Compact@{o +} (A : SetoidObject@{o o})
  (C : IsCompact (Discrete_Top@{o o} A)) : FinEnum A.
Proof.
  destruct (C A (fun a z => z ≈ a)) as [l Hl].
  - split.
    + intros a u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
    + intro x; split.
      * intros _. exists x. reflexivity.
      * intros _. exact ttt.
  - exists l. exact Hl.
Qed.

(* The finiteness premise is a real restriction: discrete ℕ is not
   compact. *)
Definition sc_nat_setoid@{o +} : SetoidObject@{o o} :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Lemma sc_in_le_fold_max@{} (l : list nat) (y : nat) :
  In y l → le y (fold_right Nat.max O l).
Proof.
  induction l as [|a l IH]; simpl; intro H; [contradiction|].
  destruct H as [<-|H].
  - apply Nat.le_max_l.
  - etransitivity; [exact (IH H)|apply Nat.le_max_r].
Qed.

Lemma nat_not_FinEnum@{o +} :
  FinEnum (sc_nat_setoid : SetoidObject@{o o}) → False.
Proof.
  intros [l Hl].
  destruct (Hl (S (fold_right Nat.max O l))) as [y [Hin Hy]].
  simpl in Hy. subst y.
  exact (Nat.nle_succ_diag_l _ (sc_in_le_fold_max l _ Hin)).
Qed.

Theorem Discrete_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False.
Proof. intro C. exact (nat_not_FinEnum (FinEnum_of_Discrete_Compact _ C)). Qed.

(* The two-point and one-point discrete spaces as objects of [CompHaus],
   at every carrier universe. *)
Lemma bool_FinEnum@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition Bool_CH@{o +} : CompHaus :=
  (Bool_Discrete@{o}; (Discrete_Compact_of_FinEnum _ bool_FinEnum,
                       Discrete_Hausdorff _)).

Definition Point_CH@{o +} : CompHaus :=
  (Point_Top@{o}; (Point_Compact, Discrete_Hausdorff _)).

(** * The finite case: the discrete space is its own compactification *)

Definition Discrete_CH@{o +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  CompHaus :=
  (Discrete_Top@{o o} X;
     (Discrete_Compact_of_FinEnum X FX, Discrete_Hausdorff X)).

Definition sc_fin_unit@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget (Discrete_CH X FX) :=
  @id Sets (Setoid_Lift@{o h} X).

(* A map out of the lifted setoid, read back at the points' universe. *)
Definition sc_unlift@{o h +} (X : SetoidObject@{o o}) {d : CompHaus}
  (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  SetoidMorphism@{o o o} X (top_carrier (`1 d)) :=
  @Build_SetoidMorphism (carrier X) (is_setoid X)
    (carrier (top_carrier (`1 d))) (is_setoid (top_carrier (`1 d)))
    (fun x => f x) (fun a b e => proper_morphism f a b e).

Definition sc_fin_ext@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  {d : CompHaus} (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  Discrete_CH X FX ~{CompHaus}~> d :=
  (Build_ContinuousMorphism (Discrete_Top X) (`1 d) (sc_unlift X f)
     (out_of_discrete_continuous X (`1 d) (sc_unlift X f)); I).

Definition sc_fin_ump@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  (d : CompHaus) (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  ∃! g : Discrete_CH X FX ~{CompHaus}~> d,
    f ≈ fmap[CompHaus_Forget] g ∘ sc_fin_unit X FX.
Proof.
  unshelve refine {| unique_obj := sc_fin_ext X FX f |}.
  - intro x. simpl. apply reflexive_lift.
  - intros v Hv x. simpl. exact (Hv x).
Defined.

Definition StoneCech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  universal_arrow_from_UMP _ _ (Discrete_CH X FX) (sc_fin_unit X FX)
    (sc_fin_ump X FX).

Example StoneCech_finite_obj@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example StoneCech_finite_unit@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(** * The reduction: continuity is free, and so is the solution set *)

(* An element [n] of a cone over [CompHaus_Forget ◯ G] is a cone over [G]
   from the one-point space. *)
Definition sc_pt_cone@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) : Cone G.
Proof.
  refine {| vertex_obj := Point_CH;
            coneFrom := @Build_ACone _ _ Point_CH G
              (fun x => ((top_point (`1 (G x)) (cone_leg N x n); I)
                          : Point_CH ~{CompHaus}~> G x)) _ |}.
  intros x y f t. simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f n).
Defined.

Definition sc_pres_pt@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) :
  carrier (top_carrier (`1 (vertex_obj[L]))) :=
  continuous_map (`1 (limit_med (limit_is_alimit L) (sc_pt_cone G N n))) ttt.

Lemma sc_pt_const_med@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N])
  (p : carrier (top_carrier (`1 (vertex_obj[L]))))
  (Hp : ∀ x : J, continuous_map (`1 (limit_leg (limit_is_alimit L) x)) p
                 ≈ cone_leg N x n) :
  sc_pres_pt G L N n ≈ p.
Proof.
  unfold sc_pres_pt.
  refine (limit_med_unique (limit_is_alimit L) (sc_pt_cone G N n)
           (top_point (`1 (vertex_obj[L])) p; I) _ ttt).
  intros x t. simpl. exact (Hp x).
Qed.

Definition sc_pres_map@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) :
  vertex_obj[N] ~{Sets}~> CompHaus_Forget L.
Proof.
  unshelve refine {| morphism := sc_pres_pt G L N |}.
  intros n n' e.
  apply sc_pt_const_med. intro x.
  transitivity (cone_leg N x n').
  - exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n') x ttt).
  - symmetry. exact (proper_morphism (cone_leg N x) n n' e).
Defined.

Theorem CompHaus_Forget_PreservesImageLimit@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget.
Proof.
  intros J G L N.
  unshelve refine {| unique_obj := sc_pres_map G L N |}.
  - intros x n.
    exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n) x ttt).
  - intros v Hv n. simpl.
    apply sc_pt_const_med. intro x. exact (Hv x n).
Qed.

(* Every object with every arrow: legal at the hom universe, because the
   whole object type of [CompHaus] lives there. *)
Definition taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d.
Proof.
  unshelve refine
    {| sol_index := { K : CompHaus & d ~{Sets}~> CompHaus_Forget K };
       sol_obj := fun p => `1 p;
       sol_arr := fun p => `2 p |}.
  intros c h. exists (c; h). exists id.
  intro x. simpl. apply reflexive_lift.
Defined.

(* GAFT with completeness as the one remaining hypothesis.  That hypothesis
   is refuted under [IEM] (Refutations.v); this is the measured reduction,
   not a construction. *)
Definition GAFT_CompHaus_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(** * Exercise 4 at the level of universal arrows *)

Theorem unit_injective_of_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  intros Hsep x y E. apply Hsep. intros K f.
  pose proof (unique_property (ump_universal_arrows UA f)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA f))))
           _ _ E).
Qed.

Theorem separated_of_unit_injective@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y.
Proof. intros Hinj x y H. apply Hinj. exact (H _ (@arrow _ _ _ _ UA)). Qed.

(* The characteristic map of a point, into the two-point space. *)
Definition sc_chi@{o h +} (X : SetoidObject@{o o})
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) (x : X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := fun z => if dec z x then true else false |}.
  intros a b e. simpl.
  destruct (dec a x) as [ha|na], (dec b x) as [hb|nb]; try reflexivity.
  - exfalso. apply nb. exact (transitivity (symmetry e) ha).
  - exfalso. apply na. exact (transitivity e hb).
Defined.

Theorem unit_injective_of_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  apply unit_injective_of_separated.
  intros x y H.
  pose proof (H Bool_CH (sc_chi X dec x)) as Hc. simpl in Hc.
  destruct (dec x x) as [_|n]; [| destruct (n (reflexivity x))].
  destruct (dec y x) as [hy|ny]; [exact (symmetry hy) | discriminate Hc].
Qed.

(* Non-vacuity: the premises are met by a universal arrow built above. *)
Definition sc_bool_dec@{o +} (x y : bool_setoid_object@{o o}) :
  (x ≈ y) + ((x ≈ y) → False).
Proof.
  destruct x, y; simpl;
    [left; reflexivity | right; discriminate | right; discriminate
    | left; reflexivity].
Defined.

Definition StoneCech_finite_bool_injective@{o h +} :=
  unit_injective_of_dec bool_setoid_object@{o o}
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
     : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} bool_setoid_object@{o o})
         CompHaus_Forget)
    sc_bool_dec.

(** * Exercise 4 at a space: the unit of the inclusion *)

(* The maps from [X] into [K] separate the points of [X].  At [K] = [0,1]
   this is the point-separating half of complete regularity. *)
Definition KSeparated@{h o +} (K : CompHaus) (X : Top@{h o}) : Type@{h} :=
  ∀ x y : top_carrier X,
    (∀ k : X ~{Top}~> CompHaus_Incl K, continuous_map k x ≈ continuous_map k y)
    → x ≈ y.

Theorem StoneCech_unit_injective_completely_regular@{h o +}
  (K : CompHaus) (X : Top@{h o}) (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y.
Proof.
  intros x y E. apply HX. intro k.
  pose proof (unique_property (ump_universal_arrows UA k)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA k))))
           _ _ E).
Qed.

(* The converse, for a [K] that separates the points of EVERY compact
   Hausdorff space.  No [K] in the tree is shown to meet this premise, and
   one with ¬¬-stable equality of points yields double-negation
   elimination (Refutations.v's [CompHaus_point_separator_stable_DNE]). *)
Theorem KSeparated_of_unit_injective@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply (sepK (@arrow_obj _ _ _ _ UA)). intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(* The same converse from the premise the proof uses: [K] separates the
   points of the universal object alone.  Unlike the premise above, this
   one is met (see [KSeparated_of_unit_injective_local_at_CompHaus]). *)
Theorem KSeparated_of_unit_injective_local@{h o +} (K : CompHaus)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply sepK. intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(* Non-vacuity of the pair of premises: at a compact Hausdorff space the
   identity is universal, and the space is separated by itself. *)
Definition CompHaus_Incl_universal@{h o +} (K : CompHaus) :
  UniversalArrow (C:=Top@{h o}) (CompHaus_Incl K) CompHaus_Incl.
Proof.
  unshelve refine (universal_arrow_from_UMP _ _ K id _).
  intros d f.
  unshelve refine {| unique_obj := (f; I) |}.
  - intro x. reflexivity.
  - intros v Hv x. simpl in *. exact (Hv x).
Defined.

Example CompHaus_Incl_universal_obj@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K) = K
  := eq_refl.

Lemma KSeparated_self@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]).
Proof. intros x y H. exact (H id). Qed.

Definition StoneCech_unit_injective_at_CompHaus@{h o +} (K : CompHaus) :=
  StoneCech_unit_injective_completely_regular K
    (CompHaus_Incl K : obj[Top@{h o}]) (KSeparated_self K)
    (CompHaus_Incl_universal K).

(* Non-vacuity of the local converse: its three premises are met at the
   identity universal arrow, the injectivity of the unit by the theorem
   just applied. *)
Definition KSeparated_of_unit_injective_local_at_CompHaus@{h o +}
  (K : CompHaus) : KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local K (CompHaus_Incl K : obj[Top@{h o}])
    (CompHaus_Incl_universal K) (fun p q H => H id)
    (StoneCech_unit_injective_at_CompHaus K).

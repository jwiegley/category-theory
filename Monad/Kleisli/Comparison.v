Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.StrictCat.
Require Import Category.Adjunction.Map.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.

Generalizable All Variables.

(** * Free algebras for a monad: restricted adjunctions and the Kleisli
      comparison functor *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.5 "Free Algebras for a Monad",
         printed pp. 147-148 (PDF pp. 156-157): the construction opening
         the section, p. 147 — maclane:VI.5:construction1; Theorem 2,
         p. 148 — maclane:VI.5:thm2; Exercises 1 and 2, p. 148 —
         maclane:VI.5:ex1, maclane:VI.5:ex2.  Exercise 3
         (maclane:VI.5:ex3) is Monad/Kleisli/Comparison/Examples.v.
   Book: Riehl, "Category Theory in Context", Lemma 5.2.14 and the
         paragraph after it, printed p. 194 (PDF p. 214) —
         riehl:5.2:lem14
   nLab: https://ncatlab.org/nlab/show/Kleisli+category
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   WHAT THE BOOKS SAY, read from the page images and the PDF.  Mac Lane,
   p. 147: "Given an adjunction ⟨F, G, φ⟩ : X ⇀ A, any full subcategory
   B ⊂ A which contains all the objects Fx for x ∈ X leads to another
   adjunction ⟨F_B, G_B, φ_B⟩ : X ⇀ B where the functor F_B is just F
   with its codomain restricted from A to B, G_B is G with domain
   restricted to B, while for x ∈ X and b ∈ B the given adjunction leads
   to a bijection φ_B hom_B(F_B x, b) = hom_A(Fx, b) ≅ hom_X(x, Gb) =
   hom_X(x, G_B b), which is manifestly natural in x and b.  Moreover,
   this second adjunction φ_B defines in X the same monad as did the
   first. ... The "smallest" such adjunction will be the one where B is
   FX, the full subcategory of A with objects all the "free" objects
   Fx ∈ A."  Theorem 2 (The comparison theorem for the Kleisli
   construction), p. 148: "Let ⟨F, G, η, ε⟩ : X ⇀ A be an adjunction and
   T = ⟨GF, η, GεF⟩ the monad it defines in X.  Then there is a unique
   functor L : X_T → A with GL = G_T and LF_T = F.  We leave the proof to
   the reader, noting that the uniqueness of L requires another (and
   somewhat different) application of Proposition IV.7.1 on maps of
   adjunctions."  Exercise 1: "Construct the Kleisli comparison functor
   L, prove its uniqueness, and show that the image of X_T under L is the
   full subcategory FX of A with objects all Fx, x ∈ X."  Exercise 2:
   "Show that the restriction of L gives an equivalence of categories
   X_T → FX."  Riehl, Lemma 5.2.14: "Let (T, η, µ) be a monad on C.  The
   canonical functor K : C_T → C^T from the Kleisli category to the
   Eilenberg–Moore category is full and faithful and its image consists
   of the free T-algebras", its proof setting Kc := (Tc, µ_c); and after
   it: "Lemma 5.2.14 also tells us precisely when the Kleisli and
   Eilenberg–Moore categories are equivalent: this is the case when all
   algebras are free."

   CONSTRUCTION 1.  Over F ⊣ G, a [Subcategory] S of A (Construction/
   Subcategory.v), its fullness [full : Full A S] and the membership
   [mem x] of every F x: [Restricted_Left] is F_B, x ↦ (F x; mem x);
   [Restricted_Right G S] is G_B, G after the inclusion; and
   [Restricted_adj_iso] is φ_B, the given transposition on the first
   components, from which [Build_Adjunction'] makes
   [Restricted_Adjunction : F_B ⊣ G_B].  "The same monad": with the two
   monads Monad/Comparison.v's [Adjunction_Induced_Monad] of the two
   adjunctions, G_B F_B and G F agree on objects and on arrows
   ([Restricted_monad_obj], [Restricted_monad_map]), and so do η and
   μ = G ε F, componentwise ([Restricted_unit_agrees],
   [Restricted_join_agrees]), all four at [eq_refl].  The composite
   functors are not convertible as records (refused at [eq_refl], R1 of
   Test/ProbeKleisliComparison475.v; their Leibniz inequality is neither
   proved nor refuted), so the two monad records have different types
   and cannot be compared at Leibniz equality at all (R2, refused by
   typing); nor are the two objects of Monad/Morphism.v's [Monads X]
   they make convertible (refused at [eq_refl], R3).  What is
   delivered is [Restricted_Monad_agrees], G_B F_B ≈ G F with the
   identity at every object ([Restricted_Monad_agrees_iso]), and
   [Restricted_Monad_iso], the two monads isomorphic in [Monads X]
   through the morphisms of monads [Restricted_Monad_to] and
   [Restricted_Monad_from], every component of both legs the identity
   ([Restricted_Monad_iso_to], [Restricted_Monad_iso_from]).

   THEOREM 2.  T is [Adjunction_Induced_Monad Adj], the monad ⟨GF, η,
   GεF⟩ the adjunction defines, and X_T is Monad/Kleisli.v's [Kleisli]
   of it.  [Kleisli_Comparison] is L: L x = F x and L f the transpose
   ⌈f⌉ of f : x ~> G F y under the adjunction (Riehl's description of
   the functor in her Proposition 5.2.13), both at [eq_refl]
   ([Kleisli_Comparison_obj], [Kleisli_Comparison_map]); L f = ε ∘ F f
   holds at ≈ ([Kleisli_Comparison_map_counit]) and is refused at
   [eq_refl] (R4).  Mac Lane's G L = G_T and L F_T = F are delivered
   three ways.  At ≈ of functors, with the identity at every object:
   [Kleisli_Comparison_Forget] and [Kleisli_Comparison_Free] (readbacks
   [Kleisli_Comparison_Forget_iso], [Kleisli_Comparison_Free_iso]).  As
   strict functor equalities, at Theory/Functor.v's
   [Functor_StrictEq_Setoid], with [eq_refl] as every object component:
   [Kleisli_Comparison_Forget_strict] and [Kleisli_Comparison_Free_strict]
   (readbacks [Kleisli_Comparison_Forget_strict_obj],
   [Kleisli_Comparison_Free_strict_obj]); their arrow halves are refused
   at [eq_refl] (R5, R6), their object halves hold there (controls C13,
   C16).  And as Mac Lane's map of adjunctions (§IV.7, Adjunction/
   Map.v): [Kleisli_Comparison_Squares], with K := L, L := Id and both
   object equations [eq_refl], its unit condition
   [Kleisli_Comparison_Squares_unit], and [Kleisli_Comparison_Map :
   MapOfAdjunctions Kleisli_Adjunction Adj].  L is full
   ([Kleisli_Comparison_Full], the preimage of g being its forward
   transpose) and faithful ([Kleisli_Comparison_Faithful]).

   UNIQUENESS.  For a functor L0 : X_T ⟶ A, Mac Lane's G L0 = G_T and
   L0 F_T = F are read with the object equation of the first the G-image
   of that of the second.  [Kleisli_Comparison_unique] takes
   Hobj : ∀ x, L0 x = F x (the object half of L0 F_T = F, at Leibniz
   equality) and the arrow half of G L0 = G_T along the G-image of Hobj,
   and concludes L0 ≈ L; [Kleisli_Comparison_unique_strict] concludes,
   from the same, that L0 and L are equal at [Functor_StrictEq_Setoid];
   the shared step is [Kleisli_Comparison_unique_map].  The arrow half
   of L0 F_T = F is not used, so these hypotheses are weaker than the
   book's equations read coherently, as above; that the two equations,
   taken as independent strict functor equalities, imply them is not
   shown.  [Kleisli_Comparison_unique_of_strict] takes the book's
   hypotheses in the form existence delivers them: L0 F_T = F and
   G L0 = G_T as strict functor equalities at [Functor_StrictEq_Setoid],
   with the coherence of their object equations (the second's the
   G-image of the first's at each x) an explicit hypothesis, and
   concludes that L0 and L are equal there.  At L0 := L the delivered
   [Kleisli_Comparison_Free_strict] and [Kleisli_Comparison_Forget_strict]
   satisfy it, the coherence at [eq_refl] (control C42).  Mac Lane's
   route, "another (and somewhat different) application of Proposition
   IV.7.1", is [Kleisli_Comparison_unique_via_map], placed beside
   [Kleisli_Comparison_Map]: the two squares of L0 make the
   [AdjSquares] [Kleisli_Comparison_Squares_of], whose unit condition
   [Kleisli_Comparison_Squares_of_unit] is immediate, the unit of the
   Kleisli adjunction being η; Adjunction/Map.v's [squares_hom_iff_unit]
   then gives the commutation of L0 with transposition, and so L0 ≈ L.
   It consumes both squares.  With an object equation for G L0 = G_T
   given apart from Hobj, both arguments would meet the cast along a loop
   G (L0 y) = G (L0 y); it is the identity under UIP on the objects of
   X, which the library does not assume, so both take the right square's
   object equation to be the G-image of the left one.

   EXERCISE 1: THE IMAGE.  FX is read as Adjunction/LeftInverse.v's
   proof-relevant image [LaliImageSub] of F, reused under its name: an
   object is an a : A with a chosen x and F x = a, and every arrow is kept
   ([image_full]).  Construction 1 at B = FX is LeftInverse.v's [ImageTo]
   of F, on both actions ([Restricted_Left_Image_obj],
   [Restricted_Left_Image_map]).  The corestriction L' : X_T ⟶ FX is
   [Kleisli_Comparison_Image]; it is [ImageTo] of L on both actions
   ([Kleisli_Comparison_Image_is_ImageTo_obj],
   [Kleisli_Comparison_Image_is_ImageTo_map]) and L = Incl ◯ L' on both
   actions ([Kleisli_Comparison_Image_incl_obj],
   [Kleisli_Comparison_Image_incl_map]), all at [eq_refl].  L' is full,
   faithful and surjective on objects as data
   ([Kleisli_Comparison_Image_surjective], the chosen preimage of
   (a; (x; e)) being x, [Kleisli_Comparison_Image_surjective_obj]): the
   image of X_T under L is FX.

   EXERCISE 2.  Mac Lane's FX is a set of objects, and his equivalence
   chooses, for each of them, an x with F x isomorphic to it.  Made data,
   that choice is the hypothesis [pick : ∀ a, sobj A S a →
   { x & F x ≅ a }] of the general form.  It is more than the choice
   made data: over a general B it also confines B to the replete image
   of F, the objects isomorphic to some F x, so that B = A is excluded
   unless every object of A is isomorphic to a free one.  For any full
   subcategory B containing every F x, with such a chooser,
   [Kleisli_Comparison_Restrict], the corestriction of L to B, is full,
   faithful and essentially surjective
   ([Kleisli_Comparison_Restrict_ESO], by Construction/Subcategory.v's
   [Full_sub_iso]), and [Kleisli_Comparison_Restrict_Equivalence] is the
   equivalence X_T → B (Theory/Equivalence/FullFaithful.v's
   [FF_ESO_Equivalence]).  With membership in Prop, an x merely existing
   with F x = a, the split [EssentiallySurjective] would need choice, so
   the general form is not stated that way.  At B = FX = [LaliImageSub],
   [Kleisli_Comparison_Image] is defined as the general functor, and
   with the projection as [pick] ([Kleisli_Comparison_Image_pick])
   [Kleisli_Comparison_Image_Equivalence] is the general equivalence
   there; [Kleisli_Comparison_Image_AdjointEquivalence] is its adjoint
   form, through Theory/Equivalence/Strict.v's
   [ff_surjective_adjoint_equivalence].

   A REMARK ON THE REPRESENTATION.  In this library a subcategory's
   membership is data, and FX read as [LaliImageSub] has an object for
   every x: L' is injective on objects
   ([Kleisli_Comparison_Image_injective]), and the corestriction is an
   ISOMORPHISM of categories for every adjunction,
   [Kleisli_Comparison_Image_StrictIso : X_T ≅[StrictCat] FX], its
   inverse Strict.v's [ff_surjective_left] and both composites the
   identity at [Functor_StrictEq_Setoid]
   ([Kleisli_Comparison_Image_inv_left],
   [Kleisli_Comparison_Image_inv_right]).  In this reading the
   conclusion of Exercise 3, that the equivalence X_T → FX need not be
   an isomorphism, would be false.  The isomorphism owes nothing to
   Kleisli categories: [ImageTo] of a full and faithful functor is an
   isomorphism onto its [LaliImageSub], which LeftInverse.v's [ImageIso]
   proves from the [ffi_full] and [ffi_faithful] fields alone of the
   [LeftAdjointFFInjective] it takes, and the same holds of
   [Kleisli_EM_Image] (not built here; NOT DELIVERED).
   Monad/Kleisli/Comparison/Examples.v takes FX as Mac Lane's set of
   objects at an adjunction where it is all of the one-object category
   1, and there Exercise 2's equivalence, the general
   [Kleisli_Comparison_Restrict_Equivalence] at that FX, is not an
   isomorphism.

   RIEHL, LEMMA 5.2.14.  [Kleisli_EM : C_T ⟶ C^T] is Riehl's K over a
   monad (T, η, μ) on C: K c = (T c, μ_c) ([Kleisli_EM_obj]), the free
   algebra [EM_Free] c of Monad/Eilenberg/Moore/Adjunction.v
   ([Kleisli_EM_obj_free]); K f is that file's [EM_extend] f, the inverse
   transpose of f under [EM_Adjunction] ([Kleisli_EM_is_transpose]),
   with underlying arrow μ ∘ T f ([Kleisli_EM_map]), and U^T K = U_T on
   arrows ([Kleisli_EM_Forget_map]), all at [eq_refl].  K is full
   ([Kleisli_EM_Full], the preimage of g being g ∘ η, by
   [EM_restrict_extend]) and faithful ([Kleisli_EM_Faithful], by
   [EM_extend_ret]).  Its image consists of the free algebras:
   [Kleisli_EM_Image] is LeftInverse.v's [ImageTo] of K, typed into the
   full subcategory [LaliImageSub] of [EM_Free], an algebra with a chosen
   c and EM_Free c equal to it; it is full, faithful and surjective on
   objects ([Kleisli_EM_Image_surjective]), and
   [Kleisli_EM_Image_Equivalence] is the equivalence of C_T with the free
   algebras.  K is L at the Eilenberg–Moore resolution on both actions
   ([Kleisli_EM_is_comparison_obj], [Kleisli_EM_is_comparison_map], at
   [eq_refl]).  The two cannot be compared as functors (R7, refused by
   typing): their sources are the Kleisli categories of the monad
   (T, η, μ) and of the monad that [EM_Adjunction] induces, which are
   not convertible (refused at [eq_refl], R8) and whose identities and
   composites differ at [eq_refl] (R9, R10) and agree at ≈ (controls
   C33, C34).

   RIEHL'S OWN CONSTRUCTION OF K.  Her proof takes K from her
   Proposition 5.2.13 at the Kleisli adjunction: "Kc := (Tc, µ_c), Tc
   being the object U_T c and µ_c being U_T of the component of the
   counit of the Kleisli adjunction at the object c".  In the tree that
   is Monad/Comparison.v's [EM_Comparison] at Monad/Kleisli/Adjunction.v's
   [Kleisli_Adjunction], constructible since PR #201 (merged 2026-07-19)
   brought [EM_Comparison].  It forgets to the functor of [Kleisli_EM]
   on both actions ([EM_Comparison_Kleisli_obj],
   [EM_Comparison_Kleisli_map], at [eq_refl]), but it lands in the
   algebras of the monad the Kleisli adjunction induces, [EilenbergMoore]
   over [Kleisli_Forget ◯ Kleisli_Free] (control C38), and is refused the
   codomain C^T by typing (R11); its structure map at c is μ ∘ T id at
   [eq_refl] ([EM_Comparison_Kleisli_alg]), μ at ≈
   ([EM_Comparison_Kleisli_alg_join]), and refused as μ at [eq_refl]
   (R12).  [Kleisli_EM] is defined directly, into the algebras of T
   itself, which Riehl's lemma and [EveryAlgebraFree] are about, and
   with K c the free algebra [EM_Free] c at [eq_refl]: by that conversion
   [Kleisli_EM_Image] is typed into [LaliImageSub] of [EM_Free].

   WHEN C_T AND C^T ARE EQUIVALENT.  [EveryAlgebraFree] says that every
   algebra is isomorphic in C^T to a free algebra EM_Free c, the c and
   the isomorphism chosen; [Kleisli_EM_equivalence_iff] proves
   [EquivalenceOfCategories Kleisli_EM ↔ EveryAlgebraFree], both
   directions constructive.  "Equivalent" is read as "K is an
   equivalence"; an equivalence of C_T with C^T through some other
   functor is not what is proved, and is not claimed.  The premise is
   witnessed in the tree: at the one-point monad of Exercise 3 every
   algebra is free (Examples.v's [kleisli_point_every_algebra_free]), so
   K is an equivalence there ([kleisli_point_K_equivalence], the
   biconditional read from right to left).  The identity monad would
   serve as well: a witness at Monad/Identity.v's [IdMonad] compiles,
   closed, in a scratch file, and is not built here.

   THE ISSUE'S PREMISES, dated.  Issue #475 was filed on 2026-07-23, and
   its appended section was added on 2026-07-31 (the body's edit
   history).  Its "the comparison functor L is absent", "no functor
   Kleisli → A for an arbitrary resolution", "no image-is-FX
   characterization" and "no X_T ≃ FX equivalence" were accurate when
   filed and held until this change.  "The tree's sole comparison
   functor is EM_Comparison", the opposite direction, was accurate when
   filed for comparison functors of monads (Theory/Lawvere/Monad.v's
   [Lawvere_EM_Comparison], of 2026-07-15, is [EM_Comparison] at one
   adjunction; Construction/Grothendieck/RoundTrip.v's [RT_Comparison]
   and [RoundTrip_Comparison], of 2026-07-10 and called comparison
   functors there, go from a Grothendieck construction back to the total
   category of a fibration) and has been stale since PR #1343 (merged
   2026-09-30), whose Instance/SupLat.v builds [SupLat_to_EM] into an
   Eilenberg–Moore category by hand; every such functor of monads points
   into C^T.  "No restriction-of-an-adjunction-to-a-full-subcategory
   construction" was accurate when filed.  For Mac Lane's form, the left
   adjoint's codomain restricted, it held until this change
   (LeftInverse.v's [ImageTo], 2026-09-02, is F_B at B = FX on both
   actions, with no adjunction stated); under the issue's words it has
   been stale since PR #1255 (merged 2026-09-03), whose
   Construction/Reflective/FixedPoints.v restricts an adjunction on both
   sides to its fixed points ([fixed_adjunction]), and PR #1334 (merged
   2026-09-27), whose Instance/Top/Separation.v restricts a reflection
   to a full subcategory containing the reflective one ([restrict_adj]),
   the dual of construction 1 for reflections.  "'X_T is the full
   subcategory of free algebras' occurs only as header prose in
   Monad/Kleisli.v" was inaccurate when filed: Monad/Eilenberg/Moore.v
   (2026-06-17) and Monad/Eilenberg/Moore/Adjunction.v (2026-07-08) said
   the same, and Comonad/Duality.v (2026-07-15) asserted the comparison
   functor out of the Kleisli category; the four carry CORRECTION (#475)
   notes.  Monad/Adjunction.v's "the Kleisli (initial) and
   Eilenberg–Moore (terminal) resolutions" (2026-06-17) asserts only
   Theorem VI.5.3's initiality and terminality, and is left to #476
   without a note.  The appended box's "no functor C_T ⟶ C^T exists
   anywhere in the tree" was accurate when appended only with C^T the
   algebras of T itself: [EM_Comparison] at [Kleisli_Adjunction] had
   been constructible since PR #201 (merged 2026-07-19), into the
   algebras of the monad the Kleisli adjunction induces (above).  No
   commit that wrote one of the four corrected sentences has
   Monad/Comparison.v in its tree (checked by ancestry): that functor
   was not constructible when any of them was written.  The issue's
   "CLAUDE.md Key Files index" was accurate when filed and has been stale
   since PR #1284 (merged 2026-09-09), which moved the index to
   docs/INDEX.md.

   STRENGTHS.  Every [Example] holds at [eq_refl] but
   [Kleisli_Comparison_Image_surjective_obj], proved by case analysis on
   the object, and Test/ProbeKleisliComparison475.v restates each one (its
   RESTATEMENTS).  Equalities of objects are Leibniz, as the tree states
   them (Hobj, surjectivity and injectivity on objects,
   [Kleisli_Comparison_Image_inv_right_obj]); arrows are compared at ≈ but
   in the readbacks, the strict functor equalities comparing them at ≈
   after the casts along their object equations.  At ≈ and refused at
   [eq_refl]: L f = ε ∘ F f (R4), the arrow halves of G L = G_T and L
   F_T = F (R5, R6), and the structure map of [EM_Comparison] at the
   Kleisli adjunction against μ (R12); G_B F_B and G F are ≈ and are
   refused as records (R1).  Fourteen proofs here end [Defined] (counted
   by token) and forty-one [Qed].  Load-bearing transparency, measured
   by closing each [Defined] of the two files alone [Qed] in a renamed
   copy of them and the probe, and naming the first command that then
   stops: [Restricted_Adjunction] ([Restricted_unit_agrees]),
   [Restricted_Monad_agrees] ([Restricted_Monad_agrees_iso]),
   [Restricted_Monad_to] and [Restricted_Monad_from] (each
   [Restricted_Monad_iso]), [Restricted_Monad_iso]
   ([Restricted_Monad_iso_to]), [Kleisli_Comparison_Forget] and
   [Kleisli_Comparison_Free] (their [_iso] readbacks),
   [Kleisli_Comparison_Forget_strict] and [Kleisli_Comparison_Free_strict]
   (their [_strict_obj] readbacks), [Kleisli_Comparison_Image_surjective]
   ([Kleisli_Comparison_Image_surjective_obj]) and
   [Kleisli_Comparison_Image_inv_right_obj]
   ([Kleisli_Comparison_Image_inv_right]): eleven.  The other three here,
   [Kleisli_Comparison_Restrict_ESO], [Kleisli_EM_Image_surjective] and
   [Kleisli_EM_equivalence_iff], are [Defined] by the data convention only
   (closed [Qed], nothing stops).  Every refutation of the probe is still
   refused, and every control accepted, in a renamed copy of the two files
   and the probe with all forty-eight [Qed]s of the two turned [Defined],
   so none is the opacity of #475's own proofs.  Read from the terms: R4 to
   R6 compare expressions in the transposition of the adjunction, a
   section variable, that agree only by its laws; R9 and R10 compare ret
   with id ∘ ret and μ with μ ∘ T id in a variable category, R12 μ ∘ T id
   with μ, and R8 the two categories built on them; R1 and R3 compare
   records whose data agree (C1, C2, C5, C6) and whose proof fields
   differ; R11 and R13 compare terms of different types.

   UNIVERSES, read off [About] (every name, by script).  No binder is
   written in this file (Examples.v declares two levels for readability
   only; its header), and no explicit universe instance of a constant
   #475 adds appears anywhere (a scan of the code of every .v file of the
   tree, comments stripped, finds none).  Every name is universe
   polymorphic, and no block mentions [Set].  Over an adjunction
   F ⊣ G : X ⇀ A, X is Category@{u u0 u0} and A Category@{u1 u2 u2}, and
   every block carries one equation, u0 = u2, identifying the hom levels
   of X and A: Theory/Adjunction.v's [Adjunction] identifies the hom and
   proof levels of its two categories (h1 = p1 = h2 = p2 in its own
   block), and a section's context reaches every constant declared in
   it.  These are the eighty-two names of the sections before Riehl's,
   binding six to thirteen levels.  The twenty-eight names over a monad
   on C (Riehl's section, the two comparison readbacks and the four of
   [EM_Comparison] at the Kleisli adjunction) carry no equation and bind
   four to eight.  Compiled on Coq 8.19.2 and 8.20.1, each of the 129
   names #475 adds (with Examples.v's) binds the same number of levels as
   on Rocq 9.1.1 and carries the same equations, and no block mentions
   [Set], compared by [About] in source overlays.  Each of the three
   versions prints the one equation in both orientations, u0 = u2 and
   u2 = u0, in some blocks: eleven on Rocq 9.1.1, three on each of Coq
   8.19.2 and 8.20.1.

   NOT DELIVERED.  Mac Lane's Theorem 3, the Kleisli resolution initial
   and the Eilenberg–Moore one terminal among the resolutions of T (issue
   #476).  For it, [Kleisli_Comparison_Map] is a map of adjunctions into
   each adjunction out of the Kleisli resolution of the monad that
   adjunction induces; at T's own Kleisli resolution that source is not
   C_T, and L is refused the type C_T ⟶ C_T by typing (R13; its type is
   control C41), so #476 needs L transported along an isomorphism of
   monads, or the Kleisli functor of a morphism of monads, which
   Monad/Morphism.v records as not built.  Riehl's two witnesses of "all
   algebras free", the free vector space monad and the maybe monad: each
   is conditional by the arguments issue #1359 records, which are not
   compiled here (Blass, Contemporary Mathematics 31, 1984, derives the
   axiom of choice in ZF from every vector space having a basis, over a
   field his proof varies; the freeness of every algebra of the maybe
   monad is argued there to need a decidable base point, the hypothesis
   Instance/Sets/Pointed/Part.v's [PointedDecidablePt] already names);
   they are left to issue #1359, the premise itself being witnessed at
   the one-point monad (Examples.v).  FX with membership in Prop
   (above).  An isomorphism X_T ≅ FX for Mac Lane's FX, false in general
   (Examples.v).  The strict isomorphism of [Kleisli_EM_Image] onto its
   [LaliImageSub]: a copy of the pattern of
   [Kleisli_Comparison_Image_StrictIso] gives it in forty-two lines,
   compiled and closed in a scratch file, and a second copy is not
   added.  Both isomorphisms follow from one generalization of
   LeftInverse.v's [ImageFrom] and [ImageIso] to a full and faithful
   functor, out of that file's section: a refactor of that file and its
   probe, not made here. *)

(* ------------------------------------------------------------------------ *)
(** ** Construction 1: restricting an adjunction to a full subcategory *)

Section Restrict.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (S : Subcategory A) (full : Full A S).
Context (mem : ∀ x : X, sobj A S (F x)).

(* F_B: F with its codomain restricted to B. *)
Program Definition Restricted_Left : X ⟶ Sub A S := {|
  fobj := fun x => (F x; mem x);
  fmap := fun x y f => (fmap[F] f; full _ _ _ _ (fmap[F] f))
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; simpl; apply fmap_comp. Qed.

(* G_B: G with its domain restricted to B. *)
Definition Restricted_Right : Sub A S ⟶ X := G ◯ Incl A S.

(* φ_B: hom_B(F_B x, b) = hom_A(F x, b) ≅ hom_X(x, G b) = hom_X(x, G_B b). *)
Program Definition Restricted_adj_iso (x : X) (b : Sub A S) :
  @Isomorphism Sets
    {| carrier := @hom (Sub A S) (Restricted_Left x) b
     ; is_setoid := @homset (Sub A S) (Restricted_Left x) b |}
    {| carrier := @hom X x (Restricted_Right b)
     ; is_setoid := @homset X x (Restricted_Right b) |} := {|
  to   := {| morphism := fun f => to (@adj _ _ _ _ Adj x (`1 b)) (`1 f) |};
  from := {| morphism := fun g =>
               (from (@adj _ _ _ _ Adj x (`1 b)) g;
                full _ _ (mem x) (`2 b) (from (@adj _ _ _ _ Adj x (`1 b)) g)) |}
|}.
Next Obligation. intros x b f g Hfg; simpl in *; now rewrite Hfg. Qed.
Next Obligation. intros x b f g Hfg; simpl in *; now rewrite Hfg. Qed.
Next Obligation. intros x b g; simpl; apply from_adj_comp_law. Qed.
Next Obligation. intros x b f; simpl; apply to_adj_comp_law. Qed.

Definition Restricted_Adjunction : Restricted_Left ⊣ Restricted_Right.
Proof using Adj full mem.
  unshelve eapply (@Build_Adjunction' (Sub A S) X Restricted_Left
                     Restricted_Right Restricted_adj_iso).
  - intros x y z f g; simpl. apply to_adj_nat_l.
  - intros x y z f g; simpl. apply to_adj_nat_r.
Defined.

(* "This second adjunction defines in X the same monad as did the first":
   the endofunctors agree on both actions, and so do η and μ = G ε F. *)

Example Restricted_monad_obj (x : X) :
  fobj[Restricted_Right ◯ Restricted_Left] x = fobj[G ◯ F] x := eq_refl.

Example Restricted_monad_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Right ◯ Restricted_Left] f = fmap[G ◯ F] f := eq_refl.

Example Restricted_unit_agrees (x : X) :
  @ret X (Restricted_Right ◯ Restricted_Left)
       (Adjunction_Induced_Monad Restricted_Adjunction) x
    = @ret X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

Example Restricted_join_agrees (x : X) :
  @join X (Restricted_Right ◯ Restricted_Left)
        (Adjunction_Induced_Monad Restricted_Adjunction) x
    = @join X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

Theorem Restricted_Monad_agrees :
  Restricted_Right ◯ Restricted_Left ≈ G ◯ F.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl. now rewrite id_left, id_right.
Defined.

Example Restricted_Monad_agrees_iso (x : X) :
  `1 Restricted_Monad_agrees x = iso_id := eq_refl.

(* The two monads as objects of Monad/Morphism.v's [Monads X]: isomorphic,
   with identity components both ways. *)

Definition Restricted_Monad_to :
  MonadHom (Adjunction_Induced_Monad Restricted_Adjunction)
           (Adjunction_Induced_Monad Adj).
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=Restricted_Right ◯ Restricted_Left) (G:=G ◯ F)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. apply id_left.
  - intros x; simpl. rewrite !id_left, !fmap_id, id_right. reflexivity.
Defined.

Definition Restricted_Monad_from :
  MonadHom (Adjunction_Induced_Monad Adj)
           (Adjunction_Induced_Monad Restricted_Adjunction).
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=G ◯ F) (G:=Restricted_Right ◯ Restricted_Left)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. apply id_left.
  - intros x; simpl. rewrite !id_left, !fmap_id, id_right. reflexivity.
Defined.

Definition Restricted_Monad_iso :
  @Isomorphism (Monads X)
    (Restricted_Right ◯ Restricted_Left;
     Adjunction_Induced_Monad Restricted_Adjunction)
    (G ◯ F; Adjunction_Induced_Monad Adj).
Proof.
  unshelve refine (@Build_Isomorphism (Monads X)
                     (Restricted_Right ◯ Restricted_Left;
                      Adjunction_Induced_Monad Restricted_Adjunction)
                     (G ◯ F; Adjunction_Induced_Monad Adj)
                     Restricted_Monad_to Restricted_Monad_from _ _).
  - intros x; simpl. apply id_left.
  - intros x; simpl. apply id_left.
Defined.

Example Restricted_Monad_iso_to (x : X) :
  transform[mh_transform (to Restricted_Monad_iso)] x = id := eq_refl.

Example Restricted_Monad_iso_from (x : X) :
  transform[mh_transform (from Restricted_Monad_iso)] x = id := eq_refl.

End Restrict.

Arguments Restricted_Right {X A} G S.

(* ------------------------------------------------------------------------ *)
(** ** Theorem 2: the comparison functor L : X_T ⟶ A *)

Section KleisliComparison.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Lemma Kleisli_Comparison_fmap_id (x : X) :
  from (@adj _ _ _ _ Adj x (F x)) (@unit _ _ _ _ Adj x) ≈ id[F x].
Proof. apply from_adj_unit. Qed.

Lemma Kleisli_Comparison_fmap_comp (x y z : X)
  (f : y ~{XT}~> z) (g : x ~{XT}~> y) :
  from (@adj _ _ _ _ Adj x (F z)) (f ∘[XT] g)
    ≈ from (@adj _ _ _ _ Adj y (F z)) f ∘ from (@adj _ _ _ _ Adj x (F y)) g.
Proof.
  rewrite !(from_adj_counit (H:=Adj)).
  simpl.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite <- (adj_counit_natural Adj (@counit _ _ _ _ Adj (F z) ∘ fmap[F] f)).
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(* L x = F x, and L f is the transpose ⌈f⌉ of f : x ~> G F y. *)
Program Definition Kleisli_Comparison : XT ⟶ A := {|
  fobj := fun x => F x;
  fmap := fun x y f => from (@adj _ _ _ _ Adj x (F y)) f
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; apply Kleisli_Comparison_fmap_id. Qed.
Next Obligation. intros x y z f g; apply Kleisli_Comparison_fmap_comp. Qed.

Example Kleisli_Comparison_obj (x : X) : fobj[Kleisli_Comparison] x = F x
  := eq_refl.

Example Kleisli_Comparison_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison] f = from (@adj _ _ _ _ Adj x (F y)) f := eq_refl.

Lemma Kleisli_Comparison_map_counit (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison] f ≈ @counit _ _ _ _ Adj (F y) ∘ fmap[F] f.
Proof. exact (from_adj_counit (H:=Adj) f). Qed.

(* G L = G_T *)
Theorem Kleisli_Comparison_Forget :
  G ◯ Kleisli_Comparison ≈ @Kleisli_Forget X (G ◯ F) T.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Defined.

Example Kleisli_Comparison_Forget_iso (x : X) :
  `1 Kleisli_Comparison_Forget x = iso_id := eq_refl.

(* L F_T = F *)
Theorem Kleisli_Comparison_Free :
  Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T ≈ F.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  symmetry. apply fmap_from_adj_unit.
Defined.

Example Kleisli_Comparison_Free_iso (x : X) :
  `1 Kleisli_Comparison_Free x = iso_id := eq_refl.

(* Mac Lane's G L = G_T and L F_T = F as strict functor equalities. *)
Definition Kleisli_Comparison_Forget_strict :
  @equiv _ (@Functor_StrictEq_Setoid XT X)
    (G ◯ Kleisli_Comparison) (@Kleisli_Forget X (G ◯ F) T).
Proof.
  refine (strict_equiv_of_id_cast_nat (G ◯ Kleisli_Comparison)
            (@Kleisli_Forget X (G ◯ F) T) (fun x => eq_refl) _).
  intros x y f; cbv beta; rewrite !id_cast_refl, id_left, id_right; simpl.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Defined.

Example Kleisli_Comparison_Forget_strict_obj (x : X) :
  `1 Kleisli_Comparison_Forget_strict x = eq_refl := eq_refl.

Definition Kleisli_Comparison_Free_strict :
  @equiv _ (@Functor_StrictEq_Setoid X A)
    (Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T) F.
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Kleisli_Comparison ◯ @Kleisli_Free X (G ◯ F) T) F
            (fun x => eq_refl) _).
  intros x y f; cbv beta; rewrite !id_cast_refl, id_left, id_right; simpl.
  symmetry. apply fmap_from_adj_unit.
Defined.

Example Kleisli_Comparison_Free_strict_obj (x : X) :
  `1 Kleisli_Comparison_Free_strict x = eq_refl := eq_refl.

(* Full and faithful: the arrow action is the transposition bijection. *)
#[export] Program Instance Kleisli_Comparison_Full :
  Category.Theory.Functor.Full Kleisli_Comparison := {|
  prefmap := fun x y g => to (@adj _ _ _ _ Adj x (F y)) g
|}.
Next Obligation. intros x y g; simpl; apply to_adj_comp_law. Qed.

#[export] Program Instance Kleisli_Comparison_Faithful :
  Faithful Kleisli_Comparison.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  rewrite <- (from_adj_comp_law (H:=Adj) f).
  rewrite <- (from_adj_comp_law (H:=Adj) g).
  now rewrite Hfg.
Qed.

(* Uniqueness: a functor agreeing with F on objects (Leibniz) and whose
   G-image agrees with G_T on arrows is L.  The arrow half of L F_T = F is
   not used. *)
Section Unique.

Context (L0 : XT ⟶ A) (Hobj : ∀ x, fobj[L0] x = F x).
Context (Hmap : ∀ (x y : X) (f : x ~{XT}~> y),
  fmap[G] (id_cast (Hobj y) ∘ fmap[L0] f ∘ id_cast (eq_sym (Hobj x)))
    ≈ fmap[@Kleisli_Forget X (G ◯ F) T] f).

Lemma Kleisli_Comparison_unique_map (x y : X) (f : x ~{XT}~> y) :
  id_cast (Hobj y) ∘ fmap[L0] f ∘ id_cast (eq_sym (Hobj x))
    ≈ fmap[Kleisli_Comparison] f.
Proof using Hmap.
  apply (snd (adj_univ (H:=Adj) _ _)).
  rewrite (to_adj_unit (H:=Adj)).
  rewrite (Hmap x y f); simpl.
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural Adj f).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ Adj (F y)).
  apply id_left.
Qed.

Theorem Kleisli_Comparison_unique : L0 ≈ Kleisli_Comparison.
Proof using Hmap.
  exists (fun x => id_cast_iso (Hobj x)).
  intros x y f; simpl.
  rewrite <- (Kleisli_Comparison_unique_map x y f).
  rewrite !comp_assoc.
  rewrite id_cast_inv_l, id_left.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(* ... and equal to L as a functor, strictly. *)
Theorem Kleisli_Comparison_unique_strict :
  @equiv _ (@Functor_StrictEq_Setoid XT A) L0 Kleisli_Comparison.
Proof using Hmap.
  refine (strict_equiv_of_id_cast_nat L0 Kleisli_Comparison Hobj _).
  intros x y f.
  rewrite <- (Kleisli_Comparison_unique_map x y f).
  rewrite <- !comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

End Unique.

(* Mac Lane's hypotheses in the form existence delivers them: G L0 = G_T
   and L0 F_T = F as strict functor equalities, with the object equation of
   the first the G-image of that of the second ([coh]).  They give the
   hypotheses of the section above. *)
Theorem Kleisli_Comparison_unique_of_strict (L0 : XT ⟶ A)
  (E1 : @equiv _ (@Functor_StrictEq_Setoid X A)
          (L0 ◯ @Kleisli_Free X (G ◯ F) T) F)
  (E2 : @equiv _ (@Functor_StrictEq_Setoid XT X)
          (G ◯ L0) (@Kleisli_Forget X (G ◯ F) T))
  (coh : ∀ x, `1 E2 x = f_equal (fobj[G]) (`1 E1 x)) :
  @equiv _ (@Functor_StrictEq_Setoid XT A) L0 Kleisli_Comparison.
Proof.
  apply (Kleisli_Comparison_unique_strict L0 (`1 E1)).
  intros x y f.
  pose proof (fst (transport_square (`1 E2 x) (`1 E2 y) _ _) (`2 E2 x y f))
    as Hs.
  rewrite !fmap_comp, !fmap_id_cast.
  rewrite <- eq_sym_map_distr.
  rewrite <- !coh.
  simpl in Hs.
  rewrite Hs.
  rewrite <- comp_assoc, id_cast_inv_r.
  apply id_right.
Qed.

(* Theorem 2 as Mac Lane's map of adjunctions (§IV.7): K := L, L := Id. *)
Program Definition Kleisli_Comparison_Squares :
  @AdjSquares XT X (@Kleisli_Free X (G ◯ F) T) (@Kleisli_Forget X (G ◯ F) T)
              A X F G := {|
  sq_K := Kleisli_Comparison;
  sq_L := Id[X];
  sq_left := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.
Next Obligation.
  intros; simpl; rewrite id_left, id_right.
  symmetry. apply fmap_from_adj_unit.
Qed.
Next Obligation.
  intros; simpl; rewrite id_left, id_right.
  rewrite (from_adj_counit (H:=Adj) f).
  now rewrite fmap_comp.
Qed.

Lemma Kleisli_Comparison_Squares_unit :
  SquaresUnit (@Kleisli_Adjunction X (G ◯ F) T) Adj Kleisli_Comparison_Squares.
Proof.
  intros x; simpl.
  rewrite id_left, fmap_id, id_left.
  reflexivity.
Qed.

Definition Kleisli_Comparison_Map :
  MapOfAdjunctions (@Kleisli_Adjunction X (G ◯ F) T) Adj :=
  MapOfAdjunctions_of_unit _ _ Kleisli_Comparison_Squares
    Kleisli_Comparison_Squares_unit.

End KleisliComparison.

(* ------------------------------------------------------------------------ *)
(** ** Uniqueness by Mac Lane's route, Proposition IV.7.1 *)

Section UniqueViaMap.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Context (L0 : XT ⟶ A) (Hobj : ∀ x, fobj[L0] x = F x).
Context (Hleft : ∀ (x y : X) (f : x ~> y),
   id_cast (Hobj y) ∘ fmap[L0] (fmap[@Kleisli_Free X (G ◯ F) T] f)
     ≈ fmap[F] f ∘ id_cast (Hobj x)).
Context (Hright : ∀ (a b : XT) (f : a ~{XT}~> b),
   id_cast (f_equal (fobj[G]) (eq_sym (Hobj b)))
       ∘ fmap[@Kleisli_Forget X (G ◯ F) T] f
     ≈ fmap[G] (fmap[L0] f) ∘ id_cast (f_equal (fobj[G]) (eq_sym (Hobj a)))).

(* The right square's object equation is the G-image of the left one. *)
Definition Kleisli_Comparison_Squares_of :
  @AdjSquares XT X (@Kleisli_Free X (G ◯ F) T) (@Kleisli_Forget X (G ◯ F) T)
              A X F G :=
  @Build_AdjSquares XT X (@Kleisli_Free X (G ◯ F) T)
    (@Kleisli_Forget X (G ◯ F) T) A X F G L0 Id[X] Hobj Hleft
    (fun a => f_equal (fobj[G]) (eq_sym (Hobj a))) Hright.

Lemma Kleisli_Comparison_Squares_of_unit :
  SquaresUnit (@Kleisli_Adjunction X (G ◯ F) T) Adj
    Kleisli_Comparison_Squares_of.
Proof using All.
  intros x; simpl.
  rewrite fmap_id_cast.
  reflexivity.
Qed.

Theorem Kleisli_Comparison_unique_via_map : L0 ≈ Kleisli_Comparison Adj.
Proof using Adj Hobj Hleft Hright.
  pose proof (snd (squares_hom_iff_unit _ _ Kleisli_Comparison_Squares_of)
                Kleisli_Comparison_Squares_of_unit) as Hh.
  exists (fun x => id_cast_iso (Hobj x)).
  intros x y f; simpl.
  specialize (Hh x y f); simpl in Hh.
  apply (snd (adj_univ (H:=Adj) _ _)) in Hh.
  rewrite <- (fmap_id_cast G (eq_sym (Hobj y))) in Hh.
  rewrite (@from_adj_nat_r _ _ _ _ Adj) in Hh.
  rewrite <- Hh.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

End UniqueViaMap.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 2, in general: any full subcategory containing every F x,
       with a chosen free preimage for each of its objects *)

Section Restrict2.

#[local] Obligation Tactic := idtac.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (S : Subcategory A) (full : Full A S).
Context (mem : ∀ x : X, sobj A S (F x)).
Context (pick : ∀ (a : A), sobj A S a → { x : X & F x ≅ a }).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

Program Definition Kleisli_Comparison_Restrict : XT ⟶ Sub A S := {|
  fobj := fun x => (F x; mem x);
  fmap := fun x y f =>
    (fmap[Kleisli_Comparison Adj] f;
     full _ _ _ _ (fmap[Kleisli_Comparison Adj] f))
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply Kleisli_Comparison_fmap_id. Qed.
Next Obligation.
  intros x y z f g; simpl; apply Kleisli_Comparison_fmap_comp.
Qed.

#[export] Program Instance Kleisli_Comparison_Restrict_Full :
  Category.Theory.Functor.Full Kleisli_Comparison_Restrict := {|
  prefmap := fun x y g => to (@adj _ _ _ _ Adj x (F y)) (`1 g)
|}.
Next Obligation. intros x y g; simpl; apply to_adj_comp_law. Qed.

#[export] Program Instance Kleisli_Comparison_Restrict_Faithful :
  Faithful Kleisli_Comparison_Restrict.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  exact (@fmap_inj _ _ _ (Kleisli_Comparison_Faithful Adj) x y f g Hfg).
Qed.

Definition Kleisli_Comparison_Restrict_ESO :
  EssentiallySurjective Kleisli_Comparison_Restrict.
Proof using Adj full mem pick.
  unshelve eapply Build_EssentiallySurjective.
  - exact (fun b => `1 (pick (`1 b) (`2 b))).
  - intros [a m]; simpl.
    exact (Full_sub_iso A S full (mem (`1 (pick a m))) m (`2 (pick a m))).
Defined.

Definition Kleisli_Comparison_Restrict_Equivalence :
  EquivalenceOfCategories Kleisli_Comparison_Restrict :=
  @FF_ESO_Equivalence _ _ Kleisli_Comparison_Restrict
    Kleisli_Comparison_Restrict_Full Kleisli_Comparison_Restrict_Faithful
    Kleisli_Comparison_Restrict_ESO.

End Restrict2.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 1's image and Exercise 2 at FX *)

Section Image.

Context {X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Notation T := (@Adjunction_Induced_Monad A X F G Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

(* Mac Lane's FX, read as Adjunction/LeftInverse.v's proof-relevant image:
   an object is an a : A with a chosen x and F x = a. *)
Notation FXS := (@LaliImageSub X A F).
Notation FX := (Sub A FXS).

(* Construction 1 at B = FX is LeftInverse.v's [ImageTo], on both actions. *)
Example Restricted_Left_Image_obj (x : X) :
  fobj[Restricted_Left FXS image_full (fun x => (x; eq_refl))] x
    = fobj[@ImageTo X A F] x := eq_refl.

Example Restricted_Left_Image_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Left FXS image_full (fun x => (x; eq_refl))] f
    = fmap[@ImageTo X A F] f := eq_refl.

(* The corestriction L' : X_T ⟶ FX, the general functor at FX. *)
Definition Kleisli_Comparison_Image : XT ⟶ FX :=
  Kleisli_Comparison_Restrict Adj FXS image_full (fun x => (x; eq_refl)).

(* L' is LeftInverse.v's [ImageTo] of L, on both actions. *)
Example Kleisli_Comparison_Image_is_ImageTo_obj (x : X) :
  fobj[Kleisli_Comparison_Image] x
    = fobj[@ImageTo XT A (Kleisli_Comparison Adj)] x := eq_refl.

Example Kleisli_Comparison_Image_is_ImageTo_map (x y : X)
  (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison_Image] f
    = fmap[@ImageTo XT A (Kleisli_Comparison Adj)] f := eq_refl.

(* L = Incl ◯ L', both actions at eq_refl. *)
Example Kleisli_Comparison_Image_incl_obj (x : X) :
  fobj[Incl A FXS ◯ Kleisli_Comparison_Image] x
    = fobj[Kleisli_Comparison Adj] x := eq_refl.

Example Kleisli_Comparison_Image_incl_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Incl A FXS ◯ Kleisli_Comparison_Image] f
    = fmap[Kleisli_Comparison Adj] f := eq_refl.

Definition Kleisli_Comparison_Image_surjective :
  SurjectiveOnObjects Kleisli_Comparison_Image.
Proof.
  intros [a [x e]].
  exists x.
  destruct e; reflexivity.
Defined.

Example Kleisli_Comparison_Image_surjective_obj (y : FX) :
  `1 (Kleisli_Comparison_Image_surjective y) = `1 (`2 y).
Proof. destruct y as [a [x e]]; reflexivity. Qed.

(* Exercise 2 at FX: the chooser is the projection. *)
Definition Kleisli_Comparison_Image_pick (a : A) (m : sobj A FXS a) :
  { x : X & F x ≅ a } := (`1 m; id_cast_iso (`2 m)).

Definition Kleisli_Comparison_Image_Equivalence :
  EquivalenceOfCategories Kleisli_Comparison_Image :=
  Kleisli_Comparison_Restrict_Equivalence Adj FXS image_full
    (fun x => (x; eq_refl)) Kleisli_Comparison_Image_pick.

Definition Kleisli_Comparison_Image_AdjointEquivalence :
  AdjointEquivalence
    (@ff_surjective_left XT FX Kleisli_Comparison_Image
       (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
       (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
       Kleisli_Comparison_Image_surjective)
    Kleisli_Comparison_Image :=
  @ff_surjective_adjoint_equivalence XT FX Kleisli_Comparison_Image
    (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
    (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
    Kleisli_Comparison_Image_surjective.

(* ... and, in this proof-relevant representation, an isomorphism of
   categories: L' is injective on objects. *)
Lemma Kleisli_Comparison_Image_injective :
  InjectiveOnObjects Kleisli_Comparison_Image.
Proof.
  intros x x' H.
  exact (f_equal (fun y : FX => `1 (`2 y)) H).
Qed.

Notation Linv :=
  (@ff_surjective_left XT FX Kleisli_Comparison_Image
     (Kleisli_Comparison_Restrict_Full Adj FXS image_full _)
     (Kleisli_Comparison_Restrict_Faithful Adj FXS image_full _)
     Kleisli_Comparison_Image_surjective).

Lemma Kleisli_Comparison_Image_inv_left :
  @equiv _ (@Functor_StrictEq_Setoid XT XT)
    (Linv ◯ Kleisli_Comparison_Image) Id[XT].
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Linv ◯ Kleisli_Comparison_Image) Id[XT] (fun x => eq_refl) _).
  intros x y f; cbv beta.
  rewrite !id_cast_refl.
  rewrite (@id_left XT), (@id_right XT).
  simpl.
  rewrite id_left, id_right.
  apply (from_adj_comp_law (H:=Adj)).
Qed.

Lemma Kleisli_Comparison_Image_inv_right_obj (y : FX) :
  fobj[Kleisli_Comparison_Image ◯ Linv] y = y.
Proof. destruct y as [a [x e]]; destruct e; reflexivity. Defined.

Lemma Kleisli_Comparison_Image_inv_right :
  @equiv _ (@Functor_StrictEq_Setoid FX FX)
    (Kleisli_Comparison_Image ◯ Linv) Id[FX].
Proof.
  refine (strict_equiv_of_id_cast_nat
            (Kleisli_Comparison_Image ◯ Linv) Id[FX]
            Kleisli_Comparison_Image_inv_right_obj _).
  intros [a [x e]] [b [y e']] [f I']; destruct e, e'; simpl.
  rewrite !id_left, !id_right.
  apply (to_adj_comp_law (H:=Adj)).
Qed.

Definition Kleisli_Comparison_Image_StrictIso :
  @Isomorphism StrictCat XT FX :=
  @Build_Isomorphism StrictCat XT FX Kleisli_Comparison_Image Linv
    Kleisli_Comparison_Image_inv_right Kleisli_Comparison_Image_inv_left.

End Image.

(* ------------------------------------------------------------------------ *)
(** ** Riehl, Lemma 5.2.14: K : C_T ⟶ C^T, full and faithful onto the free
       algebras; and when it is an equivalence *)

Section Riehl.

#[local] Obligation Tactic := idtac.

Context {C : Category}.
Context (T : C ⟶ C).
Context `{H : @Monad C T}.

Program Definition Kleisli_EM : @Kleisli C T H ⟶ EilenbergMoore T := {|
  fobj := fun c => EM_Free T c;
  fmap := fun x y f => @EM_extend C T H x (EM_Free T y) f
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros; simpl; apply join_fmap_ret. Qed.
Next Obligation.
  intros; simpl.
  exact (@fmap_comp _ _ (@Kleisli_Forget C T H) _ _ _ _ _).
Qed.

Example Kleisli_EM_obj (c : C) :
  fobj[Kleisli_EM] c = (T c; {| t_alg := @join C T H c |}) := eq_refl.

Example Kleisli_EM_obj_free (c : C) :
  fobj[Kleisli_EM] c = fobj[EM_Free T] c := eq_refl.

Example Kleisli_EM_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  t_alg_hom[fmap[Kleisli_EM] f] = join ∘ fmap[T] f := eq_refl.

Example Kleisli_EM_Forget_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[EM_Forget T ◯ Kleisli_EM] f = fmap[@Kleisli_Forget C T H] f
  := eq_refl.

(* K is the transpose under F^T ⊣ U^T, Riehl's description, at eq_refl. *)
Example Kleisli_EM_is_transpose (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[Kleisli_EM] f = from (@adj _ _ _ _ (EM_Adjunction T) x (EM_Free T y)) f
  := eq_refl.

#[export] Program Instance Kleisli_EM_Full :
  Category.Theory.Functor.Full Kleisli_EM := {|
  prefmap := fun x y g => t_alg_hom[g] ∘ ret
|}.
Next Obligation.
  intros x y g; simpl; exact (@EM_restrict_extend C T H x (EM_Free T y) g).
Qed.

#[export] Program Instance Kleisli_EM_Faithful : Faithful Kleisli_EM.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  rewrite <- (EM_extend_ret T (`2 (EM_Free T y)) f).
  rewrite <- (EM_extend_ret T (`2 (EM_Free T y)) g).
  now rewrite Hfg.
Qed.

(* The corestriction to the free algebras, LeftInverse.v's [ImageTo]. *)
Notation FreeAlgs := (@LaliImageSub C (EilenbergMoore T) (EM_Free T)).

Definition Kleisli_EM_Image :
  @Kleisli C T H ⟶ Sub (EilenbergMoore T) FreeAlgs :=
  @ImageTo (@Kleisli C T H) (EilenbergMoore T) Kleisli_EM.

#[export] Program Instance Kleisli_EM_Image_Full :
  Category.Theory.Functor.Full Kleisli_EM_Image := {|
  prefmap := fun x y g => t_alg_hom[`1 g] ∘ ret
|}.
Next Obligation.
  intros x y g; simpl.
  exact (@EM_restrict_extend C T H x (EM_Free T y) (`1 g)).
Qed.

#[export] Program Instance Kleisli_EM_Image_Faithful :
  Faithful Kleisli_EM_Image.
Next Obligation.
  intros x y f g Hfg; simpl in *.
  exact (@fmap_inj _ _ _ Kleisli_EM_Faithful x y f g Hfg).
Qed.

Definition Kleisli_EM_Image_surjective :
  SurjectiveOnObjects Kleisli_EM_Image.
Proof. intros [a [c e]]. exists c. destruct e; reflexivity. Defined.

Definition Kleisli_EM_Image_Equivalence :
  EquivalenceOfCategories Kleisli_EM_Image :=
  @ff_surj_eso_equivalence _ _ Kleisli_EM_Image _ _
    Kleisli_EM_Image_surjective.

(* "Free" is "isomorphic in C^T to a free algebra", with the free algebra
   chosen; "equivalent" is "K is an equivalence". *)
Definition EveryAlgebraFree : Type :=
  ∀ a : EilenbergMoore T, { c : C & EM_Free T c ≅ a }.

Theorem Kleisli_EM_equivalence_iff :
  EquivalenceOfCategories Kleisli_EM ↔ EveryAlgebraFree.
Proof.
  split.
  - intros E a.
    exists (@quasi_inverse _ _ _ E a).
    exact (@equivalence_counit_at _ _ _ E a).
  - intros Hfree.
    exact (@FF_ESO_Equivalence _ _ Kleisli_EM Kleisli_EM_Full
             Kleisli_EM_Faithful
             (@Build_EssentiallySurjective _ _ Kleisli_EM
                (fun a => `1 (Hfree a)) (fun a => `2 (Hfree a)))).
Defined.

End Riehl.

(* K and L at the Eilenberg–Moore resolution agree on both actions. *)

Section RiehlIsL.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Example Kleisli_EM_is_comparison_obj (c : C) :
  fobj[@Kleisli_EM C T H] c = fobj[Kleisli_Comparison (EM_Adjunction T)] c
  := eq_refl.

Example Kleisli_EM_is_comparison_map (x y : C)
  (f : x ~{@Kleisli C T H}~> y) :
  fmap[@Kleisli_EM C T H] f = fmap[Kleisli_Comparison (EM_Adjunction T)] f
  := eq_refl.

End RiehlIsL.

(* Riehl's K as her proof builds it, her Proposition 5.2.13's functor at
   the Kleisli adjunction: Monad/Comparison.v's [EM_Comparison] at
   [Kleisli_Adjunction].  It forgets to the functor of [Kleisli_EM] on both
   actions, and lands in the algebras of the monad the Kleisli adjunction
   induces, with structure map μ ∘ T id at c. *)

Section RiehlEMComparison.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Example EM_Comparison_Kleisli_obj (c : C) :
  fobj[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] c
    = fobj[EM_Forget T ◯ @Kleisli_EM C T H] c := eq_refl.

Example EM_Comparison_Kleisli_map (x y : C) (f : x ~{@Kleisli C T H}~> y) :
  fmap[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] f
    = fmap[EM_Forget T ◯ @Kleisli_EM C T H] f := eq_refl.

Example EM_Comparison_Kleisli_alg (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    = @join C T H c ∘ fmap[T] (@id C (T c)) := eq_refl.

Lemma EM_Comparison_Kleisli_alg_join (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    ≈ @join C T H c.
Proof. simpl. rewrite fmap_id. apply id_right. Qed.

End RiehlEMComparison.

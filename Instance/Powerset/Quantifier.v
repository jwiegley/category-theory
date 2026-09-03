Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.

(* The same two as Instance/Powerset.v:25-27 and Instance/Proset.v:4-5:
   [relation] and [PreOrder] below are the stdlib Prop-valued ones, not
   the [crelation] ones [Category.Lib] exports, and they must come AFTER
   [Category.Lib].  The cost is that stdlib's [equiv] then shadows
   [Category.Lib.Setoid.equiv], so every explicit occurrence below is
   written [@Category.Lib.Setoid.equiv].  The [≈] NOTATION is unaffected:
   a notation resolves its head reference when it is declared, so [≈]
   stays bound to the library's [equiv]. *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The quantifiers as adjoints to substitution

    Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5
    construction 4 (printed pp. 96-97).  Transcribed from the page
    images, in ASCII.  From p. 96, last paragraph:

      "Now consider the first projection P : U x V -> U from the product
       of two sets U and V.  Each subset S subset U x V defines two
       corresponding subsets of U by

           P_* S = {x | exists y, y in V   and       <x,y> in S},
           P_# S = {x | forall y, y in V   implies   <x,y> in S};

       they arise from <x,y> in S by applying the existential quantifier
       exists y,"

    and, continuing on p. 97:

      "'there exists a y' and the universal quantifier forall y, 'for all
       y', respectively to <x,y> in S.  Also P_* S is the direct image of
       S under the projection P.  Now for all subsets X subset U one has

          S <= P^* X <=> P_* S <= X ;    P^* X <= S <=> X <= P_# S,

       where '<=>' means 'if and only if'.  These state that P^*, which
       is the inverse image operation, has both a left adjoint P_* and a
       right adjoint P_#.  In this sense, both quantifiers exists and
       forall can be interpreted as adjoints.

       There is also a geometric interpretation: P^* X is the cylinder
       X x V subset U x V over the base X subset U, P_* S is the
       projection of S subset U x V on the base U, and P_# S is the
       largest subset X of U such that the cylinder on X is wholly
       contained in S.  This analysis has revealed several basic concepts
       of logic (and, or, not, forall y, exists y) to be adjoints.  This
       illustrates the slogan 'adjoints are everywhere'."

    Awodey, *Category Theory* (1st ed. pre-print), §9.4 Example 9.12
    (printed p. 228) and the paragraph continuing it on p. 229:

      "Example 9.12.  A related example is the adjunction on powersets
       induced by any function f : A -> B, between the inverse image
       operation f^{-1} and the direct image im(f), ...  Here we have an
       adjunction im(f) -| f^{-1} as indicated by the bicondition:

           im(f)(U) subseteq V
           -------------------
           U subseteq f^{-1}(V)

       which is plainly valid for all subsets U subseteq A and
       V subseteq B.

       The inverse image operation f^{-1} : P(B) -> P(A) also has a
       right adjoint, given by:

           f_*(U) = {b in B | f^{-1}(b) subseteq U}

       as we also leave for the reader to verify."

    and §9.6 (printed p. 236), the preservation corollaries and their
    contrapositives:

      "Similarly, for the quantifiers one has e.g.:

        forall x (phi(x) /\ psi(x)) -||- forall x phi(x) /\ forall x psi(x)

       Since this does not hold for exists x, it cannot be a right
       adjoint to some other 'quantifier'.  Similarly:

        exists x (phi(x) \/ psi(x)) -||- exists x phi(x) \/ exists x psi(x)

       And, as above, forall x cannot be a left adjoint, since it does
       not have this property."

    Riehl, *Category Theory in Context* (2nd ed.), §4.1 Example 4.1.8
    (printed pp. 134-135):

      "Example 4.1.8.  Consider a function f : A -> B between sets.  The
       subsets of A and subsets of B form posets, PA and PB, ordered by
       inclusion.  The map f induces direct image and inverse image
       functors f_* : PA -> PB and f^{-1} : PB -> PA.  The inverse image
       is right adjoint to the direct image: for A' subset A and
       B' subset B, f(A') subset B' if and only if A' subset f^{-1}(B').

       The inverse image functor has a further right adjoint f_! that
       carries a subset A' subset A to the subset of elements of B whose
       fibers lie entirely in A'.  With this definition,
       B' subset f_!(A') if and only if f^{-1}(B') subset A'.  These
       functors define an adjoint triple: [f_* -| f^{-1} -| f_!]."

    Example 4.1.9 (printed p. 135):

      "Example 4.1.9.  A predicate or propositional function is a
       function p : X -> Omega, where Omega := {bot, top} is the set of
       truth values. ...  The set Omega^X is then the set of predicates
       on X.  The set Omega is given the partial order bot <= top defined
       by logical implication.  The set Omega^X inherits a
       pointwise-defined order: p <= q if and only if p(x) <= q(x) for
       all x in X, which is the case just when p(x) implies q(x) for
       every x.

       The logical operations of universal and existential quantification
       define functors forall_X, exists_X : Omega^X => Omega in the
       expected way: forall_X p = top if and only if p(x) = top for all
       x in X, and exists_X p = top if and only if there exists x in X
       with p(x) = top.  There is also a constant functor
       Delta_X : Omega -> Omega^X, and one can verify that these functors
       define an adjoint triple: [exists_X -| Delta_X -| forall_X]."

    Exercise 4.1.ii (printed p. 138):

      "Exercise 4.1.ii.  Explain why Example 4.1.9 can be regarded as a
       special case of Example 4.1.8."

    and §4.5's generalization to an arbitrary function (printed
    pp. 156-157):

      "There is a relationship between the cartesian closed structure on
       the category of predicates on X and the adjoint triple of functors
       exists_X -| Delta_X -| forall_X introduced in Example 4.1.9, which
       we first generalize as follows.  For any function f : Y -> X,
       there is an adjoint triple of functors ... defined as follows.
       For a predicate p : X -> Omega on X, Delta_f p is the predicate on
       Y defined by composition: Delta_f p := p f, which is to say that
       Delta_f p(y) := p(f(x)).  For a predicate q : Y -> Omega on Y,
       exists_f q(x) = top if there exists y in the fiber over x so that
       q(y) = top, while forall_f q(x) = top if q(y) = top for all y in
       the fiber over x."

    Fong and Spivak, *Seven Sketches in Compositionality*, §1.4.3
    Example 1.117 (printed pp. 32-33):

      "Example 1.117.  Let f : A -> B be a function between sets.  We can
       imagine A as a set of apples, B as a set of buckets, and f as
       putting each apple in a bucket.

       Then we have the monotone map f^* : P(Y) -> P(X) that category
       theorists call 'pullback along f.'  This map takes a subset
       B' subseteq B to its preimage f^{-1}(B') subseteq A: that is, it
       takes a collection B' of buckets, and tells you all the apples
       that they contain in total.  This operation is monotonic (more
       buckets means more apples) and it has both a left and a right
       adjoint.

       The left adjoint f_!(A) is given by the direct image: it maps a
       subset A' subseteq A to

         f_!(A') := {b in B | there exists a in A' such that f(a) = b}

       This map takes a set A' of apples, and tells you all the buckets
       that contain at least one of those apples.

       The right adjoint f_* maps a subset A' subseteq A to

         f_*(A') := {b in B | for all a such that f(a) = b, we have a in A'}

       This map takes a set A' of apples, and tells you all the buckets b
       that are all-A': all the apples in b are from the chosen subset
       A'.  Note that if a bucket doesn't contain any apples at all, then
       vacuously all its apples are from A', so empty buckets count as
       far as f_* is concerned."

    (Their Example 1.117 says "Let f : A -> B" and then writes
    f^* : P(Y) -> P(X); the letters X, Y there are a slip for A, B.
    Quoted as printed.)

    ** THE FOUR BOOKS DISAGREE ABOUT [f_*] AND [f_!], TWO WAYS EACH

    Riehl's [f_*] is the DIRECT image, and Mac Lane writes [P_*] for it
    at the projection; Awodey's [f_*] and Fong-Spivak's [f_*] are the
    DUAL image, Awodey writing [im(f)] for the direct image.  The dual
    image is [f_*] for Awodey and Fong-Spivak, [f_!] for Riehl and [P_#]
    for Mac Lane at the projection; the direct image is [f_!] for
    Fong-Spivak, [f_*] for Riehl, [P_*] for Mac Lane and [im(f)] for
    Awodey.  So the starred name takes two values across the four books
    and the shrieked name two, Riehl and Fong-Spivak opposite on both;
    an earlier draft called the clash "three-way" and an audit corrected
    it.  Riehl's [f_!] for the dual image is
    the reverse of the commonest topos-theoretic convention, in which
    [f_!] is the existential.  This file therefore uses no starred or
    shrieked name at all: the three operations are [Powerset_Prop_image]
    (the donor's), [Powerset_Prop_preimage] (the donor's) and
    [Powerset_Prop_dual] (new here), with the functors [DirectImage],
    [InverseImage] and [DualImage].

    nLab: https://ncatlab.org/nlab/show/existential+quantifier
    nLab: https://ncatlab.org/nlab/show/universal+quantifier
    nLab: https://ncatlab.org/nlab/show/adjoint+triple
    nLab: https://ncatlab.org/nlab/show/Beck-Chevalley+condition
    nLab: https://ncatlab.org/nlab/show/hyperdoctrine
    Wikipedia: https://en.wikipedia.org/wiki/Galois_connection

    ** THE ISSUE'S "Current state" IS STALE, MEASURED AT THE BASE COMMIT

    The catalog entry says the power set of a set as a category "has no
    witness".  It has one: #382's Instance/Powerset.v declares
    [subset_le] (:285), [subset_le_preorder] (:288) and
    [Subsets X := Proset (subset_le_preorder X)] (:295), and supplies the
    LEFT half of this issue outright -- [image_preimage_galois] (:387),
    [DirectImage] (:397), [InverseImage] (:401),
    [image_preimage_adjunction] (:405), the meets and joins
    [subset_inter] (:504) / [subset_union] (:522) with
    [Subsets_Cartesian] .. [Subsets_Cocomplete] (:609-:641), the three
    preservation theorems (:661, :678, :700), the RAPL/LAPC routes (:737,
    :769) and the witnesses (:844, :884).  All of that is CONSUMED, none
    of it rebuilt: [exists_substitution_adjunction] is literally
    [image_preimage_adjunction] under the name this issue pins, so "the
    existential IS the direct image" holds at a general [f] BY DEFINITION
    rather than by a comparison.

    What was genuinely absent is the RIGHT half.  Three sites say so in
    terms: Instance/Powerset.v:166, :206 and :695 each record that the
    dual image and [f^* -| forall_f] are #384's.

    The issue also says "in-tree the dual image has no counterpart of any
    kind".  That is stale for finite CODES: Instance/FinSet/Subsets.v:478
    declares [finpow_dual] with [finpow_dual_mem] (:494) and six
    [eq_refl] evaluations (:520-:545, among them [dual_apple0] and
    [dual_apple01]), and its :111, :116 and :122 record that only the
    ADJUNCTION is missing and that it is this issue's.  That file is
    cited, not rebuilt, and the finite-code adjunction is NOT built here:
    the setoid-level one is the deliverable.

    Work item 4 -- the slice-level generalization -- is NOT built.
    Construction/Slice/Pullback.v:50 has [Bang_Functor] (Sigma_f) and :67
    [Star_Functor] for f^*, its adjunction is a commented stub (:121-:127),
    and no Pi_f exists anywhere.  #387 owns it.

    ** WHAT IS DELIVERED, WITH GRADES

    (A0) Three reusable general constants, in the shape #381 uses for
         general lemmas placed in a consumer file, plus one engineering
         helper ([quant_refl]) recorded under the same heading.
         [proset_adjunction_at] builds an adjunction between preorders at
         two GIVEN functors out of the bare biconditional; it is what
         lets the headline be stated at #382's [InverseImage f] rather
         than at a second, parallel preimage functor (see the note
         below).  [gal_r_preserves_glb] and [gal_l_preserves_lub] are the
         order-level "right adjoints preserve meets, left adjoints
         preserve joins".  None of the three exists in tree, measured two
         ways at the base commit: for the two preservation lemmas,
         Instance/Powerset.v is the ONLY file mentioning both [gal_] and
         [IsGLB]/[IsLUB] and it relates them nowhere; for
         [proset_adjunction_at], the eight [Instance/Proset] files build
         an adjunction between prosets only through
         Instance/Proset/Galois.v's [GaloisAdjunction], which makes its
         own two functors, and its one [Context (Adj : F ⊣ U)] (:187-188)
         -- the only [⊣] in all eight files -- runs the OTHER way,
         consuming an adjunction rather than producing one.  The two
         preservation lemmas are plain terms with no tactic;
         [proset_adjunction_at]'s six [Program] obligations -- two
         [Proper] certificates for the legs, the two isomorphism laws in
         [Sets] and the two naturality clauses -- are each equations
         between parallel arrows in a thin category ([Proset]'s hom-setoid
         is [fun _ _ => True], Instance/Proset.v:41), which is why the
         default tactic closes all six; an earlier draft said "two".

    (A)  [Powerset_Prop_dual f S] with predicate
         [fun y => forall x, f x ≈ y -> S x] -- Awodey's
         [{b | f^{-1}(b) subseteq U}], Riehl's [f_!], Fong-Spivak's
         [f_*], Mac Lane's [P_#] at the projection.  NO truncation is
         needed, and that is a fact rather than a convenience: a [forall]
         landing in [Prop] is a [Prop] whatever it quantifies over,
         whereas [Powerset_Prop_image]'s existential has the
         [Type]-valued body [S x /\ f x ≈ y] -- [≈] is [Type]-valued
         here -- and must be squashed.  [dual_mem] reads membership back
         at [eq_refl].

         Then [dual_monotone], the two transposes
         [preimage_transpose_to]/[preimage_transpose_from],
         [preimage_dual_galois] as a [GaloisConnection] (the [_to] one is
         where the subset [T] of the codomain spends its own
         respectfulness: the hypothesis gives membership only at points
         of the inverse image, and [f x ≈ y] is what carries [T y]
         there), [DualImage] as #380's [GaloisFunctor_r] of it, and the
         two pinned names
         **[exists_substitution_adjunction f : DirectImage f ⊣
         InverseImage f]** (a [:=] of #382's) and
         **[substitution_forall_adjunction f : InverseImage f ⊣
         DualImage f]**, packaged as [quantifier_triple].
         [preimage_is_precompose] records at [eq_refl] that the inverse
         image IS Riehl's [Delta_f p := p f].

         WHY THE HEADLINE IS NOT [GaloisAdjunction].  #380's
         [GaloisAdjunction PA PB G] has type
         [GaloisFunctor_l PA PB G ⊣ GaloisFunctor_r PA PB G], and
         [GaloisFunctor_l _ _ preimage_dual_galois] is NOT
         [InverseImage f], which is [GaloisFunctor_r] of the OTHER
         connection.  The two have the same [fobj] and the same [fmap] on
         the nose -- which is why [proset_adjunction_at] applies at all,
         the hom types being convertible -- but [GaloisFunctor_l] and
         [GaloisFunctor_r] are separate [Program Definition]s whose three
         law fields are separate opaque obligations, so the functor
         RECORDS differ.  Stating the theorem with a second preimage
         functor would have made "f^* has both adjoints" false as
         written, the two f^*'s being different objects.  The rejection
         is pinned as the probe's conversion negative 1.

         THE UNIT AND COUNIT ARE THE TWO INCLUSIONS ON THE NOSE.
         [forall_unit_incl] and [forall_counit_incl] are Mac Lane's
         [X <= P_# P^* X] and [P^* P_# S <= S] written as terms, and
         [adj_unit_is_forall_incl] / [adj_counit_is_forall_incl] identify
         the adjunction's OWN [unit] and [counit] with them at Leibniz
         [=].  That is STRICTLY BETTER than #382's corresponding
         [adj_unit_has_incl_type], which is an ascription only; that
         file's note (:461-:467) explains why -- its four donor lemmas
         are [Qed] -- and predicts the strict form would hold were they
         [Defined].  Here every step is a [:=] term, so it does.  In a
         thin category an [≈] between parallel arrows is [True]
         (Instance/Powerset.v:317), so the Leibniz statement is the only
         informative one available.

    (B)  MAC LANE'S OWN SITE.  [ProdSetoid U V] is [product_obj] over
         [Sets_Cartesian] (measured: for [U V : SetoidObject@{o o}] the
         product is again a [SetoidObject@{o o}], which is what lets
         [Subsets] be formed on it), [proj_fst] is [exl], and his three
         displayed operations are written LITERALLY: [proj_exists S] with
         predicate [fun x => exists y, S (x, y)], [proj_forall S] with
         [fun x => forall y, S (x, y)], and
         [cylinder X := Powerset_Prop_preimage proj_fst X] with
         [cylinder_mem : cylinder X (x, y) = X x] at [eq_refl], which is
         his [P^* X = X x V].  [proj_exists] uses stdlib's Prop-valued
         [ex], not the library's Type-valued [∃]: the body [S (x, y)] is
         already a [Prop], so again no truncation is required -- the same
         measurement (A) makes from the other side.

         His two displayed biconditionals are [proj_exists_transpose] and
         [proj_forall_transpose], proved directly as [iffT]s;
         [proj_forall_largest] is his "the largest subset X of U such
         that the cylinder on X is wholly contained in S", and the file
         says plainly that it IS the second biconditional together with
         its unit rather than separate content.  [proj_galois_exists] and
         [proj_galois_forall] package the two as [GaloisConnection]s AT
         HIS FORMULAS.

         The identifications with (A) hold at [≈] and NOT at [eq_refl],
         and the cause is measured rather than guessed: [proj_exists] is
         an [ex] over [carrier V] while [Powerset_Prop_image proj_fst] is
         a [Powerset_squash] of a [sigT] over [carrier (ProdSetoid U V)],
         and [proj_forall] quantifies over [carrier V] where
         [Powerset_Prop_dual proj_fst] quantifies over
         [carrier (ProdSetoid U V)].  [proj_exists_is_image] and
         [proj_forall_is_dual] are the [≈] forms; both [eq_refl] forms
         are pinned as probe negatives.  [proj_maps_agree] records that
         the two Galois connections' three maps agree with (A)'s -- two
         at [≈], the cylinder at [eq_refl]; the RECORDS are not compared
         and no comparison of the two ADJUNCTIONS is claimed.

    (C)  BECK-CHEVALLEY for the reindexed projection, at LEIBNIZ [=] on
         the WHOLE SUBSET.  [cyl_reindex g] is [fun z => (g (fst z),
         snd z)], built by hand rather than through [split]/[bimap].
         [beck_chevalley_exists_mem] and [beck_chevalley_forall_mem] are
         the two membership [Prop]s, at [eq_refl] because the inverse
         image is precomposition; [beck_chevalley_exists] and
         [beck_chevalley_forall] are the whole subsets, also at
         [eq_refl]; and [beck_chevalley_exists_equiv]/[_forall_equiv] are
         the [≈] readings.  The whole-subset grade was NOT expected --
         the header first predicted the opposite -- and it deserves its
         reason: [SetoidMorphism] has primitive projections with eta, so
         record equality is field equality, and the [proper_morphism]
         certificate is NOT irrelevant (two arbitrary proofs of one such
         [Proper] statement do not convert, measured out of tree).  What
         happens is that the two certificates genuinely converge, because
         [cyl_reindex] reduces at a literal pair and its own certificate
         projects the pair of hypotheses, which is exactly what the other
         side feeds to [S]'s certificate.

    (D)  AWODEY §9.6.  [dual_image_preserves_meets] is direct;
         [dual_image_preserves_meets_via_galois] is [gal_r_preserves_glb]
         at [preimage_dual_galois] (no adapter: [gal_r] of that
         connection IS the dual image), and
         [dual_image_meet_routes_agree] is the #382-style pair showing
         the two inhabit one type.  #382's
         [inverse_image_preserves_joins] (:700) is re-derived as the
         COROLLARY [inverse_image_preserves_joins_via_galois] -- that
         file proved it directly and its comment (:694-:697) says why: it
         needed f^*'s right adjoint, which is this file's -- with
         [inverse_image_join_routes_agree] beside it.  #382's
         [direct_image_preserves_joins] (:678) is cited, not restated.

         THE CONTRAPOSITIVES ARE THEOREMS ABOUT ADJUNCTIONS, not prose.
         [exists_not_right_adjoint] and [forall_not_left_adjoint] refute
         the EXISTENCE of an adjoint on the wrong side at
         [powerset_const0], by feeding #380's [GaloisOfAdjunction] to the
         (A0) preservation lemmas and contradicting a concrete refutation:
         #382's [direct_image_not_meet_preserving] (:884) for the first,
         and the new [dual_image_not_join_preserving] for the second.
         [∃] is the library's Type-valued [sigT] and each sigma binds the
         functor once.

    (E)  RIEHL 4.1.9 AND EXERCISE 4.1.ii.  In this tree a predicate on X
         IS an element of [Powerset_Prop_obj X]: [predicates_are_subsets]
         and [pointwise_is_subset_le] record both readings at [eq_refl],
         so Riehl's [Omega^X] under the pointwise order is [Subsets X] on
         the nose and her Exercise 4.1.ii is DEFINITIONAL here.  No
         functor category [[X, Omega]] is formed and none could be: X is
         a setoid, not a category, and a discrete category on its carrier
         would discard [≈].  That is the honest reading, not a shortcut.

         The triple over the unique map [X -> 1] is
         [Delta_X := InverseImage (quant_bang X)], [exists_X], [forall_X]
         and the two adjunctions INSTANTIATED ([:=] with no tactic),
         which is exactly "4.1.9 is 4.1.8 at [X -> 1]";
         [Delta_X_obj_mem] reads the constant predicate back at
         [eq_refl].  The truth-value object is [Subsets quant_one], and
         **[subsets_one_Props : Subsets quant_one ≅[Cat] Props]**
         identifies it with Instance/Props.v's [Props].  Read its
         strength: [≅[Cat]] in this library is EQUIVALENCE, [Cat]'s
         hom-setoid being [Functor_Setoid]; an isomorphism OF CATEGORIES
         is unavailable, the two object types being different, and none
         is claimed.

    (F)  SEVEN SKETCHES 1.117 AND AWODEY 9.12, in their own words.
         [apples_buckets_bicondition] is the biconditional
         [f^*(B') subseteq A' <-> B' subseteq f_*(A')] as an [iffT] over
         the two transposes, and [dual_vacuous] is "empty buckets count":
         a bucket with no apples at all lies in the dual image of every
         subset.

    (G)  NON-VACUITY, over #382's own [powerset_fin2] / [powerset_const0]
         / [powerset_sng1] and Instance/Powerset.v's [powerset_sng0],
         reused rather than rebuilt.  Every negative reaches [False] by
         eliminating a [Powerset_squash] into it or by [discriminate] on
         the discrete carrier -- never by an induction over a quotienting
         relation, which could not yield a negative.
         [dual_const0_sng0_at_1] and [dual_const0_sng0_not_at_0] compute
         the dual image of {0}, and [exists_ne_forall_at_const0] proves
         the two adjoints DIFFER at one input, which is the whole point
         of the third leg.  Over the projection,
         [proj_diag_exists_everywhere] and [proj_diag_forall_nowhere]
         evaluate Mac Lane's two operations at the diagonal, and
         [proj_row_forall_at_0] / [proj_row_forall_not_at_1] at a row.

    ** A CORRECTION TO THE BRIEF, MEASURED

    The brief predicted the dual image of {0} along the constant map at 0
    to be EMPTY, "because each fibre is the whole two-point set".  That
    is false, and the file proves the opposite: the fibre over 1 is
    EMPTY, so 1 lies in the dual image of EVERY subset, vacuously --
    which is exactly Fong-Spivak's "empty buckets count".  Only the fibre
    over 0 is the whole set.  So the dual image of {0} is {1}, not the
    empty set, and [dual_const0_sng0_at_1] proves it.  The conclusion the
    prediction was meant to support -- that the dual image does not
    preserve joins -- stands, and is witnessed at the element 0 instead.

    ** WHAT IS NOT DELIVERED

    No dual-image adjunction for Instance/FinSet/Subsets.v's
    [finpow_dual] (finite codes); that file's evaluations are cited and
    its adjunction is left open.  No slice-level
    [Sigma_f -| f^* -| Pi_f] (#387).  No hyperdoctrine, no
    Beck-Chevalley for a general pullback square (only the projection's
    reindexing along [g x id]), and no Frobenius reciprocity.  No
    naturality of any identification in [f], in [g] or in the setoid.  No
    comparison of [proj_galois_exists] with [image_preimage_galois] at
    the RECORD level, and none of the two adjunctions at any level.  No
    idempotent monad or comonad from either adjunction.  No Boolean
    connectives (#383).  No antisymmetric quotient, so two [≈]-equal
    subsets remain distinct objects, exactly as Instance/Powerset.v
    discloses for its own category.  Nothing is registered as an
    [Instance].

    ** AN ENGINEERING FINDING

    [Coq.Classes.Equivalence] and [Coq.Relations.Relation_Definitions]
    have to be imported AFTER [Category.Lib], because [Proset] and
    [GaloisConnection] want the stdlib Prop-valued [PreOrder] and
    [relation] rather than the [crelation] ones the library exports --
    Instance/Powerset.v:25-27 says so and this file copies it.  What that
    costs, and what the donor never had to pay because it writes no
    explicit [equiv], is that stdlib's [equiv] then SHADOWS
    [Category.Lib.Setoid.equiv].  Two consequences, both measured: an
    explicit [@equiv _ (is_setoid Y)] is rejected with "The term
    'is_setoid Y' has type 'Setoid Y' while it is expected to have type
    'relation ?A'", so every explicit occurrence here is written
    [@Category.Lib.Setoid.equiv]; and a bare [reflexivity] in TERM
    position is rejected with "Cannot infer the implicit parameter
    Reflexive", so the term-mode occurrences go through [quant_refl].
    The [≈] NOTATION is unaffected -- a notation resolves its head
    reference when it is declared -- and in TACTIC position the goal
    disambiguates, which is why the donors' bare [reflexivity] works
    there and is left alone.

    ** A DONOR RESTATED RATHER THAN REQUIRED, ON A MEASUREMENT

    [subset_le_antisym] -- mutual inclusion gives [≈] -- already exists,
    at Instance/Grp/Galois.v:508, with this file's exact statement and
    proof term.  It is NOT required: that module's transitive closure is
    129 modules against this file's 89, so importing it for a one-line
    definition would nearly double the cost.  The single place this file
    needs it, inside [exists_not_right_adjoint], writes the term
    [fun x => conj (H1 x) (H2 x)] inline instead, with no new name and
    hence no third homonym in the `make print-assumptions` scope.

    ** UNIVERSES

    Every constant touching a power set is at one level [o] with
    [Set < o], INHERITED from [Powerset_Prop_obj]'s codomain
    [Powerset_Prop_truth], whose carrier is [Prop : Type@{Set+1}].  The
    binder shape [X Y : SetoidObject@{o o}] is likewise the DONORS'
    identification and not one introduced here: [Powerset_Prop_obj@{o}]
    is the first to impose it, and [subset_le], [subset_le_preorder] and
    [Subsets] each impose it independently, so no one of them is "the"
    cause.  Section (B) additionally uses [product_obj] over
    [Sets_Cartesian], measured to land at [SetoidObject@{o o}] again.
    Measured over all 100 constants: NO block contains a universe
    EQUATION, and exactly 17 blocks are free of [Set] -- [quant_refl],
    the whole of (A0) ([proset_adjunction_at] with its six obligations,
    [gal_r_preserves_glb], [gal_l_preserves_lub]), and the seven
    constants that mention [Sets] but no power set ([ProdSetoid],
    [proj_fst], [proj_fst_computes], [cyl_reindex], [quant_one],
    [quant_bang], [quant_sq]).  The (A0) three are free because they
    mention no setoid at all, their blocks carrying only stdlib bounds.
    The RAPL/LAPC [Set] pin Instance/Powerset.v discloses is NOT
    inherited: nothing here routes through [Proset_Limit] or
    [DiscreteCat_Functor], and every [Set] token above is the LOWER
    bound [Set < o].

    ** CLOSURE

    89 transitive in-project dependencies, excluding this file, measured
    with coqdep given _CoqProject's list plus both new files.
    Instance/Powerset.v's own closure is 87 of the 89, so it dominates;
    per-Require MARGINAL costs, measured by dropping each in turn, are
    Instance/Powerset.v 2, Instance/Sets/Cartesian.v 1, and
    Instance/Cat.v, Instance/Props.v, Structure/Cartesian.v,
    Structure/Terminal.v, Instance/Proset/Limit.v and
    Theory/Isomorphism.v 0 each -- all six already lying inside the
    others' closures, which is why (E) can be packaged as [≅[Cat]] for
    nothing.

    ** TRANSPARENCY

    Eight proofs close with [Defined] (counted by token, inline ones
    included), and SIX are LOAD-BEARING, measured by flipping each one to
    [Qed] in a scratch copy and recompiling: [Powerset_Prop_dual],
    [proj_exists], [proj_forall], [cyl_reindex], [diag_subset] and
    [row0_subset] -- each one's predicate must reduce for the [eq_refl]
    readbacks, for the [destruct]s in the transposes, or for the witness
    computations.  The other two are NOT: [quant_refl] and the
    written-out obligation of [subsets_one_Props] (it raises two; the
    default tactic closes the other) each compile as [Qed], and they
    stay [Defined] because both produce DATA.  [quant_refl] is worth
    a word: the [eq_refl] identifications of the unit and the counit
    survive its being opaque, because [forall_counit_incl] and
    [preimage_transpose_from] both apply THE SAME term
    [quant_refl (f x)], so conversion never has to look inside it.  The
    21 remaining proofs are [Qed] and every other constant is a [:=]
    term.

    ** REGISTRATION

    Nothing here is an [Instance]: a chosen adjoint must not become
    globally resolvable, which is Instance/Powerset.v's and
    Instance/Proset/Limit.v's own convention. *)

(* ------------------------------------------------------------------------ *)
(** ** (A0) General constants, and one engineering helper *)

(* Reflexivity of a setoid's own [≈], as a TERM.  It has to be written
   out: [Coq.Classes.Equivalence] is imported above, so a bare
   [reflexivity] in TERM position cannot choose between stdlib's
   Prop-valued [Reflexive] and the [crelation] one this library uses.  In
   TACTIC position the goal disambiguates and the donors' bare
   [reflexivity] works, which is why only the term-mode occurrences below
   go through this. *)
Definition quant_refl@{o} {A : SetoidObject@{o o}} (a : carrier A) :
  @Category.Lib.Setoid.equiv _ (is_setoid A) a a.
Proof. reflexivity. Defined.

(* An adjunction between preorders AT TWO GIVEN FUNCTORS.  #380's
   [GaloisAdjunction] produces its two functors itself, so it cannot
   state an adjunction whose left functor was built earlier and
   elsewhere -- which is exactly the situation of the headline below,
   where the left functor is #382's [InverseImage].  All six obligations
   -- two [Proper] certificates, two isomorphism laws in [Sets], two
   naturality clauses -- are equations between parallel arrows in a thin
   category, so [Program]'s default tactic closes them. *)
Program Definition proset_adjunction_at {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA)
  (tr : ∀ a b, RB (fobj[F] a) b → RA a (fobj[U] b))
  (tl : ∀ a b, RA a (fobj[U] b) → RB (fobj[F] a) b)
  : F ⊣ U :=
  Build_Adjunction' (F:=F) (U:=U)
    (fun a b => {| to   := {| morphism := tr a b |}
                 ; from := {| morphism := tl a b |} |}) _ _.

(* Right adjoints preserve meets, at the level of the order: Seven
   Sketches Proposition 1.111, Riehl §4.6.3's right-adjoint half. *)
Definition gal_r_preserves_glb {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → B) (m : B) (H : IsGLB RB d m) :
  IsGLB RA (fun i => gal_r G (d i)) (gal_r G m) :=
  (fun i => gal_mono_r G (fst H i),
   fun n Hn => gal_to G n m
                 (snd H (gal_l G n)
                    (fun i => gal_from G n (d i) (Hn i)))).

(* Left adjoints preserve joins.  [IsLUB R] IS [IsGLB (op_rel R)], so the
   statement is the dual read at the reversed preorder; the term is
   nevertheless written out, its two clauses using [gal_to] and
   [gal_from] in the mirror order. *)
Definition gal_l_preserves_lub {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB RA d m) :
  IsLUB RB (fun i => gal_l G (d i)) (gal_l G m) :=
  (fun i => gal_mono_l G (fst H i),
   fun n Hn => gal_from G m n
                 (snd H (gal_r G n)
                    (fun i => gal_to G (d i) n (Hn i)))).

(* ------------------------------------------------------------------------ *)
(** ** (A) The dual image, and the right adjunction *)

(* Awodey's [f_*(U) = {b | f^{-1}(b) subseteq U}], Riehl's [f_!],
   Fong-Spivak's [f_*], Mac Lane's [P_#].  NO truncation: a [forall]
   landing in [Prop] is a [Prop] whatever it quantifies over.
   Respectfulness in [y] transports [f x ≈ y'] back to [f x ≈ y] through
   symmetry and transitivity. *)
Definition Powerset_Prop_dual@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, ∀ x : carrier X,
               @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x) _).
  intros y y' Hyy'; split; intros H x Hfx; apply H.
  - now transitivity y'.
  - transitivity y; [ exact Hfx | now symmetry ].
Defined.

Section Dual.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* Membership, on the nose.  An equality of [Prop]s, not of morphisms. *)
Example dual_mem (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier Y) :
  Powerset_Prop_dual@{o} f S y
    = (∀ x : carrier X,
         @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x)
  := eq_refl.

(* Riehl §4.5's [Delta_f p := p f] IS the inverse image, on the nose:
   again an equality of [Prop]s. *)
Example preimage_is_precompose (T : carrier (Powerset_Prop_obj@{o} Y))
  (x : carrier X) :
  Powerset_Prop_preimage@{o} f T x = T (f x) := eq_refl.

(* The dual image is order-preserving. *)
Definition dual_monotone (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le S T) :
  subset_le (Powerset_Prop_dual@{o} f S) (Powerset_Prop_dual@{o} f T) :=
  fun y Hy x Hfx => H x (Hy x Hfx).

(* Mac Lane's second displayed line at a general [f], left to right: from
   [f^* T <= S] infer [T <= forall_f S].  This is where [T]'s own
   respectfulness is spent -- the hypothesis gives [S x] only at points
   of the inverse image, and [f x ≈ y] is what carries [T y] there. *)
Definition preimage_transpose_to (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le (Powerset_Prop_preimage@{o} f T) S) :
  subset_le T (Powerset_Prop_dual@{o} f S) :=
  fun y Hy x Hfx =>
    H x (proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy).

(* ... and right to left.  Evaluating the dual image at [f x] against the
   reflexivity witness is the whole argument. *)
Definition preimage_transpose_from (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le T (Powerset_Prop_dual@{o} f S)) :
  subset_le (Powerset_Prop_preimage@{o} f T) S :=
  fun x Hx => H (f x) Hx x (quant_refl (f x)).

(* THE GALOIS CONNECTION, all six fields by name. *)
Definition preimage_dual_galois :
  GaloisConnection (@subset_le@{o} Y) (@subset_le@{o} X) :=
  {| gal_l := Powerset_Prop_preimage@{o} f
   ; gal_r := Powerset_Prop_dual@{o} f
   ; gal_mono_l := preimage_monotone f
   ; gal_mono_r := dual_monotone
   ; gal_to   := preimage_transpose_to
   ; gal_from := preimage_transpose_from |}.

(* The dual-image functor: #380's [GaloisFunctor_r] applied. *)
Definition DualImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_r (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    preimage_dual_galois.

(** *** The two pinned adjunctions *)

(* #382's, under this issue's name.  A [:=] with no tactic, so "the
   existential IS the direct image" is definitional at a general [f]. *)
Definition exists_substitution_adjunction : DirectImage f ⊣ InverseImage f :=
  image_preimage_adjunction f.

(* THE HEADLINE.  Stated at #382's [InverseImage f], not at a second
   preimage functor: see the header. *)
Definition substitution_forall_adjunction : InverseImage f ⊣ DualImage :=
  proset_adjunction_at (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage preimage_transpose_to preimage_transpose_from.

(* Mac Lane's "P^*, which is the inverse image operation, has both a left
   adjoint P_* and a right adjoint P_#", packaged.  [*] is [prod]: both
   components are data. *)
Definition quantifier_triple :
  (DirectImage f ⊣ InverseImage f) * (InverseImage f ⊣ DualImage) :=
  (exists_substitution_adjunction, substitution_forall_adjunction).

(** *** Readbacks *)

Example dual_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DualImage] S = Powerset_Prop_dual@{o} f S := eq_refl.

Example exists_adj_is_image_preimage :
  exists_substitution_adjunction = image_preimage_adjunction f := eq_refl.

(* #380's backward passage returns the connection this section supplied,
   at Leibniz [=] on the WHOLE record: [GaloisOfAdjunction] reads its six
   fields off the two functors and the hom-set isomorphism, and all of
   those were built from those very fields. *)
Example dual_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage substitution_forall_adjunction
  = preimage_dual_galois := eq_refl.

(** *** The unit and the counit ARE the two inclusions *)

(* Mac Lane's [X <= P_# P^* X], written directly. *)
Definition forall_unit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le T
    (Powerset_Prop_dual@{o} f (Powerset_Prop_preimage@{o} f T)) :=
  fun y Hy x Hfx => proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy.

(* Mac Lane's [P^* P_# S <= S]. *)
Definition forall_counit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_dual@{o} f S)) S :=
  fun x Hx => Hx x (quant_refl (f x)).

(* And the adjunction's OWN unit and counit ARE those two, at Leibniz
   [=].  This is the strict form Instance/Powerset.v:462-467 predicts for
   its own adjunction and declines to ship; here every step is a term, so
   it holds. *)
Example adj_unit_is_forall_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) DualImage substitution_forall_adjunction T
    = forall_unit_incl T := eq_refl.

Example adj_counit_is_forall_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) DualImage substitution_forall_adjunction S
    = forall_counit_incl S := eq_refl.

(** *** (F) Seven Sketches 1.117 and Awodey 9.12, in their own words *)

(* "B' subset f_!(A') if and only if f^{-1}(B') subset A'" -- Riehl's own
   phrasing of Example 4.1.8's second half, which is also Awodey's
   "as we also leave for the reader to verify".  [iffT] is the library's
   Type-valued biconditional. *)
Definition apples_buckets_bicondition
  (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  iffT (subset_le (Powerset_Prop_preimage@{o} f T) S)
       (subset_le T (Powerset_Prop_dual@{o} f S)) :=
  (preimage_transpose_to T S, preimage_transpose_from T S).

(* "if a bucket doesn't contain any apples at all, then vacuously all its
   apples are from A', so empty buckets count". *)
Definition dual_vacuous (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y)
  (Hy : ∀ x : carrier X,
          @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → False) :
  Powerset_Prop_dual@{o} f S y :=
  fun x Hfx => match Hy x Hfx with end.

(** *** (D) Awodey §9.6: what each adjoint preserves *)

(* The dual image preserves meets, directly: the second clause is the
   transpose of the family's own second clause. *)
Theorem dual_image_preserves_meets {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m).
Proof.
  split.
  - intro i; exact (dual_monotone m (S i) (fst H i)).
  - intros n Hn.
    refine (preimage_transpose_to n m _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (preimage_transpose_from n (S i) (Hn i)).
Qed.

(* The same statement read off (A0).  [gal_r preimage_dual_galois] IS the
   dual image, so the general lemma applies with no adapter. *)
Definition dual_image_preserves_meets_via_galois {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m) :=
  gal_r_preserves_glb preimage_dual_galois S m H.

(* The two routes inhabit ONE type: the pair typechecks. *)
Definition dual_image_meet_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m)
  * IsGLB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_dual@{o} f (S i))
      (Powerset_Prop_dual@{o} f m) :=
  (dual_image_preserves_meets S m H,
   dual_image_preserves_meets_via_galois S m H).

(* Instance/Powerset.v:700 proved this DIRECTLY, and its comment
   (:694-:697) says why: the adjoint route needs f^*'s right adjoint,
   which is this file's.  Here it is, as that corollary. *)
Definition inverse_image_preserves_joins_via_galois {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  gal_l_preserves_lub preimage_dual_galois T m H.

Definition inverse_image_join_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsLUB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_joins f T m H,
   inverse_image_preserves_joins_via_galois T m H).

End Dual.

Arguments dual_monotone {X Y} f S T H.
Arguments preimage_transpose_to {X Y} f T S H.
Arguments preimage_transpose_from {X Y} f T S H.
Arguments preimage_dual_galois {X Y} f.
Arguments DualImage {X Y} f.
Arguments exists_substitution_adjunction {X Y} f.
Arguments substitution_forall_adjunction {X Y} f.
Arguments quantifier_triple {X Y} f.
Arguments forall_unit_incl {X Y} f T.
Arguments forall_counit_incl {X Y} f S.
Arguments apples_buckets_bicondition {X Y} f T S.
Arguments dual_vacuous {X Y} f S y Hy.
Arguments dual_image_preserves_meets {X Y} f {Idx} S m H.

(* ------------------------------------------------------------------------ *)
(** ** (B) Mac Lane's site: the first projection U x V -> U *)

(* The product setoid.  Measured: for [U V : SetoidObject@{o o}] this is
   again a [SetoidObject@{o o}], which is what lets [Subsets] be formed
   on it. *)
Definition ProdSetoid@{o so} (U V : SetoidObject@{o o}) : SetoidObject@{o o} :=
  @product_obj Sets@{o so} Sets_Cartesian U V.

(* Mac Lane's [P : U x V -> U]. *)
Definition proj_fst@{o so} (U V : SetoidObject@{o o}) :
  ProdSetoid@{o so} U V ~{Sets@{o so}}~> U :=
  @exl Sets@{o so} Sets_Cartesian U V.

(* [P_* S = {x | exists y, y in V and <x,y> in S}].  The existential is
   stdlib's Prop-valued [ex], NOT the library's Type-valued [∃]: the body
   [S (x, y)] is already a [Prop], so no truncation is needed -- the
   mirror image of the measurement (A) makes for the dual image. *)
Definition proj_exists@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun y : carrier V => S (x, y))) _).
  intros x x' Hxx'; split; intros Hy; destruct Hy as [y Hy]; exists y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
Defined.

(* [P_# S = {x | forall y, y in V implies <x,y> in S}]. *)
Definition proj_forall@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ y : carrier V, S (x, y)) _).
  intros x x' Hxx'; split; intros H y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
Defined.

(* [P^* X], which Mac Lane calls the cylinder [X x V] over the base X. *)
Definition cylinder@{o so} {U V : SetoidObject@{o o}}
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)) :=
  Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs.

Section Projection.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).

Example proj_fst_computes (x : carrier U) (y : carrier V) :
  proj_fst@{o so} U V (x, y) = x := eq_refl.

(* The cylinder over X contains exactly the pairs whose first component
   lies in X: an equality of [Prop]s, on the nose. *)
Example cylinder_mem (Xs : carrier (Powerset_Prop_obj@{o} U))
  (x : carrier U) (y : carrier V) :
  @cylinder@{o so} U V Xs (x, y) = Xs x := eq_refl.

(** *** Mac Lane's two displayed biconditionals *)

(* [S <= P^* X <=> P_* S <= X]. *)
Theorem proj_exists_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le S (@cylinder@{o so} U V Xs))
       (subset_le (@proj_exists@{o so} U V S) Xs).
Proof.
  split.
  - intros H x Hx; destruct Hx as [y Hy]; exact (H (x, y) Hy).
  - intros H z Hz; destruct z as [x y]; exact (H x (ex_intro _ y Hz)).
Qed.

(* [P^* X <= S <=> X <= P_# S]. *)
Theorem proj_forall_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le (@cylinder@{o so} U V Xs) S)
       (subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - intros H x Hx y; exact (H (x, y) Hx).
  - intros H z Hz; destruct z as [x y]; exact (H x Hz y).
Qed.

(* "P_# S is the largest subset X of U such that the cylinder on X is
   wholly contained in S".  This IS [proj_forall_transpose] together with
   its unit -- the two components are that biconditional read at
   [Xs := proj_forall S] and at an arbitrary [Xs] -- and is stated
   separately only because Mac Lane states it separately. *)
Theorem proj_forall_largest
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  subset_le (@cylinder@{o so} U V (@proj_forall@{o so} U V S)) S
  * (∀ Xs : carrier (Powerset_Prop_obj@{o} U),
       subset_le (@cylinder@{o so} U V Xs) S
       → subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - exact (snd (proj_forall_transpose S (@proj_forall@{o so} U V S))
             (fun x Hx => Hx)).
  - intros Xs H; exact (fst (proj_forall_transpose S Xs) H).
Qed.

(** *** The two Galois connections at Mac Lane's own formulas *)

Definition proj_exists_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_exists@{o so} U V S) (@proj_exists@{o so} U V T) :=
  fun x Hx =>
    match Hx with ex_intro _ y Hy => ex_intro _ y (H (x, y) Hy) end.

Definition proj_forall_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_forall@{o so} U V S) (@proj_forall@{o so} U V T) :=
  fun x Hx y => H (x, y) (Hx y).

Definition cylinder_monotone
  (Xs Ys : carrier (Powerset_Prop_obj@{o} U)) (H : subset_le Xs Ys) :
  subset_le (@cylinder@{o so} U V Xs) (@cylinder@{o so} U V Ys) :=
  preimage_monotone (proj_fst@{o so} U V) Xs Ys H.

Definition proj_galois_exists :
  GaloisConnection (@subset_le@{o} (ProdSetoid@{o so} U V))
                   (@subset_le@{o} U) :=
  {| gal_l := @proj_exists@{o so} U V
   ; gal_r := @cylinder@{o so} U V
   ; gal_mono_l := proj_exists_monotone
   ; gal_mono_r := cylinder_monotone
   ; gal_to   := fun S Xs H => snd (proj_exists_transpose S Xs) H
   ; gal_from := fun S Xs H => fst (proj_exists_transpose S Xs) H |}.

Definition proj_galois_forall :
  GaloisConnection (@subset_le@{o} U)
                   (@subset_le@{o} (ProdSetoid@{o so} U V)) :=
  {| gal_l := @cylinder@{o so} U V
   ; gal_r := @proj_forall@{o so} U V
   ; gal_mono_l := cylinder_monotone
   ; gal_mono_r := proj_forall_monotone
   ; gal_to   := fun Xs S H => fst (proj_forall_transpose S Xs) H
   ; gal_from := fun Xs S H => snd (proj_forall_transpose S Xs) H |}.

(** *** The identifications with (A), and their exact grade *)

(* "Also P_* S is the direct image of S under the projection P."  At [≈]
   and NOT at [eq_refl]: [proj_exists] is an [ex] over [carrier V] while
   [Powerset_Prop_image proj_fst] is a [Powerset_squash] of a [sigT] over
   [carrier (ProdSetoid U V)].  The [eq_refl] form is pinned in
   Test/ProbeQuantifier384.v. *)
Theorem proj_exists_is_image
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_exists@{o so} U V S
    ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intro Hx; destruct Hx as [y Hy].
    apply Powerset_squash_intro@{o}; exists (x, y); split;
      [ exact Hy | reflexivity ].
  - intro H; refine (H (ex (fun y : carrier V => S (x, y))) _).
    intros Hz; destruct Hz as [z [Hz Hex]]; exists (snd z).
    refine (proj1 (@proper_morphism _ _ _ _ S z (x, snd z) _) Hz).
    exact (Hex, quant_refl (snd z)).
Qed.

(* And [P_#] is the dual image along the same projection, again at [≈]:
   [proj_forall] quantifies over [carrier V], the dual image over
   [carrier (ProdSetoid U V)]. *)
Theorem proj_forall_is_dual
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_forall@{o so} U V S
    ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intros H z Hz.
    exact (proj2 (@proper_morphism _ _ _ _ S z (x, snd z)
                    (Hz, quant_refl (snd z))) (H (snd z))).
  - intros H y; exact (H (x, y) (quant_refl x)).
Qed.

(* The two Galois connections' three maps agree with (A)'s.  The RECORDS
   are not compared, and no comparison of the two adjunctions is
   claimed. *)
Definition proj_maps_agree
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  (gal_l proj_galois_exists S
     ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_forall S
       ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_exists Xs
       = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs) :=
  ((proj_exists_is_image S, proj_forall_is_dual S), eq_refl).

End Projection.

(* ------------------------------------------------------------------------ *)
(** ** (C) Beck-Chevalley for the reindexed projection *)

(* [g x id], written out rather than assembled from [split]/[bimap].
   Declared at top level, as the donors declare [Powerset_Prop_image] and
   [Powerset_Prop_preimage], so that [g] occurs explicitly in every
   statement below and no [Proof using] clause is needed. *)
Definition cyl_reindex@{o so} {U U' : SetoidObject@{o o}}
  (V : SetoidObject@{o o}) (g : U' ~{Sets@{o so}}~> U) :
  ProdSetoid@{o so} U' V ~{Sets@{o so}}~> ProdSetoid@{o so} U V.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (ProdSetoid@{o so} U' V)) (is_setoid (ProdSetoid@{o so} U' V))
       (carrier (ProdSetoid@{o so} U V)) (is_setoid (ProdSetoid@{o so} U V))
       (λ z, (g (fst z), snd z)) _).
  intros z z' Hzz'; split.
  - exact (proper_morphism g _ _ (fst Hzz')).
  - exact (snd Hzz').
Defined.

Section BeckChevalley.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).

(* Both squares commute POINTWISE ON THE NOSE: the inverse image is
   precomposition, so the two membership [Prop]s beta-iota-reduce to the
   same thing.  These are equalities of [Prop]s, not of morphisms. *)
Example beck_chevalley_exists_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

Example beck_chevalley_forall_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S) x
    = @proj_forall@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

(* And at WHOLE-SUBSET Leibniz equality too, which is stronger than the
   pointwise form and than [≈].  It was not expected, and what is
   measured is kept apart from what is explained.  Measured:
   [SetoidMorphism] has primitive projections with eta, so record
   equality IS field equality, and the [proper_morphism] certificate is
   NOT irrelevant (two arbitrary proofs of one such [Proper] statement do
   NOT convert -- out of tree).  Hence a typechecking [eq_refl] here
   forces BOTH fields to converge, certificates included.  Explained,
   not measured: they converge because [cyl_reindex] reduces
   [(g (fst z), snd z)] at a literal pair and its own certificate
   projects the pair of hypotheses, which is what the other side feeds
   to [S]'s certificate.  The one experiment available -- flipping
   [cyl_reindex] to [Qed] -- breaks all SIX Beck-Chevalley statements at
   once (the two pointwise [Prop] equalities, these two, and both [≈]
   readings), so it shows transparency of [cyl_reindex] is load-bearing
   for every one of them and isolates nothing about the certificates. *)
Example beck_chevalley_exists
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

Example beck_chevalley_forall
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    = @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

(* The [≈] readings, for a consumer who wants the order-theoretic form. *)
Theorem beck_chevalley_exists_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    ≈ @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

Theorem beck_chevalley_forall_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    ≈ @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

End BeckChevalley.

(* ------------------------------------------------------------------------ *)
(** ** (E) Riehl 4.1.9, and Exercise 4.1.ii *)

(* A predicate on X in Riehl's sense IS an element of the power set here.
   Both readings are equalities of TYPES and of [Prop]s. *)
Example predicates_are_subsets@{o} (X : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} X)
    = SetoidMorphism@{o o o} X Powerset_Prop_truth@{o} := eq_refl.

Example pointwise_is_subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  @subset_le@{o} X S T = (∀ x : carrier X, S x → T x) := eq_refl.

(* The one-point setoid, and the unique map into it.  Named locally: both
   [SetsOne] (Construction/Elements.v:230, Instance/Sets/Pointed/
   Coslice.v:70) and [Sets_Terminal] are taken. *)
Definition quant_one@{o so} : SetoidObject@{o o} :=
  @terminal_obj Sets@{o so} Sets_Terminal.

Definition quant_bang@{o so} (X : SetoidObject@{o o}) :
  X ~{Sets@{o so}}~> quant_one@{o so} :=
  @one Sets@{o so} Sets_Terminal X.

Section Riehl.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(* Riehl's [Delta_X], [exists_X] and [forall_X], as the three functors of
   Example 4.1.8 at the unique map [X -> 1].  That instantiation IS her
   Exercise 4.1.ii. *)
Definition Delta_X : Subsets@{o u} quant_one@{o so} ⟶ Subsets@{o u} X :=
  InverseImage (quant_bang@{o so} X).

Definition exists_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DirectImage (quant_bang@{o so} X).

Definition forall_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DualImage (quant_bang@{o so} X).

(* [exists_X -| Delta_X -| forall_X], both legs by instantiation. *)
Definition riehl_exists_delta : exists_X ⊣ Delta_X :=
  exists_substitution_adjunction (quant_bang@{o so} X).

Definition riehl_delta_forall : Delta_X ⊣ forall_X :=
  substitution_forall_adjunction (quant_bang@{o so} X).

Definition riehl_adjoint_triple :
  (exists_X ⊣ Delta_X) * (Delta_X ⊣ forall_X) :=
  (riehl_exists_delta, riehl_delta_forall).

(* [Delta_X] is her constant functor: its value at [P] is the predicate
   constantly [P ttt].  An equality of [Prop]s, on the nose. *)
Example Delta_X_obj_mem
  (P : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) (x : carrier X) :
  fobj[Delta_X] P x = P ttt := eq_refl.

End Riehl.

(** *** The truth-value object: [Subsets 1] against [Props] *)

Section TruthValues.

Universe o so u.
Constraint o < so.

(* Evaluation at the point.  Functoriality is free: [Props] is thin. *)
Program Definition subsets_one_to_Props :
  Subsets@{o u} quant_one@{o so} ⟶ Props@{o u} := {|
  fobj := fun S => S ttt;
  fmap := fun S T (h : subset_le S T) => h ttt
|}.

(* The constant predicate on the one-point setoid.  Its respectfulness
   certificate is written out as a term rather than left to instance
   resolution: Theory/Universal/Element.v records that resolving
   [proper_morphism] for a [Sets]-morphism out of a concrete one-point
   setoid pins the carrier universe at [Set], and the pointwise term
   avoids the resolution entirely. *)
Program Definition Props_to_subsets_one :
  Props@{o u} ⟶ Subsets@{o u} quant_one@{o so} := {|
  fobj := fun P =>
    @Build_SetoidMorphism@{o o o}
      (carrier quant_one@{o so}) (is_setoid quant_one@{o so})
      Prop (is_setoid Powerset_Prop_truth@{o}) (λ _, P)
      (fun _ _ _ => conj (fun p : P => p) (fun p : P => p));
  fmap := fun P Q (h : P → Q) => fun _ (p : P) => h p
|}.

(* Both round trips.  One is the identity on the nose at the level of
   [Prop]s; the other needs the point to be destructed. *)
Example Props_subsets_one_round (P : Props@{o u}) :
  fobj[subsets_one_to_Props] (fobj[Props_to_subsets_one] P) = P := eq_refl.

Theorem subsets_one_Props_round
  (S : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) :
  fobj[Props_to_subsets_one] (fobj[subsets_one_to_Props] S) ≈ S.
Proof. intro x; destruct x; split; intro H; exact H. Qed.

(* Riehl's Omega, up to equivalence.  [≅[Cat]] IS equivalence in this
   library ([Cat]'s hom-setoid is [Functor_Setoid]); an isomorphism OF
   CATEGORIES is unavailable, the object types differing, and none is
   claimed. *)
Program Definition subsets_one_Props :
  @Isomorphism Cat (Subsets@{o u} quant_one@{o so}) Props@{o u} := {|
  to   := subsets_one_to_Props;
  from := Props_to_subsets_one
|}.
Next Obligation.
  unshelve eexists.
  - intro S; unshelve econstructor.
    + exact (fun x Hx => proj1 (subsets_one_Props_round S x) Hx).
    + exact (fun x Hx => proj2 (subsets_one_Props_round S x) Hx).
    + exact I.
    + exact I.
  - intros S T h; exact I.
Defined.

End TruthValues.

(* ------------------------------------------------------------------------ *)
(** ** (D) again: Awodey's two contrapositives, at a concrete witness *)

(* The witnesses are #382's own: [powerset_fin2] (the two-element
   discrete setoid), [powerset_const0] (the constant map at 0),
   [powerset_sng1] = {1} and Instance/Powerset.v's [powerset_sng0] = {0}.
   None is rebuilt. *)

(* The dual image of {0} along the constant map at 0 contains 1 --
   VACUOUSLY, since nothing maps to 1.  This is Fong-Spivak's "empty
   buckets count", and it refutes the brief's prediction that this dual
   image is empty. *)
Theorem dual_const0_sng0_at_1@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o}
    (Fin.FS Fin.F1).
Proof. intros x Heq; discriminate Heq. Qed.

(* ... and does NOT contain 0: the fibre over 0 is the whole set, and 1
   is not in {0}. *)
Theorem dual_const0_sng0_not_at_0@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o} Fin.F1
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(* The direct image of {1} DOES contain 0.  This is
   Instance/Sets/Powerset/Universal.v's own [powerset_direct_sng1_at_0]
   read through [Powerset_Prop_fmap_image], not a second proof. *)
Definition image_const0_sng1_at_0@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o} Fin.F1 :=
  powerset_direct_sng1_at_0@{o so}.

(* THE TWO ADJOINTS DIFFER.  At {1} the existential contains 0 and the
   universal does not: the whole point of the third leg. *)
Theorem exists_ne_forall_at_const0@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}
    ≈ Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (proj1 (H Fin.F1) image_const0_sng1_at_0@{o so}
            Fin.F1 eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(* Every element of the two-point carrier lies in {0} join {1}: the
   exhaustiveness the join witness needs, by the [Fin.caseS']/[Fin.case0]
   idiom of Structure/Limit/Product/Finite.v:393-395. *)
Lemma fin2_in_sng0_join_sng1@{o +} (i : Fin.t 2%nat) :
  subset_join powerset_sng0@{o} powerset_sng1@{o} i.
Proof.
  pattern i; apply (Fin.caseS' i).
  - exists true; apply Powerset_squash_intro@{o}; reflexivity.
  - intro j; pattern j; apply (Fin.caseS' j).
    + exists false; apply Powerset_squash_intro@{o}; reflexivity.
    + intro k; apply (Fin.case0 (fun _ => _) k).
Qed.

(* THE DUAL IMAGE DOES NOT PRESERVE JOINS.  Stated as the refutation of
   the INCLUSION, which is what the contrapositive below consumes and
   which is strictly stronger than refuting the [≈]. *)
Theorem dual_image_not_join_preserving@{o so +} :
  subset_le
    (Powerset_Prop_dual@{o} powerset_const0@{o so}
       (subset_join powerset_sng0@{o} powerset_sng1@{o}))
    (subset_join
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  assert (Hin : Powerset_Prop_dual@{o} powerset_const0@{o so}
                  (subset_join powerset_sng0@{o} powerset_sng1@{o}) Fin.F1)
    by (intros x _; exact (fin2_in_sng0_join_sng1 x)).
  destruct (H Fin.F1 Hin) as [b Hb]; destruct b.
  - refine (Hb (Fin.FS Fin.F1) eq_refl False _);
      intro Heq; discriminate Heq.
  - refine (Hb Fin.F1 eq_refl False _); intro Heq; discriminate Heq.
Qed.

Theorem dual_image_not_join_preserving_equiv@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so}
      (subset_join powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_join
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  exact (dual_image_not_join_preserving (fun x => proj1 (H x))).
Qed.

(* Awodey: "Since this does not hold for exists x, it cannot be a right
   adjoint to some other 'quantifier'."  As a theorem about adjunctions:
   the direct image along [powerset_const0] has NO left adjoint.  [∃] is
   the library's Type-valued [sigT], and the sigma binds the functor
   once. *)
Theorem exists_not_right_adjoint@{o so u +} :
  (∃ L : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     L ⊣ DirectImage powerset_const0@{o so})
  → False.
Proof.
  intros [L Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               L (DirectImage powerset_const0@{o so}) Adj).
  pose (HG := gal_r_preserves_glb G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_meet powerset_sng0@{o} powerset_sng1@{o})
                (subset_inter_IsGLB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  (* The nontrivial inclusion, from the adjoint hypothesis. *)
  assert (Hge : subset_le
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))).
  { refine (snd HG _ _); intros [|].
    - exact (subset_meet_l _ _).
    - exact (subset_meet_r _ _). }
  (* ... and the trivial one, from monotonicity. *)
  assert (Hle : subset_le
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))).
  { refine (subset_meet_greatest _ _ _ _ _).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_l _ _)).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_r _ _)). }
  (* Mutual inclusion IS [≈] -- Instance/Grp/Galois.v:508's
     [subset_le_antisym], written inline for the measured reason in the
     header. *)
  exact (direct_image_not_meet_preserving
           (fun x => conj (Hle x) (Hge x))).
Qed.

(* And dually: "as above, forall x cannot be a left adjoint, since it
   does not have this property." *)
Theorem forall_not_left_adjoint@{o so u +} :
  (∃ R : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     DualImage powerset_const0@{o so} ⊣ R)
  → False.
Proof.
  intros [R Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               (DualImage powerset_const0@{o so}) R Adj).
  pose (HG := gal_l_preserves_lub G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_join powerset_sng0@{o} powerset_sng1@{o})
                (subset_union_IsLUB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  refine (dual_image_not_join_preserving _).
  refine (snd HG _ _); intros [|].
  - exact (subset_join_l _ _).
  - exact (subset_join_r _ _).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (G) Non-vacuity over Mac Lane's own site *)

(* Both factors are the two-element discrete setoid. *)
Definition quant_sq@{o so} : SetoidObject@{o o} :=
  ProdSetoid@{o so} powerset_fin2@{o} powerset_fin2@{o}.

Section ProjectionWitness.

Universe o so.
Constraint o < so.

(* The diagonal {(x, x)}. *)
Definition diag_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = snd z) _).
  intros z z' Hzz'; destruct Hzz' as [H1 H2]; split; intro H.
  - rewrite <- H1, <- H2; exact H.
  - rewrite H1, H2; exact H.
Defined.

(* The row {(0, y) | y}. *)
Definition row0_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = Fin.F1) _).
  intros z z' Hzz'; destruct Hzz' as [H1 _]; split; intro H.
  - rewrite <- H1; exact H.
  - rewrite H1; exact H.
Defined.

(* Mac Lane's projection of the diagonal is everything: every x pairs
   with itself. *)
Theorem proj_diag_exists_everywhere (x : Fin.t 2%nat) :
  @proj_exists@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x.
Proof. exists x; reflexivity. Qed.

(* ... while [P_#] of the diagonal is empty: no x pairs with EVERY y. *)
Theorem proj_diag_forall_nowhere (x : Fin.t 2%nat) :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x
  → False.
Proof.
  intro H.
  pose proof (H Fin.F1) as H0; pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  rewrite H0 in H1; discriminate H1.
Qed.

(* At a ROW, [P_#] is the singleton {0}: the row over 0 is full, the row
   over 1 is empty. *)
Theorem proj_row_forall_at_0 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    Fin.F1.
Proof. intro y; reflexivity. Qed.

Theorem proj_row_forall_not_at_1 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    (Fin.FS Fin.F1)
  → False.
Proof. intro H; pose proof (H Fin.F1) as H0; discriminate H0. Qed.

End ProjectionWitness.

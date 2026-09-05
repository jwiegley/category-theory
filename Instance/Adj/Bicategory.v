Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.

Generalizable All Variables.

(** * Adj is two-dimensional: horizontal composition of conjugate pairs *)

(* nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
   nLab: https://ncatlab.org/nlab/show/bicategory

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8,
   book p. 104 (PDF p. 113): Theorem 2, Exercise 1 and the closing
   remark; catalog ids maclane:IV.8:thm2, maclane:IV.8:ex1,
   maclane:IV.8:remark1.

   THEOREM 2, verbatim from the printed page:

     "Theorem 2. Given two conjugate pairs
        <sigma, tau> : <F,G,eta,eps> => <F',G',eta',eps'> : X -> A,
        <sigma-, tau-> : <F-,G-,eta-,eps-> => <F-',G-',eta-',eps-'> : A -> D
      the (horizontal) composite natural transformations sigma- sigma and
      tau tau- yield a conjugate pair sigma- sigma : F- F => F-' F',
      tau tau- : G' G-' => G G- of natural transformations for the
      composite adjunctions."

   The proof diagram on that page is the chain of hom-set bijections

        D(F-'F'x, d)  ~  A(F'x, G-'d)  ~  X(x, G'G-'d)
             |                |                 |
        D(F- F x, d)  ~  A(F x, G- d)  ~  X(x, G G- d)

   whose vertical maps are precomposition with (sigma- sigma)x on the
   left, precomposition with (sigma x) after postcomposition with
   (tau- d) in the middle, and postcomposition with (tau tau- d) on the
   right.  The closing remark and Exercise 1, again verbatim:

     "Moreover, this operation of (horizontal) composition is a bifunctor
      Adj(A, D) x Adj(X, A) -> Adj(X, D).                            (1)
      This means that Adj is a 'two-dimensional' category, as is Cat
      (see SS II.5).  There is additional discussion in Chapter XII."

     "1. Prove that horizontal composition is a bifunctor, as in (1), and
      that this implies an interchange law between horizontal and vertical
      composition of conjugate pairs."

   ** The orientation dictionary

   Instance/Adj.v declares [AdjObj C D] as a triple (F, U, F <| U) with
   F : D -> C and U : C -> D, so Mac Lane's adjunction <F,G> : X -> A,
   whose F runs X -> A, is an [AdjObj A X]: the TREE's [Adj C D] is the
   BOOK's Adj(D, C), its two arguments reversed.  A 1-cell x -> y of the
   bicategory below is therefore an adjunction whose RIGHT adjoint runs
   x -> y -- the orientation Instance/Adjoints.v:110-114 already
   documents for its own 1-category -- and Mac Lane's X -> A is a 1-cell
   A -> X here, running along his G.

   The conjugate pair keeps Instance/Adj.v's variance, which is the
   book's own: sigma FORWARD on the left adjoints and tau BACKWARD on the
   right adjoints, so [ConjPair] carries
   [conj_left : adjobj_left x ==> adjobj_left y] and
   [conj_right : adjobj_right y ==> adjobj_right x], and the hom from x
   to y is [Conjugate (adjobj_adj y) (adjobj_adj x)].

   Display (1) is realized by [Adj_Hcompose], whose type at the tree's
   letters is

        (Adj y z (X) Adj x y) --> Adj x z

   pinned by the [Example] [Adj_Hcompose_shape] below, with [fst] the
   OUTER 1-cell exactly as in [Cat_Hcompose]
   (Instance/Cat/Bicategory.v:64-65, [([D,E] (X) [C,D]) --> [C,E]]).
   Read the correspondence with the
   book's own listing precisely.  Under the dictionary above his
   Adj(A, D) is the tree's [Adj D A] and his Adj(X, A) is [Adj A X], so
   his product Adj(A,D) x Adj(X,A) is the tree's [Adj D A (X) Adj A X],
   whereas [Adj_Hcompose] at x := D, y := A, z := X is
   [Adj A X (X) Adj D A --> Adj D X]: the two factors are listed in the
   OPPOSITE order, because his product puts first the factor that is
   outer along the LEFT adjoints while the tree puts first the factor
   that is outer along the RIGHT adjoints, and those are opposite.  The
   operation is the same one -- [adjobj_hcompose p q] has left adjoint
   [adjobj_left q (o) adjobj_left p] and right adjoint
   [adjobj_right p (o) adjobj_right q], which is Mac Lane's <F- F, G G->
   -- and the tree's listing is FORCED, since [Bicategory]'s [hcompose]
   field is declared at [bicat y z (X) bicat x y --> bicat x z].

   ** What is delivered, with its grade

   (A) THEOREM 2, route (a).  [conjugate_hcompose] (Qed; six rewrites after one
   [intros … ; simpl]): given [Conjugate A A' s t] and [Conjugate B B' sb tb],
   the two Godement products [nat_hcompose sb s] and [nat_hcompose t tb] are
   conjugate for [Adjunction_Compose A B] and [Adjunction_Compose A' B']. The
   proof is Mac Lane's diagram read left to right: [comp_assoc] regroups,
   [to_adj_nat_l] pulls the left leg out of the B' transpose, the two
   hypotheses fire, [to_adj_nat_r] pulls the right leg out of the A transpose,
   and one more [comp_assoc] closes.  BOTH reviewer checks are met by
   CONSTRUCTION rather than by comparison: the two components ARE
   Theory/Natural/Transformation.v:283's [nat_hcompose] and the two composite
   adjunctions ARE Adjunction/Compose.v:173's [Adjunction_Compose], and
   [hcomp_left_is_nat_hcompose], [hcomp_right_is_nat_hcompose] and
   [hcomp_obj_adj] pin all three at [eq_refl] once the bifunctor is in hand.
   Note what the proof does NOT need: [nat_hcompose]'s tau factorisation [t (V'
   e) (o) fmap[U] (tb e)] is exactly the one the goal produces, so no
   naturality step arises on this route.  What the proof DOES need is
   [Category.Instance.Sets] IMPORTED, though no [Sets] token occurs in the CODE
   below the require list (its only occurrences are in this header) and the
   module costs the closure nothing, being reachable already through
   Theory/Adjunction: with that one [Require Import] deleted, a byte-identical
   copy stops at [conjugate_hcompose]'s first [rewrite comp_assoc], the setoid
   rewrite refused on an unresolved [ProperProxy ...  Sets.morphism] --
   instance visibility, not a module, is what the line buys.

   (B) THEOREM 2, route (b), shipped as a CROSS-CHECK against #398. [conj_padL]
   and [conj_padR] (Program, two obligations each, both one application of
   [naturality] or [naturality_sym]) pad a transformation into the shape
   Adjunction/Square.v's [AdjointSquareT] wants at identity bounding functors.
   Then [routeb_hyp] records at [eq_refl] -- a Leibniz equality of TYPES --
   that [AdjointSquareT A A' Id[C] Id[D] (conj_padL s) (conj_padR t)] IS
   [Conjugate A A' s t], and [routeb_sigma] records at [eq_refl] that the sigma
   leg of Square.v's vertical paste at identity bounding functors IS
   [nat_hcompose] componentwise.  The tau leg is NOT: [routeb_tau] is `~=`
   only, one application of [naturality], because Adjunction/Square.v:1217's
   [paste_v_tau] uses the OTHER factorisation of the Godement square ([fmap[U']
   (ta2 e) (o) ta1 (V e)] against [nat_hcompose]'s [t (V' e) (o) fmap[U] (tb
   e)]).  With those, [conjugate_hcompose_via_square] proves the SAME statement
   as [conjugate_hcompose] by [adjoint_square_paste_v] plus [routeb_tau]. So
   Theorem 2 IS #398's vertical pasting at identity bounding functors, up to
   two paddings per side and one naturality of tau on the right leg; the two
   proofs are independent and their terms are not compared at any strength.
   [conj_padL] and [conj_padR] duplicate in shape
   Instance/Cat/Bicategory/Conjugate.v:112's [Cat_conj_padL] and :122's
   [Cat_conj_padR] (both are stated over arbitrary functors -- [conj_padL] over
   [P P' : X ⟶ Y], [Cat_conj_padL] with no adjunction in its discharged type --
   and the two are the same construction, their obligation scripts differing
   only by the leading [intros] that Conjugate.v:110's local [idtac] obligation
   tactic forces).  Requiring that file instead was MEASURED and declined: it
   takes this file's transitive in-project closure from 29 modules to 38, and
   the nine it adds include Adjunction/Natural/Transformation, whose class
   fields [unit] (:36) and [counit] (:37) SHADOW Theory/Adjunction.v's -- the
   same reason Adjunction/Square.v:268-272 gives for keeping its own Cat
   comparison in a sibling file.

   (C) THE BIFUNCTOR.  [AdjIdObj X] is the identity 1-cell (the identity
   adjunction, no obligation); [adjobj_hcompose] composes two 1-cells;
   [conj_pair_hcompose] composes two 2-cells, its single obligation ONE
   [exact] of [conjugate_hcompose] with no tactic work; and
   [Adj_Hcompose] assembles them.  Its three functor obligations:
   [fmap_respects] componentwise, [fmap_id] by [cat], and [fmap_comp] --
   the middle-four interchange -- by an [exact] of
   [nat_hcompose_interchange] ON EACH LEG.  That helper is itself CAT's
   OWN interchange CONSUMED rather than restated: it is a plain
   [Definition] whose body is
   [@fmap_comp _ _ (@Cat_Hcompose C D E) _ _ _ (a2, b2) (a1, b1)], with
   no tactic at all, so Instance/Cat/Bicategory.v:76-83's proof is what
   discharges both legs.  Requiring Instance/Cat/Bicategory for it costs
   exactly one module (28 -> 29 with Adjunction/Square present).  Five
   [eq_refl] readbacks: [hcomp_obj_adj], [hcomp_obj_left],
   [hcomp_obj_right], [hcomp_left_is_nat_hcompose],
   [hcomp_right_is_nat_hcompose].

   (D) EXERCISE 1, DERIVED.  [conj_interchange] is one [exact] of
   [@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g] -- the bifunctor's
   own law and nothing else -- and the four corollaries
   [conj_interchange_left], [conj_interchange_right],
   [conj_interchange_sigma] and [conj_interchange_tau] are each a single
   [exact] of [fst] or [snd] of it at explicit arguments.  No
   interchange law is proved independently anywhere in this file.  Two
   spellings that do NOT work and were measured: [apply fmap_comp] does
   not close the goal (the hom-setoid of [Adj] is a conjunction and the
   goal displays unfolded), and a bare pair [(m, n)] does not elaborate
   at a product-category hom without its three object arguments given.

   (E) UNITORS AND ASSOCIATOR, as full [Isomorphism]s in [Adj]:
   [Adj_hunit_left], [Adj_hunit_right], [Adj_hassoc], each with both legs and
   both inverse laws, all four obligations closed by [cat] after a [simpl].
   THE UNITOR DICTIONARY IS CROSSED ONCE MORE THAN CAT'S.
   Instance/Fun.v:178,:187 names [nat_lambda F : F (o) Id ~= F] and [nat_rho F
   : Id (o) F ~= F], against the usual convention, and [Cat_Bicategory] sets
   [hunit_left := nat_rho]; here the LEFT unitor uses [nat_lambda] on the left
   adjoints and [nat_rho] on the right adjoints, because [adjobj_hcompose
   (AdjIdObj y) f] has left adjoint [adjobj_left f (o) Id[y]] and right adjoint
   [Id[y] (o) adjobj_right f] -- the left adjoints compose in the opposite
   order to the right ones. Four [eq_refl] readbacks pin exactly that
   ([hunit_left_obj_left] and its three siblings).  For the same reason the
   associator cannot be one [iso_sym (nat_alpha f g h)] as in Cat: its two
   components take [nat_alpha]'s three functor arguments in OPPOSITE orders
   (left adjoints h, g, f; right adjoints f, g, h), and BOTH legs are the [to]
   direction.  Everything from [Adj_Hcompose_shape] to the end of the file runs
   under [#[local] Obligation Tactic := program_simpl], set after (C)'s
   [idtac]; that is NOT a restoration of the tree default, which
   Lib/Tactics.v:225 declares as [cat_simpl], and it is load-bearing: a
   byte-identical copy with [cat_simpl] on that line stops inside
   [Adj_hunit_left]'s obligations with "No obligations remaining", [cat_simpl]
   having already discharged what the explicit [Next Obligation] scripts of (E)
   then find nothing left to prove.  The [#[local]] keeps it inside this
   module.

   (F) THE FIVE COHERENCE LAWS, stated in [Adj]'s hom-setoid (so each is
   a PAIR of `~=`) through [adj_hcomp2], which is [Adj_Hcompose]'s [fmap]
   at a pair and which [adj_hcomp2_is_conj_pair_hcompose] reads back at
   [eq_refl]: [Adj_hunit_left_natural], [Adj_hunit_right_natural],
   [Adj_hassoc_natural], [Adj_triangle], [Adj_pentagon].  Four of the
   five close by [split; simpl; intros; cat]; only [Adj_hassoc_natural]
   needs the extra [rewrite !fmap_id, fmap_comp], which is the same extra
   step Instance/Cat/Bicategory.v:102-107's [Cat_hassoc_natural] takes.

   (G) THE BICATEGORY.  [Adj_Bicategory] is built with the RAW
   [Build_Bicategory], never [Build_Bicategory'], for the reason
   Instance/Cat/Bicategory.v:43-55 states for Cat and which was measured
   again here: the [symmetry]-derived [comp_assoc_sym] of the smart
   constructor breaks record eta, [bicat x y] is then no longer [Adj x y],
   and [hcompose] no longer typechecks against [Adj_Hcompose].  Feeding
   [Adj]'s own ten projections keeps eta, so [Adj_bicat_is_Adj] closes at
   [eq_refl], as do [Adj_hcompose_readback], [Adj_bi1id_readback] and
   [Adj_hcomp2_readback].  Two further readbacks BRIDGE to Cat at
   [eq_refl]: the two legs of a horizontal composite of 2-cells here ARE
   Cat's own [hcomp2] on the underlying left and right adjoints
   ([Adj_hcomp2_left_is_Cat_hcomp2], [Adj_hcomp2_right_is_Cat_hcomp2]),
   with the two arguments swapped on the left leg, which is the
   contravariance of [adjobj_left] made visible.  A plain [Definition],
   not an [Instance] (there is no bicategory of bicategories to resolve
   in), following [Cat_Bicategory]'s precedent.

   (H) A BRIDGE TO Instance/Adjoints.v.  [adjobj_of_morphism] and
   [morphism_of_adjobj] pass between that file's [adj_morphism] record and
   [AdjObj]; the RECORD round trip [adjoints_round_record] closes at [eq_refl]
   ([adj_morphism] has primitive projections with eta).  The sigT round trip
   does NOT (stdlib [sigT] is not covered by this repo's [Set Primitive
   Projections]), and neither does the composition comparison: [adjunction (mA
   (o) mB) = Adjunction_Compose Aa Bb] is a CONVERSION refusal at one and the
   same type, since [Adjoints] composes by Instance/Adjoints.v:83's [adj_comp].
   Both were measured and are to be pinned in the probe rather than carried
   here.  The positive half is already in tree: Adjunction/Compose.v:201-212's
   [Adjunction_Compose_adj_comp_to] and [_from] show the two constructions have
   definitionally equal transposes in both directions.

   ** Strict or weak: measured, and it is WEAK

   The structure assembled here is a [Bicategory] and not a strict
   2-category, for a TYPING reason and not a stylistic one.
   [Adjunction_Compose (Adjunction_Compose A B) Cc] and
   [Adjunction_Compose A (Adjunction_Compose B Cc)] do not even share a
   type -- the first is [H (o) (G (o) F) <| U (o) V (o) W] and the second
   [H (o) G (o) F <| U (o) (V (o) W)] -- so the associativity equation is
   not statable at all; measured, with both sides' implicits written out,
   the rejection is a plain has-type mismatch with no "cannot unify" and
   no universe clause.  Both unit laws are refused the same way.  One
   level down the underlying functor equations ARE statable and are
   refused at CONVERSION, with [fobj] and [fmap] agreeing definitionally
   on both sides, so what differs is exactly the three law fields of
   [Compose] -- the fact Adjunction/Pare.v and Instance/Cat/Bicategory.v
   already record.  At the [AdjObj] level, [adjobj_hcompose (AdjIdObj D) a
   = a] and the associativity of [adjobj_hcompose] are likewise refused at
   conversion, as is the left-adjoint component of either.

   Theory/TwoCategory.v's arrows-only [StrictTwoCategory] wants a strict 1-cell
   layer with Leibniz equations, so it is not inhabitable here for the same
   reason that file's own header gives for Cat -- underivability recorded, as
   that header is careful to say, not a refutation theorem.  Its cast-carrying
   [Class TwoCategory] does NOT need strictness, and the route with [tcat :=
   Instance/Adjoints.v]'s [Adjoints] was MEASURED and NOT taken.  Three
   findings decided it.  First, [Adjoints] composes by [adj_comp], and
   [adjunction (mA (o) mB) = Adjunction_Compose Aa Bb] is refused at conversion
   (same type), so on that route the conjugacy of the composite would be stated
   for [adj_comp] and not for [Adjunction_Compose] as the issue's second
   reviewer check demands. Second, all three of [tassoc_cast], [tunitl_cast]
   and [tunitr_cast] are genuinely needed: the 2-cell types at the two
   bracketings, and at the unit padding, are measured NON-CONVERTIBLE (each
   [eq_refl] refused with `cannot unify`); no inequality is proved.  Third,
   [Adjoints]'s arrows are RECORDS where [AdjObj] is a sigT, and only the
   record round trip holds at [eq_refl], so every cell would carry a
   record-to-sigT conversion.  Nothing on that route was built; the estimate
   that it is strictly more work is an ARGUMENT from those three measurements
   plus the field counts (25 fields against [Build_Bicategory]'s 21 arguments,
   ten of which are here literally [Adj]'s own projections), not a compiled
   comparison.

   ** Universes

   Measured off BOTH binder and constraint block, and the two halves of the
   identification are recorded in DIFFERENT places, which is why both must be
   read.  Every constant that binds categories binds them at [Category@{_ h h}]
   -- hom identified with proof -- in the BINDER, and no constraint block
   anywhere in the file states that.  The further identification of the three
   (or four) categories' HOM levels with one another is in the BINDER for the
   [Adj]-level constants ([adjobj_hcompose] reads [Category@{u3 u9 u9}],
   [Category@{u8 u9 u9}], [Category@{u2 u9 u9}], one shared [u9], its block
   carrying [u9 < u0] and bounds and no equation; likewise
   [conj_pair_hcompose], [Adj_Hcompose], [nat_hcompose_interchange], the two
   unitors and [Adj_hassoc]), and in the BLOCK for the five constants of (A)
   and (B) -- [conjugate_hcompose] in [Section HorizontalCompose], and
   [conjugate_hcompose_via_square], [routeb_hyp], [routeb_sigma] and
   [routeb_tau] in [Section RouteB], the two sections declaring
   character-identical [Context] lines -- whose binders keep the hom levels
   apart ([u0], [u2] and, for the four that bind [E], [u4]; [routeb_hyp] binds
   only [C] and [D]) and whose blocks then carry [u0 = u2] and [u0 = u4] (the
   two Theorem-2 constants one equation more, [u5 = u8] between the two Sets
   levels; the other 62 blocks carry no equation at all).  Both halves are
   INHERITED.  The binder half has several donors, each sufficient alone -- at
   levels declared apart, [Adjunction] and [Compose] are each refused with no
   other donor in the command (the probe pins both); [nat_hcompose],
   [Cat_Hcompose], Instance/Adj.v's [AdjObj] and [Adj], and this file's
   [adjobj_hcompose] and [Adj_Hcompose] are refused at their own signatures
   while the bare categories pass, though each contains a donor and so is not
   shown to add an identification of its own; [ConjPair] refuses at its
   [AdjObj] argument and measures nothing of its own; and [Functor] and
   [Transform] are NOT donors, a functor and a transformation between two
   functors both being accepted at those levels -- so a constant such as
   [conj_padL], whose type mentions only [Functor], [Transform], [Id] and
   [Compose], inherits it from [Compose] and not from anything in
   Instance/Adj.v; functors in BOTH directions moreover identify the two hom
   levels with each other before any adjunction is formed.  The block half is
   the two sections' [Context]: each declares functors in both directions
   between [C] and [D] and between [C] and [E], the donor named a sentence ago,
   and section discharge hands the resulting equations to every constant
   declared inside -- measured out of tree: a section holding only functors in
   both directions between those pairs gives a trivial [x = x] example over [D]
   the block [u0 = u2], [u0 = u4] with [C] and [E] nowhere in its statement,
   while one functor per pair gives only the bounds [u2 <= u0], [u0 <= u4] --
   which is why [routeb_hyp], binding only [C] and [D], still carries [u0 =
   u4].  Adjunction/Compose.v:173's [Adjunction_Compose], whose own block
   carries [u0 = u2], [u0 = u4], [u5 = u7], accounts only for the extra [u5 =
   u8] of the two Theorem-2 constants -- it is not the source of the other two,
   [routeb_sigma] and [routeb_tau] carrying both with no adjunction in their
   types.  The isolating probes are in the probe file, not here.  In every case
   the OBJECT universes stay free of the hom universes and of each other -- no
   equation anywhere in the file touches an object universe -- and carry bounds
   only: [<=] bounds, except in the nine constants that mention
   [Adj_Bicategory] or [Adjoints], where the object universe additionally sits
   strictly below the 0-cell universe ([Adj_bicat_is_Adj], the three
   [Adj_*_readback]s and the two [Adj_hcomp2_*_is_Cat_hcomp2] carry [u6 < u];
   [adjobj_of_morphism], [morphism_of_adjobj] and [adjoints_round_record] carry
   [u4 < u]).  [Adj_Bicategory@{u u0 u1 u2 u3 u4 u5 u6 u7} : Bicategory@{u u0
   u1 u0 u1}] is EXACTLY [Cat_Bicategory]'s instantiation shape (nine universe
   parameters against Cat's six), its block [u1 < u0], [u4 < u], [u7 < u], [u7
   < u5] and bounds with no equation, and the 0-cell type [Category] sits one
   level up just as Cat's does.  There is no word-bounded [Set] in any binder
   or block of any constant of this file.

   ** Closure

   The transitive in-project closure of the require list above, excluding
   this file, is 29 modules.  Drop-one marginals: Adjunction/Square 4
   (it brings Adjunction/Map, Construction/Quotient and
   Functor/Construction/Product with it), Instance/Adj 1,
   Instance/Cat/Bicategory 1, and every other require 0.  Without
   Adjunction/Square and without Instance/Cat/Bicategory the closure
   would be 24: route (b) costs 4 and consuming Cat's interchange costs
   1, both paid deliberately.

   ** A stale sentence of the issue

   Its current-state section says "Instance/Adj.v:43 -- a hom-category of
   adjunctions exists, but with no conjugacy condition on its arrows".
   That has been stale since #395: [ConjPair] carries [conj_pair_law] as
   its third field, so an arrow of [Adj C D] is a conjugate pair and not
   a bare pair of transformations, and that file's own header records the
   retyping.

   ** Pinned

   Test/ProbeAdjBicat399.v carries 27 refutation commands: one instrument check
   plus 26 negatives of THREE kinds told apart by the error TEXT.  ELEVEN are
   CONVERSION refusals (both bracketings and both unit paddings of [Compose];
   the four [adjobj_hcompose] laws; the route-(b) tau leg; [Adjoints]'s
   composition against [Adjunction_Compose]; the sigT round trip; and the
   [Build_Bicategory'] churn), FOUR are TYPING refusals (the associativity and
   the two unit laws of [Adjunction_Compose], which are not statable at all,
   and the sigma leg as a WHOLE transformation) and ELEVEN are FORMABILITY
   refusals ([Adjunction] and [Compose] each a donor of hom = proof on their
   own; [AdjObj], [Adj], [ConjPair], [nat_hcompose], [Cat_Hcompose],
   [adjobj_hcompose] and [Adj_Hcompose] inheriting it; and functors in BOTH
   directions identifying the two hom levels before any adjunction is formed).
   Each negative was stripped ONE AT A TIME, compiled alone and its whole error
   read; every constant a negative names is guarded by a [Check] outside every
   refutation command (118 identifiers inside the negatives, 93 also outside,
   the 25 exceptions being two keywords, seven bound variables, the fifteen
   refuted declaration names and the instrument's absent name);
   rename-simulated 15/15 over the constants of this file that a negative
   names, every break landing on a [Check] line.  Two corrections to
   expectation are recorded there: the [Build_Bicategory'] refusal carries a
   "cannot unify" clause and so is CONVERSION rather than TYPING, and the
   [ConjPair] negative refuses at its [AdjObj] ARGUMENT, so whether [ConjPair]
   identifies anything of its own is UNKNOWN, not refuted.  [make todo] grows
   by 41, ALL in the probe; this file contributes ZERO.

   ** Not delivered

   No [TwoCategory] instance, for the three measured obstructions above;
   no double category of adjunctions, and no pasting functoriality of
   mates in an ARBITRARY bicategory -- Theory/Bicategory/Mates.v's
   descope ledger entry 10 is NARROWED by this file, not discharged, and
   its note is edited in the same commit to say exactly that.  No
   comparison of the two Theorem-2 proof terms at any strength (both are
   [Qed], so nothing would reduce).  No naturality of any identification
   in C, D or E, and no functoriality of [Adj_Hcompose] in its three
   category arguments.  No concrete witness at a named pair of
   categories, so nothing here is instantiated.  No strict 2-category and
   no Leibniz equation between the two bracketings.  No relation to
   Instance/Cat/Bicategory/Conjugate.v's mate identification beyond the
   shape of the padding cited in (B).  No pseudofunctor out of
   [Adj_Bicategory] and no comparison with [Cat_Bicategory] beyond the
   two [eq_refl] leg readbacks of (G).  Nothing is registered as an
   [Instance]. *)

(** ** (A) Theorem 2: horizontal composites of conjugate pairs are
       conjugate *)

Section HorizontalCompose.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(* Mac Lane's diagram read left to right.  Nothing here appeals to the
   naturality of tau: [nat_hcompose]'s own factorisation of the Godement
   square is exactly the one the goal produces. *)
Theorem conjugate_hcompose (s : F' ⟹ F) (t : U ⟹ U')
                           (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite to_adj_nat_l.
  rewrite H1.
  rewrite H2.
  rewrite to_adj_nat_r.
  now rewrite comp_assoc.
Qed.

End HorizontalCompose.

(** ** (B) The same theorem through Adjunction/Square.v's vertical paste *)

(* Padding into the shape [AdjointSquareT] wants at identity bounding
   functors.  These duplicate in shape Instance/Cat/Bicategory/Conjugate.v's
   [Cat_conj_padL] and [Cat_conj_padR]; see the header for why that file is
   not required. *)
Program Definition conj_padL {X Y : Category} {P P' : X ⟶ Y} (s : P' ⟹ P)
  : P' ◯ Id[X] ⟹ Id[Y] ◯ P := {| transform := fun x => s x |}.
Next Obligation. apply (naturality s). Qed.
Next Obligation. apply (naturality_sym s). Qed.

Program Definition conj_padR {X Y : Category} {P P' : X ⟶ Y} (t : P ⟹ P')
  : Id[Y] ◯ P ⟹ P' ◯ Id[X] := {| transform := fun a => t a |}.
Next Obligation. apply (naturality t). Qed.
Next Obligation. apply (naturality_sym t). Qed.

Section RouteB.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(* The hypothesis transfer is a Leibniz equality of TYPES. *)
Example routeb_hyp (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareT A A' Id[C] Id[D] (conj_padL s) (conj_padR t)
    = Conjugate A A' s t := eq_refl.

(* The sigma leg of the paste IS the Godement product, componentwise. *)
Example routeb_sigma (s : F' ⟹ F) (sb : G' ⟹ G) (x : D) :
  transform (paste_v_sigma (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (F:=F) (G:=G) (F':=F') (G':=G')
               Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)) x
    = transform (nat_hcompose sb s) x := eq_refl.

(* The tau leg is not: [paste_v_tau] takes the other factorisation of the
   Godement square, and the two differ by one naturality of t. *)
Lemma routeb_tau (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  transform (paste_v_tau (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (U:=U) (V:=V) (U':=U') (V':=V')
               Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb)) e
    ≈ transform (nat_hcompose t tb) e.
Proof. simpl; apply naturality. Qed.

Theorem conjugate_hcompose_via_square
        (s : F' ⟹ F) (t : U ⟹ U') (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2.
  pose proof (adjoint_square_paste_v A B A' B' Id[D] Id[C] Id[E]
                (conj_padL s) (conj_padR t) (conj_padL sb) (conj_padR tb)
                H1 H2) as Hp.
  intros x e k.
  etransitivity; [ exact (Hp x e k) | ].
  apply compose_respects; [ | reflexivity ].
  apply routeb_tau.
Qed.

End RouteB.

(** ** (C) Horizontal composition as a bifunctor *)

(* Cat's own middle-four interchange, consumed rather than restated: this
   is [Cat_Hcompose]'s [fmap_comp] applied, with no tactic. *)
Definition nat_hcompose_interchange {C D E : Category}
  {P1 P2 P3 : C ⟶ D} {Q1 Q2 Q3 : D ⟶ E}
  (a1 : Q1 ⟹ Q2) (a2 : Q2 ⟹ Q3) (b1 : P1 ⟹ P2) (b2 : P2 ⟹ P3) :
  nat_hcompose (a2 ∙ a1) (b2 ∙ b1)
    ≈ nat_hcompose a2 b2 ∙ nat_hcompose a1 b1
  := @fmap_comp _ _ (@Cat_Hcompose C D E)
       (Q1, P1) (Q2, P2) (Q3, P3) (a2, b2) (a1, b1).

(* The identity 1-cell on a category: the identity adjunction. *)
Definition AdjIdObj (X : Category) : AdjObj X X :=
  (Id[X]; (Id[X]; @Adjunction_Id X)).

(* Composition of 1-cells.  Left adjoints compose in the opposite order to
   right adjoints, which is Mac Lane's <F- F, G G->. *)
Definition adjobj_hcompose {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) : AdjObj x z :=
  (adjobj_left q ◯ adjobj_left p;
   (adjobj_right p ◯ adjobj_right q;
    Adjunction_Compose (adjobj_adj p) (adjobj_adj q))).

(* Composition of 2-cells: the two Godement products, conjugate by
   Theorem 2.  The single obligation is one [exact], no tactic work. *)
Program Definition conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  @ConjPair x z (adjobj_hcompose p q) (adjobj_hcompose p' q') := {|
  conj_left  := nat_hcompose (conj_left et) (conj_left th);
  conj_right := nat_hcompose (conj_right th) (conj_right et)
|}.
Next Obligation.
  exact (conjugate_hcompose (adjobj_adj p') (adjobj_adj p)
           (adjobj_adj q') (adjobj_adj q)
           (conj_left th) (conj_right th) (conj_left et) (conj_right et)
           (conj_pair_law th) (conj_pair_law et)).
Qed.

#[local] Obligation Tactic := idtac.

(* Mac Lane's display (1).  [fst] is the outer 1-cell, as in
   [Cat_Hcompose]; the order of the two factors is forced by the
   [Bicategory] class's [hcompose] field. *)
Program Definition Adj_Hcompose {x y z : Category} :
  (Adj y z ∏ Adj x y) ⟶ Adj x z := {|
  fobj := fun pq => adjobj_hcompose (fst pq) (snd pq);
  fmap := fun pq pq' m => conj_pair_hcompose (fst m) (snd m)
|}.
Next Obligation.
  intros x y z [p q] [p' q'] [th et] [th' et'] [[H1 H2] [H3 H4]];
  split; simpl; intro o.
  - now rewrite (H3 _), (H1 o).
  - now rewrite (H2 _), (H4 o).
Qed.
Next Obligation. intros x y z [p q]; split; simpl; intros; cat. Qed.
(* Each leg is Cat's own interchange, applied. *)
Next Obligation.
  intros x y z [p q] [p' q'] [p'' q''] [th et] [th' et']; split.
  - exact (nat_hcompose_interchange (conj_left et') (conj_left et)
             (conj_left th') (conj_left th)).
  - exact (nat_hcompose_interchange (conj_right th) (conj_right th')
             (conj_right et) (conj_right et')).
Qed.

#[local] Obligation Tactic := program_simpl.

(* The bifunctor has exactly the shape of Mac Lane's display (1). *)
Example Adj_Hcompose_shape :
  ∀ x y z : Category, (Adj y z ∏ Adj x y) ⟶ Adj x z := @Adj_Hcompose.

(* The two reviewer checks, at Leibniz equality. *)
Example hcomp_obj_adj {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_adj (adjobj_hcompose p q)
    = Adjunction_Compose (adjobj_adj p) (adjobj_adj q) := eq_refl.

Example hcomp_obj_left {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_left (adjobj_hcompose p q)
    = adjobj_left q ◯ adjobj_left p := eq_refl.

Example hcomp_obj_right {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_right (adjobj_hcompose p q)
    = adjobj_right p ◯ adjobj_right q := eq_refl.

Example hcomp_left_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_left (conj_pair_hcompose th et)
    = nat_hcompose (conj_left et) (conj_left th) := eq_refl.

Example hcomp_right_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_right (conj_pair_hcompose th et)
    = nat_hcompose (conj_right th) (conj_right et) := eq_refl.

(** ** (D) Exercise 1: the interchange law, derived from bifunctoriality *)

(* One [exact] of the bifunctor's own [fmap_comp]. *)
Theorem conj_interchange {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  fmap[@Adj_Hcompose x y z] (f ∘ g)
    ≈ fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g.
Proof. exact (@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g). Qed.

Corollary conj_interchange_left {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_left (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_left (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (fst (conj_interchange f g)). Qed.

Corollary conj_interchange_right {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_right (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_right (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (snd (conj_interchange f g)). Qed.

(* The two readable componentwise forms, read off the same law. *)
Corollary conj_interchange_sigma {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_left et ∙ conj_left et')
               (conj_left th ∙ conj_left th')
    ≈ nat_hcompose (conj_left et) (conj_left th)
        ∙ nat_hcompose (conj_left et') (conj_left th').
Proof.
  exact (fst (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

Corollary conj_interchange_tau {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_right th' ∙ conj_right th)
               (conj_right et' ∙ conj_right et)
    ≈ nat_hcompose (conj_right th') (conj_right et')
        ∙ nat_hcompose (conj_right th) (conj_right et).
Proof.
  exact (snd (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

(** ** (E) The unitors and the associator *)

(* The dictionary is crossed: nat_λ on the left adjoints, nat_ρ on the
   right adjoints, because the two compose in opposite orders. *)
Program Definition Adj_hunit_left {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose (AdjIdObj y) f) f := {|
  to   := {| conj_left  := to   (nat_λ (adjobj_left  f))
           ; conj_right := from (nat_ρ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_λ (adjobj_left  f))
           ; conj_right := to   (nat_ρ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

Program Definition Adj_hunit_right {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose f (AdjIdObj x)) f := {|
  to   := {| conj_left  := to   (nat_ρ (adjobj_left  f))
           ; conj_right := from (nat_λ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_ρ (adjobj_left  f))
           ; conj_right := to   (nat_λ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Both legs are the [to] direction, and they take nat_α's three functor
   arguments in opposite orders. *)
Program Definition Adj_hassoc {w x y z : Category}
  (h : AdjObj y z) (g : AdjObj x y) (f : AdjObj w x) :
  @Isomorphism (Adj w z)
    (adjobj_hcompose (adjobj_hcompose h g) f)
    (adjobj_hcompose h (adjobj_hcompose g f)) := {|
  to   := {| conj_left  := to (nat_α (adjobj_left  h) (adjobj_left  g)
                                     (adjobj_left  f))
           ; conj_right := to (nat_α (adjobj_right f) (adjobj_right g)
                                     (adjobj_right h)) |};
  from := {| conj_left  := from (nat_α (adjobj_left  h) (adjobj_left  g)
                                       (adjobj_left  f))
           ; conj_right := from (nat_α (adjobj_right f) (adjobj_right g)
                                       (adjobj_right h)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Why the crossing: the padded 1-cell's two adjoints. *)
Example hunit_left_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose (AdjIdObj y) f)
    = adjobj_left f ◯ Id[y] := eq_refl.

Example hunit_left_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose (AdjIdObj y) f)
    = Id[y] ◯ adjobj_right f := eq_refl.

Example hunit_right_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose f (AdjIdObj x))
    = Id[x] ◯ adjobj_left f := eq_refl.

Example hunit_right_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose f (AdjIdObj x))
    = adjobj_right f ◯ Id[x] := eq_refl.

(** ** (F) The five coherence laws *)

(* The Godement product of two 2-cells: the bifunctor's action on a pair,
   which is exactly what the class's [hcomp2] computes to. *)
Definition adj_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q')
  : adjobj_hcompose p q ~{Adj x z}~> adjobj_hcompose p' q'
  := @fmap _ _ (@Adj_Hcompose x y z) (p, q) (p', q') (th, et).

Example adj_hcomp2_is_conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  adj_hcomp2 th et = conj_pair_hcompose th et := eq_refl.

Theorem Adj_hunit_left_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_left f)
    ≈ to (Adj_hunit_left f') ∘ adj_hcomp2 (@id (Adj y y) (AdjIdObj y)) et.
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hunit_right_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_right f)
    ≈ to (Adj_hunit_right f') ∘ adj_hcomp2 et (@id (Adj x x) (AdjIdObj x)).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hassoc_natural {w x y z : Category}
  {h h' : AdjObj y z} {g g' : AdjObj x y} {f f' : AdjObj w x}
  (th : h ~{Adj y z}~> h') (ga : g ~{Adj x y}~> g')
  (et : f ~{Adj w x}~> f') :
  adj_hcomp2 th (adj_hcomp2 ga et) ∘ to (Adj_hassoc h g f)
    ≈ to (Adj_hassoc h' g' f') ∘ adj_hcomp2 (adj_hcomp2 th ga) et.
Proof. split; simpl; intros; rewrite !fmap_id, fmap_comp; cat. Qed.

Theorem Adj_triangle {x y z : Category}
  (g : AdjObj y z) (f : AdjObj x y) :
  adj_hcomp2 (to (Adj_hunit_right g)) (@id (Adj x y) f)
    ≈ adj_hcomp2 (@id (Adj y z) g) (to (Adj_hunit_left f))
        ∘ to (Adj_hassoc g (AdjIdObj y) f).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_pentagon {v w x y z : Category}
  (k : AdjObj y z) (h : AdjObj x y) (g : AdjObj w x) (f : AdjObj v w) :
  adj_hcomp2 (@id (Adj y z) k) (to (Adj_hassoc h g f))
    ∘ to (Adj_hassoc k (adjobj_hcompose h g) f)
    ∘ adj_hcomp2 (to (Adj_hassoc k h g)) (@id (Adj v w) f)
  ≈ to (Adj_hassoc k h (adjobj_hcompose g f))
    ∘ to (Adj_hassoc (adjobj_hcompose k h) g f).
Proof. split; simpl; intros; cat. Qed.

(** ** (G) Adj as a bicategory *)

(* The raw constructor, never [Build_Bicategory']: feeding [Adj]'s own ten
   projections keeps record eta, so [bicat C D] is definitionally
   [Adj C D] and [hcompose] typechecks against [Adj_Hcompose].  A plain
   [Definition], not an [Instance], following [Cat_Bicategory]. *)
Definition Adj_Bicategory : Bicategory :=
  Build_Bicategory
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (fun C D => @comp_assoc_sym (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

Example Adj_bicat_is_Adj (C D : Category) :
  @bicat Adj_Bicategory C D = Adj C D := eq_refl.

Example Adj_hcompose_readback (x y z : Category) :
  @hcompose Adj_Bicategory x y z = @Adj_Hcompose x y z := eq_refl.

Example Adj_bi1id_readback (C : Category) :
  @bi1id Adj_Bicategory C = AdjIdObj C := eq_refl.

Example Adj_hcomp2_readback {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  @hcomp2 Adj_Bicategory x y z p p' q q' th et
    = conj_pair_hcompose th et := eq_refl.

(* The bridge to Cat: each leg of a horizontal composite of 2-cells here
   IS Cat's own [hcomp2] on the underlying adjoints.  The left leg swaps
   its two arguments, which is the contravariance of [adjobj_left]. *)
Example Adj_hcomp2_left_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_left (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory z y x
        (adjobj_left q) (adjobj_left q')
        (adjobj_left p) (adjobj_left p')
        (conj_left et) (conj_left th) := eq_refl.

Example Adj_hcomp2_right_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_right (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory x y z
        (adjobj_right p') (adjobj_right p)
        (adjobj_right q') (adjobj_right q)
        (conj_right th) (conj_right et) := eq_refl.

(** ** (H) The bridge to Instance/Adjoints.v *)

Definition adjobj_of_morphism {C D : Category}
  (m : C ~{Adjoints}~> D) : AdjObj C D :=
  (free_functor m; (forgetful_functor m; adjunction m)).

Definition morphism_of_adjobj {C D : Category}
  (x : AdjObj C D) : C ~{Adjoints}~> D := {|
  free_functor      := adjobj_left  x;
  forgetful_functor := adjobj_right x;
  adjunction        := adjobj_adj   x
|}.

(* [adj_morphism] has primitive projections with eta, so this round trip
   is Leibniz.  The sigT one is not; see the header. *)
Example adjoints_round_record {C D : Category} (m : C ~{Adjoints}~> D) :
  morphism_of_adjobj (adjobj_of_morphism m) = m := eq_refl.

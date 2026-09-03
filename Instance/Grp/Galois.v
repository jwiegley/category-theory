(** * The Galois connection of a group acting on a set *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.

(* Same two as Instance/Powerset.v:25-27 and Instance/Proset/Galois.v, and
   for the same reason and in the same position: [relation] and [PreOrder]
   below are the stdlib Prop-valued ones, not Category.Lib's [crelation]
   ones, and they must be required AFTER Category.Lib to win. *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5
    construction 1 (printed p. 96).  Transcribed from the page image, in
    ASCII:

      "A pair of order-preserving functions L and R which satisfy (1) is
       called a Galois connection from P to Q.  Here is the fundamental
       example, for a group G acting on a set U, by <sigma, x> |-> sigma . x
       for sigma in G, x in U.  Take P = P(U), the set of all subsets
       X subset U, ordered by inclusion, while Q = P(G) is the set of
       subsets S subset G also ordered by inclusion (S <= S' if and only if
       S subset S').  Let L X = {sigma | x in X implies sigma . x = x},
       R S = {x | sigma in S implies sigma . x = x}; in other words, L X is
       the subgroup of G which fixes all points x in X and R S is the set of
       fixed points of the automorphisms of S.  Then L X >= S in Q if and
       only if sigma . x = x for all sigma in S and all x in X, which in
       turn holds if and only if X <= R S in P.  Therefore, L and R form an
       adjoint pair (a Galois connection).  The original instance is that
       with G a group of automorphisms of a field U, as in the classical
       Galois theory."

    and, from printed p. 95, the theorem the paragraph is a corollary of,
    together with its two displays:

      "Theorem 1 (Galois connections are adjoint pairs).  Let P, Q be two
       preorders and L : P -> Q^op, R : Q^op -> P two order-preserving
       functions.  Then L (regarded as a functor) is a left adjoint to R if
       and only if, for all p in P and q in Q,

            L p >= q  in  Q  if and only if  p <= R q  in  P .       (1)

       When this is the case, there is exactly one adjunction phi making L
       the left adjoint of R.  For all p and q, p <= R L p and L R q >= q;
       hence also

            L p >= L R L p >= L p ,    R q <= R L R q <= R q .        (2)"

    nLab: https://ncatlab.org/nlab/show/Galois+connection
    nLab: https://ncatlab.org/nlab/show/group+action
    nLab: https://ncatlab.org/nlab/show/closure+operator
    nLab: https://ncatlab.org/nlab/show/stabilizer+group
    nLab: https://ncatlab.org/nlab/show/fixed+point
    Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
    Wikipedia:
      https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory

    ** THE CONNECTION IS ANTITONE, AND THAT IS MAC LANE'S OWN Q^op

    Display (1) reads "L p >= q in Q", not "L p <= q": Theorem 1 types L as
    a functor P -> Q^op, and the construction paragraph says "L X >= S in
    Q".  So the pair here is order-REVERSING in each variable, which is
    what the classical Galois correspondence between subgroups and
    subfields is.  Instance/Proset/Galois.v:118's [GaloisConnection RA RB]
    is stated covariantly -- its [gal_mono_l] concludes [RB (gal_l a)
    (gal_l a')] from [RA a a'] -- so the antitone reading is obtained by
    taking [RB] to be the REVERSED inclusion on P(G), which is
    Instance/Proset/Limit.v:135's [op_rel].  That is a faithful rendering
    of the book's [Q^op] and not a departure from it; the covariant
    ascription is rejected, and that rejection is pinned in
    Test/ProbeGalois381.v as a typing negative.

    ** THE ISSUE'S "Current state" IS STALE ON FOUR COUNTS, MEASURED AT THE
       BASE COMMIT

    The catalog entry says: "Absent.  Structure/Group.v:109 declares only
    [GroupObject] ... no action, no subgroup lattice", and asks for the
    group, the action, the subgroup notion and the powerset preorder to be
    built.  All four exist.

    (1) Instance/Grp.v:184's [GrpObject] is the setoid-level group (carrier,
        unit, multiplication, inversion, with the right-handed laws and
        respectfulness of inversion DERIVED), with [GrpHom] at :345 and the
        category [Grp] at :466.

    (2) A monoid acting on a setoid is
        Construction/Deloop/Functors.v:224's [Record MSetoidAction (M :
        MonObject)] -- fields [act_setoid], [act], [act_respects],
        [act_unit], [act_op], in Riehl 1.3.9's left convention
        [act (g . h) x = act g (act h x)] -- with equivariant maps at
        Instance/Fun/Action.v:115 and the category [MSet M] there.  It is
        CONSUMED below; no second action record is declared.

    (3) Instance/Grp/Quotient.v:156's [Record Subgroup (G : GrpObject)] --
        fields [sub_mem : carrier G -> Type], [sub_resp], [sub_unit],
        [sub_mul], [sub_inv] -- is the subgroup notion.  It is what
        [stab_Subgroup] below inhabits.

    (4) The powerset preorder is Instance/Powerset.v:285-295's
        [subset_le] / [subset_le_preorder] / [Subsets X := Proset
        (subset_le_preorder X)], over Instance/Sets/Powerset.v:981's
        [Powerset_Prop_obj X] -- the [equiv]-respecting Prop-valued
        predicates on a setoid, that is [SetoidMorphism X
        Powerset_Prop_truth].

    Two further corrections to the surrounding prose.  The issue's
    suggested module [Instance/Group/Galois.v] names a directory that does
    not exist; the tree's group directory is [Instance/Grp/], so the file
    is placed there.  And the bridge from a group to the monoid an
    [MSetoidAction] acts by is Instance/Rep.v:176's [grp_mon], consumed
    here.  ([Construction/Deloop.v:267] declares a SECOND record also named
    [GrpObject], layered on [MonObject]; it is not the one
    Instance/Grp/Quotient.v's [Subgroup] is over, so the file imports
    Instance.Grp LAST and every [GrpObject] below is Instance/Grp.v's.)

    ** PRIOR ART: THE THREE EXISTING GALOIS CONNECTIONS, AND WHAT IS NEW

    At the base commit exactly three library constants inhabit
    [GaloisConnection] at NAMED relations (Instance/Proset/Galois.v:190's
    [GaloisOfAdjunction] and :306's [galois_of_unit_counit] are parametric
    constructions over arbitrary [RA]/[RB], so a grep finds five):
    Instance/Proset/Galois.v:249's [nat_shift_galois]
    (truncated subtraction left adjoint to addition on the naturals),
    Instance/Powerset.v:387's [image_preimage_galois] (direct image left
    adjoint to inverse image) and Instance/FinSet/Subsets.v:599's
    [finpow_image_preimage_galois] (the same over decidable finite
    subsets).  A fourth occurrence, Test/ProbePowerset382.v:371, is a probe
    control.  ALL THREE library ones are COVARIANT: each has both maps
    monotone for the given inclusions.  [group_action_galois] below is
    therefore the tree's first ANTITONE one -- the first whose second
    relation is [op_rel] of an inclusion -- which is the shape the
    classical Galois correspondence has.

    NO closure-operator vocabulary existed anywhere: a search for a
    composite [gal_l (gal_r (gal_l _))] or [gal_r (gal_l (gal_r _))], and
    for the tokens [ClosureOperator] and [closure_op], returns nothing
    outside this file.  Section (A) supplies Mac Lane's display (2) over an
    ARBITRARY [GaloisConnection]; it is stated here because
    Instance/Proset/Galois.v is not edited by this change, and it is a
    candidate for moving there when a second consumer appears.

    ** THE ONE DEVIATION FROM THE BOOK, AND WHY IT IS FORCED

    Mac Lane's membership condition is the EQUATION [sigma . x = x] in a
    set.  Here the ambient equality is a setoid's [equiv], which in this
    library is [crelation]-valued, hence [Type]-valued -- while a member of
    [Powerset_Prop_obj X] must be [Prop]-valued, since [subset_le] has to
    be a stdlib [relation] for [Proset] and [GaloisConnection] to apply at
    all (Instance/Powerset.v:283 records that constraint).  The fixing
    condition is therefore TRUNCATED, by Instance/Sets/Powerset.v:951's
    impredicative [Powerset_squash A := forall Q : Prop, (A -> Q) -> Q],
    exactly as [Powerset_Prop_image] truncates its existential.  Nothing is
    lost where it matters: every goal into which the truncation has to be
    eliminated below is itself a [Prop], and
    Instance/Sets/Powerset/Universal.v:327's [powerset_squash_prop_inert]
    records that over a [Prop] the truncation is inert -- which is the case
    at both witnesses, whose setoids are [eq_Setoid]s.

    ** WHAT IS DELIVERED, WITH GRADES

    (A) GENERAL, over an arbitrary [GaloisConnection RA RB] with both
        preorders: [gal_lrl_below]/[gal_lrl_above] and
        [gal_rlr_below]/[gal_rlr_above], which ARE Mac Lane's display (2)
        --- [L p >= L R L p >= L p] and [R q <= R L R q <= R q] -- each a
        [:=] term with no tactic over the donor's [gal_unit] (:284) and
        [gal_counit] (:287): [gal_lrl_below] IS the counit evaluated at
        [gal_l a] and [gal_rlr_above] IS the unit evaluated at [gal_r b],
        with no further step, while [gal_lrl_above] and [gal_rlr_below]
        are the other two pushed through one monotonicity field; the
        closedness predicates [GalClosed_l]/[GalClosed_r]; that every
        image is closed ([gal_closed_l_image]/[gal_closed_r_image], again
        [:=] terms); and the characterisations
        [gal_closed_l_iff]/[gal_closed_r_iff] -- an element is closed
        exactly when it is mutually related to an image.  The donor's own
        [gal_unit]/[gal_counit] are CONSUMED, not restated.

    (B) [subset_le_antisym]: two mutually included subsets are [equiv] in
        [Powerset_Prop_obj X].  A [:=] term (the setoid's [equiv] on
        that object is pointwise [Powerset_Prop_truth_equiv], so the
        witness is [fun x => conj (H1 x) (H2 x)]).  It belongs beside
        Instance/Powerset.v:322's [subsets_iso_of_equiv], which is the
        converse direction read into the category; it is declared here
        because that file is not edited.

    (C) THE OPERATORS AND THE CONNECTION.  [stab X] is Mac Lane's [L X] and
        [fixed S] his [R S]; their memberships read back at [eq_refl]
        ([stab_mem], [fixed_mem]).  [FixesAll X S] is his "sigma . x = x
        for all sigma in S and all x in X", and it is the SAME TERM as one
        side of the biconditional: [stab_transpose_strict] is
        [subset_le S (stab X) = FixesAll X S] by [eq_refl], while
        [fixed_transpose_iff] is the other side, whose whole content is
        the swap of two quantifiers.  [group_action_galois] supplies all
        six fields by name; [gal_to]/[gal_from] are the two halves of
        [fixed_transpose_iff].

    (D) THE STABILISER IS A SUBGROUP.  [stab_Subgroup X : Subgroup G],
        with [sub_mem] the stabiliser on the nose ([stab_Subgroup_mem],
        [eq_refl]).  [sub_resp] is [stab]'s own respectfulness, [sub_unit]
        is [act_unit], [sub_mul] is [act_op], and [sub_inv] is [act_op]
        with [grp_mul_inv_l] and [act_unit].  Nothing dual is claimed for
        [fixed S], which is a subset of U and not of G.

    (E) IDEMPOTENCE.  [stab_fixed_stab] and [fixed_stab_fixed] at the
        carriers' own [equiv], which is what "idempotent" means in a
        preorder that is not a partial order; each is (B) applied to the
        two halves of (A).  The [eq_refl] form is rejected -- the two
        sides are different terms -- and pinned in the probe.

    (F) CLOSED ELEMENTS.  [ClosedG]/[ClosedU], the two general
        characterisations instantiated ([closed_G_iff],
        [closed_U_iff]: a subset of G is closed exactly when it IS a
        stabiliser, a subset of U exactly when it IS a fixed-point set),
        that every image is closed ([closed_G_stab], [closed_U_fixed]),
        and Mac Lane's "L X is the subgroup of G" read at every closed
        subset: [closed_G_Subgroup], whose [sub_mem] is the given subset
        at [eq_refl].

    (G) THE ADJUNCTION.  [StabFunctor], [FixedFunctor] and
        [group_action_adjunction], all three [:=] applications of the
        donor's [GaloisFunctor_l]/[GaloisFunctor_r]/[GaloisAdjunction] --
        no coherence obligation is discharged here, the target being thin.
        Object actions read back at [eq_refl].  The target category is
        [Proset stab_PreOrder_G]; [galois_PG_obj] and [galois_PG_hom]
        record at [eq_refl] that its objects and its homs are those of
        [(Subsets (grp_setoid G))^op], so it IS the opposite category on
        the two components that carry the data.  The WHOLE categories are
        NOT equal, and the cause is NOT [id] or [compose]: those agree at
        [eq_refl] as well, as does the hom-setoid's [equiv] (the probe
        carries all four agreements as controls).  What differs is the
        [homset] RECORD -- [Proset] is a [Program Definition], so its
        [Equivalence] witness is an opaque obligation applied at [(S, T)]
        on one side and at [(T, S)] on the other -- together with the
        rebuilt law fields.  The whole-record rejection is pinned as a
        conversion negative; an earlier draft blamed [id] and [compose],
        which an audit refuted by measurement.  [op_rel_is_flip] records that
        Instance/Proset/Limit.v's [op_rel] and stdlib's [Basics.flip],
        which Instance/Proset/Order.v:305-320 uses for the same job, are
        the SAME function by [eq_refl].

    (H) TWO WITNESSES, both over transparent groups whose operations
        compute.  Instance/Grp.v:1087's [Z2] is UNUSABLE here and that is
        measured, not guessed: it is declared [Z2@{u} : GrpObject@{u Set
        u}], so [grp_setoid Z2 : SetoidObject@{u Set}] with the SECOND
        universe the literal [Set], while [Subsets] demands a
        [SetoidObject@{o o}] with [Set < o]; [Subsets (grp_setoid Z2)] is
        rejected with "Cannot enforce Set = ...".  The witnesses are
        therefore built on [eq_Setoid] (Lib/Setoid.v:65), which is
        polymorphic in exactly the needed way.

        (H1) [GalZ2] on [bool] under [xorb], acting on [bool] by [xorb].
             [galois_stab_true_trivial] computes the stabiliser of the
             singleton {true} to be the trivial subgroup {e}, and
             [galois_fixed_true_empty] the fixed-point set of the
             non-identity element to be empty.  Both non-closure witnesses
             are then proved by [discriminate] after eliminating the
             truncation: {true} as a subset of G is NOT closed (its
             closure is all of G, since everything stabilises the empty
             set), and {true} as a subset of U is NOT closed (its closure
             is all of U).  A closed pair is exhibited alongside, and the
             action is proved to move a point, so the connection is not
             the identity one in disguise.

        (H2) THE STABILISER IS NOT ALWAYS ONE OF THE TWO TRIVIAL
             SUBGROUPS.  [GalV4], the Klein four-group on [bool * bool],
             acts on [bool] through the FIRST coordinate alone -- a
             non-free action, which is what makes a proper non-trivial
             stabiliser possible at all.  [galois_v4_stab_proper] and
             [galois_v4_stab_nontrivial] prove the stabiliser of {true}
             is neither the whole group nor the trivial one -- by
             exhibiting one element it omits and one non-unit element it
             contains -- so [stab_Subgroup] is exercised at a subgroup
             that is genuinely both.  NO CARDINALITY IS CLAIMED: nothing
             in the file counts either group and no order is computed.

    (I) MAC LANE'S OWN TYPING.  Theorem 1 types the pair as
        [L : P -> Q^op] and [R : Q^op -> P], which is exactly the shape of
        Adjunction/Right.v:342's [AdjointOnTheRight]; [StabOp], [FixedOp]
        and [group_action_AdjointOnTheRight] deliver it, with the two
        object actions at [eq_refl] and with the hom-set isomorphism's two
        legs the two projections of [fixed_transpose_iff].  Its eight
        obligations -- four naturality laws, two isomorphism laws, two
        respectfulness certificates -- are equations between parallel
        arrows in a thin category and cost nothing.  The two
        functors' arrow actions ARE [stab_antitone] and [fixed_antitone]
        with their subset arguments swapped -- which is what
        "order-reversing" becomes once the source is an opposite category.
        Requiring Adjunction/Right.v costs THREE modules of closure -- 129
        with it, 126 without, measured by dropping the [Require] -- which
        is why this is delivered rather than only cited.
        Adjunction/Right.v's own two antitone witnesses are a
        three-element chain and the contravariant power set; the tokens
        "group" and "action" occur in that whole file only in one
        unrelated comment, so a group action is a new inhabitant there as
        well.

    ** WHAT IS NOT DELIVERED

    No fundamental theorem of Galois theory, and nothing about fields:
    Mac Lane's "original instance ... a group of automorphisms of a field
    U" is not instantiated, the tree having no automorphism group of a
    field.  No lattice structure on the closed elements and no proof that
    they form a complete lattice.  No orbit, no orbit-stabiliser theorem,
    no transitivity or freeness vocabulary for actions.  No normality: the
    stabiliser is proved a subgroup, and nothing says when it is normal.
    No functoriality of the connection in G, in the action, or in U, and no
    naturality of any identification.  No comparison with
    Instance/Powerset.v's image/preimage connection, and no comparison
    with Adjunction/Right.v's own two antitone witnesses (the
    three-element chain and the contravariant power set) beyond noting
    that neither is a group action.  No proof that the two adjunction
    packagings of (G) and (I) determine one another, and no equation
    between them: they inhabit different classes and no bridge in either
    direction is built.  No dual reading as an [AdjointOnTheLeft], and
    nothing is claimed about whether one exists.  Nothing is registered as
    an [Instance].

    ** CLOSURE, MEASURED BY DROPPING EACH [Require]

    129 modules, transitive in-project [.vo] dependencies excluding the
    file itself.  Only four [Require]s cost anything at all:
    Instance/Rep.v costs 8 (it is where [grp_mon] lives),
    Adjunction/Right.v 3, Instance/Grp/Quotient.v 3 and
    Instance/Powerset.v 2; every other line in the block costs 0, being
    already inside one of those four.  Without the section (I) bridge the
    figure is 126.

    Instance/Grp/Free.v:273's [grp_deloop_monoid] is the SAME monoid
    bridge by a cheaper route -- swapping it in for [grp_mon] measures 126
    rather than 129, and unlike [grp_mon] it is a plain [Definition]
    rather than a [Program] one -- but the two produce DIFFERENT
    [MonObject] terms -- [grp_mon H = grp_deloop_monoid H] is rejected at
    [eq_refl] (measured out of tree, with "cannot unify") -- so a
    consumer's [MSetoidAction] is over one or the other and not both.
    [grp_mon] is kept, being the bridge the tree's own index names, and
    the three-module difference is recorded rather than taken.

    ** UNIVERSES

    Section (C) onwards runs over [G : GrpObject@{o o gu}] and
    [A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{o o gu} G)] under
    [Constraint Set < o] and [Constraint o <= gu].  The identification of
    the group's carrier and relation universes -- and of the action
    setoid's -- is the DONORS' and not this file's, and it has FOUR donors
    each sufficient alone: [Powerset_Prop_obj] is declared over a
    [SetoidObject@{o o}] (Instance/Sets/Powerset.v:981) and is the one
    this file meets first, in section (C); [subset_le],
    [subset_le_preorder] and [Subsets] (Instance/Powerset.v:285-295) each
    demand the same, measured out of tree at levels declared apart.  So
    both [grp_setoid G] and [act_setoid A] must have their two universes
    equal before any subset can be named, and [Set < o] is
    [Powerset_Prop_obj]'s own (Prop sits at [Type@{Set+1}]).
    [Constraint o <= gu] is [GrpObject]'s own [u <= u1, u0 <= u1].  The
    identification is pinned as the probe's two level negatives at the
    LAST of the four donors, [Subsets], with [grp_setoid G], its carrier
    and [grp_mon G] accepted at levels declared apart as the controls, so
    the rejection is not from naming the group's setoid; an earlier draft
    attributed it to [Subsets] alone.

    Section (A) is universe-free of all that: it mentions no setoid and no
    power set, and its two type parameters stay at SEPARATE levels.

    Measured over all 77 declared heads: NOT ONE carries a universe
    EQUATION, and not one carries [Set] in a universe INSTANCE.  Fifty-nine
    carry [Set] in a constraint block and in every case it is the strict LOWER
    bound [Set < _], which is [Powerset_Prop_obj]'s own ([Prop] sits at
    [Type@{Set+1}]) plus one from [Basics.flip] in [op_rel_is_flip]; a
    lower bound on a level constrains nothing above it.  The remaining
    eighteen carry no [Set] at all: the whole of section (A), plus
    [galois_two], [galois_four], [galois_v4_mul], [galois_z2_act_moves]
    and the two witness groups with their two actions (whose blocks are
    the single bound [wo <= Logic_lemmas.equality.u0]).

    Each half of Mac Lane's display (2) needs only ONE of the two
    preorders, which the discharged signatures record:
    [gal_lrl_below]/[gal_rlr_below] take [PA] and
    [gal_lrl_above]/[gal_rlr_above] take [PB], because each is one
    monotonicity step away from a unit or a counit and only the
    reflexivity of the OTHER relation is spent.  Only the two
    [gal_closed_*_iff] take both.

    ** TRANSPARENCY

    Nine [Defined] tokens, and ALL NINE ARE LOAD-BEARING -- measured by
    flipping each one to [Qed] on its own and recording what stops:
    [stab] stops [stab_mem], [fixed] stops [fixed_mem], [stab_Subgroup]
    stops [stab_Subgroup_mem], [closed_G_Subgroup] stops
    [closed_G_Subgroup_mem], [GalZ2] stops [GalZ2Act], [GalZ2Act] stops
    [galois_z2_act_moves], [galois_sub] stops [galois_z2_stab_forces],
    [GalV4] stops [GalV4Act], and [GalV4Act] stops
    [galois_v4_stab_forces].  Everything else is a [:=] term or a [Qed]
    producing no data.  All 91 constants are closed under the global
    context, with no axiom of any kind -- the 77 declared heads (54 [def]
    and 23 [prf] in the glob) plus the 14 [Program] obligations of section
    (I)'s three [Program Definition]s, which no glob or source sweep sees
    and which [Print Module] lists: three each for [StabOp] and [FixedOp]
    and eight for [group_action_AdjointOnTheRight].  A first draft of this
    paragraph said 77 and that the obligations did not exist; the count
    was corrected by [Print Module] before landing.

    ** REGISTRATION

    Nothing is an [Instance] and no hint is added.  A chosen stabiliser
    must not become globally resolvable, matching Instance/Powerset.v's
    own note on its meets and joins. *)

(* ------------------------------------------------------------------------ *)
(** ** (A) Closure operators, over an arbitrary Galois connection *)

(* Mac Lane's display (2) of Theorem 1, and the closedness vocabulary it
   supports.  Nothing here mentions a group, an action or a power set. *)

Section GaloisClosure.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (Gc : GaloisConnection RA RB).

(* [L p >= L R L p >= L p]: read at [RB], the composite [gal_l ∘ gal_r] on
   the image of [gal_l] returns it, in both directions.  Both are supplied
   by [:=] with no tactic; the first IS the donor's counit at [gal_l a],
   the second its unit pushed through [gal_mono_l]. *)
Definition gal_lrl_below (a : A) :
  RB (gal_l Gc (gal_r Gc (gal_l Gc a))) (gal_l Gc a) :=
  gal_counit Gc PA (gal_l Gc a).

Definition gal_lrl_above (a : A) :
  RB (gal_l Gc a) (gal_l Gc (gal_r Gc (gal_l Gc a))) :=
  gal_mono_l Gc (gal_unit Gc PB a).

(* [R q <= R L R q <= R q], the mirror. *)
Definition gal_rlr_below (b : B) :
  RA (gal_r Gc (gal_l Gc (gal_r Gc b))) (gal_r Gc b) :=
  gal_mono_r Gc (gal_counit Gc PA b).

Definition gal_rlr_above (b : B) :
  RA (gal_r Gc b) (gal_r Gc (gal_l Gc (gal_r Gc b))) :=
  gal_unit Gc PB (gal_r Gc b).

(* Closedness.  One direction of each is free -- [gal_counit] on the [B]
   side, [gal_unit] on the [A] side -- so the predicate records only the
   direction that is not. *)
Definition GalClosed_l (b : B) : Prop := RB b (gal_l Gc (gal_r Gc b)).
Definition GalClosed_r (a : A) : Prop := RA (gal_r Gc (gal_l Gc a)) a.

Definition gal_closed_l_image (a : A) : GalClosed_l (gal_l Gc a) :=
  gal_lrl_above a.

Definition gal_closed_r_image (b : B) : GalClosed_r (gal_r Gc b) :=
  gal_rlr_below b.

(* The characterisation: the closed elements are exactly the images.
   Without antisymmetry the sharpest available reading of "is an image" is
   mutual relatedness, which is what a preorder supplies. *)
Lemma gal_closed_l_iff (b : B) :
  GalClosed_l b ↔ ∃ a, RB b (gal_l Gc a) ∧ RB (gal_l Gc a) b.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_r Gc b); exact (H, gal_counit Gc PA b).
  - intros [a [Hba Hab]].
    exact (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _ Hba
             (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
                (gal_lrl_above a)
                (gal_mono_l Gc (gal_mono_r Gc Hab)))).
Qed.

Lemma gal_closed_r_iff (a : A) :
  GalClosed_r a ↔ ∃ b, RA a (gal_r Gc b) ∧ RA (gal_r Gc b) a.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_l Gc a); exact (gal_unit Gc PB a, H).
  - intros [b [Hab Hba]].
    exact (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
             (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
                (gal_mono_r Gc (gal_mono_l Gc Hab))
                (gal_rlr_below b))
             Hba).
Qed.

End GaloisClosure.

(* ------------------------------------------------------------------------ *)
(** ** (B) Mutual inclusion is [equiv] of subsets *)

(* [equiv] on [Powerset_Prop_obj X] is [SetoidMorphism_Setoid]'s, that is
   pointwise [Powerset_Prop_truth_equiv], which is the conjunction of two
   implications -- so the witness is the pair of the two inclusions.  This
   is an equation between OBJECTS of the power set (elements of a setoid),
   not between morphisms of a category. *)
Definition subset_le_antisym@{o} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)}
  (H1 : subset_le@{o} S T) (H2 : subset_le@{o} T S) : S ≈ T :=
  fun x => conj (H1 x) (H2 x).

(* Instance/Proset/Limit.v's reversed preorder and stdlib's [Basics.flip],
   which Instance/Proset/Order.v:305-320 uses for the same job, are the
   same function: both delta-reduce to [fun x y => R y x]. *)
Example op_rel_is_flip {A : Type} (R : relation A) :
  op_rel R = Basics.flip R := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (C) The action, the two operators, and the connection *)

Section Action.

(* [o] is the one universe at which both the group's setoid and the
   action's live; [Subsets] demands [SetoidObject@{o o}], which is what
   forces the two to coincide, and [Set < o] is [Powerset_Prop_obj]'s.
   [su] is the hom universe of the two thin categories, free of [o].
   [gu] is [GrpObject]'s own third level. *)
Universe o su gu.
Constraint Set < o.
Constraint o <= gu.

Context (G : GrpObject@{o o gu}).
Context (A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{o o gu} G)).

(* Mac Lane's [sigma . x = x], truncated: [equiv] is [Type]-valued here,
   and a member of a [Powerset_Prop_obj] must be a [Prop].  Every use below
   eliminates the truncation into a [Prop] goal, and over a [Prop] the
   truncation is inert (Instance/Sets/Powerset/Universal.v:327). *)
Definition fixes (s : carrier (grp_setoid G))
                 (x : carrier (act_setoid A)) : Prop :=
  Powerset_squash@{o} (act A s x ≈ x).

(* [L X], the set of group elements fixing every point of [X].
   Respectfulness in [s] is [act_respects]. *)
Definition stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  carrier (Powerset_Prop_obj@{o} (grp_setoid G)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (grp_setoid G)) (is_setoid (grp_setoid G))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun s => ∀ x, X x → fixes s x) _).
  intros s s' Hss'; split; intros H x Hx; specialize (H x Hx);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hss'; exact Hfix.
  - rewrite Hss'; exact Hfix.
Defined.

(* [R S], the set of points fixed by every element of [S]. *)
Definition fixed (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  carrier (Powerset_Prop_obj@{o} (act_setoid A)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (act_setoid A)) (is_setoid (act_setoid A))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → fixes s x) _).
  intros x y Hxy; split; intros H s Hs; specialize (H s Hs);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hxy; exact Hfix.
  - rewrite Hxy; exact Hfix.
Defined.

(* The two memberships, on the nose.  Equations between [Prop]s, i.e.
   between OBJECTS, not between morphisms. *)
Example stab_mem (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  stab X s = (∀ x, X x → fixes s x) := eq_refl.

Example fixed_mem (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  (x : carrier (act_setoid A)) :
  fixed S x = (∀ s, S s → fixes s x) := eq_refl.

(* Mac Lane's middle term: "sigma . x = x for all sigma in S and all x in
   X".  It is the SAME TERM as the [Q]-side inclusion. *)
Definition FixesAll (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
                    (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := ∀ s, S s → ∀ x, X x → fixes s x.

Example stab_transpose_strict
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S (stab X) = FixesAll X S := eq_refl.

(* The other side.  Its whole content is the swap of two quantifiers -- so
   the biconditional Mac Lane states as two steps costs, here, exactly one
   permutation and one [eq_refl]. *)
Lemma fixed_transpose_iff
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} X (fixed S) <-> FixesAll X S.
Proof using A G. split; intros H a Ha b Hb; exact (H b Hb a Ha). Qed.

(* Antitonicity of the two operators, in the elementary form.  The
   connection reads them at [op_rel], where they become the covariant
   fields the donor record asks for. *)
Lemma stab_antitone (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  subset_le@{o} X X' → subset_le@{o} (stab X') (stab X).
Proof using A G. intros H s Hs x Hx; exact (Hs x (H x Hx)). Qed.

Lemma fixed_antitone (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S S' → subset_le@{o} (fixed S') (fixed S).
Proof using A G. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(* THE GALOIS CONNECTION.  All six fields by name; the second relation is
   the REVERSED inclusion on P(G), which is Mac Lane's [Q^op]. *)
Definition group_action_galois :
  GaloisConnection (@subset_le@{o} (act_setoid A))
                   (op_rel (@subset_le@{o} (grp_setoid G))) :=
  {| gal_l := stab
   ; gal_r := fixed
   ; gal_mono_l := stab_antitone
   ; gal_mono_r := fun S T H => fixed_antitone T S H
   ; gal_to   := fun X S H => proj2 (fixed_transpose_iff X S) H
   ; gal_from := fun X S H => proj1 (fixed_transpose_iff X S) H |}.

(* The two preorders the connection is read at. *)
Definition stab_PreOrder_U : PreOrder (@subset_le@{o} (act_setoid A)) :=
  subset_le_preorder@{o} (act_setoid A).

Definition stab_PreOrder_G :
  PreOrder (op_rel (@subset_le@{o} (grp_setoid G))) :=
  op_PreOrder (subset_le_preorder@{o} (grp_setoid G)).

(* ------------------------------------------------------------------------ *)
(** ** (D) The stabiliser is a subgroup *)

(* Mac Lane's "L X is the subgroup of G which fixes all points x in X",
   as an inhabitant of Instance/Grp/Quotient.v:156's record.  [sub_mem]
   wants a [Type]-valued membership and [stab X s] is a [Prop], which is a
   [Type] by cumulativity; nothing is wrapped.  The four laws are the four
   the action supplies: saturation is [stab]'s own respectfulness, the unit
   is [act_unit], the product is [act_op], and the inverse is [act_op] with
   [grp_mul_inv_l] and [act_unit]. *)
Definition stab_Subgroup
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => stab X s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ (stab X) a b Hab) Ha).
  - intros x Hx; apply Powerset_squash_intro@{o}; exact (act_unit A x).
  - intros a b Ha Hb x Hx.
    refine (Ha x Hx _ _); intro Hax.
    refine (Hb x Hx _ _); intro Hbx.
    apply Powerset_squash_intro@{o}.
    rewrite (act_op A a b x); rewrite Hbx; exact Hax.
  - intros a Ha x Hx.
    refine (Ha x Hx _ _); intro Hax.
    apply Powerset_squash_intro@{o}.
    rewrite <- Hax at 1.
    rewrite <- (act_op A (grp_inv G a) a x).
    rewrite (grp_mul_inv_l G a).
    exact (act_unit A x).
Defined.

Example stab_Subgroup_mem
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  sub_mem (stab_Subgroup X) s = stab X s := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (E) The two closure operators are idempotent *)

(* Mac Lane's display (2) at this connection.  In a preorder that is not a
   partial order the conclusion is mutual inclusion, which for these
   carriers IS the setoid's own [equiv]: (B) converts. *)
Lemma stab_fixed_stab
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  stab (fixed (stab X)) ≈ stab X.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_lrl_above stab_PreOrder_G group_action_galois X).
  - exact (gal_lrl_below stab_PreOrder_U group_action_galois X).
Qed.

Lemma fixed_stab_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fixed (stab (fixed S)) ≈ fixed S.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_rlr_below stab_PreOrder_U group_action_galois S).
  - exact (gal_rlr_above stab_PreOrder_G group_action_galois S).
Qed.

(* Both operators respect [equiv], from antitonicity read both ways. *)
Lemma stab_respects
  (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) (H : X ≈ X') :
  stab X ≈ stab X'.
Proof using A G.
  apply subset_le_antisym.
  - exact (stab_antitone X' X (fun x Hx => proj2 (H x) Hx)).
  - exact (stab_antitone X X' (fun x Hx => proj1 (H x) Hx)).
Qed.

Lemma fixed_respects
  (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : S ≈ S') :
  fixed S ≈ fixed S'.
Proof using A G.
  apply subset_le_antisym.
  - exact (fixed_antitone S' S (fun x Hx => proj2 (H x) Hx)).
  - exact (fixed_antitone S S' (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The closed elements *)

(* Section (A)'s predicates, unfolded at this connection.  A subset of [G]
   is closed when it contains everything that fixes all of its own fixed
   points; the reverse inclusion is free ([gal_counit]).  Dually for [U]. *)
Definition ClosedG (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := subset_le@{o} (stab (fixed S)) S.

Definition ClosedU (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : Prop := subset_le@{o} (fixed (stab X)) X.

Example ClosedG_is_GalClosed_l
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S = GalClosed_l group_action_galois S := eq_refl.

Example ClosedU_is_GalClosed_r
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X = GalClosed_r group_action_galois X := eq_refl.

Definition closed_G_stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : ClosedG (stab X) :=
  gal_closed_l_image stab_PreOrder_G group_action_galois X.

Definition closed_U_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) : ClosedU (fixed S) :=
  gal_closed_r_image stab_PreOrder_U group_action_galois S.

(* The closed subsets of [G] are EXACTLY the stabilisers, and the closed
   subsets of [U] exactly the fixed-point sets.  Section (A)'s general
   characterisation supplies the mutual-inclusion form; (B) upgrades it to
   the carriers' own [equiv]. *)
Lemma closed_G_iff (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S ↔ ∃ X, S ≈ stab X.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois S) H) as [X [H1 H2]].
    exists X; exact (subset_le_antisym H2 H1).
  - intros [X HX].
    refine (snd (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois S) _).
    exists X; exact (fun s Hs => proj2 (HX s) Hs,
                     fun s Hs => proj1 (HX s) Hs).
Qed.

Lemma closed_U_iff (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X ↔ ∃ S, X ≈ fixed S.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois X) H) as [S [H1 H2]].
    exists S; exact (subset_le_antisym H1 H2).
  - intros [S HS].
    refine (snd (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois X) _).
    exists S; exact (fun x Hx => proj1 (HS x) Hx,
                     fun x Hx => proj2 (HS x) Hx).
Qed.

(* Mac Lane's "L X is the subgroup of G", read at EVERY closed subset: the
   membership is the given subset on the nose, and the four laws are
   transported from [stab_Subgroup (fixed S)] along the two inclusions. *)
Definition closed_G_Subgroup
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => S s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ S a b Hab) Ha).
  - exact (H _ (sub_unit (stab_Subgroup (fixed S)))).
  - intros a b Ha Hb.
    refine (H _ (sub_mul (stab_Subgroup (fixed S)) a b _ _)).
    + exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
    + exact (gal_counit group_action_galois stab_PreOrder_U S b Hb).
  - intros a Ha.
    refine (H _ (sub_inv (stab_Subgroup (fixed S)) a _)).
    exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
Defined.

Example closed_G_Subgroup_mem
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  (s : carrier (grp_setoid G)) :
  sub_mem (closed_G_Subgroup S H) s = S s := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (G) The adjunction *)

(* #380 applied: the two functors and the adjunction are [:=] terms, and
   every coherence obligation of [Adjunction] is an equation between
   parallel arrows in a thin category, hence discharged uniformly there. *)
Definition StabFunctor :
  Subsets@{o su} (act_setoid A) ⟶ Proset@{o su} stab_PreOrder_G :=
  GaloisFunctor_l stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition FixedFunctor :
  Proset@{o su} stab_PreOrder_G ⟶ Subsets@{o su} (act_setoid A) :=
  GaloisFunctor_r stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition group_action_adjunction : StabFunctor ⊣ FixedFunctor :=
  GaloisAdjunction stab_PreOrder_U stab_PreOrder_G group_action_galois.

Example StabFunctor_obj
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabFunctor] X = stab X := eq_refl.

Example FixedFunctor_obj
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedFunctor] S = fixed S := eq_refl.

(* The target category IS the opposite of [Subsets (grp_setoid G)] on the
   two components that carry data: its objects are the subsets of [G] and
   its homs are reversed inclusions.  The whole records are not equal --
   not at [id] or [compose], which agree at [eq_refl] too, but at the
   [homset] record, whose [Equivalence] witness is [Proset]'s opaque
   [Program] obligation applied at swapped arguments -- and that is
   pinned in the probe. *)
Example galois_PG_obj :
  obj[Proset@{o su} stab_PreOrder_G]
    = obj[(Subsets@{o su} (grp_setoid G))^op] := eq_refl.

Example galois_PG_hom
  (S T : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  (S ~{Proset@{o su} stab_PreOrder_G}~> T)
    = (S ~{(Subsets@{o su} (grp_setoid G))^op}~> T) := eq_refl.


(* ------------------------------------------------------------------------ *)
(** ** (I) Mac Lane's own typing: a pair adjoint on the right *)

(* Theorem 1 types the two maps as [L : P -> Q^op] and [R : Q^op -> P], and
   Adjunction/Right.v:342's [AdjointOnTheRight S T] -- for
   [S : A^op ⟶ X] and [T : X^op ⟶ A], with the hom-set isomorphism
   [A(a, T x) ≅ X(x, S a)] -- is exactly that shape.  So the pair here IS a
   pair adjoint on the right, and saying so costs three modules of closure
   (129 with the [Require], 126 without; measured), which is why it is
   delivered rather than only cited.  [Adjunction/Right.v]'s own antitone
   witnesses are a three-element chain and the contravariant power set;
   neither is a group action, and the tokens "group" and "action" occur in
   that file only in one unrelated comment.

   The functors' arrow actions ARE the elementary antitonicity lemmas with
   their two subset arguments swapped, which is what "order-reversing" is
   once the source is written as an opposite category. *)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition StabOp :
  (Subsets@{o su} (act_setoid A))^op ⟶ Subsets@{o su} (grp_setoid G) := {|
  fobj := stab;
  fmap := fun X X' f => stab_antitone X' X f
|}.

Program Definition FixedOp :
  (Subsets@{o su} (grp_setoid G))^op ⟶ Subsets@{o su} (act_setoid A) := {|
  fobj := fixed;
  fmap := fun S S' f => fixed_antitone S' S f
|}.

(* The hom-set isomorphism IS the transpose of (C): its forward leg is
   [fixed_transpose_iff]'s first projection and its backward leg the
   second, and the target of the forward leg is [FixesAll X S] on the nose
   (by [stab_transpose_strict]).  All eight obligations -- the four
   naturality laws, the two isomorphism laws and the two respectfulness
   certificates of the legs -- are equations between parallel arrows in a
   thin category, hence discharged uniformly. *)
Program Definition group_action_AdjointOnTheRight :
  AdjointOnTheRight StabOp FixedOp := {|
  aor := fun X S =>
    {| to   := {| morphism := fun h => proj1 (fixed_transpose_iff X S) h |}
     ; from := {| morphism := fun h => proj2 (fixed_transpose_iff X S) h |} |}
|}.

Example StabOp_obj (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabOp] X = stab X := eq_refl.

Example FixedOp_obj (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedOp] S = fixed S := eq_refl.

End Action.

Arguments fixes {G A} s x.
Arguments stab {G A} X.
Arguments fixed {G A} S.
Arguments FixesAll {G A} X S.
(* [A] stays EXPLICIT in [ClosedG]: its argument [S] is a subset of the
   GROUP, which determines [G] but not the action. *)
Arguments ClosedG {G} A S.
Arguments ClosedU {G A} X.

(* ------------------------------------------------------------------------ *)
(** ** (H1) A witness: the two-element group acting on two points *)

(* The two-point setoid, at ONE universe.  [eq_Setoid] (Lib/Setoid.v:65) is
   polymorphic in exactly the level [Subsets] needs, which
   Instance/Grp.v:1087's [Z2] is not: that one is declared
   [Z2@{u} : GrpObject@{u Set u}], pinning the relation universe to the
   literal [Set], and [Subsets (grp_setoid Z2)] is then rejected.  The
   rejection is pinned in Test/ProbeGalois381.v. *)
Definition galois_two@{wo} : SetoidObject@{wo wo} :=
  {| carrier := bool ; is_setoid := eq_Setoid@{wo} bool |}.

(* Z/2 as [bool] under exclusive or, with [false] the unit and every
   element its own inverse.  Transparent: the [discriminate] arguments
   below need its operation to compute. *)
Definition GalZ2@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_two@{wo}
                   ; grp_unit := false
                   ; grp_mul := xorb
                   ; grp_inv := fun b : bool => b |}.
  - exact (fun x y Hxy u v Huv => f_equal2 xorb Hxy Huv).
  - intros [|] [|] [|]; reflexivity.
  - intros [|]; reflexivity.
  - intros [|]; reflexivity.
Defined.

(* Z/2 acting on two points by the flip.  [act_respects] is supplied by
   hand rather than left to resolution, so that no instance search can pin
   a universe (the hazard Theory/Universal/Element.v records). *)
Definition GalZ2Act@{wo +} : MSetoidAction (grp_mon GalZ2@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalZ2@{wo}) galois_two@{wo}
                     (fun g x => xorb g x)
                     (fun g g' Hg x x' Hx => f_equal2 xorb Hg Hx) _ _).
  - intros [|]; reflexivity.
  - intros [|] [|] [|]; reflexivity.
Defined.

(* The action moves a point, so neither operator is the one belonging to a
   trivial action. *)
Example galois_z2_act_moves : act GalZ2Act true true = false := eq_refl.

(* Subsets of the two-point setoid.  [equiv] there is Leibniz equality, so
   respectfulness is a substitution. *)
Definition galois_sub@{wo} (p : bool → Prop) :
  carrier (Powerset_Prop_obj@{wo} galois_two@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    bool (is_setoid galois_two@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition galois_true@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = true).

Definition galois_false@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = false).

(* THE STABILISER OF {true} IS THE TRIVIAL SUBGROUP.  The forward step
   eliminates the truncation into a [Prop] goal and closes by
   [discriminate] on the computed [xorb true true]. *)
Lemma galois_z2_stab_forces (s : bool) :
  stab (A := GalZ2Act) galois_true s → s = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct s; [ discriminate Hfix | reflexivity ].
Qed.

Lemma galois_z2_stab_unit : stab (A := GalZ2Act) galois_true false.
Proof.
  intros x Hx; apply Powerset_squash_intro; reflexivity.
Qed.

Theorem galois_stab_true_trivial :
  stab (A := GalZ2Act) galois_true ≈ galois_false.
Proof.
  apply subset_le_antisym.
  - intros s Hs; exact (galois_z2_stab_forces s Hs).
  - intros s Hs; simpl in Hs; subst s; exact galois_z2_stab_unit.
Qed.

(* THE FIXED-POINT SET OF THE NON-IDENTITY ELEMENT IS EMPTY. *)
Theorem galois_fixed_true_empty (x : bool) :
  fixed (A := GalZ2Act) galois_true x → False.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct x; discriminate Hfix.
Qed.

(* NON-CLOSURE, ON THE GROUP SIDE: {true} is not a stabiliser.  Its
   closure is all of G, because every element stabilises the empty set. *)
Theorem galois_true_not_ClosedG :
  ClosedG GalZ2Act galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros x Hx.
    destruct (galois_fixed_true_empty x Hx). }
  discriminate Hfalse.
Qed.

(* NON-CLOSURE, ON THE POINT SIDE: {true} is not a fixed-point set.  Its
   closure is all of U, because the trivial subgroup fixes everything. *)
Theorem galois_true_not_ClosedU :
  ClosedU (A := GalZ2Act) galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros s Hs.
    apply Powerset_squash_intro.
    rewrite (galois_z2_stab_forces s Hs); reflexivity. }
  discriminate Hfalse.
Qed.

(* A CLOSED PAIR, exhibited rather than merely known to exist: the trivial
   subgroup is closed, and so is the whole point set.  Both are instances
   of (F)'s "every image is closed", with the concrete content supplied by
   [galois_stab_true_trivial]. *)
Theorem galois_false_ClosedG : ClosedG GalZ2Act galois_false.
Proof.
  refine (snd (closed_G_iff GalZ2 GalZ2Act galois_false) (galois_true; _)).
  symmetry; exact galois_stab_true_trivial.
Qed.

(* [stab] is not constant: it separates the empty subset from {true}. *)
Definition galois_empty@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun _ => False).

Theorem galois_stab_not_constant :
  stab (A := GalZ2Act) galois_empty true
    * (stab (A := GalZ2Act) galois_true true → False).
Proof.
  split.
  - intros x Hx; destruct Hx.
  - intro H; pose proof (galois_z2_stab_forces true H) as Heq.
    discriminate Heq.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (H2) A witness whose stabiliser is a proper non-trivial subgroup *)

(* In (H1) the action is FREE, so every stabiliser is one of the two
   trivial subgroups and [stab_Subgroup] is exercised only at those.  The
   Klein four-group acting on two points through its FIRST coordinate is
   not free, and the stabiliser of {true} is then neither the whole group
   nor the trivial one.  NO CARDINALITY IS CLAIMED: nothing below counts
   either group, and what is proved is one omitted element and one
   contained non-unit element. *)
Definition galois_four@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (bool * bool)%type
   ; is_setoid := eq_Setoid@{wo} (bool * bool)%type |}.

Definition galois_v4_mul (g h : bool * bool) : bool * bool :=
  (xorb (fst g) (fst h), xorb (snd g) (snd h)).

Definition GalV4@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_four@{wo}
                   ; grp_unit := (false, false)
                   ; grp_mul := galois_v4_mul
                   ; grp_inv := fun g : bool * bool => g |}.
  - exact (fun x y Hxy u v Huv => f_equal2 galois_v4_mul Hxy Huv).
  - intros [[|] [|]] [[|] [|]] [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
Defined.

Definition GalV4Act@{wo +} : MSetoidAction (grp_mon GalV4@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalV4@{wo}) galois_two@{wo}
                     (fun g x => xorb (fst g) x)
                     (fun g g' Hg x x' Hx =>
                        f_equal2 xorb (f_equal (@fst bool bool) Hg) Hx) _ _).
  - intros [|]; reflexivity.
  - intros [[|] [|]] [[|] [|]] [|]; reflexivity.
Defined.

(* Membership in the stabiliser of {true} is exactly "the first coordinate
   is the unit", both ways. *)
Lemma galois_v4_stab_forces (g : bool * bool) :
  stab (A := GalV4Act) galois_true g → fst g = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct g as [[|] [|]]; simpl in *; try discriminate Hfix; reflexivity.
Qed.

Lemma galois_v4_stab_holds (g : bool * bool) :
  fst g = false → stab (A := GalV4Act) galois_true g.
Proof.
  intros Hg x Hx; apply Powerset_squash_intro.
  simpl; rewrite Hg; reflexivity.
Qed.

(* NOT the trivial subgroup: it contains an element other than the unit. *)
Theorem galois_v4_stab_nontrivial :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (false, true)
    * ((false, true) = grp_unit GalV4 → False).
Proof.
  split.
  - exact (galois_v4_stab_holds (false, true) eq_refl).
  - intro Heq; discriminate Heq.
Qed.

(* NOT the whole group: it omits an element. *)
Theorem galois_v4_stab_proper :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (true, false) → False.
Proof.
  intro H; pose proof (galois_v4_stab_forces (true, false) H) as Heq.
  discriminate Heq.
Qed.

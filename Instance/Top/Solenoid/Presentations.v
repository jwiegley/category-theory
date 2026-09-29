Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Zp.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Solenoid.

Generalizable All Variables.

(** * The two presentations of the p-adic solenoid *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.1, book pp. 110-111 (PDF pp. 119-120), read from the page images
     (catalog id maclane:V.1:construction3).  Book p. 111:
       "Again, in Top, take each object F_n to be a circle S^1, and each
       arrow f_n : S^1 → S^1 to be the continuous map wrapping the domain
       circle S^1 uniformly p times around the codomain circle. ... This L
       is the limit space in Top; it is known as the p-adic solenoid."
     Book p. 110, earlier in the same section:
       "Limits in Grp and other categories may be constructed from the set
       of all cones in much the same way.  For example, if F : ω^op → Grp
       ... then each F_n is a group, the set L of all cones (all matching
       strings x) is also a group under pointwise multiplication
       ((xy)_n = x_n y_n), and the projection μ_n : L → F_n with x ↦ x_n
       is a group homomorphism"
     and, of the example between them: "The p-adic integers Z_p (with p a
     prime) illustrate this construction.  Take F : ω^op → Rng with
     F_n = Z/p^nZ".  Book p. 111, after Theorem 2: "The same argument will
     construct all small limits in Rng, Ab, R-Mod and similar algebraic
     categories, using the forgetful functors U to Set."
   Riehl, "Category Theory in Context", §3.6, Example 3.6.3, printed
     p. 116 (PDF p. 136), read from the page image (catalog id
     riehl:3.6:example3): "consider the diagram ω^op → Top whose objects
     are circles S^1 and in which each generating map is the "pth power
     map," the covering map that wraps the domain circle uniformly p times
     around the codomain circle ... The inverse limit defines the p-adic
     solenoid."
   nLab: https://ncatlab.org/nlab/show/solenoid ("The P-adic solenoid is a
     compact, connected topological group")
   Wikipedia: https://en.wikipedia.org/wiki/Solenoid_(mathematics)
   Wikipedia: https://en.wikipedia.org/wiki/Inverse_limit (Examples: "The
     p-adic solenoid is the inverse limit of the topological groups
     R/p^nZ ... Its elements are exactly of form n+r, where n is a p-adic
     integer, and r ∈ [0,1) is the "remainder".")
   Wikipedia: https://en.wikipedia.org/wiki/Covering_space ("Another
     covering of the unit circle is the map q:S¹→S¹ with q(z)=z^n")

   BACKGROUND.  Instance/Top/Solenoid.v builds the solenoid as the book
   asks, a limit of circles in a category of spaces.  The solenoid is also
   an abelian group (nLab, Wikipedia), and the p-adic integers sit inside
   it (Wikipedia's inverse-limit article).  This file relates the two
   readings on the one circle of Instance/Top/Circle.v, R/Z over the
   constructive Cauchy reals: the group-theoretic tower, the circle GROUP
   under the p-th power endomorphism in [Ab], and the space tower, the
   circle SPACE under the p-fold wrapping map; the p-adic integers, as the
   fibre of the solenoid over the base point; and Riehl's word "covering",
   as evenly covered neighbourhoods of the wrapping map, over both
   categories of spaces.

   WHAT THE APPENDED ITEM ASKS, READ AGAINST THE PAGES.  Issue #410's
   appended Riehl item asks for "the two presentations related -- the
   group-theoretic one this issue names and the covering-space one", and
   its catalog sentence describes Riehl's presentation as "a diagram of
   covering maps rather than as a limit of the p-adic groups".  That
   phrase is the issue text's own.  The page quoted above presents Mac
   Lane's solenoid as a limit of circles, the p-adic integers being the
   separate example before it; neither book draws a map between the two
   examples, and both books give the one diagram.  What Riehl does give is
   two names for its map, "pth power map" and "covering map".  On R/Z the
   p-th power is x ↦ p·x, which is Instance/Top/Circle.v's [circ_mul p],
   the map under [wrap p] and [pwrap p].  So the group-theoretic
   presentation built here is the tower of that endomorphism of the circle
   group, and the p-adic groups enter as the fibre.

   THE CIRCLE GROUP.  [CircleGroup] is Instance/Top/Circle.v's
   [Circle_setoid] with the addition, zero and negation of the reals.  An
   [AbObject] owes [cmon_prop], a [Prop]-valued mirror of its equality
   (Lib/Setoid/Propositional.v); the circle's equality keeps its integer
   as data, and Instance/Top/Circle.v's [circ_PropEquiv] supplies the
   mirror, recomputing the integer by rounding ([cround]), with no choice
   principle.  [circ_pow p] is x ↦ p·x, and its underlying map IS
   [circ_mul p] ([circ_pow_map]).

   ONE UNDERLYING TOWER.  [GroupTower p] is Instance/Top/Solenoid.v's
   [EndoTower] of [circ_pow p] in [Ab].  Three statements identify the
   underlying towers.
     - [GroupTower_points]: [Ab_Forget ◯ GroupTower p ≈ UCircleTower p].
     - [towers_agree]: [PForget ◯ PCircleTower p ≈ Ab_Forget ◯
       GroupTower p], through [UCircleTower p].
     - [CircleTower_points]: [Top_Forget ◯ CircleTower p ≈ UCircleTower p]
       for Mac Lane's tower in the Type-valued [Top].  [Top_Forget] lands
       in the lifted [Sets@{h hs}], so the right side is the tower of
       points taken at the hom universe [h], and the components
       (Instance/Top/Circle.v's [circle_lift_iso]) are the identity maps
       between the lifted [Circle_setoid@{o}] and [Circle_setoid@{h}].
   Each is [≈] in [Functor_Setoid], with identity maps as components.
   The generating function on points is x ↦ p·x at [eq_refl] in all
   three categories ([group_step_fn], [pspace_step_fn],
   [space_step_fn]).

   THE GROUP SOLENOID.  [GroupSolenoid p] is Instance/Ab/Limit.v's
   [Ab_Forget_lifts_limits] at the matching strings [Sets_tower_Limit] of
   the underlying tower: Mac Lane's sentence on book p. 110, at the circle
   group, by the creation argument of his Theorem 2.  Its points are
   #408's matching strings ([group_solenoid_points], [eq_refl]), and its
   operations are pointwise ([gsol_plus_coord], [gsol_zero_coord],
   [gsol_neg_coord], each [eq_refl]).  Against the space solenoids:
   [solenoid_carriers_agree] and [solenoid_equiv_agree] identify the
   carrier and the relation with those of Instance/Top/Solenoid.v's
   [SolPoints p] at [eq_refl]; [gsol_leg_map] identifies the group legs
   with the projections [sol_pr] at [eq_refl]; and
   [solenoid_points_iso] is the identity isomorphism in [Sets].  The
   equation [SolPoints p = Ab_Forget (GSolenoid p)] between the two setoid
   objects is refused at [eq_refl]: Instance/Sets/InverseLimit.v's
   [tower_obj] builds its [Equivalence] by a [Qed] obligation applied to
   the functor, and the two towers are different terms
   (Test/ProbeSolenoid410.v's N7, "cannot unify").  That is the donor's
   opacity and nothing more.  The probe's [p410_tower_obj], the donor's
   definition with its obligation closed [Defined], accepts [eq_refl]
   for [UCircleTower p] against [Ab_Forget ◯ GroupTower p]
   ([p410_flip_group]) and against [PForget ◯ PCircleTower p]
   ([p410_flip_ptop]).  So the identity isomorphism is the strongest
   statement available without editing the donor; it is not the
   strongest possible statement.

   THE FIBRE OVER THE BASE POINT IS Z_p.  [SolFibre p] is the kernel of
   the leg μ_0 in [Ab] (Instance/Ab.v's [AbKernel]).  Its carrier IS
   { x : SolPoints p & circ_eq (μ_0 x) 0 } ([sol_fibre_carrier],
   [eq_refl]), the fibre over 0 of the leg μ_0 of the pinned
   [solenoid_limit].  [ZpAb p] is the additive group ([ring_ab]) of
   Instance/Rng/Zp.v's [Zp ZComm p], Mac Lane's Z_p = Lim F.
   [Zp_fibre_iso p] is an isomorphism in [Ab] between them, so both
   directions are additive.  The forward map sends f to the string of
   torsion points (f_n / p^n)_n ([zp_to_fibre_coord], [eq_refl]); the
   integers of its matching condition come from Instance/Rng/Zp.v's
   [res_to_dvd], which decides divisibility.  The backward map sends x to
   the integers a_n with a_0 the integer of μ_0 x ≈ 0 and
   a_(n+1) = a_n + p^n k_n, k_n the integer of the matching condition
   p x_(n+1) ≈ x_n ([fibre_int]).  So a_n is p^n x_n as a real
   ([fibre_int_spec]).  (A remark, not formalized: multiplying the n-th
   coordinate by p^n carries this tower to the tower R/p^nZ of Wikipedia's
   inverse-limit article, whose points n+r with r = 0 are its p-adic
   integers n.)  The integers are read off the witnesses the circle's
   setoid keeps as data; by Instance/Top/Circle.v's [circ_eq_of_peq] they
   are also recomputable by rounding, but a version built on [cround]
   was not written.  [zp_one_to_unit_string]: the
   p-adic integer 1 goes to Instance/Top/Solenoid.v's [unit_string] (at
   [eq_refl] on coordinates), which [unit_string_not_zero] there
   separates from 0 when 1 < p.  The hypothesis 1 < p is Zp.v's own,
   through [res_to_dvd].

   THE COVERING PROPERTY, IN BOTH CATEGORIES OF SPACES.  A map is a
   covering when every point has an open neighbourhood that is evenly
   covered: its preimage is a disjoint union of open sheets, each carried
   homeomorphically onto it (Wikipedia, Covering space).  Over [PTopCat],
   for a point y:
     - the arc [in_arc y] is the interior of the circle's closed ball of
       radius 1/4 about y: open ([in_arc_open]), containing y
       ([in_arc_centre]);
     - [sheet_index p y z] is the residue mod p of the integer that brings
       p·z within 1/4 of y, computed by [cround] ([arc_shift]);
       [in_sheet p y k z] says p·z lies in the arc and the index is k;
     - each sheet is open ([in_sheet_open]: the index is locally
       constant, by [int_near_zero]), two sheets are disjoint
       ([in_sheet_disjoint]), and the preimage of the arc is the union of
       the sheets 0 <= k < p ([in_sheet_preimage]);
       [pwrap_evenly_covered] gathers these;
     - [pwrap_sheet_iso]: each sheet, as a subspace (Instance/Top/
       Subspace.v's [ex732_Sub], the subspace on a subset), is isomorphic
       in [PTopCat] to the arc as a subspace.  The forward arrow is the
       restriction of [pwrap p] ([pwrap_sheet_iso_to], [eq_refl]); the
       inverse is the local section [sheet_lift], x ↦ (x + m + k)/p with
       m = [arc_shift y x], continuous because it divides distances by p
       ([sheet_lift_lip]).
   So every point of the circle has an evenly covered neighbourhood with p
   sheets.  The fibre over y has exactly p points: [fibre_pt p y k] for
   0 <= k < p lies over y ([fibre_pt_over]); two of them are equal only
   when their indices are ([fibre_pt_distinct]); and every point over y
   is one of them, the index computed ([fibre_exhaust]).  Nothing uses a
   hypothesis on p beyond positivity; at p = 1 there is one sheet.

   Over the Type-valued [Top] the book's subspace does not reach the
   points' universe: Instance/Top/Subspace/TypeValued.v's [tsub_open]
   quantifies over the opens of the ambient space and is valued one
   universe above the points, and supplying it at the arc as the opens
   of a [TopSpace@{o}] is refused, "Cannot enforce o1 <= o because
   o < o1" (Test/ProbeSolenoid410.v's N8; its [p410_tsub_arc_whole] is
   the same predicate accepted one universe up).  The subspaces of the
   circle are nonetheless spaces at [o], by the technique of
   Instance/Top/Solenoid.v's [Solenoid p]: a ball base, characterised by
   its universal property.
     - [CSub P], for any Type-valued predicate [P] on the circle's
       points, has as points the points of the circle with a witness of
       [P], compared as points of the circle, and as opens the
       predicates each of whose points has a ball of the circle,
       [cball], inside them among the points of [P].  [csub_incl], the
       inclusion, is continuous ([csub_incl_cont]).  [csub_universal]: a
       setoid map from ANY space into the points of [P] is continuous
       into [CSub P] iff its composite with the inclusion is continuous
       into [Circle]; the content, [csub_lift_cont], takes the union
       over the points of an open of the preimages of the open interiors
       [cint] of the circle's balls, Instance/Top/Solenoid.v's
       [sol_lift_cont] argument without its finite intersection.
       [csub_coarsest]: every topology on the points of [P] making the
       inclusion continuous contains every open of [CSub P].  So
       [CSub P] carries the initial topology for the inclusion, which is
       the subspace topology.
     - The arc is [tarc y], the Type-valued interior [cint y (1/4)]
       itself, and [in_arc y x] IS [inhabited (tarc y x)]
       ([in_arc_squash], [eq_refl]); [tsheet p y k z] is the Type-valued
       [in_sheet].  The Prop-valued arc is not used here: the sections
       consume the radius that [tarc] carries as data.  Whether
       [in_arc y] is itself open in [Circle] is not stated in this file.
     - [wrap_evenly_covered]: the arc is open ([tarc_open]) and contains
       y ([tarc_centre]), each sheet is open ([tsheet_open]), the sheets
       are disjoint ([tsheet_disjoint]), and the preimage of the arc is
       the union of the sheets 0 <= k < p ([tsheet_preimage]), an
       [iffT].
     - [wrap_sheet_iso]: [TSheet p y k], the sheet as [CSub], is
       isomorphic in [Top] to [TArc y], the arc as [CSub].  The forward
       arrow [wrap_sheet] is the restriction of [wrap p], continuous by
       [csub_lift_cont] from the continuity of [wrap p] after the
       inclusion ([wrap_sheet_iso_to], [eq_refl]); the inverse
       [tsheet_lift_mor] is the same local section [sheet_lift].
   The sections, the index, the Lipschitz bound and the fibre count are
   statements about the circle's points, shared by the two coverings.
   The names follow Instance/Top/Circle.v's: [wrap_*] for the
   Type-valued map, [pwrap_*] for the [PTopCat] one; [ArcSpace],
   [SheetSpace] and [sheet_lift_mor] are the [PTopCat] subspaces and
   section, [TArc], [TSheet] and [tsheet_lift_mor] the [Top] ones.

   STRENGTHS.  At [eq_refl]: [circ_pow_map], [GroupTower_step],
   [group_step_fn], [pspace_step_fn], [space_step_fn],
   [group_solenoid_points], [solenoid_carriers_agree],
   [solenoid_equiv_agree], [gsol_leg_map], [gsol_plus_coord],
   [gsol_zero_coord], [gsol_neg_coord], [sol_fibre_carrier],
   [zp_to_fibre_coord], [zp_one_to_unit_string], [pwrap_sheet_iso_to],
   [in_arc_squash], [wrap_sheet_iso_to].  Up to [≈] in
   [Functor_Setoid]: [GroupTower_points], [towers_agree],
   [CircleTower_points].  Isomorphisms: [solenoid_points_iso] in [Sets],
   [Zp_fibre_iso] in [Ab], [pwrap_sheet_iso] in [PTopCat],
   [wrap_sheet_iso] in [Top].  Type-valued equivalences ([↔], the
   library's [iffT]): [csub_universal], and the last component of
   [wrap_evenly_covered].  [Print Assumptions] prints "Closed under the
   global context" for every one of the file's 164 constants, listed by
   [Print Module] and including its 30 [Program] obligations.

   UNIVERSES, read by [About] under [Set Printing Universes] on the 164
   constants.
     - Lists: [@{o}] (53 constants: the arcs, sheets and subspaces of both
       coverings and their lemmas), [@{s u o so r}] (35: the group
       solenoid, its fibre and the maps between the fibre and Z_p),
       [@{}] (28: the rational and real arithmetic), [@{h o}] (13: the
       inclusion of [CSub] and its universal property, and the maps and
       isomorphism of the [Top] covering), [@{s o so}] (9: [ZpAb], the
       coordinates [zp_coord] and the integers [fibre_int]), [@{o so}]
       (7: the maps of [PTopCat]), [@{u}] (5), [@{u o}] (4: [circ_pow]),
       [@{s u o}] (2), [@{s u o so u0 u1}] (2), and single constants at
       [@{s h o hs u u0}], [@{s u o so}], [@{s o so u}], [@{s h o hs}],
       [@{i}] and [@{o u u0 u1}].  Here [s] is [Omega]'s object
       universe, [o] the points, [so] their [Sets] and [PTopCat]
       universe, [u] [Ab]'s object universe, [h] and [hs] [Top]'s homs
       and their [Sets], [r] the limit.
     - [GroupTower_points] and [towers_agree] read [@{s u o so u0 u1}],
       [CircleTower_points] [@{s h o hs u u0}]: the two extra universes
       are Theory/Functor.v's [Functor_Setoid] setoid universes, bounded
       below by the shape and target universes.  [pspace_step_fn]'s extra
       [u] is [Compose]'s auxiliary ([About Compose]: u3 < u2).
       [zres_of_eq] is [@{o u u0 u1}]: Instance/Rng/Zp.v's [ResRing]
       universes, u1 above o by [ResRing]'s own bound.
     - [GroupSolenoid] instantiates [Ab_Forget_lifts_limits] with its
       limit universe and both auxiliaries [r], adding [u <= r] and
       [so <= r], and [Sets_tower_Limit] with its auxiliary at [o].  [ZpAb]
       instantiates Instance/Rng/Zp.v's [Zp@{o o o o so s so o so}]: the
       integer ring, the carrier and one auxiliary at [o], three
       auxiliaries at [so], one at [s].
     - No block carries an equation, and no universe is instantiated at
       [Set].  Strict bounds among the file's universes: [o < so] (55
       blocks), [o < u] (45, [Ab]'s own), [o < h] (15, [Top]'s: the 13
       [@{h o}] constants, [CircleTower_points] and [space_step_fn]),
       [h < hs] (2, [Top_Forget]'s, the last two), [o < u1] (1,
       [zres_of_eq]).
     - The word [Set] occurs 878 times: [Set < u] in 44 blocks ([Ab]'s
       own bound, first carried by [circ_pow]'s first obligation);
       [Set < so] in 31, from [PTopCat] (9 blocks, first [towers_agree])
       and from [Zp]'s own [Set] bound on the auxiliary set to [so] (22,
       first [ZpAb]); and otherwise strict lower bounds of the standard
       library's monomorphic universes: [Basics.flip.u0], [.u1], [.u2] in
       145 blocks, [Morphisms.Proper.u0] and [Morphisms.Relations.u0] in
       102 and [Morphisms.GenericInstances.u0] in 86 (all first
       [int_near_zero]), and [eq_ind_r.u0] in 78 (first [CircleGroup]'s
       first obligation).  Instance/Top/Circle.v's header explains these
       bounds; a one-line scratch lemma that rewrites with [Zlt_Qlt], an
       equation between two propositions, carries [eq_ind_r.u0] alone,
       [Prop] having sort [Set+1].
     - [<=] caps on global universes, first carriers in file order:
       [Basics.compose] and [ID] ([circ_pow]'s obligations, through
       [Ab]),
       [eq_rect_r], [eq_ind], [eq_ind_r] and [Logic_lemmas.equality]
       ([GroupTower], through [Omega]), [Projections] and [prod_rect]
       ([GroupSolenoid]), [projections] ([CircleTower_points]) and
       [Subset_projections] ([ArcSpace]); on [h], the [Top_Forget] caps
       of [CircleTower_points] and [space_step_fn].
     - [zp_coord_respects@{s o so +}], [pwrap_evenly_covered@{o +}] and
       [wrap_evenly_covered@{o +}] have extensible universe lists: Coq
       8.19.2 and 8.20.1 refuse their closed lists ("unbound"); [About]
       reads back [@{s o so}], [@{o}] and [@{o}] on Rocq 9.1 and on Coq
       8.19.2.  [csub_coarsest@{h o +}]
       has one because Rocq 9.1 itself refuses its closed list, "Universes
       ... are unbound", at the coercion of [csub_setoid P] in its binder
       for [Tp]; [About] reads back [@{h o}].

   NOT DELIVERED.  Covering-space theory beyond evenly covered
   neighbourhoods (path lifting, the fundamental group of the circle);
   the fibre as a SUBSPACE homeomorphic to Z_p with its profinite
   topology ([Zp_fibre_iso] is an isomorphism of groups, and a grep for
   [ZpCarrier], [Zp ZComm] and [Zp_int] over the tree's .v files finds
   only Instance/Rng/Zp.v, its probe, Instance/Rng/Limit.v's header and
   this file, none of them topologizing Z_p); continuity of the
   solenoid's addition, so no topological group on either solenoid;
   the tower R/p^nZ of Wikipedia's article and the presentation of the
   solenoid as (R × Z_p)/Z; an identification at [eq_refl] of the
   group solenoid's points with the space solenoids' as setoid objects
   (refused because of the donor's opacity, and the donor is not
   edited); a version of the fibre inverse that rounds instead of
   reading the witnesses; a comparison of [CSub] with the subspaces of
   Instance/Top/Subspace/TypeValued.v beyond the universal property
   both satisfy (the latter one universe up); any comparison functor
   between [Top] and [PTopCat].  Nothing here uses primality. *)

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(** ** An integer near zero *)

(* An integer that is the difference of two reals within [ra] and [rb] of
   zero, with ra + rb < 1, is zero. *)
Lemma int_near_zero@{} (t : Z) (a b : CReal) (ra rb : Q) :
  CRealLe (CReal_abs a) (inject_Q ra) →
  CRealLe (CReal_abs b) (inject_Q rb) →
  Qlt (ra + rb) 1 →
  CRealEq (CReal_minus a b) (inject_Z t) → t = 0%Z.
Proof.
  intros Ha Hb Hr Ht.
  assert (T : CRealLe (CReal_abs (inject_Z t)) (inject_Q (ra + rb))).
  { rewrite <- Ht, inject_Q_plus. unfold CReal_minus.
    apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
    rewrite CReal_abs_opp. apply CReal_plus_le_compat; assumption. }
  apply CReal_abs_def2 in T. destruct T as [T1 T2].
  rewrite <- opp_inject_Q in T2. unfold inject_Z in T1, T2.
  apply le_inject_Q in T1. apply le_inject_Q in T2.
  assert (U1 : Qlt (t # 1) 1) by (eapply Qle_lt_trans; eassumption).
  assert (U2 : Qlt (-1 # 1) (t # 1)).
  { apply (Qlt_le_trans _ (- (ra + rb))); [|exact T2].
    change (-1 # 1)%Q with (- 1)%Q. lra. }
  cbv [Qlt Qnum Qden] in U1, U2. lia.
Qed.

(** ** The circle group and its p-th power map *)

Program Definition CircleGroup@{o} : AbObject@{o o o} := {|
  ab_cmon := {|
    cmon_setoid := Circle_setoid@{o};
    cmon_zero := inject_Q 0;
    cmon_plus := CReal_plus;
    cmon_prop := circ_PropEquiv@{o}
  |};
  ab_neg := CReal_opp
|}.
Next Obligation.
  intros x x' [k1 H1] y y' [k2 H2]. exists (k1 + k2)%Z.
  rewrite inject_Z_plus, <- H1, <- H2. unfold CReal_minus. ring.
Qed.
Next Obligation. intros a b c. apply circ_eq_of_creal. simpl. ring. Qed.
Next Obligation. intros a b. apply circ_eq_of_creal. simpl. ring. Qed.
Next Obligation. intros a. apply circ_eq_of_creal. simpl. ring. Qed.
Next Obligation.
  intros x y [k Hk]. exists (- k)%Z.
  rewrite opp_inject_Z, <- Hk. unfold CReal_minus. ring.
Qed.
Next Obligation. intros a. apply circ_eq_of_creal. simpl. ring. Qed.

(* Riehl's "pth power map", written additively. *)
Program Definition circ_pow@{u o} (p : positive) :
  CircleGroup@{o} ~{Ab@{u o}}~> CircleGroup@{o} := {|
  cmon_map := circ_mul@{o} p
|}.
Next Obligation. intros p. apply circ_eq_of_creal. simpl. ring. Qed.
Next Obligation. intros p a b. apply circ_eq_of_creal. simpl. ring. Qed.

Example circ_pow_map@{u o} (p : positive) :
  cmon_map (circ_pow@{u o} p) = circ_mul@{o} p := eq_refl.

(** ** The group tower and the space towers have one underlying tower *)

Definition GroupTower@{s u o} (p : positive) :
  Omega@{s o o}^op ⟶ Ab@{u o} :=
  @EndoTower Ab@{u o} CircleGroup@{o} (circ_pow@{u o} p).

Example GroupTower_step@{s u o +} (p : positive) (n : nat) :
  fmap[GroupTower@{s u o} p] (omega_step n) = id ∘ circ_pow p := eq_refl.

Lemma GroupTower_points@{s u o so +} (p : positive) :
  Ab_Forget@{u so o} ◯ GroupTower@{s u o} p ≈ UCircleTower@{s o so} p.
Proof. exact (EndoTower_map Ab_Forget CircleGroup (circ_pow p)). Qed.

Lemma towers_agree@{s u o so +} (p : positive) :
  PForget@{o so} ◯ PCircleTower@{s o so} p
    ≈ Ab_Forget@{u so o} ◯ GroupTower@{s u o} p.
Proof.
  transitivity (UCircleTower@{s o so} p).
  - exact (PCircleTower_points p).
  - symmetry. exact (GroupTower_points p).
Qed.

(* Mac Lane's tower in the Type-valued [Top]: its underlying tower lands in
   the lifted [Sets@{h hs}], where it is the tower of points taken at the
   hom universe [h] (Instance/Top/Circle.v's [circle_lift_iso]). *)
Lemma CircleTower_points@{s h o hs + | o < h, h < hs +} (p : positive) :
  Top_Forget@{o h hs} ◯ CircleTower@{s h o} p ≈ UCircleTower@{s h hs} p.
Proof.
  exists (fun _ => circle_lift_iso@{h o hs}).
  intros m n f x. simpl.
  induction f as [|k f' IH].
  - apply circ_eq_refl.
  - exact (IH (CReal_mult (posR p) x)).
Qed.

(* The generating function of each tower, read on points. *)
Example group_step_fn@{s u o so +} (p : positive) (n : nat) (x : CReal) :
  fmap[Ab_Forget@{u so o} ◯ GroupTower@{s u o} p] (omega_step n) x
  = CReal_mult (posR p) x := eq_refl.

Example pspace_step_fn@{s o so +} (p : positive) (n : nat) (x : CReal) :
  fmap[PForget@{o so} ◯ PCircleTower@{s o so} p] (omega_step n) x
  = CReal_mult (posR p) x := eq_refl.

Example space_step_fn@{s h o hs + | o < h, h < hs +} (p : positive)
  (n : nat) (x : CReal) :
  fmap[Top_Forget@{o h hs} ◯ CircleTower@{s h o} p] (omega_step n) x
  = CReal_mult (posR p) x := eq_refl.

(** ** The group solenoid, on the same matching strings *)

(* Instance/Ab/Limit.v's creation of limits by [Ab_Forget], at the matching
   strings of the underlying tower. *)
Definition GroupSolenoid@{s u o so r | o < u, o < so +} (p : positive) :
  Limit@{r s o u} (GroupTower@{s u o} p) :=
  Ab_Forget_lifts_limits@{r r r u s o so} (GroupTower@{s u o} p)
    (Sets_tower_Limit@{s o so r o}
       (Ab_Forget@{u so o} ◯ GroupTower@{s u o} p)).

Definition GSolenoid@{s u o so r | o < u, o < so +} (p : positive) :
  AbObject@{o o o} :=
  vertex_obj[@limit_cone _ _ _ (GroupSolenoid@{s u o so r} p)].

Definition gsol_leg@{s u o so r | o < u, o < so +} (p : positive)
  (n : nat) : GSolenoid@{s u o so r} p ~{Ab@{u o}}~> CircleGroup@{o} :=
  cone_leg (@limit_cone _ _ _ (GroupSolenoid@{s u o so r} p)) n.

Example group_solenoid_points@{s u o so r | o < u, o < so +}
  (p : positive) :
  Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  = inverse_limit (Ab_Forget@{u so o} ◯ GroupTower@{s u o} p) := eq_refl.

Example solenoid_carriers_agree@{s u o so r | o < u, o < so +}
  (p : positive) :
  carrier (SolPoints@{s o so} p)
  = carrier (cmon_setoid (GSolenoid@{s u o so r} p)) := eq_refl.

Example solenoid_equiv_agree@{s u o so r | o < u, o < so +}
  (p : positive) :
  @equiv _ (is_setoid (SolPoints@{s o so} p))
  = @equiv _ (is_setoid (cmon_setoid (GSolenoid@{s u o so r} p)))
  := eq_refl.

Example gsol_leg_map@{s u o so r | o < u, o < so +} (p : positive)
  (n : nat) (x : SolPoints@{s o so} p) :
  cmon_map (gsol_leg@{s u o so r} p n) x = sol_pr@{s o so} p n x := eq_refl.

(* Mac Lane's pointwise operations (book p. 110), read back. *)
Example gsol_plus_coord@{s u o so r | o < u, o < so +} (p : positive)
  (n : nat) (a b : SolPoints@{s o so} p) :
  sol_pr@{s o so} p n (cmon_plus (GSolenoid@{s u o so r} p) a b)
  = CReal_plus (sol_pr@{s o so} p n a) (sol_pr@{s o so} p n b) := eq_refl.

Example gsol_zero_coord@{s u o so r | o < u, o < so +} (p : positive)
  (n : nat) :
  sol_pr@{s o so} p n (cmon_zero (GSolenoid@{s u o so r} p)) = inject_Q 0
  := eq_refl.

Example gsol_neg_coord@{s u o so r | o < u, o < so +} (p : positive)
  (n : nat) (a : SolPoints@{s o so} p) :
  sol_pr@{s o so} p n (ab_neg (GSolenoid@{s u o so r} p) a)
  = CReal_opp (sol_pr@{s o so} p n a) := eq_refl.

Program Definition solenoid_points_iso@{s u o so r | o < u, o < so +}
  (p : positive) :
  SolPoints@{s o so} p
    ≅[Sets@{o so}] Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  := {| to := {| morphism := fun x => x |};
        from := {| morphism := fun x => x |} |}.
Next Obligation. intros p x y H. exact H. Qed.
Next Obligation. intros p x y H. exact H. Qed.
Next Obligation. intros p x n. apply circ_eq_refl. Qed.
Next Obligation. intros p x n. apply circ_eq_refl. Qed.

(** ** The fibre over the base point is the p-adic integers *)

(* The rational identities behind the fibre, stated on bare integers so
   that [ring] sees syntactic atoms. *)
Lemma q_fibre_step@{} (p P : positive) (a b k : Z) :
  a = (b + Zpos P * k)%Z →
  Qeq ((Zpos p # 1) * (a # (p * P)) - (b # P)) (k # 1).
Proof.
  intro E. subst a. cbv [Qeq Qminus Qplus Qmult Qopp Qnum Qden].
  rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma q_fibre_base@{} (a : Z) : Qeq ((a # 1) - 0) (a # 1).
Proof. cbv [Qeq Qminus Qplus Qopp Qnum Qden]. rewrite ?Pos2Z.inj_mul. ring. Qed.

Lemma q_fibre_diff@{} (P : positive) (a b k : Z) :
  a = (b + Zpos P * k)%Z → Qeq ((a # P) - (b # P)) (k # 1).
Proof.
  intro E. subst a. cbv [Qeq Qminus Qplus Qopp Qnum Qden].
  rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma q_fibre_add@{} (P : positive) (a b : Z) :
  Qeq (((a + b)%Z) # P) ((a # P) + (b # P)).
Proof.
  cbv [Qeq Qplus Qnum Qden]. rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma q_fibre_zero@{} (P : positive) : Qeq (0 # P) 0.
Proof. reflexivity. Qed.

Lemma q_fibre_split@{} (P : positive) (a : Z) :
  Qeq (a # P) ((1 # P) * (a # 1)).
Proof.
  cbv [Qeq Qmult Qnum Qden]. rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma q_fibre_unit@{} (P : positive) : Qeq ((1 # P) * (Zpos P # 1)) 1.
Proof.
  cbv [Qeq Qmult Qnum Qden]. rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma creal_fibre_add@{} (P : positive) (a b : Z) :
  CRealEq (inject_Q (((a + b)%Z) # P))
          (CReal_plus (inject_Q (a # P)) (inject_Q (b # P))).
Proof.
  rewrite <- inject_Q_plus. apply inject_Q_morph_T. exact (q_fibre_add _ _ _).
Qed.

(* Dividing by p^n undoes multiplying by it. *)
Lemma creal_recover@{} (P : positive) (a : Z) (x : CReal) :
  CRealEq (inject_Z a) (CReal_mult (inject_Z (Zpos P)) x) →
  CRealEq (inject_Q (a # P)) x.
Proof.
  intro H.
  assert (E : CRealEq (CReal_mult (inject_Q (1 # P)) (inject_Z (Zpos P)))
                      (inject_Q 1)).
  { unfold inject_Z. rewrite <- inject_Q_mult. apply inject_Q_morph_T.
    exact (q_fibre_unit P). }
  rewrite (inject_Q_morph_T _ _ (q_fibre_split P a)), inject_Q_mult.
  change (inject_Q (a # 1)) with (inject_Z a). rewrite H.
  rewrite <- CReal_mult_assoc, E. ring.
Qed.

Lemma creal_scale_back@{} (P : positive) (a : Z) :
  CRealEq (CReal_mult (inject_Z (Zpos P)) (inject_Q (a # P))) (inject_Z a).
Proof.
  unfold inject_Z. rewrite <- inject_Q_mult. apply inject_Q_morph_T.
  cbv [Qeq Qmult Qnum Qden]. rewrite !Pos2Z.inj_mul. ring.
Qed.

(* The real identities behind the inverse, on universally quantified reals
   so that [ring] sees syntactic atoms. *)
Lemma fibre_real_step@{} (P p s0 s1 a k : CReal) :
  CRealEq a (CReal_mult P s0) →
  CRealEq (CReal_minus (CReal_mult p s1) s0) k →
  CRealEq (CReal_plus a (CReal_mult P k)) (CReal_mult (CReal_mult p P) s1).
Proof.
  intros H1 H2. rewrite H1, <- H2. unfold CReal_minus. ring.
Qed.

Lemma fibre_real_diff@{} (P x y w a b : CReal) :
  CRealEq a (CReal_mult P x) → CRealEq b (CReal_mult P y) →
  CRealEq (CReal_minus x y) w →
  CRealEq (CReal_plus a (CReal_opp b)) (CReal_mult P w).
Proof.
  intros H1 H2 H3. rewrite H1, H2, <- H3. unfold CReal_minus. ring.
Qed.

Lemma fibre_real_sum@{} (P x y a b c : CReal) :
  CRealEq a (CReal_mult P (CReal_plus x y)) →
  CRealEq b (CReal_mult P x) → CRealEq c (CReal_mult P y) →
  CRealEq a (CReal_plus b c).
Proof. intros H1 H2 H3. rewrite H1, H2, H3. ring. Qed.

Lemma fibre_real_zero@{} (P a : CReal) :
  CRealEq a (CReal_mult P (inject_Q 0)) → CRealEq a (inject_Q 0).
Proof. intro H. rewrite H. ring. Qed.

Lemma fibre_real_base@{} (s0 z0 : CReal) :
  CRealEq (CReal_minus s0 (inject_Q 0)) z0 →
  CRealEq z0 (CReal_mult (inject_Q 1) s0).
Proof. intro H. rewrite <- H. unfold CReal_minus. ring. Qed.

Lemma dpow_ppow@{i} (p : positive) (n : nat) :
  @dpow Int_Ring@{i i i} (Zpos p) n = Zpos (ppow p n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(* The additive group of Instance/Rng/Zp.v's p-adic integers. *)
Definition ZpAb@{s o so | o < so +} (p : positive) : AbObject@{o o o} :=
  ring_ab@{o o o} (Zp@{o o o o so s so o so} ZComm@{o o o} (Zpos p)).

(* Equal integers are equal residues. *)
Lemma zres_of_eq@{o +} (p : positive) (n : nat) (x y : Z) :
  x = y → @equiv _ (rig_setoid (ResRing ZComm@{o o o} (Zpos p) n)) x y.
Proof. intro E. apply (res_of_dvd (Zpos p) n x y 0%Z). lia. Qed.

(** *** From the p-adic integers into the fibre: f ↦ (f_n / p^n)_n *)

Definition zp_coord@{s o so | o < so +} (p : positive)
  (f : carrier (cmon_setoid (ZpAb@{s o so} p))) (n : nat) : CReal :=
  inject_Q ((`1 f n) # ppow p n).

Lemma zp_coord_compat@{s o so | o < so +} (p : positive)
  (Hp : (1 < p)%positive) (f : carrier (cmon_setoid (ZpAb@{s o so} p)))
  (n : nat) :
  circ_eq@{o} (CReal_mult (posR p) (zp_coord@{s o so} p f (S n)))
              (zp_coord@{s o so} p f n).
Proof.
  assert (Hz : (1 < Zpos p)%Z) by lia.
  destruct (res_to_dvd (Zpos p) Hz n (`1 f (S n)) (`1 f n) (`2 f n))
    as [k Hk].
  rewrite dpow_ppow in Hk.
  exists k. unfold zp_coord, posR, inject_Z. rewrite <- inject_Q_mult.
  apply inject_Q_minus_int. apply (q_fibre_step p (ppow p n)). lia.
Qed.

Definition zp_string@{s o so | o < so +} (p : positive)
  (Hp : (1 < p)%positive) (f : carrier (cmon_setoid (ZpAb@{s o so} p))) :
  SolPoints@{s o so} p.
Proof.
  exists (zp_coord@{s o so} p f). exact (zp_coord_compat p Hp f).
Defined.

Lemma zp_coord_base@{s o so | o < so +} (p : positive)
  (f : carrier (cmon_setoid (ZpAb@{s o so} p))) :
  circ_eq@{o} (zp_coord@{s o so} p f 0) (inject_Q 0).
Proof.
  exists (`1 f 0%nat). unfold zp_coord, inject_Z. apply inject_Q_minus_int.
  exact (q_fibre_base _).
Qed.

Lemma zp_coord_respects@{s o so + | o < so +} (p : positive)
  (Hp : (1 < p)%positive) (f g : carrier (cmon_setoid (ZpAb@{s o so} p))) :
  f ≈ g → ∀ n, circ_eq@{o} (zp_coord@{s o so} p f n) (zp_coord@{s o so} p g n).
Proof.
  intros H n.
  assert (Hz : (1 < Zpos p)%Z) by lia.
  destruct (res_to_dvd (Zpos p) Hz n (`1 f n) (`1 g n) (H n)) as [k Hk].
  rewrite dpow_ppow in Hk.
  exists k. unfold zp_coord, inject_Z. apply inject_Q_minus_int.
  apply q_fibre_diff. lia.
Qed.

(* The fibre of the leg μ_0 over the base point 0: the kernel of μ_0. *)
Definition SolFibre@{s u o so r | o < u, o < so +} (p : positive) :
  AbObject@{o o o} :=
  AbKernel@{o o o o o o u u} (gsol_leg@{s u o so r} p 0).

Example sol_fibre_carrier@{s u o so r | o < u, o < so +} (p : positive) :
  carrier (cmon_setoid (SolFibre@{s u o so r} p))
  = { x : SolPoints@{s o so} p &
      circ_eq@{o} (sol_pr@{s o so} p 0 x) (inject_Q 0) } := eq_refl.

Program Definition zp_to_fibre_map@{s u o so r | o < u, o < so +}
  (p : positive) (Hp : (1 < p)%positive) :
  SetoidMorphism@{o o o} (cmon_setoid (ZpAb@{s o so} p))
    (cmon_setoid (SolFibre@{s u o so r} p)) := {|
  morphism := fun f => (zp_string@{s o so} p Hp f; zp_coord_base p f)
|}.
Next Obligation. intros p Hp f g H. exact (zp_coord_respects p Hp f g H). Qed.

Program Definition zp_to_fibre@{s u o so r | o < u, o < so +}
  (p : positive) (Hp : (1 < p)%positive) :
  ZpAb@{s o so} p ~{Ab@{u o}}~> SolFibre@{s u o so r} p := {|
  cmon_map := zp_to_fibre_map@{s u o so r} p Hp
|}.
Next Obligation.
  intros p Hp n. apply circ_eq_of_creal. apply inject_Q_morph_T.
  exact (q_fibre_zero _).
Qed.
Next Obligation.
  intros p Hp f g n. apply circ_eq_of_creal. exact (creal_fibre_add _ _ _).
Qed.

Example zp_to_fibre_coord@{s u o so r | o < u, o < so +} (p : positive)
  (Hp : (1 < p)%positive) (f : carrier (cmon_setoid (ZpAb@{s o so} p)))
  (n : nat) :
  sol_pr@{s o so} p n (projT1 (cmon_map (zp_to_fibre@{s u o so r} p Hp) f))
  = inject_Q ((`1 f n) # ppow p n) := eq_refl.

(* The p-adic integer 1 goes to Instance/Top/Solenoid.v's [unit_string]. *)
Example zp_one_to_unit_string@{s u o so r | o < u, o < so +}
  (p : positive) (Hp : (1 < p)%positive) :
  `1 (projT1 (cmon_map (zp_to_fibre@{s u o so r} p Hp)
                (rig_one (Zp@{o o o o so s so o so} ZComm@{o o o} (Zpos p)))))
  = `1 (unit_string@{s o so} p) := eq_refl.

(** *** From the fibre back: the integers p^n x_n, read off the witnesses *)

Fixpoint fibre_int@{s o so | o < so +} (p : positive)
  (x : SolPoints@{s o so} p) (z0 : Z) (n : nat) : Z :=
  match n with
  | O => z0
  | S m => (fibre_int p x z0 m + Zpos (ppow p m) * projT1 (`2 x m))%Z
  end.

Lemma fibre_int_step@{s o so | o < so +} (p : positive)
  (x : SolPoints@{s o so} p) (z0 : Z) (n : nat) :
  (fibre_int p x z0 (S n) + - fibre_int p x z0 n
   = Zpos (ppow p n) * projT1 (`2 x n))%Z.
Proof. cbn [fibre_int]. lia. Qed.

Lemma fibre_int_spec@{s o so | o < so +} (p : positive)
  (x : SolPoints@{s o so} p) (z0 : Z)
  (H0 : CRealEq (CReal_minus (sol_pr@{s o so} p 0 x) (inject_Q 0))
                (inject_Z z0))
  (n : nat) :
  CRealEq (inject_Z (fibre_int p x z0 n))
          (CReal_mult (inject_Z (Zpos (ppow p n))) (sol_pr@{s o so} p n x)).
Proof.
  induction n as [|m IH]; cbn [fibre_int].
  - exact (fibre_real_base _ _ H0).
  - destruct (`2 x m) as [k Hk]; cbn [projT1].
    rewrite inject_Z_plus, creal_inject_Z_mult.
    change (Zpos (ppow p (S m))) with (Zpos p * Zpos (ppow p m))%Z.
    rewrite creal_inject_Z_mult.
    exact (fibre_real_step _ _ _ _ _ _ IH Hk).
Qed.

Definition fibre_coord@{s u o so r | o < u, o < so +} (p : positive)
  (a : carrier (cmon_setoid (SolFibre@{s u o so r} p))) (n : nat) : Z :=
  fibre_int@{s o so} p (projT1 a) (projT1 (projT2 a)) n.

Lemma fibre_coord_spec@{s u o so r | o < u, o < so +} (p : positive)
  (a : carrier (cmon_setoid (SolFibre@{s u o so r} p))) (n : nat) :
  CRealEq (inject_Z (fibre_coord@{s u o so r} p a n))
          (CReal_mult (inject_Z (Zpos (ppow p n)))
                      (sol_pr@{s o so} p n (projT1 a))).
Proof. exact (fibre_int_spec p (projT1 a) _ (projT2 (projT2 a)) n). Qed.

Definition fibre_to_zp_pt@{s u o so r | o < u, o < so +} (p : positive)
  (a : carrier (cmon_setoid (SolFibre@{s u o so r} p))) :
  carrier (cmon_setoid (ZpAb@{s o so} p)).
Proof.
  exists (fibre_coord@{s u o so r} p a). intro n.
  apply (res_of_dvd (Zpos p) n _ _
           (projT1 (`2 (projT1 a : SolPoints@{s o so} p) n))).
  rewrite dpow_ppow. exact (fibre_int_step p (projT1 a) _ n).
Defined.

Program Definition fibre_to_zp_map@{s u o so r | o < u, o < so +}
  (p : positive) :
  SetoidMorphism@{o o o} (cmon_setoid (SolFibre@{s u o so r} p))
    (cmon_setoid (ZpAb@{s o so} p)) := {|
  morphism := fibre_to_zp_pt@{s u o so r} p
|}.
Next Obligation.
  intros p a b H n. destruct (H n) as [w Hw].
  apply (res_of_dvd (Zpos p) n _ _ w). rewrite dpow_ppow.
  apply creal_inject_Z_injective.
  rewrite inject_Z_plus, opp_inject_Z, creal_inject_Z_mult.
  exact (fibre_real_diff _ _ _ _ _ _ (fibre_coord_spec p a n)
           (fibre_coord_spec p b n) Hw).
Qed.

Program Definition fibre_to_zp@{s u o so r | o < u, o < so +}
  (p : positive) :
  SolFibre@{s u o so r} p ~{Ab@{u o}}~> ZpAb@{s o so} p := {|
  cmon_map := fibre_to_zp_map@{s u o so r} p
|}.
Next Obligation.
  intros p n. apply zres_of_eq.
  apply creal_inject_Z_injective.
  exact (fibre_real_zero _ _ (fibre_coord_spec p (cmon_zero (SolFibre p)) n)).
Qed.
Next Obligation.
  intros p a b n. apply zres_of_eq.
  assert (E : fibre_coord p (cmon_plus (SolFibre p) a b) n
              = (fibre_coord p a n + fibre_coord p b n)%Z).
  { apply creal_inject_Z_injective. rewrite inject_Z_plus.
    exact (fibre_real_sum _ _ _ _ _ _
             (fibre_coord_spec p (cmon_plus (SolFibre p) a b) n)
             (fibre_coord_spec p a n) (fibre_coord_spec p b n)). }
  exact E.
Qed.

(* The fibre of μ_0 over the base point is Z_p, as abelian groups. *)
Program Definition Zp_fibre_iso@{s u o so r | o < u, o < so +}
  (p : positive) (Hp : (1 < p)%positive) :
  @Isomorphism Ab@{u o} (ZpAb@{s o so} p) (SolFibre@{s u o so r} p) := {|
  to := zp_to_fibre@{s u o so r} p Hp;
  from := fibre_to_zp@{s u o so r} p
|}.
Next Obligation.
  intros p Hp a n. apply circ_eq_of_creal. simpl.
  exact (creal_recover _ _ _ (fibre_coord_spec p a n)).
Qed.
Next Obligation.
  intros p Hp f n. apply zres_of_eq.
  apply creal_inject_Z_injective.
  rewrite (fibre_coord_spec p (cmon_map (zp_to_fibre p Hp) f) n).
  exact (creal_scale_back _ _).
Qed.

(** ** The covering in [PTopCat]: evenly covered neighbourhoods *)

Lemma qmin_pos@{} (a b : Q) :
  Qlt 0 a → Qlt 0 b → { e : Q & (Qlt 0 e * Qle e a * Qle e b)%type }.
Proof.
  intros Ha Hb. destruct (Qlt_le_dec a b) as [H|H].
  - exists a. split; [split|]; [exact Ha|apply Qle_refl|apply Qlt_le_weak, H].
  - exists b. split; [split|]; [exact Hb|exact H|apply Qle_refl].
Qed.

Lemma q_quarter_half@{} : Qeq (1 # 2) ((1 # 4) + (1 # 4)).
Proof. reflexivity. Qed.

Lemma q_scale_le@{} (p : positive) (e f : Q) :
  Qle e (f * (Zpos p # 1)) → Qle (e * (1 # p)) f.
Proof.
  destruct e as [n d], f as [n' d']; cbv [Qle Qmult Qnum Qden].
  rewrite !Pos2Z.inj_mul. nia.
Qed.

Lemma q_p_pos@{} (p : positive) (f : Q) : Qlt 0 f → Qlt 0 (f * (Zpos p # 1)).
Proof.
  intro H. apply Qmult_lt_0_compat; [exact H|]. cbv [Qlt Qnum Qden]. lia.
Qed.

(* Multiplication by [p], with the integer translate kept explicit. *)
Lemma mul_ball@{} (p : positive) (z z' : CReal) (i : Z) (e : Q) :
  CRealLe (CReal_abs (CReal_plus (CReal_minus z' z) (inject_Z i)))
          (inject_Q (e * (1 # p))) →
  CRealLe (CReal_abs (CReal_plus
             (CReal_minus (CReal_mult (posR p) z') (CReal_mult (posR p) z))
             (inject_Z (Zpos p * i)))) (inject_Q e).
Proof.
  intro b.
  assert (E : CRealEq
    (CReal_plus (CReal_minus (CReal_mult (posR p) z') (CReal_mult (posR p) z))
                (inject_Z (Zpos p * i)))
    (CReal_mult (posR p) (CReal_plus (CReal_minus z' z) (inject_Z i)))).
  { rewrite creal_inject_Z_mult. unfold posR, CReal_minus. ring. }
  rewrite E, CReal_abs_mult, (CReal_abs_right (posR p) (posR_nonneg p)).
  apply (CReal_le_trans _ (CReal_mult (posR p) (inject_Q (e * (1 # p))))).
  - apply CReal_mult_le_compat_l; [exact (posR_nonneg p)|exact b].
  - unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_le.
    destruct e as [n d]; cbv [Qle Qmult Qnum Qden].
    rewrite !Pos2Z.inj_mul; nia.
Qed.

(* The arc about [y]: the interior of the closed ball of radius 1/4. *)
Definition in_arc@{o} (y : CReal) (x : Circle_setoid@{o}) : Prop :=
  inhabited (cint@{o} y (1 # 4) x).

Lemma in_arc_open@{o} (y : CReal) : POpen PCircle@{o} (in_arc@{o} y).
Proof.
  apply (proj2 (pcircle_open_balls _)).
  intros x [H]. destruct (cint_balls y (1 # 4) x H) as [e [He Hb]].
  exists e. split; [exact He|]. intros z b. exact (inhabits (Hb z b)).
Qed.

Lemma in_arc_centre@{o} (y : CReal) : in_arc@{o} y y.
Proof. constructor. apply cint_centre. reflexivity. Qed.

(* The integer that carries a point of the arc to within 1/4 of [y],
   computed by rounding. *)
Definition arc_shift@{} (y x : CReal) : Z := cround (CReal_minus y x).

Lemma in_arc_shift@{o} (y x : CReal) : in_arc@{o} y x →
  CRealLe (CReal_abs (CReal_plus (CReal_minus x y) (inject_Z (arc_shift y x))))
          (inject_Q (1 # 4)).
Proof.
  intros [H]. destruct (cint_sub y (1 # 4) x H) as [j Hj].
  assert (Ej : arc_shift y x = j).
  { apply cround_ball.
    assert (E : CRealEq (CReal_minus (CReal_minus y x) (inject_Z j))
                  (CReal_opp (CReal_plus (CReal_minus x y) (inject_Z j))))
      by (unfold CReal_minus; ring).
    rewrite E, CReal_abs_opp. exact Hj. }
  rewrite Ej. exact Hj.
Qed.

(* The sheet of [z] over the arc: the residue mod p of the integer that
   brings p z within 1/4 of [y]. *)
Definition sheet_index@{} (p : positive) (y z : CReal) : Z :=
  Z.modulo (- arc_shift y (CReal_mult (posR p) z)) (Zpos p).

Definition in_sheet@{o} (p : positive) (y : CReal) (k : Z)
  (z : Circle_setoid@{o}) : Prop :=
  in_arc@{o} y (CReal_mult (posR p) z) /\ sheet_index p y z = k.

Lemma in_sheet_open@{o} (p : positive) (y : CReal) (k : Z) :
  POpen PCircle@{o} (in_sheet@{o} p y k).
Proof.
  apply (proj2 (pcircle_open_balls _)).
  intros z [HU Hs].
  destruct (proj1 (pcircle_open_balls _) (in_arc_open y) _ HU)
    as [e1 [He1 Hb1]].
  destruct (qmin_pos e1 (1 # 4) He1 ltac:(reflexivity))
    as [e [[He Hle1] Hle2]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros z' [i Hi].
  pose proof (mul_ball p z z' i e Hi) as Hs'.
  assert (HU' : in_arc y (CReal_mult (posR p) z')).
  { apply Hb1. exists (Zpos p * i)%Z.
    apply (CReal_le_trans _ _ _ Hs'). apply inject_Q_le. exact Hle1. }
  split; [exact HU'|].
  pose proof (in_arc_shift y _ HU) as B.
  pose proof (in_arc_shift y _ HU') as B'.
  unfold sheet_index in Hs |- *.
  set (m := arc_shift y (CReal_mult (posR p) z)) in *.
  set (m' := arc_shift y (CReal_mult (posR p) z')) in *.
  assert (Et : (m' + - m + - (Zpos p * i))%Z = 0%Z).
  { apply (int_near_zero _
      (CReal_plus (CReal_minus (CReal_mult (posR p) z') y) (inject_Z m'))
      (CReal_plus (CReal_plus (CReal_minus (CReal_mult (posR p) z) y)
                              (inject_Z m))
                  (CReal_plus (CReal_minus (CReal_mult (posR p) z')
                                           (CReal_mult (posR p) z))
                              (inject_Z (Zpos p * i))))
      (1 # 4) (1 # 2) B').
    - rewrite (inject_Q_morph_T _ _ q_quarter_half), inject_Q_plus.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply CReal_plus_le_compat; [exact B|].
      apply (CReal_le_trans _ _ _ Hs'). apply inject_Q_le. exact Hle2.
    - reflexivity.
    - rewrite !inject_Z_plus, !opp_inject_Z. unfold CReal_minus. ring. }
  rewrite <- Hs.
  replace (- m')%Z with (- m + (- i) * Zpos p)%Z by lia.
  apply Z.mod_add. lia.
Qed.

Lemma in_sheet_disjoint@{o} (p : positive) (y : CReal) (k k' : Z)
  (z : Circle_setoid@{o}) :
  in_sheet@{o} p y k z → in_sheet@{o} p y k' z → k = k'.
Proof. intros [_ H] [_ H']. rewrite <- H, <- H'. reflexivity. Qed.

(* The preimage of the arc under the wrapping map is the union of the p
   sheets. *)
Lemma in_sheet_preimage@{o} (p : positive) (y : CReal)
  (z : Circle_setoid@{o}) :
  in_arc@{o} y (CReal_mult (posR p) z)
  <-> ex (fun k : Z => (0 <= k < Zpos p)%Z /\ in_sheet@{o} p y k z).
Proof.
  split.
  - intro H. exists (sheet_index p y z). split.
    + apply Z.mod_pos_bound. lia.
    + split; [exact H|reflexivity].
  - intros [k [_ [H _]]]. exact H.
Qed.

(** *** The local sections of the wrapping map *)

(* On the arc about [y], the lift of [x] into sheet [k]:
   (x + arc_shift y x + k) / p. *)
Definition sheet_lift@{} (p : positive) (y : CReal) (k : Z) (x : CReal) :
  CReal :=
  CReal_mult (inject_Q (1 # p))
    (CReal_plus (CReal_plus x (inject_Z (arc_shift y x))) (inject_Z k)).

Lemma inv_p_unit@{} (p : positive) :
  CRealEq (CReal_mult (inject_Q (1 # p)) (posR p)) (inject_Q 1).
Proof.
  unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_morph_T.
  exact (q_fibre_unit p).
Qed.

Lemma inv_p_mul@{} (p : positive) (w : CReal) :
  CRealEq (CReal_mult (inject_Q (1 # p)) (CReal_mult (posR p) w)) w.
Proof. rewrite <- CReal_mult_assoc, inv_p_unit. ring. Qed.

Lemma p_sheet_lift@{} (p : positive) (y : CReal) (k : Z) (x : CReal) :
  CRealEq (CReal_mult (posR p) (sheet_lift p y k x))
          (CReal_plus (CReal_plus x (inject_Z (arc_shift y x))) (inject_Z k)).
Proof.
  unfold sheet_lift. rewrite <- CReal_mult_assoc,
    (CReal_mult_comm (posR p)), inv_p_unit. ring.
Qed.

Lemma circ_mul_sheet_lift@{u} (p : positive) (y : CReal) (k : Z) (x : CReal) :
  circ_eq@{u} (CReal_mult (posR p) (sheet_lift p y k x)) x.
Proof.
  exists (arc_shift y x + k)%Z. rewrite p_sheet_lift, inject_Z_plus.
  unfold CReal_minus. ring.
Qed.

Lemma sheet_lift_in@{o} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) (x : CReal) :
  in_arc@{o} y x → in_sheet@{o} p y k (sheet_lift p y k x).
Proof.
  intro Hx. split.
  - apply (popen_proper PCircle (in_arc y) (in_arc_open y) x); [|exact Hx].
    apply circ_eq_sym. apply circ_mul_sheet_lift.
  - unfold sheet_index.
    assert (E : arc_shift y (CReal_mult (posR p) (sheet_lift p y k x))
                = (- k)%Z).
    { unfold arc_shift at 1. apply cround_ball. rewrite p_sheet_lift.
      pose proof (in_arc_shift y x Hx) as B.
      assert (E : CRealEq
        (CReal_minus (CReal_minus y (CReal_plus (CReal_plus x
           (inject_Z (arc_shift y x))) (inject_Z k))) (inject_Z (- k)))
        (CReal_opp (CReal_plus (CReal_minus x y)
                               (inject_Z (arc_shift y x))))).
      { rewrite opp_inject_Z. unfold CReal_minus. ring. }
      rewrite E, CReal_abs_opp. exact B. }
    rewrite E, Z.opp_involutive. apply Z.mod_small. exact Hk.
Qed.

Lemma sheet_lift_respects@{u} (p : positive) (y : CReal) (k : Z)
  (x x' : CReal) :
  in_arc@{u} y x → in_arc@{u} y x' → circ_eq@{u} x x' →
  circ_eq@{u} (sheet_lift p y k x) (sheet_lift p y k x').
Proof.
  intros Hx Hx' [i Hi]. exists 0%Z.
  pose proof (in_arc_shift y x Hx) as B.
  pose proof (in_arc_shift y x' Hx') as B'.
  assert (Et : (i + arc_shift y x + - arc_shift y x')%Z = 0%Z).
  { apply (int_near_zero _
             (CReal_plus (CReal_minus x y) (inject_Z (arc_shift y x)))
             (CReal_plus (CReal_minus x' y) (inject_Z (arc_shift y x')))
             (1 # 4) (1 # 4) B B' ltac:(reflexivity)).
    rewrite !inject_Z_plus, !opp_inject_Z, <- Hi. unfold CReal_minus. ring. }
  assert (Em : arc_shift y x' = (i + arc_shift y x)%Z) by lia.
  unfold sheet_lift. rewrite Em, inject_Z_plus, <- Hi.
  change (inject_Z 0) with (inject_Q 0). unfold CReal_minus. ring.
Qed.

(* The lift contracts distances by the factor p. *)
Lemma sheet_lift_lip@{u} (p : positive) (y : CReal) (k : Z) (x x' : CReal)
  (d : Q) :
  Qle d (1 # 4) → in_arc@{u} y x → in_arc@{u} y x' → cball@{u} x x' d →
  cball@{u} (sheet_lift p y k x) (sheet_lift p y k x') (d * (1 # p)).
Proof.
  intros Hd Hx Hx' [i Hi]. exists 0%Z.
  pose proof (in_arc_shift y x Hx) as B.
  pose proof (in_arc_shift y x' Hx') as B'.
  assert (Et : (arc_shift y x' + - arc_shift y x + - i)%Z = 0%Z).
  { apply (int_near_zero _
      (CReal_plus (CReal_minus x' y) (inject_Z (arc_shift y x')))
      (CReal_plus (CReal_plus (CReal_minus x y) (inject_Z (arc_shift y x)))
                  (CReal_plus (CReal_minus x' x) (inject_Z i)))
      (1 # 4) (1 # 2) B').
    - rewrite (inject_Q_morph_T _ _ q_quarter_half), inject_Q_plus.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply CReal_plus_le_compat; [exact B|].
      apply (CReal_le_trans _ _ _ Hi). apply inject_Q_le. exact Hd.
    - reflexivity.
    - rewrite !inject_Z_plus, !opp_inject_Z. unfold CReal_minus. ring. }
  assert (Em : arc_shift y x' = (arc_shift y x + i)%Z) by lia.
  assert (E : CRealEq
    (CReal_plus (CReal_minus (sheet_lift p y k x') (sheet_lift p y k x))
                (inject_Z 0))
    (CReal_mult (inject_Q (1 # p))
                (CReal_plus (CReal_minus x' x) (inject_Z i)))).
  { unfold sheet_lift. rewrite Em, inject_Z_plus.
    change (inject_Z 0) with (inject_Q 0). unfold CReal_minus. ring. }
  assert (P0 : CRealLe (inject_Q 0) (inject_Q (1 # p))).
  { apply inject_Q_le. cbv [Qle Qnum Qden]. lia. }
  rewrite E, CReal_abs_mult, (CReal_abs_right _ P0).
  apply (CReal_le_trans _ (CReal_mult (inject_Q (1 # p)) (inject_Q d))).
  - apply CReal_mult_le_compat_l; [exact P0|exact Hi].
  - rewrite <- inject_Q_mult. apply inject_Q_le. rewrite Qmult_comm.
    apply Qle_refl.
Qed.

(* On sheet [k], lifting after wrapping gives the point back. *)
Lemma sheet_lift_wrap@{u} (p : positive) (y : CReal) (k : Z) (z : CReal) :
  in_sheet@{u} p y k z →
  circ_eq@{u} (sheet_lift p y k (CReal_mult (posR p) z)) z.
Proof.
  intros [_ Hs]. unfold sheet_index in Hs.
  set (m := arc_shift y (CReal_mult (posR p) z)) in *.
  pose proof (Z.div_mod (- m) (Zpos p) ltac:(lia)) as D. rewrite Hs in D.
  set (q := ((- m) / Zpos p)%Z) in *.
  exists (- q)%Z.
  assert (Mk : (m + k = - (Zpos p * q))%Z) by lia.
  assert (E : CRealEq
    (CReal_plus (CReal_plus (CReal_mult (posR p) z) (inject_Z m))
                (inject_Z k))
    (CReal_mult (posR p) (CReal_plus z (inject_Z (- q))))).
  { rewrite CReal_plus_assoc, <- inject_Z_plus, Mk, !opp_inject_Z,
      creal_inject_Z_mult. unfold posR. ring. }
  unfold sheet_lift. fold m. rewrite E, inv_p_mul. unfold CReal_minus. ring.
Qed.

(** *** Each sheet is homeomorphic to the arc, by the wrapping map *)

(* The subspaces are Instance/Top/Subspace.v's [ex732_Sub], the subspace
   topology on a subset, reused. *)
Definition ArcSpace@{o} (y : CReal) : PTop@{o} :=
  ex732_Sub PCircle@{o} (in_arc@{o} y).

Definition SheetSpace@{o} (p : positive) (y : CReal) (k : Z) : PTop@{o} :=
  ex732_Sub PCircle@{o} (in_sheet@{o} p y k).

Program Definition pwrap_sheet_map@{o} (p : positive) (y : CReal) (k : Z) :
  SetoidMorphism@{o o o} (ex732_Y PCircle@{o} (in_sheet@{o} p y k))
                         (ex732_Y PCircle@{o} (in_arc@{o} y)) := {|
  morphism := fun a => exist _ (CReal_mult (posR p) (proj1_sig a))
                         (proj1 (proj2_sig a))
|}.
Next Obligation.
  intros p y k a b H. exact (proper_morphism (circ_mul p) _ _ H).
Qed.

Lemma pwrap_sheet_cont@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) :
  @PCont (SheetSpace@{o} p y k) (ArcSpace@{o} y) (pwrap_sheet_map@{o} p y k).
Proof.
  apply (proj2 (psub_universal PCircle (ex732_Y PCircle (in_arc y))
                  (ex732_incl PCircle (in_arc y)) (SheetSpace p y k) _)).
  apply (pcont_respects
           (pmap (pcompose (pwrap@{o so} p)
                           (ex732_incl_mor PCircle (in_sheet p y k))))).
  - intro a. apply circ_eq_refl.
  - exact (pcont _).
Qed.

Definition pwrap_sheet@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) : SheetSpace@{o} p y k ~{PTopCat@{o so}}~> ArcSpace@{o} y :=
  @Build_PMor (SheetSpace p y k) (ArcSpace y) (pwrap_sheet_map p y k)
    (pwrap_sheet_cont@{o so} p y k).

Program Definition sheet_lift_map@{o} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  SetoidMorphism@{o o o} (ex732_Y PCircle@{o} (in_arc@{o} y))
                         (ex732_Y PCircle@{o} (in_sheet@{o} p y k)) := {|
  morphism := fun a => exist _ (sheet_lift p y k (proj1_sig a))
                         (sheet_lift_in p y k Hk _ (proj2_sig a))
|}.
Next Obligation.
  intros p y k Hk a b H.
  exact (sheet_lift_respects p y k _ _ (proj2_sig a) (proj2_sig b) H).
Qed.

Lemma sheet_lift_cont@{o} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  @PCont (ArcSpace@{o} y) (SheetSpace@{o} p y k)
    (sheet_lift_map@{o} p y k Hk).
Proof.
  apply (proj2 (psub_universal PCircle (ex732_Y PCircle (in_sheet p y k))
                  (ex732_incl PCircle (in_sheet p y k)) (ArcSpace y) _)).
  intros W HW.
  exists (fun x => in_arc y x /\ W (sheet_lift p y k x)). split.
  - apply (proj2 (pcircle_open_balls _)). intros x [Hx Hw].
    destruct (proj1 (pcircle_open_balls _) HW _ Hw) as [eW [HeW HbW]].
    destruct (proj1 (pcircle_open_balls _) (in_arc_open y) _ Hx)
      as [eU [HeU HbU]].
    destruct (qmin_pos eU (1 # 4) HeU ltac:(reflexivity))
      as [e1 [[He1 Hle1] Hle2]].
    destruct (qmin_pos e1 (eW * (Zpos p # 1)) He1 (q_p_pos p eW HeW))
      as [e [[He Hle3] Hle4]].
    exists e. split; [exact He|]. intros x' b.
    assert (Hx' : in_arc y x').
    { apply HbU. apply (cball_mono _ _ e); [|exact b].
      exact (Qle_trans _ _ _ Hle3 Hle1). }
    split; [exact Hx'|].
    apply HbW. apply (cball_mono _ _ (e * (1 # p))).
    + exact (q_scale_le p e eW Hle4).
    + apply sheet_lift_lip;
        [exact (Qle_trans _ _ _ Hle3 Hle2)|exact Hx|exact Hx'|exact b].
  - intro a. split.
    + intro w. split; [exact (proj2_sig a)|exact w].
    + intros [_ w]. exact w.
Qed.

Definition sheet_lift_mor@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) :
  ArcSpace@{o} y ~{PTopCat@{o so}}~> SheetSpace@{o} p y k :=
  @Build_PMor (ArcSpace y) (SheetSpace p y k) (sheet_lift_map p y k Hk)
    (sheet_lift_cont p y k Hk).

Program Definition pwrap_sheet_iso@{o so | o < so +} (p : positive)
  (y : CReal) (k : Z) (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism PTopCat@{o so} (SheetSpace@{o} p y k) (ArcSpace@{o} y) := {|
  to := pwrap_sheet@{o so} p y k;
  from := sheet_lift_mor@{o so} p y k Hk
|}.
Next Obligation. intros p y k Hk a. exact (circ_mul_sheet_lift p y k _). Qed.
Next Obligation.
  intros p y k Hk b. exact (sheet_lift_wrap p y k _ (proj2_sig b)).
Qed.

Example pwrap_sheet_iso_to@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) (b : SheetSpace@{o} p y k) :
  proj1_sig (pmap (to (pwrap_sheet_iso@{o so} p y k Hk)) b)
  = circ_mul@{o} p (proj1_sig b) := eq_refl.

(* The evenly covered neighbourhood, gathered: the arc is an open
   neighbourhood of [y]; each sheet is open; the sheets are disjoint; and
   the preimage of the arc is their union.  Each sheet is carried onto the
   arc homeomorphically by [pwrap_sheet_iso]. *)
Theorem pwrap_evenly_covered@{o +} (p : positive) (y : CReal) :
  POpen PCircle@{o} (in_arc@{o} y) /\ in_arc@{o} y y /\
  (∀ k, POpen PCircle@{o} (in_sheet@{o} p y k)) /\
  (∀ k k' (z : Circle_setoid@{o}),
     in_sheet@{o} p y k z → in_sheet@{o} p y k' z → k = k') /\
  (∀ z : Circle_setoid@{o}, in_arc@{o} y (CReal_mult (posR p) z)
     <-> ex (fun k : Z => (0 <= k < Zpos p)%Z /\ in_sheet@{o} p y k z)).
Proof.
  split; [exact (in_arc_open y)|].
  split; [exact (in_arc_centre y)|].
  split; [exact (in_sheet_open p y)|].
  split; [exact (in_sheet_disjoint p y)|].
  exact (in_sheet_preimage p y).
Qed.

(** *** The fibre of the wrapping map over a point has exactly p points *)

Definition fibre_pt@{} (p : positive) (y : CReal) (k : Z) : CReal :=
  sheet_lift p y k y.

Lemma fibre_pt_over@{u} (p : positive) (y : CReal) (k : Z) :
  circ_eq@{u} (CReal_mult (posR p) (fibre_pt p y k)) y.
Proof. exact (circ_mul_sheet_lift p y k y). Qed.

Lemma fibre_pt_distinct@{o} (p : positive) (y : CReal) (k k' : Z)
  (Hk : (0 <= k < Zpos p)%Z) (Hk' : (0 <= k' < Zpos p)%Z) :
  circ_eq@{o} (fibre_pt p y k) (fibre_pt p y k') → k = k'.
Proof.
  intro H.
  apply (in_sheet_disjoint@{o} p y k k' (fibre_pt p y k)).
  - exact (sheet_lift_in p y k Hk y (in_arc_centre y)).
  - apply (popen_proper PCircle (in_sheet p y k') (in_sheet_open p y k')
             (fibre_pt p y k') (fibre_pt p y k) (circ_eq_sym _ _ H)).
    exact (sheet_lift_in p y k' Hk' y (in_arc_centre y)).
Qed.

(* Every point over [y] is one of them, and which one is computed. *)
Definition fibre_exhaust@{o} (p : positive) (y z : CReal) :
  circ_eq@{o} (CReal_mult (posR p) z) y →
  { k : Z & ((0 <= k < Zpos p)%Z * circ_eq@{o} z (fibre_pt p y k))%type }.
Proof.
  intro H.
  assert (HU : in_arc@{o} y (CReal_mult (posR p) z)).
  { apply (popen_proper PCircle (in_arc y) (in_arc_open y) y _
             (circ_eq_sym _ _ H)).
    exact (in_arc_centre y). }
  exists (sheet_index p y z). split; [apply Z.mod_pos_bound; lia|].
  apply (circ_eq_trans _ (sheet_lift p y (sheet_index p y z)
                                     (CReal_mult (posR p) z))).
  - apply circ_eq_sym. apply sheet_lift_wrap. split; [exact HU|reflexivity].
  - exact (sheet_lift_respects p y _ _ _ HU (in_arc_centre y) H).
Defined.

(** ** A subspace of the circle over the Type-valued [Top], by its balls *)

(* The points of a Type-valued predicate [P] on the circle, compared as
   points of the circle; the membership data is invisible to [≈]. *)
Program Definition csub_setoid@{o} (P : Circle_setoid@{o} → Type@{o}) :
  SetoidObject@{o o} := {|
  carrier := { x : CReal & P x };
  is_setoid := {| equiv := fun a b => circ_eq@{o} (projT1 a) (projT1 b) |}
|}.
Next Obligation.
  intros P. constructor.
  - intro a; apply circ_eq_refl.
  - intros a b H; exact (circ_eq_sym _ _ H).
  - intros a b c H1 H2; exact (circ_eq_trans _ _ _ H1 H2).
Qed.

(* An open: every point has a ball of the circle inside it, among the
   points of [P].  It quantifies over a radius, never over opens, so it
   sits at the points' universe. *)
Definition csub_open@{o} (P : Circle_setoid@{o} → Type@{o})
  (V : csub_setoid@{o} P → Type@{o}) : Type@{o} :=
  ∀ a, V a → { e : Q & (Qlt 0 e * ∀ b : csub_setoid@{o} P,
     cball@{o} (projT1 a) (projT1 b) e → V b)%type }.

Lemma csub_open_respects@{o} (P : Circle_setoid@{o} → Type@{o})
  (U V : csub_setoid@{o} P → Type@{o}) :
  (∀ x, U x ↔ V x) → csub_open P U → csub_open P V.
Proof.
  intros H HU a v. destruct (HU a (snd (H a) v)) as [e [He Hb]].
  exists e; split; [exact He|]. intros b c; exact (fst (H b) (Hb b c)).
Qed.

Lemma csub_open_proper@{o} (P : Circle_setoid@{o} → Type@{o})
  (U : csub_setoid@{o} P → Type@{o}) :
  csub_open P U → ∀ a b : csub_setoid@{o} P, a ≈ b → U a → U b.
Proof.
  intros HU a b Hab u. destruct (HU a u) as [e [He Hb]].
  apply Hb. apply cball_of_eq; [exact He|exact Hab].
Qed.

Lemma csub_open_union@{o} (P : Circle_setoid@{o} → Type@{o}) (I : Type@{o})
  (U : I → (csub_setoid@{o} P → Type@{o})) :
  (∀ i, csub_open P (U i)) → csub_open P (fun x => { i : I & U i x }).
Proof.
  intros HU a [i u]. destruct (HU i a u) as [e [He Hb]].
  exists e; split; [exact He|]. intros b c. exact (i; Hb b c).
Qed.

Lemma csub_open_whole@{o} (P : Circle_setoid@{o} → Type@{o}) :
  csub_open P (fun _ => poly_unit@{o}).
Proof. intros a _. exists 1%Q. split; [reflexivity|intros; exact ttt]. Qed.

Lemma csub_open_inter@{o} (P : Circle_setoid@{o} → Type@{o})
  (U V : csub_setoid@{o} P → Type@{o}) :
  csub_open P U → csub_open P V → csub_open P (fun x => U x ∧ V x).
Proof.
  intros HU HV a [u v].
  destruct (HU a u) as [e1 [He1 Hb1]], (HV a v) as [e2 [He2 Hb2]].
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros b c; split.
    + exact (Hb1 b c).
    + apply Hb2, (cball_mono _ _ e1); [apply Qlt_le_weak; exact Hlt|exact c].
  - exists e2; split; [exact He2|]. intros b c; split.
    + apply Hb1, (cball_mono _ _ e2); [exact Hle|exact c].
    + exact (Hb2 b c).
Qed.

Definition CSub@{o} (P : Circle_setoid@{o} → Type@{o}) : TopSpace@{o} := {|
  top_carrier   := csub_setoid@{o} P;
  IsOpen        := csub_open@{o} P;
  open_respects := csub_open_respects@{o} P;
  open_proper   := csub_open_proper@{o} P;
  open_union    := csub_open_union@{o} P;
  open_whole    := csub_open_whole@{o} P;
  open_inter    := csub_open_inter@{o} P
|}.

Program Definition csub_incl_map@{o} (P : Circle_setoid@{o} → Type@{o}) :
  SetoidMorphism@{o o o} (csub_setoid@{o} P) Circle_setoid@{o} := {|
  morphism := fun a => projT1 a
|}.
Next Obligation. intros P a b H. exact H. Qed.

Lemma csub_incl_cont@{h o | o < h +} (P : Circle_setoid@{o} → Type@{o}) :
  Continuous@{h o} (CSub@{o} P) Circle@{o} (csub_incl_map@{o} P).
Proof.
  intros U HU a u. destruct (fst (circle_open_balls U) HU _ u) as [e [He Hb]].
  exists e; split; [exact He|]. intros b c. exact (Hb _ c).
Qed.

Definition csub_incl@{h o | o < h +} (P : Circle_setoid@{o} → Type@{o}) :
  CSub@{o} P ~{Top@{h o}}~> Circle@{o} :=
  @Build_ContinuousMorphism (CSub P) Circle (csub_incl_map P)
    (csub_incl_cont@{h o} P).

(* The half of the universal property with content: a setoid map into the
   points of [P] is continuous as soon as its composite with the inclusion
   is.  The preimage of an open is the union, over its points, of the
   preimages of the open interiors [cint] of the circle's balls. *)
Lemma csub_lift_cont@{h o | o < h +} (P : Circle_setoid@{o} → Type@{o})
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (csub_setoid@{o} P))
  (Hg : Continuous@{h o} Z Circle@{o}
          (setoid_morphism_compose (csub_incl_map P) g)) :
  Continuous@{h o} Z (CSub@{o} P) g.
Proof.
  intros W HW.
  apply (open_respects Z (fun z => { i : { z0 : Z & W (g z0) } &
     cint (projT1 (g (projT1 i))) (projT1 (HW (g (projT1 i)) (projT2 i)))
          (projT1 (g z)) })).
  - intro z; split.
    + intros [i b].
      destruct (HW (g (projT1 i)) (projT2 i)) as [e [He Hb]] eqn:Ew.
      simpl in b. apply Hb. exact (cint_sub _ _ _ b).
    + intros w. exists (z; w). cbn [projT1 projT2].
      destruct (HW (g z) w) as [e [He Hb]]; simpl.
      exact (cint_centre _ _ He).
  - apply open_union. intros [z0 w0]. cbn [projT1 projT2].
    destruct (HW (g z0) w0) as [e [He Hb]]; simpl.
    exact (Hg (cint (projT1 (g z0)) e) (cint_open _ _)).
Qed.

(* The universal property of the subspace topology, over ANY space
   mapping in. *)
Theorem csub_universal@{h o | o < h +} (P : Circle_setoid@{o} → Type@{o})
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (csub_setoid@{o} P)) :
  Continuous@{h o} Z (CSub@{o} P) g ↔
  Continuous@{h o} Z Circle@{o} (setoid_morphism_compose (csub_incl_map P) g).
Proof.
  split.
  - intros Hg U HU. exact (Hg _ (csub_incl_cont P U HU)).
  - exact (csub_lift_cont P Z g).
Qed.

(* The coarsest topology making the inclusion continuous. *)
Lemma csub_coarsest@{h o + | o < h +} (P : Circle_setoid@{o} → Type@{o})
  (T : (csub_setoid@{o} P → Type@{o}) → Type@{o})
  (Tr : ∀ U V, (∀ x, U x ↔ V x) → T U → T V)
  (Tp : ∀ U, T U → ∀ x y : csub_setoid P, x ≈ y → U x → U y)
  (Tu : ∀ (I : Type@{o}) (U : I → csub_setoid P → Type@{o}),
          (∀ i, T (U i)) → T (fun x => { i : I & U i x }))
  (Tw : T (fun _ => poly_unit@{o}))
  (Ti : ∀ U V, T U → T V → T (fun x => U x ∧ V x))
  (Hc : ∀ U : Circle_setoid@{o} → Type@{o}, IsOpen Circle@{o} U →
          T (fun a => U (projT1 a))) :
  ∀ V, csub_open P V → T V.
Proof.
  intros V HV.
  pose (Z := @Build_TopSpace (csub_setoid P) T Tr Tp Tu Tw Ti).
  exact (csub_lift_cont@{h o} P Z (@setoid_morphism_id (csub_setoid P))
           (fun U HU => Hc U HU) V HV).
Qed.

(** ** The covering over the Type-valued [Top] *)

(* The arc about [y], Type-valued: the interior of the closed ball of
   radius 1/4 itself.  The Prop-valued [in_arc] is its squash. *)
Definition tarc@{o} (y : CReal) : Circle_setoid@{o} → Type@{o} :=
  cint@{o} y (1 # 4).

Example in_arc_squash@{o} (y x : CReal) :
  in_arc@{o} y x = inhabited (tarc@{o} y x) := eq_refl.

(* Sheet [k] over the arc, Type-valued. *)
Definition tsheet@{o} (p : positive) (y : CReal) (k : Z)
  (z : Circle_setoid@{o}) : Type@{o} :=
  (tarc@{o} y (CReal_mult (posR p) z) * (sheet_index p y z = k))%type.

Lemma tarc_open@{o} (y : CReal) : IsOpen Circle@{o} (tarc@{o} y).
Proof. exact (cint_open y (1 # 4)). Qed.

Lemma tarc_centre@{o} (y : CReal) : tarc@{o} y y.
Proof. exact (cint_centre y (1 # 4) ltac:(reflexivity)). Qed.

Lemma tsheet_open@{o} (p : positive) (y : CReal) (k : Z) :
  IsOpen Circle@{o} (tsheet@{o} p y k).
Proof.
  apply (snd (circle_open_balls _)).
  intros z [HU Hs].
  destruct (cint_balls y (1 # 4) _ HU) as [e1 [He1 Hb1]].
  destruct (qmin_pos e1 (1 # 4) He1 ltac:(reflexivity))
    as [e [[He Hle1] Hle2]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros z' [i Hi].
  pose proof (mul_ball p z z' i e Hi) as Hs'.
  assert (HU' : tarc y (CReal_mult (posR p) z')).
  { apply Hb1. exists (Zpos p * i)%Z.
    apply (CReal_le_trans _ _ _ Hs'). apply inject_Q_le. exact Hle1. }
  split; [exact HU'|].
  pose proof (in_arc_shift y _ (inhabits HU)) as B.
  pose proof (in_arc_shift y _ (inhabits HU')) as B'.
  unfold sheet_index in Hs |- *.
  set (m := arc_shift y (CReal_mult (posR p) z)) in *.
  set (m' := arc_shift y (CReal_mult (posR p) z')) in *.
  assert (Et : (m' + - m + - (Zpos p * i))%Z = 0%Z).
  { apply (int_near_zero _
      (CReal_plus (CReal_minus (CReal_mult (posR p) z') y) (inject_Z m'))
      (CReal_plus (CReal_plus (CReal_minus (CReal_mult (posR p) z) y)
                              (inject_Z m))
                  (CReal_plus (CReal_minus (CReal_mult (posR p) z')
                                           (CReal_mult (posR p) z))
                              (inject_Z (Zpos p * i))))
      (1 # 4) (1 # 2) B').
    - rewrite (inject_Q_morph_T _ _ q_quarter_half), inject_Q_plus.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply CReal_plus_le_compat; [exact B|].
      apply (CReal_le_trans _ _ _ Hs'). apply inject_Q_le. exact Hle2.
    - reflexivity.
    - rewrite !inject_Z_plus, !opp_inject_Z. unfold CReal_minus. ring. }
  rewrite <- Hs.
  replace (- m')%Z with (- m + (- i) * Zpos p)%Z by lia.
  apply Z.mod_add. lia.
Qed.

Lemma tsheet_disjoint@{o} (p : positive) (y : CReal) (k k' : Z)
  (z : Circle_setoid@{o}) :
  tsheet@{o} p y k z → tsheet@{o} p y k' z → k = k'.
Proof. intros [_ H] [_ H']. rewrite <- H, <- H'. reflexivity. Qed.

Lemma tsheet_preimage@{o} (p : positive) (y : CReal)
  (z : Circle_setoid@{o}) :
  tarc@{o} y (CReal_mult (posR p) z)
  ↔ { k : Z & ((0 <= k < Zpos p)%Z * tsheet@{o} p y k z)%type }.
Proof.
  split.
  - intro H. exists (sheet_index p y z). split.
    + apply Z.mod_pos_bound. lia.
    + split; [exact H|reflexivity].
  - intros [k [_ [H _]]]. exact H.
Qed.

(* The evenly covered neighbourhood in [Top], gathered: the arc is an open
   neighbourhood of [y]; each sheet is open; the sheets are disjoint; and
   the preimage of the arc is their union.  Each sheet is carried onto the
   arc homeomorphically by [wrap_sheet_iso]. *)
Theorem wrap_evenly_covered@{o +} (p : positive) (y : CReal) :
  (IsOpen Circle@{o} (tarc@{o} y) * tarc@{o} y y *
   (∀ k, IsOpen Circle@{o} (tsheet@{o} p y k)) *
   (∀ k k' (z : Circle_setoid@{o}),
      tsheet@{o} p y k z → tsheet@{o} p y k' z → k = k') *
   (∀ z : Circle_setoid@{o}, tarc@{o} y (CReal_mult (posR p) z)
      ↔ { k : Z & ((0 <= k < Zpos p)%Z * tsheet@{o} p y k z)%type }))%type.
Proof.
  refine (_, _, _, _, _).
  - exact (tarc_open y).
  - exact (tarc_centre y).
  - exact (tsheet_open p y).
  - exact (tsheet_disjoint p y).
  - exact (tsheet_preimage p y).
Qed.

(* The arc and the sheets as spaces: ball subspaces of the circle. *)
Definition TArc@{o} (y : CReal) : TopSpace@{o} := CSub@{o} (tarc@{o} y).

Definition TSheet@{o} (p : positive) (y : CReal) (k : Z) : TopSpace@{o} :=
  CSub@{o} (tsheet@{o} p y k).

Program Definition wrap_sheet_map@{o} (p : positive) (y : CReal) (k : Z) :
  SetoidMorphism@{o o o} (csub_setoid@{o} (tsheet@{o} p y k))
                         (csub_setoid@{o} (tarc@{o} y)) := {|
  morphism := fun a => (CReal_mult (posR p) (projT1 a); fst (projT2 a))
|}.
Next Obligation.
  intros p y k a b H. exact (proper_morphism (circ_mul p) _ _ H).
Qed.

(* The restriction of [wrap p] is continuous, because [wrap p] after the
   inclusion is. *)
Lemma wrap_sheet_cont@{h o | o < h +} (p : positive) (y : CReal) (k : Z) :
  Continuous@{h o} (TSheet@{o} p y k) (TArc@{o} y) (wrap_sheet_map@{o} p y k).
Proof.
  apply csub_lift_cont.
  apply (@tcont_respects (TSheet p y k) Circle
           (continuous_map
              (top_compose (wrap@{h o} p) (csub_incl (tsheet p y k))))).
  - intro a. apply circ_eq_refl.
  - exact (continuity (top_compose (wrap p) (csub_incl (tsheet p y k)))).
Qed.

Definition wrap_sheet@{h o | o < h +} (p : positive) (y : CReal) (k : Z) :
  TSheet@{o} p y k ~{Top@{h o}}~> TArc@{o} y :=
  @Build_ContinuousMorphism (TSheet p y k) (TArc y) (wrap_sheet_map p y k)
    (wrap_sheet_cont@{h o} p y k).

(* The local section [sheet_lift] lands in sheet [k]. *)
Lemma tsheet_lift_in@{o} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) (x : CReal) :
  tarc@{o} y x → tsheet@{o} p y k (sheet_lift p y k x).
Proof.
  intro Hx. split.
  - apply (open_proper Circle (tarc y) (tarc_open y) x); [|exact Hx].
    apply circ_eq_sym. apply circ_mul_sheet_lift.
  - exact (proj2 (sheet_lift_in p y k Hk x (inhabits Hx))).
Qed.

Program Definition tsheet_lift_map@{o} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  SetoidMorphism@{o o o} (csub_setoid@{o} (tarc@{o} y))
                         (csub_setoid@{o} (tsheet@{o} p y k)) := {|
  morphism := fun a => (sheet_lift p y k (projT1 a);
                        tsheet_lift_in p y k Hk _ (projT2 a))
|}.
Next Obligation.
  intros p y k Hk a b H.
  exact (sheet_lift_respects p y k _ _ (inhabits (projT2 a))
           (inhabits (projT2 b)) H).
Qed.

Lemma tsheet_lift_cont@{h o | o < h +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  Continuous@{h o} (TArc@{o} y) (TSheet@{o} p y k)
    (tsheet_lift_map@{o} p y k Hk).
Proof.
  apply csub_lift_cont. intros W HW a w.
  change (W (sheet_lift p y k (projT1 a))) in w.
  destruct (fst (circle_open_balls W) HW _ w) as [eW [HeW HbW]].
  destruct (qmin_pos (1 # 4) (eW * (Zpos p # 1)) ltac:(reflexivity)
              (q_p_pos p eW HeW)) as [e [[He Hle1] Hle2]].
  exists e. split; [exact He|]. intros b c.
  change (W (sheet_lift p y k (projT1 b))).
  apply HbW. apply (cball_mono _ _ (e * (1 # p))).
  - exact (q_scale_le p e eW Hle2).
  - exact (sheet_lift_lip p y k (projT1 a) (projT1 b) e Hle1
             (inhabits (projT2 a)) (inhabits (projT2 b)) c).
Qed.

Definition tsheet_lift_mor@{h o | o < h +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) :
  TArc@{o} y ~{Top@{h o}}~> TSheet@{o} p y k :=
  @Build_ContinuousMorphism (TArc y) (TSheet p y k) (tsheet_lift_map p y k Hk)
    (tsheet_lift_cont@{h o} p y k Hk).

(* Each sheet is homeomorphic to the arc, by the wrapping map, in [Top]. *)
Program Definition wrap_sheet_iso@{h o | o < h +} (p : positive)
  (y : CReal) (k : Z) (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism Top@{h o} (TSheet@{o} p y k) (TArc@{o} y) := {|
  to := wrap_sheet@{h o} p y k;
  from := tsheet_lift_mor@{h o} p y k Hk
|}.
Next Obligation. intros p y k Hk a. exact (circ_mul_sheet_lift p y k _). Qed.
Next Obligation.
  intros p y k Hk b.
  exact (sheet_lift_wrap p y k _
           (conj (inhabits (fst (projT2 b))) (snd (projT2 b)))).
Qed.

Example wrap_sheet_iso_to@{h o | o < h +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) (b : TSheet@{o} p y k) :
  projT1 (continuous_map (to (wrap_sheet_iso@{h o} p y k Hk)) b)
  = circ_mul@{o} p (projT1 b) := eq_refl.

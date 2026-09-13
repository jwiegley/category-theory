Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(** * Limits of rings are computed on underlying sets *)

(* nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings
   Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
   Riehl:    Category Theory in Context, §5.6 Example 5.6.8

   [Rng_Forget] (Instance/Rng.v:129) STRICTLY CREATES every limit.  Given a
   limiting cone over the underlying diagram of sets, there is exactly one
   ring structure on its apex making every projection a homomorphism
   ([rlim_structure_unique], Mac Lane's Theorem 2), the resulting cone lies
   over the given one ON THE NOSE ([rlim_over_obj] and [rlim_over_legs] are
   both [eq_refl], because [Rng_Forget]'s object map is the [rig_setoid]
   projection -- Instance/Rng.v:615 already records that as an [eq_refl]),
   it is limiting ([rlim_created]), and a cone of rings whose image is
   limiting is itself limiting ([rng_reflects]).  Packaged as
   Structure/Limit/Creation.v's own classes --
   [Rng_Forget_StrictlyCreatesLimit]
   ([StrictlyCreatesLimit], :325), [Rng_Forget_CreatesLimit] and
   [Rng_Forget_creates_limits] ([CreatesAllLimits], :228) -- from which the
   standard corollaries follow by application: [Rng_Complete] (Mac Lane's
   Theorem 3) and [Rng_Forget_continuous : ContinuousFunctor Rng_Forget],
   the cone-level reading, with the apex-only
   [Rng_Forget_PreservesAllLimits] derived from it and
   [Rng_Forget_reflects_limits] alongside.

   WHAT HAS TO BE LIFTED, AND HOW MUCH MORE IT IS THAN THE GROUP CASE.  An
   object of [Rng] is Theory/Algebra/Rig.v:469's [RingObject]: a
   [RigObject] (:103) extended by [ring_neg] with [ring_neg_respects] and
   [ring_neg_l].  So FIVE operations are lifted -- [rig_zero], [rig_one],
   [rig_add], [rig_mul], [ring_neg] -- against the group case's three, and
   ELEVEN laws are proved: the four counted off Definition 5.36's clauses
   (a) [rig_add_assoc], [rig_add_comm], [rig_add_zero_l]; (b)
   [rig_mul_assoc], [rig_mul_one_l], [rig_mul_one_r]; (c) [rig_distr_l],
   [rig_distr_r]; (d) [rig_mul_zero_l], [rig_mul_zero_r] -- ten in all --
   plus [ring_neg_l].  Every one is three lines: apply the joint-monicity
   lemma, rewrite the defining triangles, apply the law in [K j].  THE
   METHOD IS UNCHANGED; only the bookkeeping grows.

   ONE PLACE WHERE THE RING SIGNATURE IS GENUINELY DIFFERENT, NOT MERELY
   BIGGER.  [RigHom] (Theory/Algebra/Rig.v:162) has FOUR clauses --
   [rig_map_zero], [rig_map_add], [rig_map_one], [rig_map_mul] -- and NO
   clause for negation, because Rig.v:482's [RigHom_neg] proves preservation
   of negation from uniqueness of additive inverses.  Two consequences, both
   visible below.  The coherence of the negation cone ([rlim_neg_coherence])
   is therefore discharged by that THEOREM where its four siblings use a
   projection; and the negation clause of [rlim_structure_unique] is stated
   by hand rather than being read off the hom type, since no leg condition
   on negation is available from [RigHom] at all.  The uniqueness clause
   nevertheless holds at the same strength as its four siblings: it consumes
   only that the legs carry the candidate negation to [ring_neg] in each
   [K j], and no law of the candidate structure.

   THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED.  At
   the limits [Sets_Complete] chooses -- the compatible families of
   Instance/Sets/Complete.v ([Sets_limit_obj] at :144, [Sets_limit_leg] at
   :157, [Sets_Complete] at :196) -- the created ring is the COORDINATEWISE
   one on the nose: [rng_complete_carrier], [rng_complete_zero],
   [rng_complete_one], [rng_complete_add], [rng_complete_mul],
   [rng_complete_neg] and [rng_complete_leg] are SEVEN [eq_refl] Examples,
   at an ARBITRARY shape and an ARBITRARY diagram of rings.  Nothing in them
   is specific to a witness category, and no isomorphism is interposed; this
   file therefore needs no concrete witness to be non-vacuous, and builds
   none.

   ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]: four statements
   here write [=] between morphisms -- [rlim_over_legs], [rng_lift_legs],
   [rng_fcone_leg] and [rng_complete_leg] -- and each does so because both
   sides are the SAME TERM, the witness being [eq_refl].  They record
   Mac Lane's [F sigma = tau] at full strength, which is strictly stronger
   than the [≈] the [StrictLift] clause (Structure/Limit/Creation.v:288)
   asks for; every law, every proof and the [slift_legs] clause consumed by
   [rng_strict_lift] use [≈].  The same applies to the object-level [=] of
   [rlim_over_obj], [rng_lift_apex], [rng_fcone_apex],
   [rng_complete_carrier] and the five [rng_complete_*] element equations,
   which compare OBJECTS and ELEMENTS rather than morphisms and are the
   discipline's sanctioned exception.

   WHAT IS NEW HERE AND WHAT IS NOT, MEASURED RATHER THAN ASSERTED.  This
   is the SECOND algebraic category to get a creation result and the second
   to get [@Complete], not the first: Instance/Grp/Limit.v is the precedent
   ([Grp_Forget_creates_limits] at :645, [Grp_Complete] at :691) and this
   file is its clause-for-clause transposition.  Sweeping declaration heads
   of the form "Definition/Program Definition/Theorem/Lemma/Example <name> :
   @?Complete|Cocomplete" over all [.v] files, the roster before this file
   was [Sets_Complete] and [ConeSet_Complete] (Instance/Sets/Complete.v:196,
   :464), [Sets_Complete_via_Manes] (Structure/Equalizer/Coreflexive.v:602),
   [Subsets_Complete]/[Subsets_Cocomplete] (Instance/Powerset.v:637, :641),
   [Grp_Complete] (Instance/Grp/Limit.v:691), one biconditional at [Proset]
   (Instance/Proset/Limit.v:549) and two probe files -- nothing for [Rng],
   [Ab], [CMon], [RMod], [Mon] or [Top].

   AND THE CLAIM "NO LIMIT OF RINGS EXISTED IN TREE" WOULD BE FALSE, SO IT
   IS NOT MADE.  Instance/Rng/Zp.v already builds THREE: [Zp_limit :
   IsALimit (ResTower Rcomm d) Zp] (:505), [Zp_int_limit] (:567) and
   [PowerSeries_limit] (:587), each at an [Omega^op]-shaped tower with a
   hand-built carrier.  It also already has the ELEMENTWISE uniqueness at
   that one diagram -- [zp_zero_forced] (:519), [zp_one_forced] (:523),
   [zp_add_forced] (:527), [zp_mul_forced] (:533), [zp_neg_forced] (:539) --
   and its header (:126-129) states in terms what it does not prove: "Riehl
   §5.6 Example 5.6.8 observes that the underlying-set functor of [Rng] is
   MONADIC and therefore CREATES the limit cone ... Monadicity is NOT proved
   here and is not used".  THIS FILE SUPPLIES THE CREATION, at an arbitrary
   shape and an arbitrary diagram, and it too does NOT go through
   monadicity: no file in the tree exhibits [Rng] as an Eilenberg-Moore
   category, so the argument is rerun one level down exactly as the group
   case reruns it.  Nothing here is stated about [Zp]; relating [Zp_limit]
   to the created limit at [ResTower] is left undone.

   THE CONTINUITY COROLLARY IS NOT NEW, AND AN EARLIER REVISION OF THIS
   HEADER OVERSTATED HOW NOT-NEW IT IS IN THE WRONG DIRECTION.  That
   revision said continuity of [Rng_Forget] was available "in PRINCIPLE"
   but not as an instantiation, because "transporting [ContinuousFunctor]
   along a natural isomorphism of functors is nowhere in tree".  That is
   false, and the audit of this file refuted it by building the alternative
   in twelve lines out of constants that already existed:
   Functor/Hom/Continuous.v:319's [Section Transport] and :371's
   [ContinuousFunctor_transport] are exactly that construction.  So the
   honest statement is that continuity of [Rng_Forget] WAS reachable before
   this file, by [zpoly_representation] (Instance/Rng/Polynomial.v:791) and
   [zpoly_representable] (:795) — note the names; a previous revision cited
   a [zpoly_hom_iso] that does not exist anywhere in the tree — composed
   with Functor/Hom/Limit.v:338's [hom_ContinuousFunctor] and then
   transported.

   RAPL is not the route, and here too the earlier revision's PREMISE was
   wrong while its conclusion held.  It said "the only ring adjunction in
   tree is [free_rng_ab_adjunction]"; there are at least four
   ([free_rng_ab_adjunction], Instance/Rng/Free.v:676;
   [zmring_adjunction], Instance/Rng/MonoidRing.v:726;
   [grp_ring_adjunction], Instance/Rng/GroupRing.v:306;
   [poly_pointed_adjunction], Instance/Rng/Pointed.v:231).  What is true is
   the thing that matters: NONE of them has [Rng_Forget : Rng ⟶ Sets] as
   its right adjoint (measured, [grep -P '⊣\s*Rng_Forget(?![A-Za-z0-9_])']
   returns nothing), so Adjunction/Continuity.v:209's
   [right_adjoint_Continuous] does not reach it.

   WHAT IS NEW WITHOUT QUALIFICATION is therefore the CREATION result, and
   [Rng_Complete], which no route above gives at all.  Continuity is
   re-derived here as its corollary rather than claimed as a first.

   THE ENGINE IS ONE REUSABLE LEMMA WITH NOTHING RING-THEORETIC IN IT.
   [rng_sets_limit_ext] says the legs of a limiting cone in [Sets] are
   jointly monic ELEMENTWISE: two points of the apex agreeing at every leg
   are equal.  It is proved from the mediator's uniqueness alone, with the
   two constant maps out of the apex itself as probes -- so it needs no
   terminal object and pulls in no further module.  It is the same lemma
   Instance/Grp/Limit.v declares as [sets_limit_ext], RE-DECLARED here under
   a distinct name rather than imported, for two reasons: importing it would
   make this file depend on [Grp], which is an architectural inversion, and
   its natural home is beside its donors in Instance/Sets/Complete.v, which
   this change does not touch.  The duplication is real and is recorded as
   such; whoever upstreams the lemma should retire both copies.

   UNIVERSES, measured off BOTH binder and block over all 122 constants
   (104 [.glob] declaration heads plus the 18 [Program] obligations, which
   no source-level reading sees): ZERO word-bounded [Set] occurrences
   anywhere, and TWELVE carry a block equation at all.  (An earlier
   revision of this paragraph said ELEVEN and added "the 18 obligations
   carry no block equation"; both were wrong, and the cause is worth
   recording -- after [Require Import Category.Instance.Rng.Limit] the BARE
   obligation names are not bound, so [About rng_sets_const_obligation_1]
   answers "not found" and an unqualified sweep silently reports nothing.
   Re-measured with fully qualified names,
   [Category.Instance.Rng.Limit.<name>], over all 122 constants.)  Four are
   the generic [Sets] section -- [rng_sets_pre], [rng_sets_med_eq],
   [rng_sets_limit_ext] and [rng_sets_const] -- all four carrying
   [u0 = u3], which identifies the shape's hom-and-proof universe with
   [Sets]' carrier universe, and the first three additionally [u1 = u2],
   which identifies two of the ambient's; that [u0 = u3] is [IsALimit]'s
   doing and not this file's.  Seven are the [rng_complete_*] readbacks,
   which BIND their shape explicitly and so carry [u = u0], identifying the
   shape's object universe with its hom-and-proof universe -- that is
   [Complete]'s own [@{u u u u0}] shape written out, inherited from
   [Sets_Complete] and not narrowed here.  The twelfth is
   [rng_sets_const_obligation_1], carrying the same [u0 = u3] as the
   constant it belongs to; the other 17 obligations carry none.  The remaining constants carry none either, with
   [Rng_Complete@{u u0 u1} : Complete@{u u u u0}] ([u < u0], [u < u1]) and
   [Rng_Forget_creates_limits@{u u0 u1 u2 u3 u4}] among them, so the
   smallness discipline is exactly [Sets_Complete]'s.  This mirrors the
   group case's reading exactly, at the same count of equation-carrying
   generic constants.

   [Print Assumptions] reports "Closed under the global context" for all
   six headline constants -- [Rng_Complete], [Rng_Forget_continuous],
   [Rng_Forget_creates_limits], [Rng_Forget_PreservesAllLimits],
   [Rng_Forget_StrictlyCreatesLimits] and [Rng_Forget_reflects_limits].
   This is worth saying because Instance/Rng.v itself reaches ZArith and
   QArith for its concrete witnesses; none of that arrives here, the file
   consuming only the category, the forgetful functor and the rig algebra.

   NOT delivered.  (1) No creation result for [Rng_Forget_Ab]
   (Instance/Rng.v:117), and the reason is structural rather than a matter
   of effort: the cone-mediator method used below does not transpose to
   [Ab].  Multiplication would need a cone whose apex is a direct sum with
   leg [(a, b) ↦ leg a · leg b], and that map is BILINEAR, not additive, so
   it is not a morphism of [Ab] and there is no cone to take a mediator of;
   the multiplicative unit is worse, since the only canonical maps out of
   [Ab]'s zero object (Instance/Ab.v:262, :276) send everything to zero and
   so cannot select [1].  The available repair is the free abelian group on
   one generator (Instance/Ab/Free.v:561's [FreeAb]) as the probe object,
   with the multiplication rebuilt one argument at a time as an
   element-indexed family of mediators [L ⟶ L] and respectfulness in the
   outer argument recovered from joint monicity.  That is a different
   argument, not this one instantiated, so it is left for its own change.
   (2) No colimits and no cocompleteness for [Rng].  (3) No
   signature-generic variant covering [CMon], [Ab], [Rng] and [RMod] at
   once, though the engine transfers unchanged.  (4) No comparison of the
   created limit with Instance/Rng/Zp.v's [Zp_limit], and no comparison of
   the created binary product with any product structure on [Rng].  (5) No
   monadicity statement and no comparison functor, so nothing here says
   [Rng] IS an Eilenberg-Moore category, and Riehl's Example 5.6.8 remains
   an observation rather than a theorem in tree.  (6) No refusal-probe file
   under Test/: the boundaries this file meets are the group case's
   boundaries and Test/ProbeGrpLimit411.v already pins them, but nothing
   here is guarded by a probe of its own, which is a gap and not a claim.
   (7) NOTHING is registered as an [Instance] -- the file declares none,
   following its template, since a chosen limit must not become globally
   resolvable.

   This file contributes ZERO hits to [make todo]. *)

(** * Joint monicity of limit legs in [Sets], elementwise *)

Section RngSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition rng_sets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma rng_sets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (rng_sets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition rng_sets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma rng_sets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (rng_sets_med_eq (rng_sets_const x) (rng_sets_const y)
           (fun j a => Hxy j) x).
Qed.

End RngSetsExt.

(** * The created ring structure on a limit of underlying sets *)

Section RngLift.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (L : Limit (Rng_Forget ◯ K)).

Definition rlim_leg (j : J) : vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma rlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  rig_map (fmap[K] f) (rlim_leg x a) ≈ rlim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma rlim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, rlim_leg j x ≈ rlim_leg j y) → x ≈ y.
Proof. exact (rng_sets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition *)

Definition rlim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition rlim_add_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_add (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_add_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_add_leg x ≈ rlim_add_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_add.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_add_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_add_leg (@rlim_add_coherence)).

Definition rlim_add_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_add_cone.

Definition rlim_add (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_add_map (a, b).

Lemma rlim_add_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_add a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_add_cone j (a, b)).
Qed.

Lemma rlim_add_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_add.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_add_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The multiplication *)

Program Definition rlim_mul_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_mul (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_mul_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_mul_leg x ≈ rlim_mul_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_mul.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_mul_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_mul_leg (@rlim_mul_coherence)).

Definition rlim_mul_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_mul_cone.

Definition rlim_mul (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_mul_map (a, b).

Lemma rlim_mul_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_mul a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_mul_cone j (a, b)).
Qed.

Lemma rlim_mul_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_mul.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_mul_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The additive unit *)

Program Definition rlim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_zero (K j) |}.

Lemma rlim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_zero_leg x ≈ rlim_zero_leg y.
Proof. intro p; simpl; apply rig_map_zero. Qed.

Definition rlim_zero_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_zero_leg (@rlim_zero_coherence)).

Definition rlim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_zero_cone.

Definition rlim_zero : carrier vertex_obj[L] := rlim_zero_map ttt.

Lemma rlim_zero_triangle (j : J) :
  rlim_leg j rlim_zero ≈ rig_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_zero_cone j ttt).
Qed.

(** ** The multiplicative unit *)

Program Definition rlim_one_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_one (K j) |}.

Lemma rlim_one_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_one_leg x ≈ rlim_one_leg y.
Proof. intro p; simpl; apply rig_map_one. Qed.

Definition rlim_one_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_one_leg (@rlim_one_coherence)).

Definition rlim_one_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_one_cone.

Definition rlim_one : carrier vertex_obj[L] := rlim_one_map ttt.

Lemma rlim_one_triangle (j : J) :
  rlim_leg j rlim_one ≈ rig_one (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_one_cone j ttt).
Qed.

(** ** The additive inverse *)

Program Definition rlim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun a => ring_neg (K j) (rlim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma rlim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_neg_leg x ≈ rlim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite RigHom_neg.
  now rewrite rlim_leg_coherence.
Qed.

Definition rlim_neg_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Rng_Forget ◯ K)
       rlim_neg_leg (@rlim_neg_coherence)).

Definition rlim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_neg_cone.

Definition rlim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_neg_map a.

Lemma rlim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  rlim_leg j (rlim_neg a) ≈ ring_neg (K j) (rlim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_neg_cone j a).
Qed.

Lemma rlim_neg_respects : Proper (equiv ==> equiv) rlim_neg.
Proof. intros a b Hab; exact (proper_morphism rlim_neg_map a b Hab). Qed.

(** ** The eleven laws, each by joint monicity of the legs *)

Lemma rlim_add_assoc (a b c : carrier vertex_obj[L]) :
  rlim_add (rlim_add a b) c ≈ rlim_add a (rlim_add b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_assoc.
Qed.

Lemma rlim_add_comm (a b : carrier vertex_obj[L]) :
  rlim_add a b ≈ rlim_add b a.
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_comm.
Qed.

Lemma rlim_add_zero_l (a : carrier vertex_obj[L]) :
  rlim_add rlim_zero a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_zero_triangle.
  apply rig_add_zero_l.
Qed.

Lemma rlim_mul_assoc (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_mul a b) c ≈ rlim_mul a (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_mul_triangle.
  apply rig_mul_assoc.
Qed.

Lemma rlim_mul_one_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_one a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_l.
Qed.

Lemma rlim_mul_one_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_one ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_r.
Qed.

Lemma rlim_distr_l (a b c : carrier vertex_obj[L]) :
  rlim_mul a (rlim_add b c)
    ≈ rlim_add (rlim_mul a b) (rlim_mul a c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_l.
Qed.

Lemma rlim_distr_r (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_add a b) c
    ≈ rlim_add (rlim_mul a c) (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_r.
Qed.

Lemma rlim_mul_zero_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_zero a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_l.
Qed.

Lemma rlim_mul_zero_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_zero ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_r.
Qed.

Lemma rlim_neg_l (a : carrier vertex_obj[L]) :
  rlim_add (rlim_neg a) a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_neg_triangle, rlim_zero_triangle.
  apply ring_neg_l.
Qed.

(** ** The lifted rig and the lifted ring *)

Definition LimitRig : RigObject :=
  {| rig_setoid       := vertex_obj[L]
   ; rig_zero         := rlim_zero
   ; rig_add          := rlim_add
   ; rig_one          := rlim_one
   ; rig_mul          := rlim_mul
   ; rig_add_respects := rlim_add_respects
   ; rig_mul_respects := rlim_mul_respects
   ; rig_add_assoc    := rlim_add_assoc
   ; rig_add_comm     := rlim_add_comm
   ; rig_add_zero_l   := rlim_add_zero_l
   ; rig_mul_assoc    := rlim_mul_assoc
   ; rig_mul_one_l    := rlim_mul_one_l
   ; rig_mul_one_r    := rlim_mul_one_r
   ; rig_distr_l      := rlim_distr_l
   ; rig_distr_r      := rlim_distr_r
   ; rig_mul_zero_l   := rlim_mul_zero_l
   ; rig_mul_zero_r   := rlim_mul_zero_r |}.

Definition LimitRing : RingObject :=
  {| ring_rig          := LimitRig
   ; ring_neg          := rlim_neg
   ; ring_neg_respects := rlim_neg_respects
   ; ring_neg_l        := rlim_neg_l |}.

(** ** The legs are ring homomorphisms *)

Program Definition rlim_hom (j : J) : RigHom LimitRing (K j) :=
  {| rig_map := rlim_leg j |}.
Next Obligation. apply rlim_zero_triangle. Qed.
Next Obligation. apply rlim_add_triangle. Qed.
Next Obligation. apply rlim_one_triangle. Qed.
Next Obligation. apply rlim_mul_triangle. Qed.

Lemma rlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ rlim_hom x ≈ rlim_hom y.
Proof. intro a; exact (rlim_leg_coherence f a). Qed.

Definition rlim_cone : Cone K :=
  @Build_Cone J Rng K LimitRing
    (@Build_ACone J Rng LimitRing K rlim_hom (@rlim_hom_coherence)).

(** ** Strictness: the lifted cone lies over [L] on the nose *)

Definition rlim_over_obj : Rng_Forget LimitRing = vertex_obj[L] := eq_refl.

Definition rlim_over_legs (j : J) :
  fmap[Rng_Forget] (cone_leg rlim_cone j) = rlim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition rlim_car_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Rng_Forget N).

Lemma rlim_car_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rlim_leg j (rlim_car_med N a) ≈ rig_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Rng_Forget N) j a).
Qed.

Lemma rlim_car_med_zero (N : Cone K) :
  rlim_car_med N (rig_zero vertex_obj[N]) ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_zero_triangle.
  apply rig_map_zero.
Qed.

Lemma rlim_car_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_add vertex_obj[N] a b)
    ≈ rlim_add (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_add_triangle, !rlim_car_med_commutes.
  apply rig_map_add.
Qed.

Lemma rlim_car_med_one (N : Cone K) :
  rlim_car_med N (rig_one vertex_obj[N]) ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_one_triangle.
  apply rig_map_one.
Qed.

Lemma rlim_car_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_mul vertex_obj[N] a b)
    ≈ rlim_mul (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_mul_triangle, !rlim_car_med_commutes.
  apply rig_map_mul.
Qed.

Program Definition rlim_med (N : Cone K) : vertex_obj[N] ~{Rng}~> LimitRing :=
  {| rig_map := rlim_car_med N |}.
Next Obligation. apply rlim_car_med_zero. Qed.
Next Obligation. apply rlim_car_med_add. Qed.
Next Obligation. apply rlim_car_med_one. Qed.
Next Obligation. apply rlim_car_med_mul. Qed.

Definition rlim_created : IsALimit K LimitRing.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ rlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := rlim_med N |}.
  - intros j a.
    exact (rlim_car_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

(** ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) *)

Lemma rlim_zero_unique (z : carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j)) : z ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hz, rlim_zero_triangle.
Qed.

Lemma rlim_one_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j)) : e ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  now rewrite He, rlim_one_triangle.
Qed.

Lemma rlim_add_unique
  (p : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : p a b ≈ rlim_add a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hp, rlim_add_triangle.
Qed.

Lemma rlim_mul_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ rlim_mul a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hm, rlim_mul_triangle.
Qed.

Lemma rlim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ rlim_neg a.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hn, rlim_neg_triangle.
Qed.

(* The five clauses together: Mac Lane's "there is exactly one ring
   structure on the limit making every projection a homomorphism".  No law
   of the candidate structure is consumed -- only that the legs preserve
   it. *)
Lemma rlim_structure_unique
  (z e : carrier vertex_obj[L])
  (p m : carrier vertex_obj[L] → carrier vertex_obj[L] →
           carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j))
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j))
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a)) :
  (((z ≈ rlim_zero) * (e ≈ rlim_one))
     * ((∀ a b, p a b ≈ rlim_add a b) * (∀ a b, m a b ≈ rlim_mul a b)))
    * (∀ a, n a ≈ rlim_neg a).
Proof.
  split; [ split; [ split | split ] | ].
  - exact (rlim_zero_unique z Hz).
  - exact (rlim_one_unique e He).
  - exact (rlim_add_unique p Hp).
  - exact (rlim_mul_unique m Hm).
  - exact (rlim_neg_unique n Hn).
Qed.

End RngLift.

(** * Reflection: a cone of rings whose image is limiting is limiting *)

Section RngReflect.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Rng_Forget M)).

Definition rrefl_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> rig_setoid vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone Rng_Forget N).

Lemma rrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rig_map (cone_leg M j) (rrefl_med N a) ≈ rig_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Rng_Forget N) j a).
Qed.

Lemma rrefl_ext (x y : carrier (rig_setoid vertex_obj[M])) :
  (∀ j : J, rig_map (cone_leg M j) x ≈ rig_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (rng_sets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma rrefl_med_zero (N : Cone K) :
  rrefl_med N (rig_zero vertex_obj[N]) ≈ rig_zero vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_zero.
  reflexivity.
Qed.

Lemma rrefl_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_add vertex_obj[N] a b)
    ≈ rig_add vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_add, !rrefl_med_commutes.
  reflexivity.
Qed.

Lemma rrefl_med_one (N : Cone K) :
  rrefl_med N (rig_one vertex_obj[N]) ≈ rig_one vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_one.
  reflexivity.
Qed.

Lemma rrefl_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_mul vertex_obj[N] a b)
    ≈ rig_mul vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_mul, !rrefl_med_commutes.
  reflexivity.
Qed.

Program Definition rrefl_hom (N : Cone K) :
  vertex_obj[N] ~{Rng}~> vertex_obj[M] := {| rig_map := rrefl_med N |}.
Next Obligation. apply rrefl_med_zero. Qed.
Next Obligation. apply rrefl_med_add. Qed.
Next Obligation. apply rrefl_med_one. Qed.
Next Obligation. apply rrefl_med_mul. Qed.

Definition rng_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := rrefl_hom N |}.
  - intros j a.
    exact (rrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

End RngReflect.

(** * [Rng_Forget] strictly creates every limit *)

Section RngStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Rng).

Definition rng_strict_lift (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Rng_Forget N :=
  @Build_StrictLift J Rng Sets K Rng_Forget N
    (rlim_cone K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Rng_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Rng_Forget.
Proof.
  unshelve refine {| screates := rng_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (rlim_created K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))).
  - intros M HM.
    exact (rng_reflects K M HM).
Defined.

Definition Rng_Forget_CreatesLimit : CreatesLimit K Rng_Forget :=
  StrictlyCreatesLimit_CreatesLimit Rng_Forget_StrictlyCreatesLimit.

End RngStrictlyCreates.

Definition Rng_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Rng_Forget :=
  fun J K => Rng_Forget_StrictlyCreatesLimit K.

Definition Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget :=
  fun J K => Rng_Forget_CreatesLimit K.

Definition Rng_Forget_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget :=
  creates_reflects_limits (Rng_Forget_CreatesLimit K).

(* Mac Lane's uniqueness clause at the categorical level: any cone of
   rings lying over [N] is canonically isomorphic to the created one.
   This is the generic [screates_lift_unique] at this instance, not a
   restatement. *)

Definition Rng_lift_cone_unique {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Rng_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Rng_Forget_StrictlyCreatesLimit K) N HN M i.

(** * The image of a cone of rings is the elementwise cone *)

Example rng_fcone_apex {J : Category} (K : J ⟶ Rng) (N : Cone K) :
  vertex_obj[FCone Rng_Forget N] = rig_setoid vertex_obj[N] := eq_refl.

Example rng_fcone_leg {J : Category} (K : J ⟶ Rng) (N : Cone K) (j : J) :
  cone_leg (FCone Rng_Forget N) j = rig_map (cone_leg N j) := eq_refl.

(** * Mac Lane's Theorem 2: the lifting half *)

Definition Rng_Forget_lifts_limits {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Rng_Forget_CreatesLimit K) L.

Example rng_lift_apex {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) :
  Rng_Forget (vertex_obj[Rng_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example rng_lift_legs {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) (j : J) :
  fmap[Rng_Forget]
    (cone_leg (@limit_cone _ _ _ (Rng_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** * Corollaries: [Rng] is complete and [Rng_Forget] is continuous *)

Definition Rng_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget Sets_Complete Rng_Forget_creates_limits.

(* [ContinuousFunctor] is [PreservesLimitCone] quantified over every shape
   and diagram, which is what the word means in Mac Lane §V.4 -- the
   apex-only [PreservesAllLimits] below is its CONSEQUENCE, not the
   definition (Structure/Limit/Preservation.v:46-56). *)

Definition Rng_Forget_continuous : ContinuousFunctor Rng_Forget :=
  creates_limits_continuous Rng_Forget Sets_Complete Rng_Forget_creates_limits.

Definition Rng_Forget_PreservesAllLimits : PreservesAllLimits Rng_Forget :=
  creates_limits_PreservesAllLimits Rng_Forget Sets_Complete
    Rng_Forget_creates_limits.

(** * "Limits of rings are computed on underlying sets", literally *)

Section RngComputed.

Context {J : Category}.
Context (K : J ⟶ Rng).

Example rng_complete_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

Example rng_complete_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

Example rng_complete_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

Example rng_complete_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

Example rng_complete_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

End RngComputed.

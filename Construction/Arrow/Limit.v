Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(** * The arrow-category projection creates limits *)

(* Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
   Exercise 3 (book p. 112): the projection [C^→ ⟶ C × C] sending an arrow
   to its (domain, codomain) pair creates limits.  nLab: "arrow category",
   "created limit".

   WHAT IS DELIVERED, AND AT WHAT STRENGTH.  The exercise is the case
   [S = T = Id] of a statement about the TWO-SIDED comma projection
   [comma_proj : (S ↓ T) ⟶ A ∏ B] of Construction/Comma.v, and the proof
   at [Id] IS the general proof, so the general form is what is built and
   the arrow category is read off it.  Over [S : A ⟶ C], [T : B ⟶ C], a
   diagram [K : J ⟶ (S ↓ T)] and the ONE hypothesis
   [HT : PreservesLimitCone (comma_proj2 ◯ K) T] — that [T] carries the
   limit of the codomain diagram to a limit; nothing whatever is asked of
   [S], and the section binds nothing about [S] beyond its type —

     - [comma_lift_arrow N HN : S (fst apex) ~> T (snd apex)], the
       comparison arrow induced between the two limits, is the mediator of
       the cone [dom_cone N] (apex [S] of the domain apex, legs the comma
       arrows of [K] after the domain legs) into [FCone T (cod_cone N)],
       limiting by [HT]; [comma_lift_arrow_commutes] is its square with
       every leg and [comma_lift_arrow_unique] is Mac Lane's uniqueness
       clause — ANY arrow making all the squares commute IS this one.
     - [comma_lift_cone N HN : Cone K] with apex [(vertex_obj[N]; h)] and
       legs [(cone_leg N j; square)]; [comma_lift_apex_strict] and
       [comma_lift_leg_strict] record that its projection IS [N]'s apex
       and legs at [eq_refl], which is what makes
       [comma_lift_StrictLift : StrictLift K comma_proj N] a record literal
       with [eq_refl] for the object equation.
     - [comma_proj_reflect]: a cone over [K] whose projection is limiting
       is limiting.  The mediator's square is forced by JOINT MONICITY of
       the legs [T q_j] of the preserved limit ([limit_med_eq] at
       [FCone T (cod_cone (FCone comma_proj M))]), and its uniqueness is
       the downstairs uniqueness read through the comma hom-setoid, which
       compares underlying pairs only.
     - [comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj]
       — Riehl's on-the-nose reading (Structure/Limit/Creation.v:325) — and
       [comma_proj_CreatesLimit : CreatesLimit K comma_proj] through the
       bridge [StrictlyCreatesLimit_CreatesLimit]; [comma_proj_Limit] is the
       existence half bundled, its apex the downstairs apex and its arrow
       [comma_lift_arrow] at [eq_refl] ([comma_proj_Limit_apex],
       [comma_proj_Limit_arrow]).

   For the arrow category [C^→ := Id[C] ↓ Id[C]] (Construction/Arrow.v):
   [arrow_proj_creates_limits] (the issue's pinned name),
   [arrow_proj_strictly_creates_limits], [arrow_proj_creates_all_limits],
   and the corollary the exercise is used for, [Arrow_Complete : Complete C
   → Complete (C^→)] (the issue's other pinned name), through
   [creates_limits_Complete] over Construction/Product/Limit.v's
   [Product_Complete HC HC].  Limits are COMPUTED COMPONENTWISE and that is
   a readback, not prose: [Arrow_Complete_dom]/[Arrow_Complete_cod] show at
   [eq_refl] that the chosen limit's domain and codomain are [HC]'s own
   chosen limits of [Fst ◯ (comma_proj ◯ K)] and [Snd ◯ (comma_proj ◯ K)].
   The [Id] instantiation needs [Id_PreservesLimitCone], which the tree
   did not have (measured: no constant of the shape [PreservesLimitCone _
   Id] anywhere; the nearest neighbour, Theory/Equivalence/Creation.v:102's
   [Id_CreatesAllLimits], does not serve, because turning creation into
   cone-level preservation through Structure/Limit/Creation.v:205's
   [creation_preserves_limit] costs an extra [L : Limit (F ◯ K)] that the
   new lemma does not need); it is declared at the head of this file and
   belongs beside [PreservesLimitCone] in Structure/Limit/Preservation.v,
   where it
   is not placed only because that module is upstream of most of the tree
   and the move would cost a wide rebuild for one twelve-line lemma.

   WHAT IS CONSUMED.  #418's [Snd_PreservesLimitCone] (Construction/
   Product/Limit.v, unconditional) is what turns a limiting cone in
   [A ∏ B] into a limiting cone in [B]; [cod_cone] repackages its image
   over [comma_proj2 ◯ K], because [Snd ◯ (comma_proj ◯ K)] and
   [comma_proj2 ◯ K] agree on BOTH actions at [eq_refl] but are different
   functor RECORDS ([Compose]'s law fields are separate opaque obligations),
   so a cone over one is not a cone over the other — pinned in the probe
   with the two action agreements as controls.  Structure/Limit/Creation.v
   supplies the classes, the bridge and [creates_limits_Complete];
   Structure/Limit/Preservation.v supplies [limit_med_eq].  The ONE-SIDED
   donor the issue points at, Construction/Comma/Creation.v's
   [comma_CreatesLimit] for [comma_proj2 : (=(d) ↓ U) ⟶ C], is NOT
   consumed, and the [apex_obj]/[apex_leg] beneath it — declared in
   Construction/Comma/Limit.v (:161, :165), the module Creation.v builds
   on, and not in Creation.v itself — are not reused: those are stated
   over the constant-domain comma, whose objects are [(ttt, b)]-pairs and
   whose lifting argument goes through the fixed [Gdiag]; the two-sided
   projection needs the domain half to vary, and the argument here is the
   same shape one level up rather than an instance.  Issue #438, which
   asks for that one-sided lemma (Mac Lane §V.6 Lemma 1), is still OPEN at
   the time of writing although its content is in that file; nothing here
   depends on how it is resolved.

   STRICTNESS, MEASURED STRICT FIRST.  Six statements close by [eq_refl]
   in this file (the two [comma_lift_*_strict] readbacks, the two
   [comma_proj_Limit_*] readbacks, [Arrow_Complete_dom],
   [Arrow_Complete_cod]); the probe adds the witness readbacks.  The WHOLE
   record [FCone comma_proj (comma_lift_cone N HN) = N] is refused at
   [eq_refl] although apex and every leg are [N]'s on the nose — the
   coherence field is a rebuilt proof and [≈] is Type-valued — pinned
   with those two controls.  Non-vacuity COMPUTES, at a shape that is
   DEGENERATE and labelled so: over [Coq] at the point shape [_1] (one
   object, one arrow, so cone coherence is vacuous and the comparison
   arrow is the diagram's own), with the diagram constant at the arrow
   [negb] and the limiting cone Structure/Limit/Initial.v's [initial_cone]
   (whose mediator is definitionally the leg), the created arrow IS [negb]
   at [eq_refl], and [true ↦ false], [false ↦ true] by computation — what
   that shows is that the whole chain REDUCES, not that a non-trivial
   limit is computed; it lives in the probe because it costs
   [Instance/Coq], [Instance/One] and [Structure/Limit/Initial] and this
   file should not.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  Every one of the 24
   constants of the two-sided section binds [A : Category@{u u0 u0}],
   [B : Category@{u1 u2 u2}], [C : Category@{u3 u4 u4}],
   [J : Category@{u5 u6 u6}] — hom identified with proof in the BINDER,
   with no such equation in any block.  EIGHTEEN of them carry the block
   equations [u0 = u2], [u0 = u4], [u0 = u6] and [u0 = u9], so the four
   categories' hom-and-proof levels collapse to one — [u9] is NOT the
   comma category's own level (that category sits at
   [Category@{u7 u4 u4}], its hom level being C's [u4], and [u7] carries
   no equation anywhere) but the level instantiating [comma_proj2]'s own
   universe [u6], an auxiliary bounded below by A's and B's hom levels
   (a mislabel the fess audit caught); the SIX cone-building constants of
   the two halves — [cod_leg], [cod_coherence], [cod_cone], [dom_leg],
   [dom_coherence], [dom_cone] — carry [u2 = u4], [u2 = u6], [u2 = u9]
   instead and leave A's hom level [u0] only BOUNDED; the ten
   [Section Lift] constants add [u15 = u20] and [u17 = u18] on auxiliary
   levels that occur in no [Category] binder (they sit inside the
   [PreservesLimitCone], [Compose] and [IsLimitCone] instances of the
   [HT] and [HN] binders).  No equation
   in any of the 31 blocks touches an OBJECT universe.  The collapse is
   NOT the comma category's doing: [Comma@{…}] binds [A], [B] and [C] at
   three separate hom levels and [Su ↓ Tu] is ACCEPTED at [ah < bh]; it is
   [Compose]'s, met first at [comma_proj ◯ K] — at a shape whose homs are
   declared strictly below the factors', [Su ↓ Tu], [K] and a [Cone] over
   [K] are accepted while [comma_proj ◯ K] is refused ("Cannot enforce
   ch = jh"), and [comma_proj_CreatesLimit] with it (pinned as the probe's
   universe negative, with those three as controls).  The arrow section's
   six constants carry NO block equation at all — the identification is
   discharged in the binders [C : Category@{u u0 u0}] and, where a shape is
   bound, [J : Category@{u17 u0 u0}], J's hom-and-proof at C's level — and
   [Arrow_Complete] is accepted at [Set < ch]; [Id_PreservesLimitCone]
   likewise carries none, binding [J : Category@{u2 u4 u4}] and
   [D : Category@{u3 u4 u4}].  No word-bounded [Set] occurs in the binder
   or block of any of the 31 constants.

   COUNTS.  31 constants — 26 declared heads plus the 5 [Qed]-closed
   lemmas [Print Module] renders as [Parameter] are all 31 [Print Module]
   entries; the file has no [Program], no [Record]/[Class]/[Inductive], so
   there is no obligation and no unlisted [Build_*] — all closed under the
   global context with zero [Axioms:] lines, and all gated fully qualified
   in [make print-assumptions].  Four [Defined] tokens, THREE load-bearing
   by flipping each alone to [Qed]: [Id_PreservesLimitCone] and
   [cod_limiting] each stop the probe's witness at [neg_created = negb]
   (the created arrow no longer reduces), and
   [comma_proj_StrictlyCreatesLimit] stops this file's own
   [comma_proj_Limit_apex]; [comma_proj_reflect] flips with both files
   compiling and is [Defined] by the data convention only.  Transitive
   in-project closure 33 modules excluding this file (probe 65), measured
   per [Require]: Construction/Product/Limit costs 6, Construction/Arrow
   1, every other [Require] 0.  [make todo] grows by the probe's
   refutation commands and the prose lines naming that token, this file
   contributing ZERO — so the issue's "adds no new hits" box is NOT met
   as written; CLAUDE.md carries the exact figure.

   NOT DELIVERED.  Colimits: no [Arrow_Cocomplete] and no dual of the
   two-sided statement — it would need [S] to preserve the COLIMIT of the
   domain diagram and a comma read at the opposites, and neither the
   duality [(S ↓ T)^op] against [(T^op ↓ S^op)] nor a direct cocone
   development is attempted here.  No converse: nothing says [T] MUST
   preserve the limit for [comma_proj] to create it.  No comparison of
   [Arrow_Complete]'s limits with the one-sided [Comma_Complete]'s, and no
   identification of [Fst ◯ comma_proj] with [comma_proj1] beyond their
   agreeing actions (both exhibited at [eq_refl] in the probe, mirroring
   the [Snd] pair), and none with [Arrow_dom] at all — the readbacks are
   stated in the [Fst ◯ (comma_proj ◯ K)] form [Product_Complete] chooses.
   No
   functoriality of the lift in [K], no naturality of the comparison
   arrow, and nothing registered as an [Instance]: a chosen limit must not
   become globally resolvable. *)

(** ** The identity functor preserves limiting cones *)

(* [FCone Id[D] N] has [N]'s apex and legs on the nose, over the diagram
   [Id[D] ◯ G] instead of [G]; the two [Cone] types differ only in that
   functor record, so a competitor over one repackages over the other. *)

Definition Id_PreservesLimitCone {J D : Category} (G : J ⟶ D) :
  PreservesLimitCone G Id[D].
Proof.
  intros N HN M.
  pose (M' := @Build_Cone J D G vertex_obj[M]
                (@Build_ACone J D vertex_obj[M] G (cone_leg M)
                   (fun x y f => cone_leg_coh M f))).
  destruct (HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

(** ** The two-sided comma projection creates limits *)

Section TwoSided.

Context {A B C : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.
Context {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(* The codomain half of a cone over the projected diagram, read over
   [comma_proj2 ◯ K].  [FCone Snd N] is a cone over [Snd ◯ (comma_proj ◯ K)],
   a different functor record with the same actions. *)

Definition cod_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  snd vertex_obj[N] ~{B}~> (comma_proj2 ◯ K) j := snd (cone_leg N j).

Lemma cod_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[comma_proj2 ◯ K] f ∘ cod_leg N x ≈ cod_leg N y.
Proof. exact (snd (cone_leg_coh N f)). Qed.

Definition cod_cone (N : Cone (comma_proj ◯ K)) : Cone (comma_proj2 ◯ K) :=
  @Build_Cone J B (comma_proj2 ◯ K) (snd vertex_obj[N])
    (@Build_ACone J B (snd vertex_obj[N]) (comma_proj2 ◯ K) (cod_leg N)
       (fun x y f => cod_coherence N f)).

(* #418's second projection preserves limiting cones unconditionally; the
   competitor is repackaged across the same record boundary. *)

Definition cod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (cod_cone N).
Proof.
  intro M.
  pose (M' := @Build_Cone J B (Snd ◯ (comma_proj ◯ K)) vertex_obj[M]
                (@Build_ACone J B vertex_obj[M] (Snd ◯ (comma_proj ◯ K))
                   (cone_leg M) (fun x y f => cone_leg_coh M f))).
  destruct (Snd_PreservesLimitCone (comma_proj ◯ K) N HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

Definition tcod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (FCone T (cod_cone N)) :=
  HT (cod_cone N) (cod_limiting N HN).

(* The cone over [T ◯ (comma_proj2 ◯ K)] with apex [S] of the domain apex,
   whose legs are the comma arrows of [K] after the domain legs. *)

Definition dom_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  S (fst vertex_obj[N]) ~{C}~> (T ◯ (comma_proj2 ◯ K)) j :=
  `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).

Lemma dom_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[T ◯ (comma_proj2 ◯ K)] f ∘ dom_leg N x ≈ dom_leg N y.
Proof.
  unfold dom_leg.
  change (fmap[T] (snd `1 (fmap[K] f))
            ∘ (`2 (K x) ∘ fmap[S] (fst (cone_leg N x)))
            ≈ `2 (K y) ∘ fmap[S] (fst (cone_leg N y))).
  rewrite comp_assoc.
  rewrite <- (`2 (fmap[K] f)).
  rewrite <- comp_assoc, <- fmap_comp.
  now rewrite (fst (cone_leg_coh N f)).
Qed.

Definition dom_cone (N : Cone (comma_proj ◯ K)) :
  Cone (T ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J C (T ◯ (comma_proj2 ◯ K)) (S (fst vertex_obj[N]))
    (@Build_ACone J C (S (fst vertex_obj[N])) (T ◯ (comma_proj2 ◯ K))
       (dom_leg N) (fun x y f => dom_coherence N f)).

Section Lift.

Context (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N).

(* The comparison arrow: the mediator of [dom_cone N] into the preserved
   codomain limit. *)

Definition comma_lift_arrow :
  S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N]) :=
  unique_obj (tcod_limiting N HN (dom_cone N)).

Lemma comma_lift_arrow_commutes (j : J) :
  fmap[T] (snd (cone_leg N j)) ∘ comma_lift_arrow
    ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).
Proof. exact (unique_property (tcod_limiting N HN (dom_cone N)) j). Qed.

(* Mac Lane's uniqueness clause: any arrow making every square commute is
   the comparison arrow. *)

Lemma comma_lift_arrow_unique
  (h : S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N])) :
  (∀ j : J, fmap[T] (snd (cone_leg N j)) ∘ h
              ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j))) →
  comma_lift_arrow ≈ h.
Proof. intro Hh. exact (uniqueness (tcod_limiting N HN (dom_cone N)) h Hh). Qed.

Definition comma_lift_obj : S ↓ T := (vertex_obj[N]; comma_lift_arrow).

Definition comma_lift_leg (j : J) : comma_lift_obj ~{S ↓ T}~> K j :=
  (cone_leg N j; symmetry (comma_lift_arrow_commutes j)).

Lemma comma_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_lift_leg x ≈ comma_lift_leg y.
Proof. exact (cone_leg_coh N f). Qed.

Definition comma_lift_cone : Cone K :=
  @Build_Cone J (S ↓ T) K comma_lift_obj
    (@Build_ACone J (S ↓ T) comma_lift_obj K comma_lift_leg
       (fun x y f => comma_lift_coherence f)).

(* The lift lies over [N] ON THE NOSE. *)

Example comma_lift_apex_strict :
  comma_proj vertex_obj[comma_lift_cone] = vertex_obj[N] := eq_refl.

Example comma_lift_leg_strict (j : J) :
  fmap[comma_proj] (cone_leg comma_lift_cone j) = cone_leg N j := eq_refl.

Definition comma_lift_StrictLift : StrictLift K comma_proj N :=
  @Build_StrictLift J (S ↓ T) (A ∏ B) K comma_proj N comma_lift_cone eq_refl
    (fun j => reflexivity _).

End Lift.

(* Reflection: a cone over [K] whose projection is limiting is limiting.
   The mediator downstairs is a comma morphism because the legs of the
   preserved codomain limit are jointly monic. *)

Definition comma_proj_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj M)) : IsLimitCone M.
Proof using HT.
  intro M'.
  destruct (HM (FCone comma_proj M')) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ fmap[S] (fst w)
                  ≈ fmap[T] (snd w) ∘ (`2 vertex_obj[M'])).
  { apply (limit_med_eq
             (limitcone_isalimit (tcod_limiting (FCone comma_proj M) HM))
             (dom_cone (FCone comma_proj M'))).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ ((`2 vertex_obj[M]) ∘ fmap[S] (fst w))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc.
      rewrite <- (`2 (cone_leg M j)).
      rewrite <- comp_assoc, <- fmap_comp.
      now rewrite (fst (Hw j)).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ (fmap[T] (snd w) ∘ (`2 vertex_obj[M']))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (snd (Hw j)).
      symmetry.
      exact (`2 (cone_leg M' j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j. exact (Hw j).
  - intros v Hv. apply Hwu. intro j. exact (Hv j).
Defined.

Definition comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj.
Proof using HT.
  unshelve refine {| screates := fun N HN => comma_lift_StrictLift N HN |}.
  - intros N HN.
    apply comma_proj_reflect.
    exact (limitcone_transport
             (ConeIso_sym (slift_iso (comma_lift_StrictLift N HN);
                           slift_iso_legs (comma_lift_StrictLift N HN))) HN).
  - exact comma_proj_reflect.
Defined.

Definition comma_proj_CreatesLimit : CreatesLimit K comma_proj :=
  StrictlyCreatesLimit_CreatesLimit comma_proj_StrictlyCreatesLimit.

Definition comma_proj_Limit (L : Limit (comma_proj ◯ K)) : Limit K :=
  creates_limit_lift comma_proj_CreatesLimit L.

Example comma_proj_Limit_apex (L : Limit (comma_proj ◯ K)) :
  (`1 vertex_obj[comma_proj_Limit L]) = vertex_obj[L] := eq_refl.

Example comma_proj_Limit_arrow (L : Limit (comma_proj ◯ K)) :
  (`2 vertex_obj[comma_proj_Limit L])
    = comma_lift_arrow (@limit_cone _ _ _ L) (limit_limitcone L) := eq_refl.

End TwoSided.

(** ** The arrow category: Mac Lane §V.1 Exercise 3 *)

Section ArrowLimit.

Context {C : Category}.

Definition arrow_proj_creates_limits {J : Category} (K : J ⟶ @Arrow C) :
  CreatesLimit K comma_proj :=
  comma_proj_CreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_strictly_creates_limits {J : Category}
  (K : J ⟶ @Arrow C) :
  StrictlyCreatesLimit K comma_proj :=
  comma_proj_StrictlyCreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_creates_all_limits :
  CreatesAllLimits (@comma_proj C C C Id[C] Id[C]) :=
  fun J K => arrow_proj_creates_limits K.

(* The corollary: the arrow category is complete whenever the base is, its
   limits computed on domains and codomains. *)

Definition Arrow_Complete (HC : @Complete C) : @Complete (@Arrow C) :=
  creates_limits_Complete comma_proj (Product_Complete HC HC)
    arrow_proj_creates_all_limits.

Example Arrow_Complete_dom (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  fst (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Fst ◯ (comma_proj ◯ K))] := eq_refl.

Example Arrow_Complete_cod (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  snd (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Snd ◯ (comma_proj ◯ K))] := eq_refl.

End ArrowLimit.

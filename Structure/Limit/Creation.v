Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Creation of limits and colimits by a functor *)

(* nLab:      https://ncatlab.org/nlab/show/created+limit
   nLab:      https://ncatlab.org/nlab/show/preserved+limit
   Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
              §V.1 Definition 3 (book p. 112) and §V.4 Theorem 2
              (book p. 117)
   Riehl:     Category Theory in Context, 2nd ed., §3.4 Definition 3.4.1
              clause (iii) with the remark following it (p. 104), and
              Definition 3.4.7 (p. 105)
   Awodey:    Category Theory, 2nd ed., §5.6 Definition 5.31 (p. 119)

   Preservation says that a functor carries limit cones to limit cones;
   reflection says that it recognizes them; creation says that it
   CONSTRUCTS them.  Mac Lane's §V.1 Definition 3 reads: [F : A ⟶ X]
   creates the limit of [K : J ⟶ A] when, to every limiting cone
   [τ : x → F K] in [X], there is exactly one pair [(a, σ)] with
   [F a = x] and [F σ = τ], and that [σ] is a limiting cone.

   The interest of the notion is practical rather than taxonomic.  It is
   what makes "limits in an algebraic category are computed on underlying
   sets" a theorem rather than a slogan: the forgetful functor of a
   category of algebras creates limits, so the limit upstairs is the limit
   of the carriers, equipped with the one structure map that makes every
   projection a homomorphism.  That is exactly the witness shipped with
   this file — [EM_Forget] strictly creates every limit
   (Monad/Eilenberg/Moore/Limit.v) — and Mac Lane's §V.4 Theorem 2 then
   converts creation into completeness and continuity, which is how [Set],
   [Top], [Grp] and module categories are shown complete in the first
   place.

   Riehl's remark on Definition 3.4.1 is the calibration point, and this
   file follows it exactly.  Creation entails reflection outright: that is
   [creates_reflects_limits], a projection.  Creation entails preservation
   ONLY where the limit downstairs exists — with nothing limiting
   downstairs the creation clause never fires, so creation does not by
   itself give preservation.  Accordingly [creation_preserves_limit] takes
   [L : Limit (F ◯ K)] as an explicit hypothesis, and the reader can see
   in its signature which half of Riehl's remark is being used.

   Contents: the cone-level limit predicate and its conversions; the
   calculus of cone isomorphisms, including uniqueness of limits up to a
   compatible isomorphism; the image of a cone under a functor; cone-level
   preservation and reflection; the class [CreatesLimit] with Mac Lane's
   remaining two clauses derived; §V.4 Theorem 2 in both halves with the
   shape variants; the strict (Riehl 3.4.7) variant and the bridge between
   the two classes; creation under composition; and the colimit duals.

   CONE LEVEL, NOT APEX LEVEL.  The predicate [IsLimitCone] below says
   that a GIVEN cone is universal.  The library's [IsALimit]
   (Structure/Limit.v:129) pins only the apex and carries its own chosen
   [limit_acone], whose legs are unrelated to any cone one holds; the
   argument at Construction/Comma/Limit.v:47-66 shows why that is
   genuinely too weak here.  The cone-level notion was already being
   written out by hand at three places — [PreservesImageLimit]
   (Construction/Comma/Limit.v:110), the leg hypothesis of
   [ff_reflect_ump] (Theory/Equivalence/Limit.v:391) and [rapl_ump]
   (Adjunction/Continuity.v:176) — so this file names an existing notion
   rather than introducing one.  The two bridges to [PreservesImageLimit]
   are identity functions and live in Construction/Comma/Creation.v; the
   leg side condition of [ff_reflect_ump] discharges by [reflexivity]
   because the legs of [FCone] ARE the image legs.  Issue #427 owns
   cone-level preservation as such; when it lands, [IsLimitCone],
   [PreservesLimitCone] and [FCone] belong next to [cone_leg] in
   Structure/Limit/Preservation.v, and [FCone] merges with [fmap_cone]
   (Theory/Equivalence/Limit.v:283).  They are restated here — some 35
   lines, including [cone_leg_coh] — only because that file sits above
   this layer: importing it here would compile, but it would invert the
   layering.  The name [ReflectsLimit]
   is deliberately left unused; #481 may want it.

   THE STRICTNESS QUESTION, AND WHAT THE SETOID SETTING FORCES.  Mac
   Lane's definition asks for a pair [(a, σ)] with [F a = x] and
   [F σ = τ].  Object equality is available here (obj is a bare Type, and
   Instance/Discrete.v, Construction/Grothendieck/Strict.v and
   Theory/Category/Monoid.v all use it), so [StrictLift] states the apex
   clause with [=] and the leg clause with [≈] through [hom_rew]; that is
   Riehl's Definition 3.4.7, which she flags as an "evil" strictification
   not generally satisfied by equivalences — and indeed the apex of
   [equivalence_creates_limits] is the quasi-inverse of the given apex, in
   general only isomorphic to it.  The iso-invariant reading is the usable default and
   is the one [CreatesLimit] carries, following the same decision recorded
   at Monad/Monadicity/Beck.v:39-59 for one diagram shape.  Both notions
   ship, and [StrictlyCreatesLimit_CreatesLimit] relates them in the
   derivable direction.

   UNIQUENESS OF THE LIFT.  Mac Lane's "exactly one pair" cannot be a
   FIELD here, because a field must hold at every intended instance and the
   obstruction at the two that matter is not a matter of effort: for [EM_Forget] two lifts of one
   limiting cone carry algebra structures whose actions agree only up to
   [≈], and equality of the [TAlgebra] records would additionally require
   equality of those actions and of their law proofs; the comma projection
   behaves the same way for its mediating triangle.  (In special cases the
   on-the-nose clause is inhabited — for [Id[C]] both lifts have the given
   apex — which is why it is stated below as a derived theorem rather than
   ruled out.)  Uniqueness is
   therefore a theorem rather than a field, in the form the setting
   supports and the one Monad/Monadicity/Beck.v:187 already uses at its
   own shape: [creates_lift_unique] says any cone lying over N is
   canonically isomorphic to the created one.  With it, Mac Lane's second
   clause ([creates_limiting], the lift is itself limiting) is likewise
   derived — from the reflection field — rather than assumed, so the class
   carries three fields and no redundancy.  The reflection field is not
   derivable from the other two: relating a lift to a competing cone
   upstairs would need F full and conservative, which is why Beck.v
   carries [create_coeq_reflects] separately and needed a section of its
   own (Beck.v:795-905) to discharge it.

   CONVENTIONS.  Arguments are DIAGRAM FIRST, [CreatesLimit K F], matching
   [PreservesLimit K F] (Structure/Limit/Preservation.v:48) so the two
   read alike in the same statement.  None of the classes below is
   registered for instance resolution: creation witnesses are always
   passed explicitly, exactly as Structure/Limit/Preservation.v:35-36
   records for preservation.  On size: [CreatesLimit] pins J, C and D to
   one hom/proof universe just as [PreservesLimit] does, and
   [creates_limits_Complete] additionally shares one shape universe
   between its two [Complete] occurrences; the library's [Complete] carries
   no explicit smallness hypothesis (Structure/Complete.v:27-37), so
   "creates all small limits" here reads as "creates limits of every shape
   the use site's universes allow".  Creation of finite limits is out of
   scope: the tree has no finiteness predicate on shapes
   (Structure/Topos.v and Structure/Regular.v spell finite limits as
   terminal, products and pullbacks), and [CreatesLimitsOfShape] at a
   named shape is what is offered instead.  [(F ◯ K)^op] and
   [F^op ◯ K^op] are not convertible, so the colimit side repackages cones
   field by field, following [preserves_colimit]
   (Structure/Limit/Preservation.v:205) and [isalimit_op_comp]
   (Theory/Equivalence/Limit.v:539); the covariant strict-side accessors
   are not provided, since every in-tree colimit-side creation consumer
   speaks the elementary cofork API of Structure/Coequalizer.v instead. *)

(** ** The cone-level limit predicate *)

(* [N] is a limiting cone: every cone over the same diagram factors through
   it uniquely, and the factorization is compatible with the legs OF N —
   which is what distinguishes this from the apex-pinned [IsALimit]. *)

Definition IsLimitCone {J C : Category} {K : J ⟶ C} (N : Cone K) : Type :=
  ∀ M : Cone K, ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x.

(* The four conversions against the existing classes are pure repackaging:
   every one is a term, with no proof obligation. *)

Definition limitcone_isalimit {J C : Category} {K : J ⟶ C} {N : Cone K}
  (H : IsLimitCone N) : IsALimit K vertex_obj[N] :=
  @Build_IsALimit J C K vertex_obj[N] (@coneFrom _ _ _ N) H.

Definition isalimit_limitcone {J C : Category} {K : J ⟶ C} {c : C}
  (H : IsALimit K c) :
  @IsLimitCone J C K (@Build_Cone J C K c (@limit_acone _ _ _ _ H)) :=
  @ump_limit _ _ _ _ H.

Definition limit_limitcone {J C : Category} {K : J ⟶ C} (L : Limit K) :
  IsLimitCone (@limit_cone _ _ _ L) := @ump_limits _ _ _ L.

Definition limitcone_limit {J C : Category} {K : J ⟶ C} (N : Cone K)
  (H : IsLimitCone N) : Limit K := @Build_Limit J C K N H.

(** ** Isomorphism of cones *)

(* A cone isomorphism is an isomorphism of apexes commuting with the legs.
   It is [sigT], hence data: the comparison morphism can be projected and
   computed with. *)

Definition ConeIso {J C : Category} {K : J ⟶ C} (N M : Cone K) : Type :=
  { i : vertex_obj[N] ≅ vertex_obj[M]
  & ∀ x : J, cone_leg M x ∘ to i ≈ cone_leg N x }.

Section ConeIsoLemmas.

Context {J C : Category}.
Context {K : J ⟶ C}.

Lemma coneiso_from {N M : Cone K} (i : ConeIso N M) (x : J) :
  cone_leg N x ∘ from `1 i ≈ cone_leg M x.
Proof.
  destruct i as [i Hi]; simpl.
  rewrite <- (Hi x).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

Definition ConeIso_sym {N M : Cone K} (i : ConeIso N M) : ConeIso M N :=
  (iso_sym `1 i; coneiso_from i).

Definition ConeIso_id (N : Cone K) : ConeIso N N.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition ConeIso_comp {N M P : Cone K}
  (j : ConeIso M P) (i : ConeIso N M) : ConeIso N P.
Proof.
  exists (iso_compose `1 j `1 i).
  intro x; simpl.
  rewrite comp_assoc.
  rewrite (`2 j x).
  exact (`2 i x).
Defined.

(* Limit-ness is invariant under isomorphism of cones. *)

Lemma limitcone_transport {N M : Cone K} (i : ConeIso N M)
  (HN : IsLimitCone N) : IsLimitCone M.
Proof.
  intro P.
  unshelve refine {| unique_obj := to `1 i ∘ unique_obj (HN P) |}.
  - intro x.
    rewrite comp_assoc.
    rewrite (`2 i x).
    exact (unique_property (HN P) x).
  - intros v Hv.
    assert (Hfv : ∀ x : J, cone_leg N x ∘ (from `1 i ∘ v) ≈ cone_leg P x).
    { intro x.
      rewrite comp_assoc.
      rewrite (coneiso_from i x).
      exact (Hv x). }
    rewrite (uniqueness (HN P) _ Hfv).
    rewrite comp_assoc.
    rewrite iso_to_from.
    now rewrite id_left.
Defined.

(* Uniqueness of limits, in the cone-level form: any two limiting cones over
   the same diagram are isomorphic by a leg-compatible isomorphism.  This is
   what makes the created lift unique up to canonical isomorphism below. *)

Definition limitcone_iso {N M : Cone K}
  (HN : IsLimitCone N) (HM : IsLimitCone M) : ConeIso N M.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine {| to := unique_obj (HM N); from := unique_obj (HN M) |}.
    + transitivity (unique_obj (HM M)).
      * symmetry.
        apply (uniqueness (HM M)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HM N) x).
        exact (unique_property (HN M) x).
      * apply (uniqueness (HM M)).
        intro x; now rewrite id_right.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN M) x).
        exact (unique_property (HM N) x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - exact (unique_property (HM N)).
Defined.

End ConeIsoLemmas.

(** ** The image of a cone under a functor *)

Section ImageCone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

(* The coherence of a cone, read through [cone_leg].  This duplicates
   [cone_leg_coherence] (Theory/Equivalence/Limit.v:92), which sits above
   this layer: importing it here would compile, but it would invert the
   layering. *)

Lemma cone_leg_coh (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

Definition fcone_leg (N : Cone K) (x : J) :
  F (vertex_obj[N]) ~{D}~> (F ◯ K) x := fmap[F] (cone_leg N x).

Lemma fcone_coherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ K] f ∘ fcone_leg N x ≈ fcone_leg N y.
Proof.
  unfold fcone_leg; simpl.
  rewrite <- fmap_comp.
  now rewrite (cone_leg_coh N f).
Qed.

Definition FCone (N : Cone K) : Cone (F ◯ K) :=
  @Build_Cone J D (F ◯ K) (F (vertex_obj[N]))
    (@Build_ACone J D (F (vertex_obj[N])) (F ◯ K) (fcone_leg N)
       (fun x y f => fcone_coherence N f)).

(* The legs of [FCone N] ARE the image legs, definitionally; this is what
   discharges the leg side conditions of the reflection lemmas downstream. *)

Lemma FCone_leg (N : Cone K) (x : J) :
  cone_leg (FCone N) x ≈ fmap[F] (cone_leg N x).
Proof. reflexivity. Qed.

Definition FCone_iso {N M : Cone K} (i : ConeIso N M) :
  ConeIso (FCone N) (FCone M).
Proof.
  exists (fobj_iso F _ _ `1 i).
  intro x; simpl.
  change (fmap[F] (cone_leg M x) ∘ fmap[F] (to `1 i) ≈ fmap[F] (cone_leg N x)).
  rewrite <- fmap_comp.
  now rewrite (`2 i x).
Defined.

End ImageCone.

(** ** Cone-level preservation and reflection *)

Definition PreservesLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone N → IsLimitCone (FCone F N).

Definition ReflectsLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone (FCone F N) → IsLimitCone N.

(* The cone-level notion is stronger than the apex-only class of
   Structure/Limit/Preservation.v; this is the bridge, and only this
   direction holds (the argument at Construction/Comma/Limit.v:47-66 is
   precisely that the converse does not go through). *)

Definition PreservesLimitCone_PreservesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesLimitCone K F) : PreservesLimit K F.
Proof.
  constructor.
  intro L.
  exact (limitcone_isalimit (P (@limit_cone _ _ _ L) (limit_limitcone L))).
Defined.

(** ** Creation of limits (the iso-invariant reading) *)

(* Mac Lane §V.1 Definition 3, in the form the setoid setting supports: a
   lift of every limiting cone downstairs, a cone isomorphism identifying
   its image with the given cone, and reflection.  The remaining two
   clauses of the book — that the lift is limiting, and that it is unique —
   are the theorems [creates_limiting] and [creates_lift_unique] below. *)

Class CreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  creates_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : Cone K;
  creates_lift_over (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    ConeIso (FCone F (creates_lift N HN)) N;
  creates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

(* Mac Lane's clause (b): the lift is itself a limiting cone. *)

Definition creates_limiting {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (creates_lift N HN) :=
  creates_reflect (creates_lift N HN)
    (limitcone_transport (ConeIso_sym (creates_lift_over N HN)) HN).

(* Mac Lane's uniqueness clause, in the form the setting supports: any cone
   upstairs lying over N is canonically isomorphic to the created one.  This
   is the pattern of [create_coeq_unique] (Monad/Monadicity/Beck.v:187) one
   level up. *)

Definition creates_lift_unique {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (creates_lift N HN) :=
  limitcone_iso
    (creates_reflect M (limitcone_transport (ConeIso_sym j) HN))
    (creates_limiting CR N HN).

(* Creation entails reflection (Riehl §3.4, the remark following Definition
   3.4.1): here, definitionally. *)

Definition creates_reflects_limits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) : ReflectsLimitCone K F :=
  @creates_reflect J C D K F CR.

(* The existence half, bundled: a limit downstairs yields a limit upstairs. *)

Definition creates_limit_lift {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  Limit K :=
  @Build_Limit J C K
    (creates_lift (@limit_cone _ _ _ L) (limit_limitcone L))
    (creates_limiting CR (@limit_cone _ _ _ L) (limit_limitcone L)).

(** ** Mac Lane §V.4 Theorem 2, first half *)

(* Creation plus existence of the limit downstairs gives preservation, at
   the cone level.  The hypothesis [L] is Riehl's proviso, and it is
   load-bearing: the creation clause only fires on a limiting cone
   downstairs, so with no [Limit (F ◯ K)] there is nothing to feed it. *)

Theorem creation_preserves_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  PreservesLimitCone K F.
Proof.
  intros M HM.
  (* the created lift of the given limit downstairs *)
  pose (N := @limit_cone _ _ _ L).
  pose (HN := limit_limitcone L).
  pose (M' := creates_lift N HN).
  pose (HM' := creates_limiting CR N HN).
  (* M and M' are both limiting upstairs, hence isomorphic as cones *)
  pose (i := limitcone_iso HM' HM).
  (* transport limit-ness along  N ≅ F M' ≅ F M *)
  exact (limitcone_transport
           (ConeIso_comp (FCone_iso F i)
              (ConeIso_sym (creates_lift_over N HN))) HN).
Defined.

(** ** Shape-quantified creation *)

Definition CreatesLimitsOfShape (J : Category) {C D : Category} (F : C ⟶ D)
  : Type := ∀ K : J ⟶ C, CreatesLimit K F.

Definition CreatesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesLimit K F.

(* "Creates products" is the discrete-shape case, over
   Instance/Discrete.v's [DiscreteCat], mirroring how
   Structure/Limit/Product.v reaches indexed products. *)

Definition CreatesProducts {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (A : Type) (K : DiscreteCat A ⟶ C), CreatesLimit K F.

Definition CreatesAllLimits_CreatesProducts {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : CreatesProducts F :=
  fun A K => CR (DiscreteCat A) K.

(** ** Mac Lane §V.4 Theorem 2, second half *)

(* Creation of all limits transports completeness ... *)

Definition creates_limits_Complete {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : @Complete C :=
  fun J K => creates_limit_lift (CR J K) (HD J (F ◯ K)).

(* ... and makes the functor continuous, at the cone level ... *)

Definition creates_limits_continuous {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) :
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F :=
  fun J K => creation_preserves_limit (CR J K) (HD J (F ◯ K)).

(* ... hence also in the apex-only vocabulary already in the tree. *)

Definition creates_limits_PreservesAllLimits {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit
               (creates_limits_continuous F HD CR J K).

(** ** Strict creation (Riehl §3.4 Definition 3.4.7) *)

(* Transport of a morphism along an equality of its domain.  Objects use
   [eq]; morphisms are still compared with [≈]. *)

Definition hom_rew {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) : d' ~{D}~> t :=
  match p in _ = z return z ~{D}~> t with eq_refl => f end.

(* The isomorphism induced by an equality of objects.  Deliberately not
   named [iso_of_eq]: that name is taken by Instance/StrictCat/ToCat.v:36,
   which this Structure-layer file must not import. *)

Definition obj_eq_iso {D : Category} {d d' : D} (p : d = d') : d ≅ d' :=
  match p in _ = z return d ≅ z with eq_refl => iso_id end.

Lemma hom_rew_obj_eq_iso {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) (g : d' ~{D}~> t) :
  hom_rew p f ≈ g → g ∘ to (obj_eq_iso p) ≈ f.
Proof. destruct p; simpl; intro H. rewrite id_right. now symmetry. Qed.

(* An on-the-nose lift: the image apex is EQUAL to the given apex, and the
   image legs agree with the given legs up to [≈] after that transport. *)

Record StrictLift {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  (N : Cone (F ◯ K)) := {
  slift_cone : Cone K;
  slift_eq   : F (vertex_obj[slift_cone]) = vertex_obj[N];
  slift_legs : ∀ x : J,
    hom_rew slift_eq (fmap[F] (cone_leg slift_cone x)) ≈ cone_leg N x
}.

Arguments slift_cone {J C D K F N} _.
Arguments slift_eq {J C D K F N} _.
Arguments slift_legs {J C D K F N} _ _.

Definition slift_iso {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) :
  F (vertex_obj[slift_cone L]) ≅ vertex_obj[N] := obj_eq_iso (slift_eq L).

Lemma slift_iso_legs {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) (x : J) :
  cone_leg N x ∘ to (slift_iso L) ≈ fmap[F] (cone_leg (slift_cone L) x).
Proof. exact (hom_rew_obj_eq_iso _ _ _ (slift_legs L x)). Qed.

(* Every cone upstairs is tautologically a strict lift of its own image.
   Provided for reference: it has no consumer here, the uniqueness clause
   it was intended to feed having become the derived
   [screates_lift_unique] rather than a field. *)

Definition self_lift {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (M : Cone K) : StrictLift K F (FCone F M) :=
  @Build_StrictLift J C D K F (FCone F M) M eq_refl (fun x => reflexivity _).

(* Riehl's Definition 3.4.7 asks for a UNIQUE on-the-nose lift that is
   limiting.  This class keeps the on-the-nose lift and the limiting
   clause and replaces her uniqueness clause by reflection, for the reason
   given in the header; it is therefore neither weaker nor stronger than
   the book's.  Uniqueness in the form this setting supports is
   [screates_lift_unique] below, through the bridge to [CreatesLimit]. *)

Class StrictlyCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  screates (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  screates_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (screates N HN));
  screates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

Definition StrictlyCreatesLimit_CreatesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F) :
  CreatesLimit K F.
Proof.
  unshelve refine {| creates_lift := fun N HN => slift_cone (screates N HN) |}.
  - intros N HN.
    exists (slift_iso (screates N HN)).
    intro x.
    exact (slift_iso_legs (screates N HN) x).
  - exact screates_reflect.
Defined.

Definition screates_lift_unique {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F)
  (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  creates_lift_unique (StrictlyCreatesLimit_CreatesLimit SC) N HN M j.

Definition StrictlyCreatesLimitsOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, StrictlyCreatesLimit K F.

Definition StrictlyCreatesLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), StrictlyCreatesLimit K F.

(** ** Creation composes *)

Section Compose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

(* [(G ◯ F) ◯ K] and [G ◯ (F ◯ K)] have the same cones, but the two record
   types are not convertible, so the repackaging is field by field. *)

Definition cone_assoc (N : Cone ((G ◯ F) ◯ K)) : Cone (G ◯ (F ◯ K)) :=
  @Build_Cone J E (G ◯ (F ◯ K)) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) (G ◯ (F ◯ K))
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_assoc_inv (N : Cone (G ◯ (F ◯ K))) : Cone ((G ◯ F) ◯ K) :=
  @Build_Cone J E ((G ◯ F) ◯ K) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) ((G ◯ F) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_assoc {N : Cone ((G ◯ F) ◯ K)} (H : IsLimitCone N) :
  IsLimitCone (cone_assoc N) := fun M => H (cone_assoc_inv M).

Definition CreatesLimit_compose
  (CF : CreatesLimit K F) (CG : CreatesLimit (F ◯ K) G) :
  CreatesLimit K (G ◯ F).
Proof.
  unshelve refine {| creates_lift := _ |}.
  - (* the two-stage lift *)
    intros N HN.
    exact (creates_lift
             (creates_lift (cone_assoc N) (islimitcone_assoc HN))
             (creates_limiting CG (cone_assoc N) (islimitcone_assoc HN))).
  - (* the comparison isomorphism *)
    intros N HN; simpl.
    set (mid := creates_lift (cone_assoc N) (islimitcone_assoc HN)).
    set (Hmid := creates_limiting CG (cone_assoc N) (islimitcone_assoc HN)).
    pose (iF := creates_lift_over mid Hmid).
    pose (iG := creates_lift_over (cone_assoc N) (islimitcone_assoc HN)).
    exists (iso_compose `1 iG (fobj_iso G _ _ `1 iF)).
    intro x.
    assert (H1 : cone_leg N x ∘ to `1 iG ≈ fmap[G] (cone_leg mid x))
      by exact (`2 iG x).
    transitivity ((cone_leg N x ∘ to `1 iG) ∘ fmap[G] (to `1 iF)).
    + apply comp_assoc.
    + rewrite H1.
      transitivity (fmap[G] (cone_leg mid x ∘ to `1 iF)).
      * exact (symmetry (@fmap_comp _ _ G _ _ _ (cone_leg mid x) (to `1 iF))).
      * exact (@fmap_respects _ _ G _ _ _ _ (`2 iF x)).
  - (* reflection, one stage at a time *)
    intros M H.
    apply (creates_reflect (F:=F)).
    apply (creates_reflect (F:=G)).
    exact (fun M0 => H (cone_assoc_inv M0)).
Defined.

End Compose.

(** ** Creation of colimits, by duality *)

(* The definitions cost one line each; the covariant accessors do not,
   because [(F ◯ K)^op] and [F^op ◯ K^op] are not convertible. *)

Definition CreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @CreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition StrictlyCreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @StrictlyCreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition CreatesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesColimit K F.

Section Dual.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.

Definition cone_op_comp (N : Cone ((F ◯ K)^op)) : Cone (F^op ◯ K^op) :=
  @Build_Cone (J^op) (D^op) (F^op ◯ K^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) (F^op ◯ K^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_op_comp_inv (N : Cone (F^op ◯ K^op)) : Cone ((F ◯ K)^op) :=
  @Build_Cone (J^op) (D^op) ((F ◯ K)^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ K)^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_op_comp {N : Cone ((F ◯ K)^op)} (H : IsLimitCone N) :
  IsLimitCone (cone_op_comp N) := fun M => H (cone_op_comp_inv M).

Definition colimit_op_comp (L : Colimit (F ◯ K)) : Limit (F^op ◯ K^op) :=
  @Build_Limit (J^op) (D^op) (F^op ◯ K^op)
    (cone_op_comp (@limit_cone _ _ _ L))
    (islimitcone_op_comp (limit_limitcone L)).

Definition creates_colimit_lift (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : Colimit K :=
  creates_limit_lift CR (colimit_op_comp L).

(* The dual of §V.4 Theorem 2's first half, stated in op form. *)

Definition creation_preserves_colimit (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : PreservesLimitCone (K^op) (F^op) :=
  creation_preserves_limit CR (colimit_op_comp L).

End Dual.

Definition creates_colimits_Cocomplete {C D : Category} (F : C ⟶ D)
  (HD : @Cocomplete D) (CR : CreatesAllColimits F) : @Cocomplete C :=
  fun J K => creates_colimit_lift (CR J K) (HD J (F ◯ K)).

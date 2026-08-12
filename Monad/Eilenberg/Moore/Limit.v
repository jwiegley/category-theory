Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.

Generalizable All Variables.

(** * Limits of algebras are computed on carriers *)

(* nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category#limits
   Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §VI.2 Theorem 1 and the §V.1 creation vocabulary (p. 112)

   For any monad T on D, the forgetful functor [EM_Forget T] STRICTLY
   creates every limit: given a limiting cone over [EM_Forget T ◯ K]
   downstairs, the mediating map into its apex from the cone whose legs are
   [t_alg ∘ fmap[T] π] is an algebra structure, the resulting cone upstairs
   lies over the given one on the nose ([em_over_obj] and [em_over_legs] are
   both [eq_refl], because EM_Forget's object map is the first projection),
   it is limiting ([em_created]), its structure map is the only one over
   that cone ([em_alg_unique]), and a cone upstairs whose image is limiting
   is itself limiting ([em_reflects]).

   On the house rule that morphisms are compared with [≈]: [em_over_legs]
   is the one statement here that writes [=] between morphisms, and it does
   so because both sides are the SAME term — the witness is [eq_refl].  It
   records Mac Lane's [F σ = τ] at full strength, which is strictly
   stronger than the [≈] the class asks for; every law, every proof and the
   [StrictLift] leg clause consumed by [em_strict_lift] use [≈].

   This makes Structure/Limit/Creation.v's classes inhabited by a functor
   the library already builds, and it turns the prose claim at
   Structure/Complete.v:58-60 into the theorem [EM_Complete].

   It is the limit-side companion to [monadic_creates]
   (Monad/Monadicity/Beck.v:911), which creates U-split coequalizers only;
   no comparison lemma between the two is attempted here —
   [CreatesUSplitCoequalizers] quantifies over pairs supplied with a split
   coequalizer of their U-image, which is strictly more data than a
   colimiting cocone, so the honest bridge is a class-indexed restriction
   statement rather than an instance, and [U ◯ APair f g] is not
   convertible with [APair (fmap[U] f) (fmap[U] g)].  The statement that
   was costed and declined is [CreatesUSplitCoequalizers U → ∀ {x y}
   (f g : x ~> y), SplitCoequalizer (fmap[U] f) (fmap[U] g) →
   CreatesColimit (APair f g) U], routed through
   [split_coequalizer_is_coequalizer] (Structure/Coequalizer/Split.v) and
   the op repackaging of Structure/Limit/Creation.v; it is recorded here
   rather than shipped, and the issue's request for it is unmet.  Neither Beck.v nor
   BeckObjects.v is modified: [CreatedSplitCoequalizer]
   (Monad/Monadicity/BeckObjects.v:385) is the same pattern at one shape,
   its [created_hom_carrier] being the [slift_legs] clause and its
   [created_alg_unique] the [≈]-form of uniqueness at a pinned carrier.

   The file imports no [Instance/*], mirroring the Beck.v /
   Monad/Monadicity/Examples.v split; the hypothesis-free instantiation
   lives in Monad/Eilenberg/Moore/Limit/Examples.v. *)

Section EMCreates.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).
Context (L : Limit (EM_Forget T ◯ K)).

(** ** Generic cone precomposition *)

Definition cone_pre {c : D} (N : Cone (EM_Forget T ◯ K))
  (u : c ~{D}~> vertex_obj[N]) : Cone (EM_Forget T ◯ K).
Proof.
  unshelve refine (@Build_Cone J D (EM_Forget T ◯ K) c
    (@Build_ACone J D c (EM_Forget T ◯ K) (fun j => cone_leg N j ∘ u) _)).
  intros x y f; simpl.
  rewrite comp_assoc.
  rewrite (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
  reflexivity.
Defined.

(** ** The action cone: apex [T L], legs [ν_j ∘ T π_j] *)

Definition em_act_leg (j : J) : T (vertex_obj[L]) ~{D}~> (EM_Forget T ◯ K) j :=
  t_alg[`2 (K j)] ∘ fmap[T] (limit_leg (limit_is_alimit L) j).

Lemma em_act_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[EM_Forget T ◯ K] f ∘ em_act_leg x ≈ em_act_leg y.
Proof.
  unfold em_act_leg.
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (fmap[K] f)).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (limit_leg_coherence (limit_is_alimit L) f).
  reflexivity.
Qed.

Definition em_act_cone : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (T (vertex_obj[L]))
    (@Build_ACone J D (T (vertex_obj[L])) (EM_Forget T ◯ K)
       em_act_leg (@em_act_coherence)).

(* The created structure map is the mediator of that cone. *)

Definition em_act : T (vertex_obj[L]) ~{D}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) em_act_cone.

Lemma em_act_triangle (j : J) :
  limit_leg (limit_is_alimit L) j ∘ em_act ≈ em_act_leg j.
Proof. exact (limit_med_commutes (limit_is_alimit L) em_act_cone j). Qed.

(** ** The algebra laws for the created action *)

Lemma em_alg_t_id : em_act ∘ ret ≈ id.
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (@Build_Cone J D (EM_Forget T ◯ K) (vertex_obj[L])
              (@limit_acone _ _ _ _ (limit_is_alimit L)))).
  - intro j.
    rewrite comp_assoc.
    rewrite (em_act_triangle j).
    unfold em_act_leg.
    rewrite <- comp_assoc.
    rewrite <- fmap_ret.
    rewrite comp_assoc.
    rewrite t_id.
    rewrite id_left.
    reflexivity.
  - intro j.
    rewrite id_right.
    reflexivity.
Qed.

Lemma em_action_left (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ fmap[T] em_act)
    ≈ em_act_leg j ∘ (@join D T H (vertex_obj[L])).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  unfold em_act_leg at 1.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (em_act_triangle j).
  unfold em_act_leg.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite t_action.
  rewrite <- !comp_assoc.
  rewrite join_fmap_fmap.
  reflexivity.
Qed.

Lemma em_action_right (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ (@join D T H (vertex_obj[L])))
    ≈ em_act_leg j ∘ (@join D T H (vertex_obj[L])).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  reflexivity.
Qed.

Lemma em_alg_t_action :
  em_act ∘ fmap[T] em_act ≈ em_act ∘ (@join D T H (vertex_obj[L])).
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (cone_pre em_act_cone (@join D T H (vertex_obj[L])))).
  - exact em_action_left.
  - exact em_action_right.
Qed.

Definition em_alg : @TAlgebra D T H (vertex_obj[L]) :=
  {| t_alg := em_act ; t_id := em_alg_t_id ; t_action := em_alg_t_action |}.

Definition em_apex : EilenbergMoore T := (vertex_obj[L]; em_alg).

Definition em_leg (j : J) : em_apex ~{EilenbergMoore T}~> K j :=
  @Build_TAlgebraHom D T H (vertex_obj[L]) (`1 (K j)) em_alg (`2 (K j))
    (limit_leg (limit_is_alimit L) j) (em_act_triangle j).

Lemma em_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ em_leg x ≈ em_leg y.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f). Qed.

Definition em_cone : Cone K :=
  @Build_Cone J (EilenbergMoore T) K em_apex
    (@Build_ACone J (EilenbergMoore T) em_apex K em_leg (@em_leg_coherence)).

(** ** Strictness: the created cone lies over L on the nose *)

Definition em_over_obj : EM_Forget T em_apex = vertex_obj[L] := eq_refl.

Definition em_over_legs (j : J) :
  fmap[EM_Forget T] (cone_leg em_cone j) = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** ** The lift is limiting *)

Definition car_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (`1 vertex_obj[N])
    (@Build_ACone J D (`1 vertex_obj[N]) (EM_Forget T ◯ K)
       (fun j => t_alg_hom[cone_leg N j])
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition car_med (N : Cone K) : (`1 vertex_obj[N]) ~{D}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (car_cone N).

Lemma car_med_commutes (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ car_med N ≈ t_alg_hom[cone_leg N j].
Proof. exact (limit_med_commutes (limit_is_alimit L) (car_cone N) j). Qed.

Lemma car_med_hom_left (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (car_med N ∘ t_alg[`2 vertex_obj[N]])
    ≈ em_act_leg j ∘ fmap[T] (car_med N).
Proof.
  rewrite comp_assoc.
  rewrite (car_med_commutes N j).
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg N j)).
  unfold em_act_leg.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (car_med_commutes N j).
  reflexivity.
Qed.

Lemma car_med_hom_right (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ fmap[T] (car_med N))
    ≈ em_act_leg j ∘ fmap[T] (car_med N).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  reflexivity.
Qed.

Lemma car_med_is_hom (N : Cone K) :
  car_med N ∘ t_alg[`2 vertex_obj[N]] ≈ em_act ∘ fmap[T] (car_med N).
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (cone_pre em_act_cone (fmap[T] (car_med N)))).
  - exact (car_med_hom_left N).
  - exact (car_med_hom_right N).
Qed.

Definition em_med (N : Cone K) : vertex_obj[N] ~{EilenbergMoore T}~> em_apex :=
  @Build_TAlgebraHom D T H (`1 vertex_obj[N]) (vertex_obj[L])
    (`2 vertex_obj[N]) em_alg (car_med N) (car_med_is_hom N).

Definition em_created : IsALimit K em_apex.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ em_cone |}.
  intro N.
  unshelve refine {| unique_obj := em_med N |}.
  - exact (car_med_commutes N).
  - intros v Hv.
    exact (limit_med_unique (limit_is_alimit L) (car_cone N) t_alg_hom[v] Hv).
Defined.

(** ** Uniqueness of the lift: the algebra structure is the only one *)

(* The [≈]-form of Mac Lane's uniqueness clause at a pinned carrier, the
   same statement [created_alg_unique] (BeckObjects.v:391) makes at its own
   shape. *)

Lemma em_alg_unique (alg' : @TAlgebra D T H (vertex_obj[L]))
  (Halg : ∀ j, limit_leg (limit_is_alimit L) j ∘ t_alg[alg'] ≈ em_act_leg j) :
  t_alg[alg'] ≈ t_alg[em_alg].
Proof.
  symmetry.
  exact (limit_med_unique (limit_is_alimit L) em_act_cone t_alg[alg'] Halg).
Qed.

End EMCreates.

(** ** Reflection: a cone whose image is limiting is limiting *)

Section EMReflects.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).
Context (M : Cone K).
Context (HM : IsALimit (EM_Forget T ◯ K) (`1 vertex_obj[M])).
Context (Hlegs : ∀ j, limit_leg HM j ≈ t_alg_hom[cone_leg M j]).

Definition rcar_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (`1 vertex_obj[N])
    (@Build_ACone J D (`1 vertex_obj[N]) (EM_Forget T ◯ K)
       (fun j => t_alg_hom[cone_leg N j])
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition rcar_med (N : Cone K) :
  (`1 vertex_obj[N]) ~{D}~> (`1 vertex_obj[M]) :=
  limit_med HM (rcar_cone N).

Lemma rcar_med_commutes (N : Cone K) (j : J) :
  t_alg_hom[cone_leg M j] ∘ rcar_med N ≈ t_alg_hom[cone_leg N j].
Proof using All.
  rewrite <- (Hlegs j).
  exact (limit_med_commutes HM (rcar_cone N) j).
Qed.

Definition ract_leg (N : Cone K) (j : J) :
  T (`1 vertex_obj[N]) ~{D}~> (EM_Forget T ◯ K) j :=
  t_alg[`2 (K j)] ∘ fmap[T] (t_alg_hom[cone_leg N j]).

Lemma ract_coherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[EM_Forget T ◯ K] f ∘ ract_leg N x ≈ ract_leg N y.
Proof using All.
  assert (Hc : t_alg_hom[fmap[K] f] ∘ t_alg_hom[cone_leg N x]
                 ≈ t_alg_hom[cone_leg N y])
    by exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
  unfold ract_leg.
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (fmap[K] f)).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite Hc.
  reflexivity.
Qed.

Definition ract_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (T (`1 vertex_obj[N]))
    (@Build_ACone J D (T (`1 vertex_obj[N])) (EM_Forget T ◯ K)
       (ract_leg N) (@ract_coherence N)).

Lemma rcar_hom_left (N : Cone K) (j : J) :
  limit_leg HM j ∘ (rcar_med N ∘ t_alg[`2 vertex_obj[N]]) ≈ ract_leg N j.
Proof using All.
  rewrite (Hlegs j).
  rewrite comp_assoc.
  rewrite (rcar_med_commutes N j).
  exact (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg N j)).
Qed.

Lemma rcar_hom_right (N : Cone K) (j : J) :
  limit_leg HM j ∘ (t_alg[`2 vertex_obj[M]] ∘ fmap[T] (rcar_med N))
    ≈ ract_leg N j.
Proof using All.
  rewrite (Hlegs j).
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg M j)).
  unfold ract_leg.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (rcar_med_commutes N j).
  reflexivity.
Qed.

Lemma rcar_med_is_hom (N : Cone K) :
  rcar_med N ∘ t_alg[`2 vertex_obj[N]]
    ≈ t_alg[`2 vertex_obj[M]] ∘ fmap[T] (rcar_med N).
Proof using All.
  apply (limit_med_eq HM (ract_cone N)).
  - exact (rcar_hom_left N).
  - exact (rcar_hom_right N).
Qed.

Definition rem_med (N : Cone K) :
  vertex_obj[N] ~{EilenbergMoore T}~> vertex_obj[M] :=
  @Build_TAlgebraHom D T H (`1 vertex_obj[N]) (`1 vertex_obj[M])
    (`2 vertex_obj[N]) (`2 vertex_obj[M]) (rcar_med N) (rcar_med_is_hom N).

Definition em_reflects : IsALimit K vertex_obj[M].
Proof using All.
  unshelve refine {| limit_acone := @coneFrom _ _ _ M |}.
  intro N.
  unshelve refine {| unique_obj := rem_med N |}.
  - exact (rcar_med_commutes N).
  - intros v Hv.
    apply (limit_med_unique HM (rcar_cone N) t_alg_hom[v]).
    intro j.
    rewrite (Hlegs j).
    exact (Hv j).
Defined.

End EMReflects.

(** ** [EM_Forget] strictly creates every limit *)

Section EMStrictlyCreates.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).

Definition em_strict_lift (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone N) :
  StrictLift K (EM_Forget T) N :=
  @Build_StrictLift J (EilenbergMoore T) D K (EM_Forget T) N
    (em_cone T K (@Build_Limit J D (EM_Forget T ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition em_forget_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (EM_Forget T).
Proof.
  unshelve refine {| screates := em_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (em_created T K (@Build_Limit J D (EM_Forget T ◯ K) N HN))).
  - intros M HM.
    exact (@ump_limit _ _ _ _
             (em_reflects T K M (limitcone_isalimit HM)
                (fun j => reflexivity _))).
Defined.

Definition em_forget_CreatesLimit : CreatesLimit K (EM_Forget T) :=
  StrictlyCreatesLimit_CreatesLimit em_forget_StrictlyCreatesLimit.

End EMStrictlyCreates.

Definition em_forget_StrictlyCreatesLimits {D : Category} (T : D ⟶ D)
  `{H : @Monad D T} : StrictlyCreatesLimits (EM_Forget T) :=
  fun J K => em_forget_StrictlyCreatesLimit T K.

Definition em_forget_CreatesAllLimits {D : Category} (T : D ⟶ D)
  `{H : @Monad D T} : CreatesAllLimits (EM_Forget T) :=
  fun J K => em_forget_CreatesLimit T K.

(** ** Algebras over a complete base are complete *)

(* Mac Lane §V.4 Theorem 2 applied to the witness above; this is the
   standing claim of Structure/Complete.v:58-60, as a theorem. *)

Definition EM_Complete {D : Category} (T : D ⟶ D) `{H : @Monad D T}
  (HD : @Complete D) : @Complete (EilenbergMoore T) :=
  creates_limits_Complete (EM_Forget T) HD (em_forget_CreatesAllLimits T).

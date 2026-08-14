Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Preservation of limits and colimits; reflection of isomorphisms *)

(* nLab:      https://ncatlab.org/nlab/show/preserved+limit
   nLab:      https://ncatlab.org/nlab/show/continuous+functor
   nLab:      https://ncatlab.org/nlab/show/conservative+functor
   Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
              §V.4 "Preservation of limits" (book p. 117), with Exercise 1
   Awodey:    Category Theory, 2nd ed., §5.5 (the canonical comparison map)
              and §5.6 Definition 5.31 (p. 119)
   Riehl:     Category Theory in Context, 2nd ed., §3.3 and §3.4
   Wikipedia:
   https://en.wikipedia.org/wiki/Limit_(category_theory)#Preservation_of_limits

   WHICH OF THE TWO READINGS IS THE DEFINITION.  Mac Lane's §V.4 says that a
   functor F preserves the limit of a diagram K when it carries a LIMITING
   CONE over K to a LIMITING CONE over F ◯ K: the image cone — apex F L,
   legs fmap[F] of the legs of L — must itself be universal.  That is
   [PreservesLimitCone] below, and it is what this file leads with.

   The class [PreservesLimit] records something visibly weaker: that the
   image APEX F L carries SOME limit structure of F ◯ K, whose legs are
   unconstrained and need not be the image legs.  The two notions are
   genuinely different.  [PreservesLimitCone_PreservesLimit] goes one way,
   and the converse is refuted by an explicit countermodel in
   Structure/Limit/Preservation/Separation.v: over the walking span
   (Instance/Roof.v), the functor sending both legs to the first projection
   of bool × bool satisfies [PreservesLimit] and provably not
   [PreservesLimitCone] — the image cone and the genuine product cone share
   an apex and differ by precomposition with the non-invertible
   [fun p => (fst p, fst p)].  The prose of Construction/Comma/Limit.v and
   its consumers asserted exactly this about apex-only preservation; it is
   now a theorem.

   CONTINUITY.  A functor is continuous when it preserves the limits of all
   diagrams of all shapes IN THE CONE SENSE: [ContinuousFunctor] below is
   [PreservesLimitCone] quantified over every shape and diagram, and that is
   what the word means in Mac Lane §V.4, Awodey §5.6 and Riehl §3.3.  The
   apex-only quantification [PreservesAllLimits] is kept, because
   Adjunction/Continuity.v and Theory/Equivalence/Limit.v export it, but it
   is a CONSEQUENCE — [Continuous_PreservesAllLimits] — and not the
   definition.  An earlier version of this header called it "continuous";
   that presentation was wrong and this paragraph is the correction.  The
   name [ContinuousFunctor] rather than [Continuous] avoids the clash with
   Instance/Top.v, exactly as [obj_eq_iso] avoids [iso_of_eq]
   (Structure/Limit/Creation.v).  [ContinuousFunctor] is also,
   definitionally, the hypothesis [PreservesImageLimit] that
   Construction/Comma/Limit.v introduced and that Adjunction/GAFT.v and
   Adjunction/SAFT.v consume; the two bridges are identity functions at
   Construction/Comma/Creation.v.

   THE CANONICAL COMPARISON MAP (Awodey §5.5).  Given a cone N over K and a
   limiting cone M over F ◯ K, the universal property of M sends the image
   cone to a unique [cone_comparison F N : F (lim K) ~> lim (F ◯ K)].
   Cone-level preservation is exactly invertibility of that map
   ([LimitCone_comparison_iso] and its converse [comparison_iso_LimitCone]),
   which pins down the sense in which apex-only preservation is weak: it
   yields SOME isomorphism F L ≅ lim (F ◯ K) ([apex_iso_of_PreservesLimit])
   and says nothing about the canonical one.

   Issue #427 asked for these under the names [PreservesConeLimit] and
   [PreservesConeColimit]; the tree's [PreservesLimitCone] and
   [PreservesColimitCocone] are those constants, with the words in the
   library's order.

   Quantification over a fixed shape and over an arbitrary class of shapes
   is here; finite shapes and the discrete (product) case are in
   Structure/Limit/Preservation/Shapes.v, which may import the named shape
   categories that this file must not.

   None of the classes below is registered for instance resolution:
   preservation witnesses are always passed explicitly. *)

(** ** Preservation of limits *)

(* The APEX-ONLY class, kept for its downstream consumers: F preserves the
   limit of G when the image of any limit apex of G underlies SOME limit of
   F ◯ G, with the legs of that limit unrelated to the image legs.  The
   cone-level [PreservesLimitCone] is the definition proper, and
   Structure/Limit/Preservation/Separation.v shows this one does not imply
   it. The apex is written [F L]: since
   [limit_cone] is a class projection whose [Limit] argument is resolved by
   typeclass inference, it cannot be applied to the term [L] directly;
   instead [F L] elaborates through the coercion chain
   [Limit >-> Cone >-> vertex_obj], so the explicit spelling of the image
   apex is [F (@vertex_obj _ _ _ (@limit_cone _ _ _ L))]. *)

Class PreservesLimit `(G : J ⟶ C) `(F : C ⟶ D) := {
  preserves_limit (L : Limit G) : IsALimit (F ◯ G) (F L)
}.

(** ** Covariant accessors for apex-pinned limits *)

(* The leg of a cone N at x, as a first-class function (the notation
   [vertex_map[N]] leaves the diagram object as a hole, so it resists
   explicit application). *)

Definition cone_leg `{F : J ⟶ C} (N : Cone F) (x : J) :
  vertex_obj[N] ~{C}~> F x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

(* The legs of a limit witness at a fixed apex c. *)

Definition limit_leg `(H : @IsALimit J C F c) (x : J) : c ~{C}~> F x :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma limit_leg_coherence `(H : @IsALimit J C F c) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ limit_leg H x ≈ limit_leg H y.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f). Qed.

(* The mediating morphism from a competing cone into the limit apex, and
   its defining properties. *)

Definition limit_med `(H : @IsALimit J C F c) (N : Cone F) :
  vertex_obj[N] ~{C}~> c :=
  unique_obj (@ump_limit _ _ _ _ H N).

Lemma limit_med_commutes `(H : @IsALimit J C F c) (N : Cone F) (x : J) :
  limit_leg H x ∘ limit_med H N ≈ cone_leg N x.
Proof. exact (unique_property (@ump_limit _ _ _ _ H N) x). Qed.

Lemma limit_med_unique `(H : @IsALimit J C F c) (N : Cone F)
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  limit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (@ump_limit _ _ _ _ H N) v Hv). Qed.

(* Two morphisms into the limit apex that agree on every leg are equal;
   useful for identifying mediators without naming [limit_med]. *)

Lemma limit_med_eq `(H : @IsALimit J C F c) (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ u ≈ cone_leg N x) →
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (limit_med H N).
  - symmetry. exact (limit_med_unique H N u Hu).
  - exact (limit_med_unique H N v Hv).
Qed.

(* A bundled limit, viewed as a limit witness pinned at its own apex. *)

Definition limit_is_alimit `(L : @Limit J C G) : IsALimit G L :=
  @Build_IsALimit _ _ G _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

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

(** ** The canonical comparison map [F (lim K) ~> lim (F ◯ K)] (Awodey §5.5) *)

Section Comparison.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context (F : C ⟶ D).

Definition cone_comparison (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) :
  F (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  unique_obj (HM (FCone F N)).

Lemma cone_comparison_commutes (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (x : J) :
  cone_leg M x ∘ cone_comparison N HM ≈ fmap[F] (cone_leg N x).
Proof. exact (unique_property (HM (FCone F N)) x). Qed.

Lemma cone_comparison_unique (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (v : F (vertex_obj[N]) ~{D}~> vertex_obj[M]) :
  (∀ x : J, cone_leg M x ∘ v ≈ fmap[F] (cone_leg N x)) →
  cone_comparison N HM ≈ v.
Proof. intro Hv. exact (uniqueness (HM (FCone F N)) v Hv). Qed.

(* Cone-level preservation IS invertibility of the comparison, both ways. *)

Definition LimitCone_comparison_iso (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (HN : IsLimitCone (FCone F N)) :
  IsIsomorphism (cone_comparison N HM) :=
  {| two_sided_inverse := from `1 (limitcone_iso HN HM);
     is_right_inverse  := iso_to_from `1 (limitcone_iso HN HM);
     is_left_inverse   := iso_from_to `1 (limitcone_iso HN HM) |}.

Definition comparison_iso_LimitCone (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (Hi : IsIsomorphism (cone_comparison N HM)) :
  IsLimitCone (FCone F N).
Proof.
  assert (ci : ConeIso (FCone F N) M).
  { exists (IsIsoToIso _ Hi).
    intro x; exact (cone_comparison_commutes N HM x). }
  exact (limitcone_transport (ConeIso_sym ci) HM).
Defined.

Definition PreservesLimitCone_of_comparison {M : Cone (F ◯ K)}
  (HM : IsLimitCone M)
  (H : ∀ N : Cone K, IsLimitCone N → IsIsomorphism (cone_comparison N HM)) :
  PreservesLimitCone K F :=
  fun N HN => comparison_iso_LimitCone N HM (H N HN).

Definition comparison_iso_of_PreservesLimitCone
  (P : PreservesLimitCone K F) {M : Cone (F ◯ K)} (HM : IsLimitCone M)
  (N : Cone K) (HN : IsLimitCone N) :
  IsIsomorphism (cone_comparison N HM) :=
  LimitCone_comparison_iso N HM (P N HN).

(* The apex-only class produces SOME isomorphism between the image apex and
   the limit apex, with no claim that it is the canonical comparison; the
   Separation development exhibits the isomorphism existing while the
   comparison is provably not invertible. *)

Definition apex_iso_of_PreservesLimit (P : PreservesLimit K F) (L : Limit K)
  {M : Cone (F ◯ K)} (HM : IsLimitCone M) :
  F (vertex_obj[L]) ≅ vertex_obj[M] :=
  `1 (limitcone_iso (isalimit_limitcone (preserves_limit L)) HM).

(* The bundled reading, for chosen limits (Awodey's F (lim D) → lim (F D)). *)

Definition limit_comparison (L : Limit K) (M : Limit (F ◯ K)) :
  F (vertex_obj[L]) ~{D}~> vertex_obj[M] :=
  cone_comparison (@limit_cone _ _ _ L) (limit_limitcone M).

End Comparison.



(** ** Repackagings across functor-composition associativity and op *)

Section ConeAssoc.

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

Definition islimitcone_assoc_inv {N : Cone (G ◯ (F ◯ K))}
  (H : IsLimitCone N) : IsLimitCone (cone_assoc_inv N) :=
  fun M => H (cone_assoc M).

End ConeAssoc.

(* Mac Lane §V.4 Exercise 1, per diagram: the image under G of an
   already-limiting image cone is limiting, so preservation composes. *)
Definition PreservesLimitCone_compose {J C D E : Category}
  {K : J ⟶ C} {F : C ⟶ D} {G : D ⟶ E}
  (PF : PreservesLimitCone K F) (PG : PreservesLimitCone (F ◯ K) G) :
  PreservesLimitCone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCone F N) (PF N HN) (cone_assoc M)).
Defined.

Section OpComp.

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

End OpComp.

(* (F ◯ G)^op and F^op ◯ G^op share their object and morphism maps but
   differ in the proofs of functoriality, so an apex-pinned limit witness
   over the one repackages field by field as a witness over the other
   (the [preserves_colimit] precedent in Structure/Limit/Preservation.v).
   No destructuring: everything is spelled with projections, so the
   result stays convertible with the input on legs and mediators. *)

Definition isalimit_op_comp {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  {c : D} (H : IsALimit ((F ◯ G)^op) c) : IsALimit (F^op ◯ G^op) c :=
  @Build_IsALimit (J^op) (D^op) (F^op ◯ G^op) c
    (@Build_ACone (J^op) (D^op) c (F^op ◯ G^op)
       (fun x => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x)
       (fun x y f =>
          @cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f))
    (fun N =>
       @ump_limit _ _ _ _ H
         (@Build_Cone (J^op) (D^op) ((F ◯ G)^op) (@vertex_obj _ _ _ N)
            (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ G)^op)
               (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
               (fun x y f =>
                  @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).


(** ** Covariant accessors for cocones and apex-pinned colimits *)

(* A cocone over F is a cone over F^op (Structure/Cone.v); its legs run
   from the diagram into the apex. [cocone_inj] re-reads those legs
   covariantly, as injections F x ~> N in C. *)

Definition cocone_inj `{F : J ⟶ C} (N : Cocone F) (x : J) :
  F x ~{C}~> vertex_obj[N] :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

Lemma cocone_inj_coherence `{F : J ⟶ C} (N : Cocone F)
  {x y : J} (f : x ~{J}~> y) :
  cocone_inj N y ∘ fmap[F] f ≈ cocone_inj N x.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f). Qed.

(* [IsAColimit F c] pins the apex of a colimit of F at c, dually to
   [IsALimit]: it is [IsALimit] for the opposite diagram, at the same
   object. The accessors below restate its legs and universal property
   covariantly, entirely in terms of C. *)

Definition IsAColimit `(F : J ⟶ C) (c : C) : Type := IsALimit (F^op) c.

(* The injections of the colimit: the legs of the underlying opposite
   cone, read in C. *)

Definition colimit_inj `(H : @IsAColimit J C F c) (x : J) : F x ~{C}~> c :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma colimit_inj_coherence `(H : @IsAColimit J C F c) {x y : J}
  (f : x ~{J}~> y) :
  colimit_inj H y ∘ fmap[F] f ≈ colimit_inj H x.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) y x f). Qed.

(* Universal property, covariantly: every cocone N over F factors through
   the colimit apex by a unique mediating morphism out of c. Transparent,
   so downstream constructions can extract the mediator. *)

Definition ump_colimit `(H : @IsAColimit J C F c) (N : Cocone F) :
  ∃! u : c ~{C}~> vertex_obj[N],
    ∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (@ump_limit _ _ _ _ H N). Defined.

Definition colimit_med `(H : @IsAColimit J C F c) (N : Cocone F) :
  c ~{C}~> vertex_obj[N] :=
  unique_obj (ump_colimit H N).

Lemma colimit_med_commutes `(H : @IsAColimit J C F c) (N : Cocone F) (x : J) :
  colimit_med H N ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (unique_property (ump_colimit H N) x). Qed.

Lemma colimit_med_unique `(H : @IsAColimit J C F c) (N : Cocone F)
  (v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  colimit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (ump_colimit H N) v Hv). Qed.

Lemma colimit_med_eq `(H : @IsAColimit J C F c) (N : Cocone F)
  (u v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x) →
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (colimit_med H N).
  - symmetry. exact (colimit_med_unique H N u Hu).
  - exact (colimit_med_unique H N v Hv).
Qed.

(* The apex of a bundled colimit, read as an object of C, and the bundled
   colimit viewed as a colimit witness pinned at that apex. *)

Definition colimit_apex `(L : @Colimit J C G) : C :=
  @vertex_obj _ _ _ (@limit_cone _ _ _ L).

Definition colimit_is_acolimit `(L : @Colimit J C G) :
  IsAColimit G (colimit_apex L) :=
  @Build_IsALimit _ _ (G^op) _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

(** ** Preservation of colimits *)

(* F preserves the colimit of G exactly when F^op preserves the limit of
   the opposite diagram G^op; this is the one-line dual definition, in the
   style of [Colimit] itself. *)

Definition PreservesColimit `(G : J ⟶ C) `(F : C ⟶ D) : Type :=
  @PreservesLimit (J^op) (C^op) (G^op) (D^op) (F^op).

(* Covariant accessor: a colimit-preservation witness sends the apex of
   any colimit of G to the apex of a colimit of F ◯ G. The functors
   (F ◯ G)^op and F^op ◯ G^op share their object and morphism maps up to
   conversion, differing only in the proofs of functoriality, so the
   witness produced by [preserves_limit] is repackaged field by field. *)

Definition preserves_colimit {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  (P : PreservesColimit G F) (L : Colimit G) :
  IsAColimit (F ◯ G) (F (colimit_apex L)).
Proof.
  destruct (@preserves_limit _ _ _ _ _ P L) as [ac um].
  unshelve refine (@Build_IsALimit _ _ ((F ◯ G)^op) _ _ _).
  - exact (@Build_ACone _ _ _ ((F ◯ G)^op)
      (fun x => @vertex_map _ _ _ _ ac x)
      (fun x y f => @cone_coherence _ _ _ _ ac x y f)).
  - intro N.
    exact (um (@Build_Cone _ _ (F^op ◯ G^op)
      (@vertex_obj _ _ _ N)
      (@Build_ACone _ _ _ (F^op ◯ G^op)
         (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
         (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).
Defined.

(** ** Continuity and cocontinuity *)

(* A functor preserving the limits of all diagrams of all shapes
   (continuous), respectively all colimits (cocontinuous). These are plain
   Definitions: preservation of a class of limits is data to be supplied,
   never inferred. *)

Definition PreservesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesLimit G F.

Definition PreservesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesColimit G F.

(** ** Continuity, cocontinuity, and quantification over shapes *)

(* Continuity is preservation of every limit of every shape in the CONE
   sense (Mac Lane §V.4); [Continuous_PreservesAllLimits] descends to the
   apex-only quantification, and the countermodel of
   Structure/Limit/Preservation/Separation.v shows the descent has no
   inverse.  These are plain Definitions: preservation of a class of limits
   is data to be supplied, never inferred. *)

Definition ContinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F.

Definition Continuous_PreservesAllLimits {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit (H J K).

(* Riehl §3.4: preservation over all diagrams of a given shape, and over an
   arbitrary class of shapes. *)

Definition PreservesLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition PreservesLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition Continuous_PreservesLimitConesOver {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ContinuousFunctor F) :
  PreservesLimitConesOver S F := fun J _ K => H J K.

Definition Continuous_OfShape {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) (J : Category) :
  PreservesLimitConesOfShape J F := H J.

(* Mac Lane §V.4 Exercise 1 at full strength. *)

Definition continuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : ContinuousFunctor F) (PG : ContinuousFunctor G) :
  ContinuousFunctor (G ◯ F) :=
  fun J K => PreservesLimitCone_compose (PF J K) (PG J (F ◯ K)).

(** ** Reflection of isomorphisms *)

(* A conservative functor: any morphism whose image under F is invertible
   is itself invertible. Stated with the two-sided-inverse predicate
   [IsIsomorphism] (Theory/Isomorphism.v). Fully faithful functors are the
   standard source of such witnesses (Phase consumers derive them there);
   none is registered here. *)

Class ReflectsIsos {C D : Category} (F : C ⟶ D) := {
  reflects_iso {x y : C} (f : x ~> y) :
    IsIsomorphism (fmap[F] f) → IsIsomorphism f
}.

(** ** The cocone-level colimit predicate, preservation, and cocontinuity *)

(* [IsColimitCocone] is [IsLimitCone] for the opposite diagram at the same
   cocone; unfolded in C it says every cocone over K receives a unique
   mediator out of N compatible with the injections. *)

Definition IsColimitCocone {J C : Category} {K : J ⟶ C} (N : Cocone K) : Type :=
  @IsLimitCone (J^op) (C^op) (K^op) N.

Definition colimitcocone_ump {J C : Category} {K : J ⟶ C} {N : Cocone K}
  (H : IsColimitCocone N) (M : Cocone K) :
  ∃! u : vertex_obj[N] ~{C}~> vertex_obj[M],
    ∀ x : J, u ∘ cocone_inj N x ≈ cocone_inj M x := H M.

Definition colimitcocone_isacolimit {J C : Category} {K : J ⟶ C}
  {N : Cocone K} (H : IsColimitCocone N) : IsAColimit K vertex_obj[N] :=
  limitcone_isalimit H.

Definition colimit_colimitcocone {J C : Category} {K : J ⟶ C}
  (L : Colimit K) : IsColimitCocone (@limit_cone _ _ _ L) :=
  @ump_limits _ _ _ L.

Section ImageCocone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

Definition fcocone_inj (N : Cocone K) (x : J) :
  (F ◯ K) x ~{D}~> F (vertex_obj[N]) := fmap[F] (cocone_inj N x).

Lemma fcocone_coherence (N : Cocone K) {x y : J} (f : x ~{J}~> y) :
  fcocone_inj N y ∘ fmap[F ◯ K] f ≈ fcocone_inj N x.
Proof.
  unfold fcocone_inj; simpl.
  rewrite <- fmap_comp.
  now rewrite (cocone_inj_coherence N f).
Qed.

Definition FCocone (N : Cocone K) : Cocone (F ◯ K).
Proof.
  unshelve refine (@Build_Cone (J^op) (D^op) ((F ◯ K)^op)
                     (F (vertex_obj[N])) _).
  unshelve refine (@Build_ACone (J^op) (D^op) (F (vertex_obj[N]))
                     ((F ◯ K)^op) (fcocone_inj N) _).
  intros x y f; exact (fcocone_coherence N f).
Defined.

Lemma FCocone_inj (N : Cocone K) (x : J) :
  cocone_inj (FCocone N) x ≈ fmap[F] (cocone_inj N x).
Proof. reflexivity. Qed.

Definition cocone_comparison (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) :
  vertex_obj[M] ~{D}~> F (vertex_obj[N]) :=
  unique_obj (HM (FCocone N)).

End ImageCocone.

Definition PreservesColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone N → IsColimitCocone (FCocone F N).

Definition ReflectsColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone (FCocone F N) → IsColimitCocone N.

Definition PreservesColimitCocone_PreservesColimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesColimitCocone K F) :
  PreservesColimit K F.
Proof.
  constructor.
  intro L.
  exact (isalimit_op_comp
           (limitcone_isalimit
              (P (@limit_cone _ _ _ L) (limit_limitcone L)))).
Defined.

Section CoCompose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

Definition cocone_assoc (N : Cocone ((G ◯ F) ◯ K)) : Cocone (G ◯ (F ◯ K)) :=
  @Build_Cone (J^op) (E^op) ((G ◯ (F ◯ K))^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (E^op) (@vertex_obj _ _ _ N) ((G ◯ (F ◯ K))^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition PreservesColimitCocone_compose
  (PF : PreservesColimitCocone K F) (PG : PreservesColimitCocone (F ◯ K) G) :
  PreservesColimitCocone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCocone F N) (PF N HN) (cocone_assoc M)).
Defined.

End CoCompose.

Definition CocontinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesColimitCocone K F.

Definition Cocontinuous_PreservesAllColimits {C D : Category} {F : C ⟶ D}
  (H : CocontinuousFunctor F) : PreservesAllColimits F :=
  fun J K => PreservesColimitCocone_PreservesColimit (H J K).

Definition PreservesColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesColimitCocone K F.

Definition cocontinuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : CocontinuousFunctor F) (PG : CocontinuousFunctor G) :
  CocontinuousFunctor (G ◯ F) :=
  fun J K => PreservesColimitCocone_compose (PF J K) (PG J (F ◯ K)).

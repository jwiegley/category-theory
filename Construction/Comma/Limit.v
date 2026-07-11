Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.One.

Set Universe Polymorphism.

Generalizable All Variables.

(** * Creation of limits in a comma category [=(d) ↓ U] *)

(* nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits
   nLab: https://ncatlab.org/nlab/show/created+limit

   Fix a functor [U : C ⟶ D] and an object [d : D].  The comma category
   [=(d) ↓ U] (built with the constant functor [=(d) : 1 ⟶ D] of
   [Functor/Diagonal.v] on the left) has as objects the pairs [(c, h)] of an
   object [c : C] and a morphism [h : d ~> U c], encoded as the dependent pair
   [(( _ , c ); h)] with the first component the point of the terminal category
   [1]; and as morphisms [(c, h) ~> (c', h')] the [g : c ~> c'] with the
   commuting triangle [h' ≈ U g ∘ h] (the constant functor sends every arrow to
   [id[d]], so the general comma square [h' ∘ =(d) f ≈ U g ∘ h] collapses to
   that triangle — this is [comma_square] below).

   Standard fact: if [C] has and [U] preserves [J]-limits, then [=(d) ↓ U] has
   [J]-limits, and the projection [comma_proj2 : =(d) ↓ U ⟶ C] creates them.
   Concretely, given a diagram [K : J ⟶ (=(d) ↓ U)]:

     - its [C]-projection [G := comma_proj2 ◯ K] has a limit [L] in [C];
     - the family [h_j := `2 (K j) : d ~> U (G j)] is a cone over [U ◯ G] with
       apex [d] (the coherence is exactly the collapsed comma square of [K f]);
     - preservation makes the image cone [(U L, fmap[U] π_•)] a limit of
       [U ◯ G], so that cone mediates the [(d, h_•)] cone by a unique
       [φ : d ~> U L];
     - the pair [(L, φ)] with the projected legs [(c := π_j)] is the limit of
       [K] in [=(d) ↓ U]; its universal property is the [C]-universal property
       of [L] on the base component together with the mediating uniqueness of
       the image cone on the [d]-component.

   STATUS / hypothesis form.  The mathematically correct meaning of "U
   preserves the limit of G" is that U carries the *limit cone* to a *limit
   cone* — equivalently, the image cone [(U L, fmap[U] π_•)] is universal.  This
   is precisely what [Adjunction/Continuity.v] establishes for right adjoints:
   its [rapl_is_alimit] is built from [rapl_acone], whose legs
   [rapl_leg x = fmap[U] (limit_leg (limit_is_alimit L) x)] are the image legs.

   The bare class [PreservesLimit] of [Structure/Limit/Preservation.v] records
   only that the *apex object* [U L] carries *some* limit structure of [U ◯ G]
   ([IsALimit (U ◯ G) (U L)]); the legs of that structure are left
   unconstrained and need not be the image legs [fmap[U] π_•].  Two distinct
   cone structures on the same apex can differ by precomposition with a
   non-invertible endomorphism, only one of them being a limit, so apex-only
   preservation does not by itself make the image cone universal — and it is the
   image cone whose universal property is needed to lift both the existence of
   [φ] and the uniqueness of the comma mediator.  We therefore take as the
   preservation hypothesis the honest, cone-level statement [PreservesImageLimit]
   below (the image cone is universal), which is exactly the universal property
   [rapl_ump] delivers.  This is a strengthening to the correct notion of
   preservation, never a weakening of the conclusion [Comma_Complete]. *)

Section CommaLimit.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.

(** ** The collapsed comma square *)

(* Every morphism of [=(d) ↓ U] has domain-side leg [=(d) f = id[d]], so its
   commuting square is just [`2 Y ≈ fmap[U] (snd `1 m) ∘ `2 X]. *)
Lemma comma_square {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  `2 Y ≈ fmap[U] (snd (`1 m)) ∘ `2 X.
Proof.
  transitivity (`2 Y ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 m).
Qed.

(** ** The image cone and the honest preservation hypothesis *)

(* The legs of the image cone: [fmap[U]] applied to the legs of a [C]-limit L
   of G.  The codomain [U (G x)] is convertible with [(U ◯ G) x]. *)
Definition image_leg {J : Category} {G : J ⟶ C} (L : Limit G) (x : J) :
  U L ~{D}~> (U ◯ G) x :=
  fmap[U] (limit_leg (limit_is_alimit L) x).

Lemma image_coherence {J : Category} {G : J ⟶ C} (L : Limit G)
  {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[G] f) ∘ image_leg L x ≈ image_leg L y.
Proof.
  unfold image_leg.
  rewrite <- fmap_comp.
  now rewrite (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition image_acone {J : Category} {G : J ⟶ C} (L : Limit G) :
  ACone (U L) (U ◯ G) :=
  @Build_ACone J D (U L) (U ◯ G) (image_leg L) (@image_coherence J G L).

(* U preserves limits, cone-faithfully: for every diagram the image cone above
   is a limit of [U ◯ G].  (See the STATUS header for why this — rather than the
   apex-only [PreservesAllLimits] — is the operative hypothesis.) *)
Definition PreservesImageLimit : Type :=
  ∀ (J : Category) (G : J ⟶ C) (L : Limit G) (N : Cone (U ◯ G)),
    ∃! φ : vertex_obj[N] ~{D}~> U L,
      ∀ x : J, image_leg L x ∘ φ ≈ cone_leg N x.

(* Packaged apex-pinned limit whose legs are the image legs. *)
Definition image_is_alimit (HU : PreservesImageLimit)
  {J : Category} {G : J ⟶ C} (L : Limit G) : IsALimit (U ◯ G) (U L) :=
  @Build_IsALimit J D (U ◯ G) (U L) (image_acone L) (HU J G L).

(** ** Creation of the limit of one diagram *)

Section Create.

Context (HC : @Complete C).
Context (HU : PreservesImageLimit).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* The base diagram in C and its limit. *)
Definition Gdiag : J ⟶ C := comma_proj2 ◯ K.
Definition Ldiag : Limit Gdiag := HC J Gdiag.

(* The cone over [U ◯ Gdiag] with apex [d] built from the [d]-legs of K. *)
Definition base_leg (j : J) : d ~{D}~> (U ◯ Gdiag) j := `2 (K j).

Lemma base_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[Gdiag] f) ∘ base_leg x ≈ base_leg y.
Proof.
  unfold base_leg.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition base_cone : Cone (U ◯ Gdiag) :=
  @Build_Cone J D (U ◯ Gdiag) d
    (@Build_ACone J D d (U ◯ Gdiag) base_leg (@base_coherence)).

(* The mediating morphism into the preserved (image) limit. *)
Definition phi : d ~{D}~> U Ldiag :=
  limit_med (image_is_alimit HU Ldiag) base_cone.

Lemma phi_commutes (j : J) :
  fmap[U] (limit_leg (limit_is_alimit Ldiag) j) ∘ phi ≈ `2 (K j).
Proof. exact (limit_med_commutes (image_is_alimit HU Ldiag) base_cone j). Qed.

(* The apex object of the comma limit: [(Ldiag, φ)]. *)
Definition apex_obj : (=(d) ↓ U) := ((ttt, vertex_obj[Ldiag]); phi).

(* The legs of the comma limit cone: the projected [C]-legs [π_j], upgraded to
   comma morphisms by the triangle [`2 (K j) ≈ fmap[U] π_j ∘ φ]. *)
Definition apex_leg (j : J) : apex_obj ~{=(d) ↓ U}~> K j.
Proof.
  unshelve refine ((ttt, limit_leg (limit_is_alimit Ldiag) j); _).
  change (`2 (K j) ∘ id[d]
          ≈ fmap[U] (limit_leg (limit_is_alimit Ldiag) j) ∘ phi).
  rewrite id_right.
  symmetry.
  exact (phi_commutes j).
Defined.

Lemma apex_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ apex_leg x ≈ apex_leg y.
Proof.
  split.
  - reflexivity.
  - exact (limit_leg_coherence (limit_is_alimit Ldiag) f).
Qed.

Definition apex_cone : Cone K :=
  @Build_Cone J (=(d) ↓ U) K apex_obj
    (@Build_ACone J (=(d) ↓ U) apex_obj K apex_leg (@apex_coherence)).

(** *** Universal property *)

(* From a competing comma cone N, its [C]-projection is a cone over Gdiag. *)
Definition qleg (N : Cone K) (j : J) :
  snd (`1 vertex_obj[N]) ~{C}~> Gdiag j :=
  snd (`1 (cone_leg N j)).

Lemma qcoherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[Gdiag] f ∘ qleg N x ≈ qleg N y.
Proof. exact (snd (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)). Qed.

Definition qcone (N : Cone K) : Cone Gdiag :=
  @Build_Cone J C Gdiag (snd (`1 vertex_obj[N]))
    (@Build_ACone J C (snd (`1 vertex_obj[N])) Gdiag (qleg N) (@qcoherence N)).

(* The mediating morphism in C. *)
Definition wmed (N : Cone K) : snd (`1 vertex_obj[N]) ~{C}~> Ldiag :=
  limit_med (limit_is_alimit Ldiag) (qcone N).

(* The comma mediator: [wmed N] upgraded to a comma morphism. *)
Definition umed (N : Cone K) : vertex_obj[N] ~{=(d) ↓ U}~> apex_obj.
Proof.
  unshelve refine ((ttt, wmed N); _).
  change (phi ∘ id[d] ≈ fmap[U] (wmed N) ∘ `2 vertex_obj[N]).
  rewrite id_right.
  apply (limit_med_eq (image_is_alimit HU Ldiag) base_cone).
  - exact (limit_med_commutes (image_is_alimit HU Ldiag) base_cone).
  - intro j.
    change (fmap[U] (limit_leg (limit_is_alimit Ldiag) j)
              ∘ (fmap[U] (wmed N) ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
    unfold wmed.
    rewrite comp_assoc, <- fmap_comp.
    rewrite (limit_med_commutes (limit_is_alimit Ldiag) (qcone N) j).
    symmetry.
    exact (comma_square (cone_leg N j)).
Defined.

Definition comma_ump (N : Cone K) :
  ∃! u : vertex_obj[N] ~{=(d) ↓ U}~> apex_obj,
    ∀ j : J, apex_leg j ∘ u ≈ cone_leg N j.
Proof.
  unshelve refine {| unique_obj := umed N |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (limit_med_commutes (limit_is_alimit Ldiag) (qcone N) j).
  - intros v Hv; split.
    + now destruct (fst (`1 v)).
    + unfold wmed.
      apply (limit_med_unique (limit_is_alimit Ldiag) (qcone N)).
      intro j.
      exact (snd (Hv j)).
Defined.

Definition comma_limit : Limit K :=
  @Build_Limit J (=(d) ↓ U) K apex_cone comma_ump.

End Create.

(** ** Completeness of the comma category *)

Definition Comma_Complete
  (HU : PreservesImageLimit) (HC : @Complete C) :
  @Complete (=(d) ↓ U) :=
  fun J K => comma_limit HC HU K.

End CommaLimit.

(** ** The preservation hypothesis is inhabited by right adjoints *)

Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Continuity.

(* Every right adjoint satisfies [PreservesImageLimit]: for an adjunction
   [A : F ⊣ U], RAPL exhibits the image cone over [U L] as universal, and its
   legs [rapl_leg x = fmap[U] (limit_leg (limit_is_alimit L) x)] are exactly the
   image legs [image_leg L x], so [rapl_ump] has, up to conversion, the type
   demanded by [PreservesImageLimit].  This ties the honest cone-level
   hypothesis to the preservation vocabulary of [Structure/Limit/Preservation.v]
   and [Adjunction/Continuity.v]. *)
Definition right_adjoint_PreservesImageLimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  @PreservesImageLimit C D U.
Proof. intros J G L N. exact (rapl_ump A G L N). Defined.

(* Capstone: the comma category [=(d) ↓ U] over a right adjoint [U] into a
   complete category [C] is complete. *)
Definition Comma_Complete_right_adjoint
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (HC : @Complete C) : @Complete (=(d) ↓ U) :=
  Comma_Complete (right_adjoint_PreservesImageLimit A) HC.

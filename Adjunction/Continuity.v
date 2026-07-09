Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Adjoint (co)continuity: RAPL and LAPC *)

(* nLab: https://ncatlab.org/nlab/show/adjoints+preserve+(co-)limits
   Wikipedia:
   https://en.wikipedia.org/wiki/Adjoint_functors#Preservation_of_limits

   "The most important property of adjoints is their continuity: every
    functor that has a left adjoint (and therefore is a right adjoint) is
    continuous (i.e. commutes with limits in the category theoretical
    sense); every functor that has a right adjoint (and therefore is a
    left adjoint) is cocontinuous (i.e. commutes with colimits)."
                                                             -- Wikipedia

   This file proves both statements for the hom-setoid adjunctions of
   [Theory/Adjunction.v], packaged in the preservation vocabulary of
   [Structure/Limit/Preservation.v].

   Fix an adjunction A : F ⊣ U, with F : D ⟶ C the left adjoint and
   U : C ⟶ D the right adjoint, and write ⌊-⌋ : (F x ~> y) → (x ~> U y)
   for the forward transpose and ⌈-⌉ for its inverse. Given a limit L of
   a diagram G : J ⟶ C, the object U L is exhibited directly as a limit
   of U ◯ G ([rapl_is_alimit]):

   - the legs of the image cone are fmap[U] applied to the legs of L
     ([rapl_acone]);
   - a competing cone N over U ◯ G transposes leg by leg along ⌈-⌉ into
     a cone over G whose apex is F applied to the vertex of N, the leg
     coherence being [from_adj_nat_r] combined with the coherence of N
     ([rapl_transposed_cone]);
   - the mediating morphism supplied by L in C transposes back along ⌊-⌋
     to the mediating morphism in D ([rapl_med]), which commutes with
     the image legs by [to_adj_nat_r] ([rapl_med_commutes]);
   - a competitor v that also commutes with the image legs transposes
     along ⌈-⌉ to a mediator for the transposed cone, so ⌈v⌉ agrees with
     the C-side mediator by L's universal property, and v with
     [rapl_med] because the two transposes are mutually inverse up to ≈
     ([rapl_med_unique]).

   Continuity of the right adjoint is then packaged as
   [right_adjoint_preserves_limits] : [PreservesAllLimits] U, with the
   per-diagram form [right_adjoint_preserves_limit] and a bundled
   [Limit (U ◯ G)] witness [rapl_limit]. The dual results
   [left_adjoint_preserves_colimit] / [left_adjoint_preserves_colimits]
   ride [Adjunction/Opposite.v]: the opposite adjunction U^op ⊣ F^op
   makes F^op a right adjoint between the opposite categories, and
   [PreservesColimit] is by definition [PreservesLimit] of the opposite
   diagram for the opposite functor, so LAPC is RAPL read backwards.

   Nothing below is registered for instance resolution; preservation
   witnesses are always passed explicitly, following the convention of
   [Structure/Limit/Preservation.v]. *)

Section RAPL.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Notation "⌊ f ⌋" := (to (@adj _ _ _ _ A _ _) f).
Notation "⌈ f ⌉" := (from (@adj _ _ _ _ A _ _) f).

Section Diagram.

Context {J : Category}.
Context (G : J ⟶ C).
Context (L : Limit G).

(** ** The image cone over [U L] *)

(* The legs of the image cone: U applied to the legs of the limit cone.
   The codomain [U (G x)] is convertible with [(U ◯ G) x], so the family
   assembles into an [ACone] over the composite diagram below. *)

Definition rapl_leg (x : J) : U L ~{D}~> U (G x) :=
  fmap[U] (limit_leg (limit_is_alimit L) x).

Lemma rapl_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[G] f) ∘ rapl_leg x ≈ rapl_leg y.
Proof using G L U.
  unfold rapl_leg.
  rewrite <- fmap_comp.
  now rewrite (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition rapl_acone : ACone (U L) (U ◯ G) :=
  @Build_ACone J D (U L) (U ◯ G) rapl_leg (@rapl_leg_coherence).

(** ** Transposing a competing cone across the adjunction *)

(* A cone N over U ◯ G with vertex n has legs n ~> U (G x); the inverse
   transpose ⌈-⌉ turns them into legs F n ~> G x, i.e. into a cone over
   G with apex F n, ready to be mediated by the limit L in C. *)

Definition rapl_transposed_leg (N : Cone (U ◯ G)) (x : J) :
  F (vertex_obj[N]) ~{C}~> G x := ⌈ cone_leg N x ⌉.

Lemma rapl_transposed_coherence (N : Cone (U ◯ G)) {x y : J}
  (f : x ~{J}~> y) :
  fmap[G] f ∘ rapl_transposed_leg N x ≈ rapl_transposed_leg N y.
Proof using A G.
  unfold rapl_transposed_leg.
  etransitivity.
  - symmetry.
    apply (@from_adj_nat_r C D F U A _ _ _ (fmap[G] f) (cone_leg N x)).
  - apply from_adj_respects.
    exact (@cone_coherence J D _ (U ◯ G) (@coneFrom _ _ _ N) x y f).
Qed.

Definition rapl_transposed_cone (N : Cone (U ◯ G)) : Cone G :=
  @Build_Cone J C G (F (vertex_obj[N]))
    (@Build_ACone J C (F (vertex_obj[N])) G
       (rapl_transposed_leg N) (@rapl_transposed_coherence N)).

(** ** The mediating morphism and the universal property *)

(* Mediate the transposed cone through L in C, then transpose the
   resulting morphism back along ⌊-⌋ to land in D. *)

Definition rapl_med (N : Cone (U ◯ G)) : vertex_obj[N] ~{D}~> U L :=
  ⌊ limit_med (limit_is_alimit L) (rapl_transposed_cone N) ⌋.

Lemma rapl_med_commutes (N : Cone (U ◯ G)) :
  ∀ x : J, rapl_leg x ∘ rapl_med N ≈ cone_leg N x.
Proof using A G L.
  intro x.
  unfold rapl_med, rapl_leg.
  etransitivity.
  - symmetry.
    apply (@to_adj_nat_r C D F U A _ _ _
             (limit_leg (limit_is_alimit L) x)
             (limit_med (limit_is_alimit L) (rapl_transposed_cone N))).
  - etransitivity.
    + apply to_adj_respects.
      apply (limit_med_commutes (limit_is_alimit L)
               (rapl_transposed_cone N) x).
    + apply from_adj_comp_law.
Qed.

Lemma rapl_med_unique (N : Cone (U ◯ G)) :
  ∀ v : vertex_obj[N] ~{D}~> U L,
    (∀ x : J, rapl_leg x ∘ v ≈ cone_leg N x) → rapl_med N ≈ v.
Proof using A G L.
  intros v Hv.
  unfold rapl_med.
  etransitivity.
  - apply to_adj_respects.
    apply (limit_med_unique (limit_is_alimit L) (rapl_transposed_cone N)
             ⌈ v ⌉).
    intro x.
    etransitivity.
    + symmetry.
      apply (@from_adj_nat_r C D F U A _ _ _
               (limit_leg (limit_is_alimit L) x) v).
    + apply from_adj_respects.
      exact (Hv x).
  - apply from_adj_comp_law.
Qed.

Definition rapl_ump (N : Cone (U ◯ G)) :
  ∃! u : vertex_obj[N] ~{D}~> U L,
    ∀ x : J, rapl_leg x ∘ u ≈ cone_leg N x :=
  Build_Unique _ _ _ (rapl_med N) (rapl_med_commutes N) (rapl_med_unique N).

(* RAPL for one diagram, apex-pinned: U L underlies a limit of U ◯ G. *)

Definition rapl_is_alimit : IsALimit (U ◯ G) (U L) :=
  @Build_IsALimit J D (U ◯ G) (U L) rapl_acone rapl_ump.

(* The bundled form of the same witness. *)

Definition rapl_cone : Cone (U ◯ G) :=
  @Build_Cone J D (U ◯ G) (U L) rapl_acone.

Definition rapl_limit : Limit (U ◯ G) :=
  @Build_Limit J D (U ◯ G) rapl_cone rapl_ump.

End Diagram.

(** ** Right adjoints preserve limits *)

Definition right_adjoint_preserves_limit {J : Category} (G : J ⟶ C) :
  PreservesLimit G U :=
  @Build_PreservesLimit J C G D U (rapl_is_alimit G).

Definition right_adjoint_preserves_limits : PreservesAllLimits U :=
  fun J G => right_adjoint_preserves_limit G.

End RAPL.

(** ** Left adjoints preserve colimits *)

(* By duality: [Opposite_Adjunction] turns A : F ⊣ U into U^op ⊣ F^op, in
   which F^op is the right adjoint, and [PreservesColimit G F] is by
   definition [PreservesLimit G^op F^op], so it is an instance of RAPL for
   the opposite adjunction at the opposite diagram. The explicit constants
   [Opposite] / [Opposite_Functor] / [Opposite_Adjunction] are used instead
   of the three ^op notations, which would otherwise compete for the same
   syntax across scopes. *)

Definition left_adjoint_preserves_colimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  {J : Category} (G : J ⟶ D) : PreservesColimit G F :=
  right_adjoint_preserves_limits (Opposite_Adjunction F U A)
    (Opposite J) (Opposite_Functor G).

Definition left_adjoint_preserves_colimits
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesAllColimits F :=
  fun J G => left_adjoint_preserves_colimit A G.

(* Covariant accessor: the image of a colimit apex under the left adjoint,
   pinned as a colimit of the composite diagram via the covariant reading
   [preserves_colimit] of [Structure/Limit/Preservation.v]. *)

Definition lapc_is_acolimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  {J : Category} {G : J ⟶ D} (L : Colimit G) :
  IsAColimit (F ◯ G) (F (colimit_apex L)) :=
  preserves_colimit (left_adjoint_preserves_colimit A G) L.

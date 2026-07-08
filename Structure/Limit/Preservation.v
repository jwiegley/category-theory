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
   Wikipedia:
   https://en.wikipedia.org/wiki/Limit_(category_theory)#Preservation_of_limits

   A functor F : C ⟶ D preserves the limit of a diagram G : J ⟶ C when it
   sends the apex of any limit of G to the apex of a limit of the composite
   diagram F ◯ G : J ⟶ D. A functor preserving the limits of all diagrams
   of all shapes is called continuous; dually for colimits and
   cocontinuity. The companion notion [ReflectsIsos] (a conservative
   functor) is stated with the predicate [IsIsomorphism] from
   [Theory/Isomorphism.v].

   This file provides the reusable preservation vocabulary consumed by the
   adjoint (co)continuity results of [Adjunction/Continuity.v] (right
   adjoints preserve limits; left adjoints preserve colimits) and by the
   equivalence-transport results of [Theory/Equivalence/Limit.v], together
   with covariant accessors for the dual (colimit) notions, following the
   ergonomic-accessor pattern of [Structure/Pushout.v].

   None of the classes below is registered for instance resolution:
   preservation witnesses are always passed explicitly. *)

(** ** Preservation of limits *)

(* F preserves the limit of the diagram G when the image of any limit apex
   of G underlies a limit of F ◯ G. The apex is written [F L]: since
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

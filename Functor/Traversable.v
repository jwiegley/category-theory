Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Applicative.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Natural.Transformation.Monoidal.
Require Import Category.Natural.Transformation.Applicative.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Applicative.

Generalizable All Variables.

Section Traversable.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

#[local] Obligation Tactic := idtac.

Program Instance Id_Applicative : @Applicative C _ (Id[C]) := {
  applicative_is_strong := Id_StrongFunctor;
  applicative_is_lax_monoidal := Id_LaxMonoidalFunctor
}.

Program Instance Compose_Applicative
  `{@Applicative C _ G}
  `{@Applicative C _ K} :
  @Applicative C _ (Compose G K) := {
  applicative_is_strong := Compose_StrongFunctor G K _ _;
  applicative_is_lax_monoidal := Compose_LaxMonoidalFunctor _ _
}.

Class Traversable := {
  sequence {G : C ⟶ C} `{@Applicative C _ G} : F ◯ G ⟹ G ◯ F;

  sequence_naturality {G : C ⟶ C} `{@Applicative C _ G}
                      {H : C ⟶ C} `{@Applicative C _ H} (N : G ⟹ H)
                      (f : @Applicative_Transform C _ _ _ _ _ N) {X} :
    transform[N] (F X) ∘ transform[@sequence G _] X
      ≈ transform[@sequence H _] X ∘ fmap[F] (transform[N] _);

  sequence_Id {X} : transform[@sequence Id _] X ≈ id;
  sequence_Compose {G : C ⟶ C} `{@Applicative C _ G}
                   {H : C ⟶ C} `{@Applicative C _ H} {X} :
    transform[@sequence (Compose G H) _] X
      ≈ fmap[G] (transform[sequence] X) ∘ transform[sequence] _
}.

End Traversable.

Arguments Traversable {_ _} F.

#[export]
Program Instance Id_Traversable `{@ClosedMonoidal C} (x : C) :
  Traversable (@Id C) := {
  sequence := fun _ _ => {| transform := fun _ => id |}
}.

Require Import Category.Functor.Diagonal.

#[export]
Program Instance Diagonal_Traversable
  {C J : Category} `{@ClosedMonoidal C} (x : C) :
  Traversable (Diagonal C x) := {
  sequence := fun G _ => {| transform := fun _ => pure[G] |}
}.
Next Obligation.
  unfold pure.
  simpl; normal.
  rewrite <- !comp_assoc.
  normal.
  rewrite <- naturality.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite (lax_pure_transform[N]).
  rewrite <- strength_transform; simpl.
  rewrite <- !comp_assoc; cat.
  apply compose_respects; [reflexivity|].
  now rewrite bimap_comp_id_left.
Qed.
Next Obligation.
  unfold pure, bimap; simpl; cat.
  apply iso_to_from.
Qed.
Next Obligation.
  unfold pure; simpl.
  normal.
  rewrite <- !comp_assoc.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc; cat.
  rewrite iso_from_to, id_right.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  spose (@strength_natural _ _ G _ x _ id _ _ lax_pure) as X0.
  rewrite bimap_id_id in X0.
  rewrite fmap_id in X0.
  rewrite id_right in X0.
  rewrite X0.
  cat.
Qed.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Natural.Transformation.Monoidal.
Require Import Category.Natural.Transformation.Applicative.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Applicative.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Traversable.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context `{@Closed C _}.
Context {F : C ⟶ C}.

#[local] Obligation Tactic := idtac.

Program Instance Id_Applicative : @Applicative C _ _ _ (Id[C]) := {
  applicative_is_strong := Id_StrongFunctor;
  applicative_is_lax_monoidal :=
      @Id_LaxMonoidalFunctor C InternalProduct_Monoidal
                             C InternalProduct_Monoidal
}.

Program Instance Compose_Applicative
        {G : C ⟶ C} `{@Applicative C _ _ _ G}
        {H : C ⟶ C} `{@Applicative C _ _ _ H} :
  @Applicative C _ _ _ (Compose G H) := {
  applicative_is_strong := Compose_StrongFunctor G H _ _;
  applicative_is_lax_monoidal :=
    (* Order of arguments here is reversed *)
    @Compose_LaxMonoidalFunctor C InternalProduct_Monoidal
                                C InternalProduct_Monoidal H
                                C InternalProduct_Monoidal G _ _
}.

Class Traversable := {
  sequence {G : C ⟶ C} `{@Applicative C _ _ _ G} : F ◯ G ⟹ G ◯ F;

  sequence_naturality {G : C ⟶ C} `{@Applicative C _ _ _ G}
                      {H : C ⟶ C} `{@Applicative C _ _ _ H} (N : G ⟹ H)
                      (f : @Applicative_Transform C _ _ _ _ _ _ _ N) {X} :
    transform[N] (F X) ∘ transform[@sequence G _] X
      ≈ transform[@sequence H _] X ∘ fmap[F] (transform[N] _);

  sequence_Id {X} : transform[@sequence Id _] X ≈ id;
  sequence_Compose {G : C ⟶ C} `{@Applicative C _ _ _ G}
                   {H : C ⟶ C} `{@Applicative C _ _ _ H} {X} :
    transform[@sequence (Compose G H) _] X
      ≈ fmap[G] (transform[sequence] X) ∘ transform[sequence] _
}.

End Traversable.

Arguments Traversable {_ _ _ _} F.

#[export]
Program Instance Id_Traversable {C : Category}
        `{@Cartesian C} `{@Terminal C} `{@Closed C _} (x : C) :
  Traversable (@Id C) := {
  sequence := fun _ _ => {| transform := fun _ => id |}
}.

Require Import Category.Functor.Diagonal.

#[export]
Program Instance Diagonal_Traversable {C J : Category}
        `{@Cartesian C} `{@Terminal C} `{@Closed C _} (x : C) :
  Traversable (Diagonal C x) := {
  sequence := fun G _ => {| transform := fun _ => pure[G] |}
}.
Next Obligation.
  unfold pure.
  simpl; normal.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  normal.
  rewrite <- naturality.
  rewrite !fork_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite lax_pure_transform.
  rewrite <- strength_transform; simpl.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation.
  unfold pure, bimap; simpl; cat.
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
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite (comp_assoc exr).
  rewrite exr_fork.
  rewrite one_comp.
  normal.
  pose proof (@strength_natural C InternalProduct_Monoidal G _).
  simpl in X0.
  specialize
    (X0 x x id 1 (H3 I)
        (@lax_pure C C InternalProduct_Monoidal
                   InternalProduct_Monoidal H3 _ ∘ (@one C H0 1))).
  normal.
  rewrite <- !fork_comp in X0.
  rewrite !fork_exl_exr in X0.
  normal.
  rewrite <- (@one_comp _ _ _ _ exr).
  normal.
  rewrites.
  rewrite <- !comp_assoc.
  simpl.
  rewrite (@one_unique _ _ _ _ id).
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

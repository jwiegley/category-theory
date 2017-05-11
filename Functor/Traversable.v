Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Structure.Monoidal.
Require Export Category.Functor.Structure.Monoidal.Id.
Require Export Category.Functor.Structure.Monoidal.Compose.
Require Export Category.Functor.Product.
Require Export Category.Functor.Product.Internal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(* jww (2017-05-09): TODO: Preserve all aspects of the strong lax monoidal
   functor. *)
Class StrongLaxMonoidalTransformation
      `{C : Category} `{@Monoidal C}
      (F : C ⟶ C) `{@StrongFunctor _ _ F} `{@LaxMonoidalFunctor _ _ _ _ F}
      (G : C ⟶ C) `{@StrongFunctor _ _ G} `{@LaxMonoidalFunctor _ _ _ _ G}
  := {
  slm_transform : F ⟹ G
}.

Section Traversable.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.

Class Traversable := {
  sequence `{G : C ⟶ C}
           `{@StrongFunctor C _ G}
           `{@LaxMonoidalFunctor C C _ _ G} : F ○ G ⟹ G ○ F;

  sequence_naturality
    `{G : C ⟶ C}
    `{@StrongFunctor C _ G}
    `{@LaxMonoidalFunctor C C _ _ G}
    `{H : C ⟶ C}
    `{@StrongFunctor C _ H}
    `{@LaxMonoidalFunctor C C _ _ H}
    (f : StrongLaxMonoidalTransformation G H) {X} :
    transform[@slm_transform _ _ _ _ _ _ _ _ f] (F X)
      ∘ transform[@sequence G _ _] X
      ≈ transform[@sequence H _ _] X
          ∘ fmap[F] (transform[@slm_transform _ _ _ _ _ _ _ _ f] X);

  sequence_Id {X} : transform[@sequence Id _ _] X ≈ id;
  sequence_Compose
    `{G : C ⟶ C} `{@StrongFunctor C _ G} `{@LaxMonoidalFunctor C C _ _ G}
    `{H : C ⟶ C} `{@StrongFunctor C _ H} `{@LaxMonoidalFunctor C C _ _ H} {X} :
    transform[@sequence (Compose G H) _ _] X
      ≈ fmap[G] (transform[sequence] X) ∘ transform[sequence] _
}.

End Traversable.

Arguments Traversable {_ _} F.

Program Instance Id_Traversable `{C : Category} `{@Monoidal C} (x : C) :
  Traversable (@Id C) := {
  sequence := fun _ _ _ => {| transform := fun _ => id |}
}.

(*
Require Import Category.Functor.Constant.

Program Instance Constant_Traversable `{C : Category} `{@Monoidal C} (x : C) :
  Traversable (@Constant C C x) := {
  sequence := fun G _ _ => {| transform := fun _ => pure[G] |}
}.
Next Obligation.
  unfold pure, bimap; simpl; cat.
  rewrite iso_to_from; reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  unfold pure; simpl.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite iso_from_to.
  rewrite id_right.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  unfold bimap; simpl.
  repeat (unfold strength; simpl).
  pose proof (@naturality _ _ _ _ (@strength_nat C _ G H0)
                          (x, I) (x, _) (id[x], lax_pure)).
  simpl in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (transform (@strength_nat C H G H0) (x, H2 (@I C H)))).
  rewrite <- X0.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)
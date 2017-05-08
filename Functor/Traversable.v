Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Monoidal.
Require Export Category.Functor.Product.
Require Export Category.Functor.Product.Internal.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Traversable.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.

Class Traversable := {
  sequence `{G : C ⟶ C}
           `{@StrongFunctor C _ G}
           `{@LaxMonoidalFunctor C C _ _ G} : F ○ G ⟹ G ○ F;

  sequence_id {X} : transform[@sequence Id _ _] X ≈ id;
  sequence_comp
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
  pose proof (@natural_transformation _ _ _ _ (@strength_nat C _ G H0)
                                      (x, I) (x, _) (id[x], lax_pure)).
  simpl in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((@strength_nat C H G H0) (x, H2 (@I C H)))).
  rewrite <- X0.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

Local Obligation Tactic := idtac; simpl; intros.

(*
Program Instance Product_Traversable
        `{C : Category} `{@Cartesian C} `{@Monoidal C}
        `{F : C ⟶ C} `{@Traversable _ _ F}
        `{@StrongFunctor C _ F} `{@LaxMonoidalFunctor C C _ _ F}
        `{G : C ⟶ C} `{@Traversable _ _ G}
        `{@StrongFunctor C _ G} `{@LaxMonoidalFunctor C C _ _ G} :
  Traversable (F ∏⟶ G) := {
  sequence := fun H _ _ => {| transform := fun X =>
    (* ((F × G) ○ H) X ~{ C ∏ C }~> (H ○ (F × G)) X *) _ |}
}.
Next Obligation.
  assert (((F ∏⟶ G) ○ H) X ~{ C ∏ C }~> (H ○ (F ∏⟶ G)) X).
    given (f : ((C ∏ C) ⟶ C ∏ C) -> (C ×[Cat] C ~> C ×[Cat] C)).
      intros.
      exact X0.
    assert (f (F ∏⟶ G) ∘ f H ≈ @split Cat _ _ _ _ _ F G ∘ f H). {
      constructive; simpl; intros; simplify; intros.
      - exact id.
      - exact id.
      - simpl; cat.
      - simpl; cat.
      - exact id.
      - exact id.
      - simpl; cat.
      - simpl; cat.
      - simpl; cat.
      - simpl; cat.
      - simpl; cat.
      - simpl; cat.
    }
    unfold f in X0; clear f.
  simplify; simpl.
  destruct H; simpl in *.
  pose proof (transform[@sequence C _ _ H1 _ _ _] x).
  pose proof (fst (fmap (F x, y) (F x, G y) (id, pure))); simpl in X0.
  exact (X0 ∘ X).
Admitted.
Next Obligation.
  simplify; simpl.
  assert (StrongFunctor (@ProductFunctor_proj2 _ _ _ _ _ H x)) as X1 by admit.
  assert (LaxMonoidalFunctor (@ProductFunctor_proj2 _ _ _ _ _ H x)) as X2 by admit.
  pose proof (transform[@sequence C _ _ H4 (ProductFunctor_proj2 H) X1 X2] y).
  destruct H; simpl in *.
  pose proof (snd (fmap (x, G y) (F x, G y) (pure, id))); simpl in X0.
  exact (X0 ∘ X).
Admitted.
Next Obligation.
  (* assert (StrongFunctor (@ProductFunctor_proj2 _ _ _ _ _ H x)) as X4 by admit. *)
  (* assert (LaxMonoidalFunctor (@ProductFunctor_proj2 _ _ _ _ _ H x)) as X5 by admit. *)
  (* pose proof (@sequence C _ _ H2 (ProductFunctor_proj2 H) X4 X5). *)
  (* pose proof (transform[X] y) as X6; simpl in *; clear X. *)
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
  pose proof (@natural_transformation _ _ _ _ (@strength_nat C _ G H0)
                                      (x, I) (x, _) (id[x], lax_pure)).
  simpl in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((@strength_nat C H G H0) (x, H2 (@I C H)))).
  rewrite <- X0.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Monoidal.
Require Export Category.Functor.Product.
Require Export Category.Functor.Product.Internal.

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

Theorem Product_Traversable `{C : Category} `{@Cartesian C} `{@Monoidal C}
        `{F : C ⟶ C} `{G : C ⟶ C} :
  Traversable F * Traversable G <--> Traversable (F ∏⟶ G).
Proof.
  split.
    intros [O P].
    { unshelve econstructor; intros.
      { unshelve econstructor.
          intros [x y]; simpl; split.
          pose proof (@sequence _ _ _ O).
Abort.

(*
Proof.
  split; intros.
  { unshelve econstructor; intros; simpl; simplify.
    - natural; intros; simpl; simplify.
      + { unshelve (refine (let H :=
            {| fobj := fun x => fst (G0 (x, snd X))
             ; fmap := fun x y f =>
                 fst (@fmap _ _ G0 (x, snd X) (y, snd X) (f, id)) |} in _)).
          - intros; proper.
            rewrite X1; abstract reflexivity.
          - intros.
            rewrite bimap_fmap.
            rewrite bimap_id_id.
            abstract reflexivity.
          - intros.
            rewrite fst_comp.
            rewrite !bimap_fmap.
            rewrite <- bimap_comp.
            rewrite id_left.
            abstract reflexivity.
          - destruct X; simpl.
            pose proof (@sequence _ _ _ x).
            pose proof (fst (@strength _ _ _ H1 (I, I) (F o, G o0))).
            simpl in X.
            pose proof (fst (@bimap _ _ _ G0 _ _ _ _ id (to unit_left))
                            ∘ fst (@strength _ _ _ H1 (o, o0) (F o, G o0))).
         }
        simpl in H.
        given (H3 : StrongFunctor H). {
          unshelve econstructor; simpl.
          - natural; simpl; intros; simplify; simpl in *.
            + exact (fst (@bimap _ _ _ G0 _ _ _ _ id (to unit_left))
                         ∘ fst (@strength _ _ _ H1 (x0, I) (y0, snd X))).
            + simpl.
              pose proof (fst (@strength_id_left _ _ G0 _ X)) as X0;
              simpl in X0.
              destruct X; simpl in X0; simpl.
        }
        pose proof (transform[@sequence C H0 F x H _ _]).
*)

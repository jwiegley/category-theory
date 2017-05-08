Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Product.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Class StrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  strength_nat : (⨂) ○ Id ∏⟶ F ~{[C ∏ C, C]}~> F ○ (⨂);

  strength {X Y} : X ⨂ F Y ~> F (X ⨂ Y) := transform[strength_nat] (X, Y);

  strength_id_left {X} :
    fmap[F] (to unit_left) ∘ strength ≈ to (@unit_left _ _ (F X));
  strength_assoc {X Y Z} :
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ X Y (F Z))
      ≈ fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ strength
}.

Class RightStrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (⨂) ○ F ∏⟶ Id ~{[C ∏ C, C]}~> F ○ (⨂);

  rstrength {X Y} : F X ⨂ Y ~> F (X ⨂ Y) := transform[rstrength_nat] (X, Y);

  rrstrength_id_right {X} :
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F X));
  rstrength_assoc {X Y Z} :
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F X) Y Z)
      ≈ fmap[F] (from (@tensor_assoc _ _ X Y Z)) ∘ rstrength
}.

Require Import Category.Functor.Product.

Section Strong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.

Global Program Instance Id_StrongFunctor : StrongFunctor Id[C] := {
  strength_nat := {| transform := fun p => _ |}
}.
Next Obligation. exact id. Defined.
Next Obligation. unfold bimap; cat. Qed.

Local Obligation Tactic := program_simpl.

Global Program Instance Compose_StrongFunctor (F G : C ⟶ C) :
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F ○ G) := {
  strength_nat := {| transform := fun _ => fmap[F] strength ∘ strength |}
}.
Next Obligation.
  destruct H0, H1; simpl in *.
  unfold strength in *.
  unfold strength_nat in *.
  unfold strength0, strength1 in *.
  destruct strength_nat0, strength_nat1; simpl in *.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (natural_transformation0 (o1, o2) (o, o0) (h, h0)).
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply (natural_transformation (o1, G o2) (o, G o0) (h, fmap[G] h0)).
Qed.
Next Obligation.
  destruct H0, H1; simpl in *.
  unfold strength in *.
  unfold strength_nat in *.
  unfold strength0, strength1 in *.
  destruct strength_nat0, strength_nat1; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_id_left1.
  apply strength_id_left0.
Qed.
Next Obligation.
  destruct H0, H1; simpl in *.
  unfold strength in *.
  unfold strength_nat in *.
  unfold strength0, strength1 in *.
  destruct strength_nat0, strength_nat1; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- strength_assoc1.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- strength_assoc0.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite (natural_transformation (X, Y ⨂ G Z) (X, G (Y ⨂ Z))
                                  (id[X], transform0 (Y, Z))).
  unfold bimap; simpl.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp; simpl.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  split; simpl; cat.
Qed.

Theorem ProductFunctor_Strong (G : C ⟶ C) :
  StrongFunctor F * StrongFunctor G <--> StrongFunctor (F ∏⟶ G).
Proof.
  split; intros.
  { unshelve econstructor.
    destruct X as [O P].
    - natural; simplify; intros;
      simplify; simpl in *; simplify; simpl in *.
      + exact (transform[@strength_nat _ _ _ O] (x1, x0)).
      + exact (transform[@strength_nat _ _ _ P] (y, y0)).
      + destruct O, strength_nat0; simpl in *.
        abstract apply (natural_transformation (x5, x4)).
      + destruct P, strength_nat0; simpl in *.
        abstract apply (natural_transformation (y3, y4)).
    - intros.
      destruct X, X0; simpl.
      split; abstract apply strength_id_left.
    - intros.
      destruct X, X0, Y, Z; simpl.
      split; abstract apply strength_assoc.
  }
  { split.
    { destruct X.
      unshelve econstructor.
      - natural; simplify; simpl; intros; simplify.
        + exact (fst (transform[strength_nat0] ((x, I), (y, I)))).
        + simpl in *.
          abstract exact (fst (@natural_transformation
                                 _ _ _ _ strength_nat0
                                 (x1, I, (y1, I)) (x0, I, (y0, I))
                                 ((x, id), (y, id)))).
      - simpl; intros.
        abstract exact (fst (strength_id_left0 (X, I))).
      - simpl; intros.
        pose proof (@unit_left C H I) as X0.
        pose proof (fst (@natural_transformation _ _ _ _ strength_nat0
                           (X, I, (Y ⨂ Z, I))
                           (X, I, (Y ⨂ Z, I ⨂ I))
                           ((id[X], id[I]), (id[Y ⨂ Z], from X0)))) as X1.
        simpl in X1.
        rewrite bimap_id_id in X1.
        rewrite !fmap_id in X1.
        rewrite id_left in X1.
        rewrite bimap_id_id in X1.
        rewrite id_right in X1.
        rewrite X1; clear X1.
        pose proof (fst (@natural_transformation _ _ _ _ strength_nat0
                           (X ⨂ Y, I, (Z, I))
                           (X ⨂ Y, I ⨂ I, (Z, I))
                           ((id[X ⨂ Y], from X0), (id[Z], id[I])))) as X1.
        simpl in X1.
        rewrite bimap_id_id in X1.
        rewrite !fmap_id in X1.
        rewrite id_left in X1.
        rewrite bimap_id_id in X1.
        rewrite id_right in X1.
        rewrite X1; clear X1.
        abstract exact (fst (strength_assoc0 (X, I) (Y, I) (Z, I))).
    }
    { destruct X.
      unshelve econstructor.
      - natural; simplify; simpl; intros; simplify.
        + exact (snd (transform[strength_nat0] ((I, x), (I, y)))).
        + simpl in *.
          abstract exact (snd (@natural_transformation
                                 _ _ _ _ strength_nat0
                                 (I, x1, (I, y1)) (I, x0, (I, y0))
                                 ((id, x), (id, y)))).
      - simpl; intros.
        abstract exact (snd (strength_id_left0 (I, X))).
      - simpl; intros.
        pose proof (@unit_left C H I) as X0.
        pose proof (snd (@natural_transformation _ _ _ _ strength_nat0
                           (I, X, (I, Y ⨂ Z))
                           (I, X, (I ⨂ I, Y ⨂ Z))
                           ((id[I], id[X]), (from X0, id[Y ⨂ Z])))) as X1.
        simpl in X1.
        rewrite bimap_id_id in X1.
        rewrite !fmap_id in X1.
        rewrite id_left in X1.
        rewrite bimap_id_id in X1.
        rewrite id_right in X1.
        rewrite X1; clear X1.
        pose proof (snd (@natural_transformation _ _ _ _ strength_nat0
                           (I, X ⨂ Y, (I, Z))
                           (I ⨂ I, X ⨂ Y, (I, Z))
                           ((from X0, id[X ⨂ Y]), (id[I], id[Z])))) as X1.
        simpl in X1.
        rewrite bimap_id_id in X1.
        rewrite !fmap_id in X1.
        rewrite id_left in X1.
        rewrite bimap_id_id in X1.
        rewrite id_right in X1.
        rewrite X1; clear X1.
        abstract exact (snd (strength_assoc0 (I, X) (I, Y) (I, Z))).
    }
  }
Qed.

End Strong.

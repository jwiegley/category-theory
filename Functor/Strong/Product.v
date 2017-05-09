Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductStrong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.

Local Obligation Tactic := program_simpl.

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
      + destruct O, strength_nat; simpl in *.
        abstract apply (natural_transformation (x5, x4)).
      + destruct P, strength_nat; simpl in *.
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
        + exact (fst (transform[strength_nat] ((x, I), (y, I)))).
        + simpl in *.
          abstract exact (fst (@natural_transformation
                                 _ _ _ _ strength_nat
                                 (x1, I, (y1, I)) (x0, I, (y0, I))
                                 ((x, id), (y, id)))).
      - simpl; intros.
        abstract exact (fst (strength_id_left (X, I))).
      - simpl; intros.
        pose proof (@unit_left C H I) as X0.
        pose proof (fst (@natural_transformation _ _ _ _ strength_nat
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
        pose proof (fst (@natural_transformation _ _ _ _ strength_nat
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
        abstract exact (fst (strength_assoc (X, I) (Y, I) (Z, I))).
    }
    { destruct X.
      unshelve econstructor.
      - natural; simplify; simpl; intros; simplify.
        + exact (snd (transform[strength_nat] ((I, x), (I, y)))).
        + simpl in *.
          abstract exact (snd (@natural_transformation
                                 _ _ _ _ strength_nat
                                 (I, x1, (I, y1)) (I, x0, (I, y0))
                                 ((id, x), (id, y)))).
      - simpl; intros.
        abstract exact (snd (strength_id_left (I, X))).
      - simpl; intros.
        pose proof (@unit_left C H I) as X0.
        pose proof (snd (@natural_transformation _ _ _ _ strength_nat
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
        pose proof (snd (@natural_transformation _ _ _ _ strength_nat
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
        abstract exact (snd (strength_assoc (I, X) (I, Y) (I, Z))).
    }
  }
Qed.

End ProductStrong.

Theorem ProductFunctor_proj_Strong
        `{C : Category} `{@Monoidal C}
        (P : (C ∏ C) ⟶ (C ∏ C)) :
  { p : (C ⟶ C) * (C ⟶ C)
  & StrongFunctor P -> StrongFunctor ((fst p) ∏⟶ (snd p)) }.
Proof.
  unshelve eexists.
    split.
    { refine
        {| fobj := fun x => fst (P (x, I))
         ; fmap := fun x y f => fst (@fmap _ _ P (x, I) (y, I) (f, id))
         ; fmap_respects := fun x y f g eqv =>
             fst (@fmap_respects _ _ P (x, I) (y, I) (f, id) (g, id)
                                 (eqv, reflexivity _))
         ; fmap_id := fun x => fst (@fmap_id _ _ P (x, I))
         ; fmap_comp := fun x y z f g =>
             _ (fst (@fmap_comp _ _ P (x, I) (y, I) (z, I) (f, id) (g, id)))
         |}.
      intros.
      rewrite fst_comp.
      rewrite <- fmap_comp; simpl.
      rewrite id_left; reflexivity.
    }
    { refine
        {| fobj := fun x => snd (P (I, x))
         ; fmap := fun x y f => snd (@fmap _ _ P (I, x) (I, y) (id, f))
         ; fmap_respects := fun x y f g eqv =>
             snd (@fmap_respects _ _ P (I, x) (I, y) (id, f) (id, g)
                                 (reflexivity _, eqv))
         ; fmap_id := fun x => snd (@fmap_id _ _ P (I, x))
         ; fmap_comp := fun x y z f g =>
             _ (snd (@fmap_comp _ _ P (I, x) (I, y) (I, z) (id, f) (id, g)))
         |}.
      intros.
      rewrite snd_comp.
      rewrite <- fmap_comp; simpl.
      rewrite id_left; reflexivity.
    }
  simpl; intros.
  remember {| fobj := _ |} as F.
  remember {| fobj := λ x : C, snd (P (I, x)) |} as G.
  apply (fst (@ProductFunctor_Strong _ _ F G)).
  rewrite HeqF, HeqG; clear HeqF HeqG.
  split.
  { unshelve econstructor; simpl.
    - natural; simplify; simpl; intros; simplify.
      + exact (fst (bimap id (to unit_left)
                      ∘ transform[@strength_nat _ _ _ X] ((x, I), (y, I)))).
      + simpl in *.
        pose proof (fst (@natural_transformation
                           _ _ _ _ (@strength_nat _ _ _ X)
                           (x1, I, (y1, I)) (x0, I, (y0, I))
                           ((x, id), (y, id)))) as X0.
        simpl in X0.
        rewrite comp_assoc.
        rewrite !bimap_fmap.
        rewrite fst_comp.
        rewrite <- bimap_comp.
        rewrite id_left, id_right.
        rewrite <- comp_assoc.
        rewrite <- X0.
        rewrite comp_assoc.
        rewrite fst_comp.
        rewrite bimap_fmap.
        rewrite <- bimap_comp.
        rewrite bimap_id_id.
        rewrite id_left, id_right.
        reflexivity.
    - simpl; intros.
      pose (fst (@strength_id_left _ _ _ X (X0, I))).
      rewrite comp_assoc.
      rewrite fst_comp.
      rewrite bimap_fmap.
      rewrite <- bimap_comp.
      rewrite id_left, id_right.
      simpl in e.
      rewrite e; clear e.
      destruct (P (X0, I)); reflexivity.
    - simpl; intros.
      rewrite !bimap_fmap.
      rewrite comp_assoc.
      rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite id_left, id_right.

      pose proof (fst (@strength_assoc _ _ _ X (X0, I) (Y, I) (Z, I))) as X2;
      simpl in X2.

      pose proof (fst (@natural_transformation _ _ _ _
                         (@strength_nat _ _ _ X)
                         (X0, I, (Y ⨂ Z, I ⨂ I))
                         (X0, I, (Y ⨂ Z, I))
                         ((id[X0], id[I]),
                          (id[Y ⨂ Z], to unit_left)))) as X3.
      simpl in X3.
      rewrite !bimap_fmap in X3.
      rewrite bimap_id_id in X3.
      rewrite <- (id_right (id[X0])).
      rewrite bimap_comp.
      rewrite !comp_assoc.
      rewrite <- (comp_assoc (fst _)).
      rewrite <- (comp_assoc (fst _)).
      rewrite <- X3; clear X3.

      pose proof (fst (@natural_transformation _ _ _ _
                         (@strength_nat _ _ _ X)
                         (X0 ⨂ Y, I ⨂ I, (Z, I))
                         (X0 ⨂ Y, I, (Z, I))
                         ((id[X0 ⨂ Y], to unit_left),
                          (id[Z], id[I])))) as X4.
      simpl in X4.
      rewrite !bimap_fmap in X4.
      rewrite !bimap_id_id in X4.
      rewrite id_right in X4.
      rewrite <- X4; clear X4.

      rewrite !comp_assoc.
      rewrite !fst_comp.
      rewrite <- !bimap_comp.
      rewrite !id_left, id_right.
      revert X2 F G.
      replace (fst
                 (let
                     (x, y) as p
                     return
                     (((X0 ⨂ Y) ⨂ fst p ~{ C }~> X0 ⨂ Y ⨂ fst p) *
                      ((I ⨂ I) ⨂ snd p ~{ C }~> I ⨂ I ⨂ snd p)) := P (Z, I) in
                   (to tensor_assoc, to tensor_assoc)))
        with (@to C ((X0 ⨂ Y) ⨂ (fst (P (Z, I))))
                  (X0 ⨂ Y ⨂ (fst (P (Z, I))))
                  (@tensor_assoc C H X0 Y (fst (P (Z, I))))).
        intros.
        rewrite <- !comp_assoc.
        rewrite (comp_assoc _ (bimap _ _)).
        rewrite X2; clear X2.
        rewrite comp_assoc.
        rewrite fst_comp.
        rewrite bimap_fmap.
        rewrite <- bimap_comp.
        rewrite id_left.
        apply compose_respects; [|reflexivity].
        enough ((to unit_left ∘ bimap (id[I]) (to unit_left) ∘ to tensor_assoc)
                  ≈ (to unit_left ∘ bimap (to unit_left) (id[I]))).
          rewrite X1; reflexivity.
        rewrite <- comp_assoc.
        apply compose_respects; [reflexivity|].
        rewrite <- triangle_identity.
        apply bimap_respects; [|reflexivity].
        symmetry.
        apply unit_identity.
      destruct (P (Z, I)); reflexivity.
  }
Abort.

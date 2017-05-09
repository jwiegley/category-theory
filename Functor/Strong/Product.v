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

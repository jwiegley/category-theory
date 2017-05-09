Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Monoidal.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductMonoidal.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{D : Category}.
Context `{@Monoidal D}.
Context `{G : C ⟶ D}.

Context `{E : Category}.
Context `{@Monoidal E}.
Context `{F : D ⟶ E}.

Local Obligation Tactic := program_simpl.

Theorem ProductFunctor_Monoidal :
  MonoidalFunctor F * MonoidalFunctor G <--> MonoidalFunctor (F ∏⟶ G).
Proof.
  split; intros.
  { unshelve econstructor.
    destruct X as [O P].
    - simpl; unshelve esplit; simpl; simplify; apply pure_iso.
    - isomorphism; simpl.
      + natural; simplify; intros;
        simplify; simpl in *; simplify; simpl in *.
        * exact (transform[to (@ap_functor_iso _ _ _ _ _ x)] (x2, x1)).
        * exact (transform[to (@ap_functor_iso _ _ _ _ _ y)] (y0, y1)).
        * abstract apply (@natural_transformation
                            _ _ _ _
                            (to (@ap_functor_iso _ _ _ _ _ x)) (x5, x4)).
        * abstract apply (@natural_transformation
                            _ _ _ _
                            (to (@ap_functor_iso _ _ _ _ _ y5)) (y3, y4)).
      + natural; simplify; intros;
        simplify; simpl in *; simplify; simpl in *.
        * exact (transform[from (@ap_functor_iso _ _ _ _ _ x)] (x2, x1)).
        * exact (transform[from (@ap_functor_iso _ _ _ _ _ y)] (y0, y1)).
        * abstract apply (@natural_transformation
                            _ _ _ _
                            (from (@ap_functor_iso _ _ _ _ _ x))
                            (x5, x4) (x3, x2) (x1, x0)).
        * abstract apply (@natural_transformation
                            _ _ _ _
                            (from (@ap_functor_iso _ _ _ _ _ y5))
                            (y3, y4) (y1, y2) (y, y0)).
      + destruct X, A, p, p0; simpl.
        split.
          pose proof (iso_to_from (@ap_functor_iso _ _ _ _ _ m)).
          simpl in X; abstract apply X.
        pose proof (iso_to_from (@ap_functor_iso _ _ _ _ _ m0)).
        simpl in X; abstract apply X.
      + destruct X, A, p, p0; simpl.
        split.
          pose proof (iso_from_to (@ap_functor_iso _ _ _ _ _ m) (o, o1)).
          simpl in X; abstract apply X.
        pose proof (iso_from_to (@ap_functor_iso _ _ _ _ _ m0) (o0, o2)).
        simpl in X; abstract apply X.
    - intros.
      destruct X, X0; simpl.
      isomorphism; simpl; simplify;
      apply pure_iso_left || apply pure_iso_right.
    - intros.
      destruct X, X0; simpl.
      isomorphism; simpl; simplify;
      apply pure_iso_left || apply pure_iso_right.
    - simpl; intros; simplify; simpl.
      isomorphism; simpl; simplify;
      apply ap_iso_assoc.
  }
  { split.
    { destruct X.
      unshelve econstructor.
      - simpl; unshelve esplit; simpl; simplify; apply pure_iso.
      - isomorphism; simpl.
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (fst (transform[to (ap_functor_iso)] ((x, I), (y, I)))).
          * simpl in *.
            abstract exact (fst (@natural_transformation
                                   _ _ _ _ (to ap_functor_iso)
                                   (x1, I, (y1, I)) (x0, I, (y0, I))
                                   ((x, id), (y, id)))).
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (fst (transform[from (ap_functor_iso)] ((x, I), (y, I)))).
          * simpl in *.
            abstract exact (fst (@natural_transformation
                                   _ _ _ _ (from ap_functor_iso)
                                   (x1, I, (y1, I)) (x0, I, (y0, I))
                                   ((x, id), (y, id)))).
        + destruct A; simpl.
          abstract apply (iso_to_from ap_functor_iso (o, I, (o0, I))).
        + destruct A; simpl.
          abstract apply (iso_from_to ap_functor_iso (o, I, (o0, I))).
      - simpl; intros.
        pose (fst (to (pure_iso_left (X, I)))).
        pose (fst (from (pure_iso_left (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_left _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (pure_iso_right (X, I)))).
        pose (fst (from (pure_iso_right (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_right _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (ap_iso_assoc (X, I) (Y, I) (Z, I)))).
        pose (fst (from (ap_iso_assoc (X, I) (Y, I) (Z, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_iso_assoc _ _ _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
    }
    { destruct X.
      unshelve econstructor.
      - simpl; unshelve esplit; simpl; simplify; apply pure_iso.
      - isomorphism; simpl.
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (snd (transform[to (ap_functor_iso)] ((I, x), (I, y)))).
          * simpl in *.
            abstract exact (snd (@natural_transformation
                                   _ _ _ _ (to ap_functor_iso)
                                   (I, x1, (I, y1)) (I, x0, (I, y0))
                                   ((id, x), (id, y)))).
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (snd (transform[from (ap_functor_iso)] ((I, x), (I, y)))).
          * simpl in *.
            abstract exact (snd (@natural_transformation
                                   _ _ _ _ (from ap_functor_iso)
                                   (I, x1, (I, y1)) (I, x0, (I, y0))
                                   ((id, x), (id, y)))).
        + destruct A; simpl.
          apply (iso_to_from ap_functor_iso (I, o, (I, o0))).
        + destruct A; simpl.
          apply (iso_from_to ap_functor_iso (I, o, (I, o0))).
      - simpl; intros.
        pose (snd (to (pure_iso_left (I, X)))).
        pose (snd (from (pure_iso_left (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_left _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (pure_iso_right (I, X)))).
        pose (snd (from (pure_iso_right (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_right _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (ap_iso_assoc (I, X) (I, Y) (I, Z)))).
        pose (snd (from (ap_iso_assoc (I, X) (I, Y) (I, Z)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_iso_assoc _ _ _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
    }
  }
Qed.

Theorem ProductFunctor_LaxMonoidal :
  LaxMonoidalFunctor F * LaxMonoidalFunctor G <--> LaxMonoidalFunctor (F ∏⟶ G).
Proof.
  split; intros.
  { unshelve econstructor.
    destruct X as [O P].
    - simpl; simplify; apply lax_pure.
    - natural; simplify; intros;
      simplify; simpl in *; simplify; simpl in *.
      + exact (transform[@ap_functor_nat _ _ _ _ _ x] (x2, x1)).
      + exact (transform[@ap_functor_nat _ _ _ _ _ y] (y0, y1)).
      + destruct x, ap_functor_nat; simpl in *.
        abstract apply (natural_transformation (x5, x4)).
      + destruct y5, ap_functor_nat; simpl in *.
        abstract apply (natural_transformation (y3, y4)).
    - intros.
      destruct X, X0; simpl.
      isomorphism; simpl; simplify;
      apply pure_left || apply pure_right.
    - intros.
      destruct X, X0; simpl.
      isomorphism; simpl; simplify;
      apply pure_left || apply pure_right.
    - simpl; intros; simplify; simpl.
      isomorphism; simpl; simplify;
      apply ap_assoc.
  }
  { split.
    { destruct X.
      unshelve econstructor.
      - apply lax_pure.
      - natural; simplify; simpl; intros; simplify; simpl.
        + exact (fst (transform[ap_functor_nat] ((x, I), (y, I)))).
        + simpl in *.
          abstract exact (fst (@natural_transformation
                                 _ _ _ _ ap_functor_nat
                                 (x1, I, (y1, I)) (x0, I, (y0, I))
                                 ((x, id), (y, id)))).
      - simpl; intros.
        pose (fst (to (pure_left (X, I)))).
        pose (fst (from (pure_left (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_left _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (pure_right (X, I)))).
        pose (fst (from (pure_right (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_right _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (ap_assoc (X, I) (Y, I) (Z, I)))).
        pose (fst (from (ap_assoc (X, I) (Y, I) (Z, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_assoc _ _ _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
    }
    { destruct X.
      unshelve econstructor.
      - abstract apply lax_pure.
      - natural; simplify; simpl; intros; simplify; simpl.
        + exact (snd (transform[ap_functor_nat] ((I, x), (I, y)))).
        + simpl in *.
          abstract exact (snd (@natural_transformation
                                 _ _ _ _ ap_functor_nat
                                 (I, x1, (I, y1)) (I, x0, (I, y0))
                                 ((id, x), (id, y)))).
      - simpl; intros.
        pose (snd (to (pure_left (I, X)))).
        pose (snd (from (pure_left (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_left _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (pure_right (I, X)))).
        pose (snd (from (pure_right (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_right _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (ap_assoc (I, X) (I, Y) (I, Z)))).
        pose (snd (from (ap_assoc (I, X) (I, Y) (I, Z)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_assoc _ _ _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
    }
  }
Qed.

End ProductMonoidal.

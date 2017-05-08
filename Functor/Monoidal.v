Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Hom.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section MonoidalFunctor.

Context `{C : Category}.
Context `{D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context `{F : C ⟶ D}.

(* The strong monoidal functor isomorphism can be projected to an isomorphism
   between objects in D. This forgets the naturality of the original natural
   isomorphism, which is why it is only provided as a convenience definition
   below in [StrongMonoidalFunctor]. *)

Program Definition project_monoidal_iso
        (iso : (⨂) ○ F ∏⟶ F ≅[[C ∏ C, D]] F ○ (⨂)) (X Y : C) :
  F X ⨂ F Y ≅[D] F (X ⨂ Y) := {|
  to   := to   iso (X, Y);
  from := from iso (X, Y)
|}.
Next Obligation.
  rewrite (iso_to_from iso (X, Y)); simpl.
  rewrite fmap_id; cat.
Qed.
Next Obligation.
  rewrite (iso_from_to iso (X, Y)); simpl.
  rewrite <- fmap_id.
  apply fmap_respects.
  split; simpl; cat.
Qed.

Class MonoidalFunctor := {
  pure_iso : I ≅ F I;

  ap_functor_iso : (⨂) ○ F ∏⟶ F ≅[[C ∏ C, D]] F ○ (⨂);

  ap_iso {X Y} : F X ⨂ F Y ≅ F (X ⨂ Y) :=
    project_monoidal_iso ap_functor_iso X Y;

  pure_iso_left {X}  : I ⨂ F X ≅ F (I ⨂ X);
  pure_iso_right {X} : F X ⨂ I ≅ F (X ⨂ I);

  ap_iso_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≅ F (X ⨂ (Y ⨂ Z))
}.

(* A lax monoidal functor's natural transformation can be projected to a
   morphism between objects in D. This forgets the naturality of the
   transformation, which is why it is only provided as a convenience
   definition below in [LaxMonoidalFunctor]. *)

Class LaxMonoidalFunctor := {
  lax_pure : I ~> F I;

  ap_functor_nat : ((⨂) ○ F ∏⟶ F) ~{[C ∏ C, D]}~> (F ○ (⨂));

  ap {X Y} : F X ⨂ F Y ~> F (X ⨂ Y) := transform[ap_functor_nat] (X, Y);

  pure_left {X}  : I ⨂ F X ≅ F (I ⨂ X);
  pure_right {X} : F X ⨂ I ≅ F (X ⨂ I);

  ap_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≅ F (X ⨂ (Y ⨂ Z))
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  lax_pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.

End MonoidalFunctor.

Notation "ap[ F ]" := (@ap _ _ _ _ F _ _ _) (at level 9, format "ap[ F ]").

Arguments LaxMonoidalFunctor {C D _ _} F.
Arguments MonoidalFunctor {C D _ _} F.

Section Pure.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.
Context `{@StrongFunctor C _ F}.
Context `{@LaxMonoidalFunctor C C _ _ F}.

Definition pure {A} : A ~> F A :=
  fmap[F] (to (@unit_right _ _ A))
      ∘ strength
      ∘ bimap id lax_pure
      ∘ from (@unit_right _ _ A).

Lemma fmap_pure {a b} (f : a ~> b) : pure ∘ f ≈ fmap f ∘ pure.
Proof.
Admitted.

End Pure.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 9, format "pure[ F ]") : morphism_scope.

Section MonoidalFunctors.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{D : Category}.
Context `{@Monoidal D}.
Context `{G : C ⟶ D}.

Context `{E : Category}.
Context `{@Monoidal E}.
Context `{F : D ⟶ E}.

(* jww (2017-05-05): Move the below into its own file.
   Separate functors from  Cartesian, Closed, etc. *)

Local Obligation Tactic := program_simpl.

Global Program Instance Id_MonoidalFunctor :
  @MonoidalFunctor C C _ _ Id[C] := {
  pure_iso := id_iso;
  ap_functor_iso := {| to   := {| transform := fun _ => _ |}
                     ; from := {| transform := fun _ => _ |} |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation.
  simpl; intros.
  destruct H1; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. apply tensor_assoc. Qed.

(* Any two monoidal functors compose to create a monoidal functor. This is
   composition in the groupoid of categories with monoidal structure. *)

Global Program Instance Compose_MonoidalFunctor
       `(M : @MonoidalFunctor D E _ _ F)
       `(N : @MonoidalFunctor C D _ _ G) :
  `{@MonoidalFunctor C E _ _ (F ○ G)} := {
  pure_iso := compose_iso (fmap_iso F _ _ (@pure_iso _ _ _ _ G _))
                          (@pure_iso _ _ _ _ F _);
  ap_functor_iso :=
    {| to   := {| transform := fun p =>
         fmap (to ap_iso) ∘ to (@ap_iso _ _ _ _ F _ (G (fst p)) (G (snd p))) |}
     ; from := {| transform := fun p =>
         from (@ap_iso _ _ _ _ F _ (G (fst p)) (G (snd p))) ∘ fmap (from ap_iso) |}
     |}
}.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@natural_transformation
             _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ N))
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@natural_transformation
                _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  simpl in X; rewrite <- X.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  pose proof (@natural_transformation
                _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  simpl in X; rewrite X.
  simpl.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- (@natural_transformation
                _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ N))
                (o1, o2) (o, o0) (h, h0)).
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite fmap_id.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((@to _ _ _ (@ap_functor_iso _ _ _ _ _ M)) (G o, G o0))).
  pose proof (@iso_to_from _ _ _ (@ap_functor_iso _ _ _ _ _ M) (G o, G o0)).
  simpl in X; rewrite X.
  rewrite fmap_id.
  rewrite comp_assoc.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  rewrite <- comp_assoc.
  pose proof (@fmap_id _ _ (@tensor D H0)).
  simpl in X0; rewrite X0.
  rewrite id_left.
  pose proof (@fmap_id _ _ (@tensor C H)).
  rewrite (@iso_to_from _ _ _ (@ap_functor_iso _ _ _ _ _ N) (o, o0)).
  simpl.
  rewrite fmap_id.
  apply fmap_id.
Qed.
Next Obligation.
  simpl.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap ((@from _ _ _ (@ap_functor_iso _ _ _ _ _ N)) (o, o0)))).
  rewrite <- fmap_comp.
  rewrite (@iso_from_to _ _ _ (@ap_functor_iso _ _ _ _ _ N) (o, o0)).
  simpl.
  pose proof (@fmap_respects _ _ (@tensor D H0) (G o, G o0) (G o, G o0)
                             (fmap[G] (id[o]), fmap[G] (id[o0]))).
  simpl in X; rewrite X.
    pose proof (@fmap_id _ _ (@tensor D H0)) as X0.
    simpl in X0; rewrite X0.
    rewrite !fmap_id.
    rewrite id_left.
    rewrite (@iso_from_to _ _ _ (@ap_functor_iso _ _ _ _ _ M) (G o, G o0)).
    simpl.
    pose proof (@fmap_respects _ _ (@tensor E H1)
                               (F (G o), F (G o0)) (F (G o), F (G o0))
                               (fmap[F] (fmap[G] (id[o])),
                                fmap[F] (fmap[G] (id[o0])))) as X1.
    rewrite <- (@fmap_id _ _ G o).
    rewrite <- (@fmap_id _ _ G o0).
    rewrite X1.
      pose proof (@fmap_id _ _ (@tensor E H1)) as X2.
      simpl in X2; rewrite X2.
      pose proof (@fmap_respects _ _ (@tensor E H1)) as X3.
      reflexivity.
    simpl; split;
    rewrite fmap_id;
    apply fmap_id.
  simpl; split;
  apply fmap_id.
Qed.
Next Obligation.
  transitivity (F (I ⨂ G X)).
    transitivity (F (G X)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_iso_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I)).
    transitivity (F (G X)).
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_iso_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z)).
    apply ap_iso_assoc.
  apply fmap_iso.
  transitivity ((G X ⨂ G Y) ⨂ G Z).
    symmetry.
    apply tensor_assoc.
  apply ap_iso_assoc.
Qed.

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
      - simpl; unshelve esplit; simpl; simplify; apply pure_iso0.
      - isomorphism; simpl.
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (fst (transform[to (ap_functor_iso0)] ((x, I), (y, I)))).
          * simpl in *.
            abstract exact (fst (@natural_transformation
                                   _ _ _ _ (to ap_functor_iso0)
                                   (x1, I, (y1, I)) (x0, I, (y0, I))
                                   ((x, id), (y, id)))).
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (fst (transform[from (ap_functor_iso0)] ((x, I), (y, I)))).
          * simpl in *.
            abstract exact (fst (@natural_transformation
                                   _ _ _ _ (from ap_functor_iso0)
                                   (x1, I, (y1, I)) (x0, I, (y0, I))
                                   ((x, id), (y, id)))).
        + destruct A; simpl.
          abstract apply (iso_to_from ap_functor_iso0 (o, I, (o0, I))).
        + destruct A; simpl.
          abstract apply (iso_from_to ap_functor_iso0 (o, I, (o0, I))).
      - simpl; intros.
        pose (fst (to (pure_iso_left0 (X, I)))).
        pose (fst (from (pure_iso_left0 (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_left0 _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (pure_iso_right0 (X, I)))).
        pose (fst (from (pure_iso_right0 (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_right0 _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (ap_iso_assoc0 (X, I) (Y, I) (Z, I)))).
        pose (fst (from (ap_iso_assoc0 (X, I) (Y, I) (Z, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_iso_assoc0 _ _ _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
    }
    { destruct X.
      unshelve econstructor.
      - simpl; unshelve esplit; simpl; simplify; apply pure_iso0.
      - isomorphism; simpl.
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (snd (transform[to (ap_functor_iso0)] ((I, x), (I, y)))).
          * simpl in *.
            abstract exact (snd (@natural_transformation
                                   _ _ _ _ (to ap_functor_iso0)
                                   (I, x1, (I, y1)) (I, x0, (I, y0))
                                   ((id, x), (id, y)))).
        + natural; simplify; simpl; intros; simplify; simpl.
          * exact (snd (transform[from (ap_functor_iso0)] ((I, x), (I, y)))).
          * simpl in *.
            abstract exact (snd (@natural_transformation
                                   _ _ _ _ (from ap_functor_iso0)
                                   (I, x1, (I, y1)) (I, x0, (I, y0))
                                   ((id, x), (id, y)))).
        + destruct A; simpl.
          apply (iso_to_from ap_functor_iso0 (I, o, (I, o0))).
        + destruct A; simpl.
          apply (iso_from_to ap_functor_iso0 (I, o, (I, o0))).
      - simpl; intros.
        pose (snd (to (pure_iso_left0 (I, X)))).
        pose (snd (from (pure_iso_left0 (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_left0 _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (pure_iso_right0 (I, X)))).
        pose (snd (from (pure_iso_right0 (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_iso_right0 _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (ap_iso_assoc0 (I, X) (I, Y) (I, Z)))).
        pose (snd (from (ap_iso_assoc0 (I, X) (I, Y) (I, Z)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_iso_assoc0 _ _ _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
    }
  }
Qed.

Global Program Instance Id_LaxMonoidalFunctor :
  @LaxMonoidalFunctor C C _ _ Id[C] := {
  lax_pure := id;
  ap_functor_nat := {| transform := fun _ => _ |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. apply tensor_assoc. Qed.

(* Likewise, any two lax monoidal functors compose to create a lax monoidal
   functor. This is composition in the category of categories with monoidal
   structure. *)

Global Program Instance Compose_LaxMonoidalFunctor
       `(M : @LaxMonoidalFunctor D E _ _ F)
       `(N : @LaxMonoidalFunctor C D _ _ G) :
  `{@LaxMonoidalFunctor C E _ _ (F ○ G)} := {
  lax_pure := fmap lax_pure ∘ lax_pure;
  ap_functor_nat := {| transform := fun p =>
    fmap ap ∘ @ap _ _ _ _ F _ (G (fst p)) (G (snd p)) |}
}.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@natural_transformation
             _ _ _ _ (@ap_functor_nat _ _ _ _ _ N)
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@natural_transformation
                _ _ _ _ (@ap_functor_nat _ _ _ _ _ M)
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  simpl in X; rewrite <- X.
  reflexivity.
Qed.
Next Obligation.
  transitivity (F (I ⨂ G X)).
    transitivity (F (G X)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I)).
    transitivity (F (G X)).
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z)).
    apply ap_assoc.
  apply fmap_iso.
  transitivity ((G X ⨂ G Y) ⨂ G Z).
    symmetry.
    apply tensor_assoc.
  apply ap_assoc.
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
      + destruct x, ap_functor_nat0; simpl in *.
        abstract apply (natural_transformation (x5, x4)).
      + destruct y5, ap_functor_nat0; simpl in *.
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
      - apply lax_pure0.
      - natural; simplify; simpl; intros; simplify; simpl.
        + exact (fst (transform[ap_functor_nat0] ((x, I), (y, I)))).
        + simpl in *.
          abstract exact (fst (@natural_transformation
                                 _ _ _ _ ap_functor_nat0
                                 (x1, I, (y1, I)) (x0, I, (y0, I))
                                 ((x, id), (y, id)))).
      - simpl; intros.
        pose (fst (to (pure_left0 (X, I)))).
        pose (fst (from (pure_left0 (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_left0 _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (pure_right0 (X, I)))).
        pose (fst (from (pure_right0 (X, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_right0 _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
      - simpl; intros.
        pose (fst (to (ap_assoc0 (X, I) (Y, I) (Z, I)))).
        pose (fst (from (ap_assoc0 (X, I) (Y, I) (Z, I)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_assoc0 _ _ _); simpl.
          abstract apply (fst iso_to_from).
        abstract apply (fst iso_from_to).
    }
    { destruct X.
      unshelve econstructor.
      - abstract apply lax_pure0.
      - natural; simplify; simpl; intros; simplify; simpl.
        + exact (snd (transform[ap_functor_nat0] ((I, x), (I, y)))).
        + simpl in *.
          abstract exact (snd (@natural_transformation
                                 _ _ _ _ ap_functor_nat0
                                 (I, x1, (I, y1)) (I, x0, (I, y0))
                                 ((id, x), (id, y)))).
      - simpl; intros.
        pose (snd (to (pure_left0 (I, X)))).
        pose (snd (from (pure_left0 (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_left0 _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (pure_right0 (I, X)))).
        pose (snd (from (pure_right0 (I, X)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (pure_right0 _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
      - simpl; intros.
        pose (snd (to (ap_assoc0 (I, X) (I, Y) (I, Z)))).
        pose (snd (from (ap_assoc0 (I, X) (I, Y) (I, Z)))).
        isomorphism; simpl; simplify; auto;
        unfold h, h0; simpl;
        destruct (ap_assoc0 _ _ _); simpl.
          abstract apply (snd iso_to_from).
        abstract apply (snd iso_from_to).
    }
  }
Qed.

End MonoidalFunctors.

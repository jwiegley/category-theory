Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
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
  to   := transform[to iso] (X, Y);
  from := transform[from iso] (X, Y)
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

  ap_iso_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≅ F (X ⨂ (Y ⨂ Z));

  monoidal_unit_left {X} :
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ to ap_iso ∘ bimap (to pure_iso) (id[F X]);

  monoidal_unit_right {X} :
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ to ap_iso ∘ bimap (id[F X]) (to pure_iso);

  monoidal_assoc {X Y Z} :
    fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ to ap_iso ∘ bimap (to ap_iso) id
      ≈ to ap_iso ∘ bimap id (to ap_iso) ∘ to tensor_assoc
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

  ap_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≅ F (X ⨂ (Y ⨂ Z));

  lax_monoidal_unit_left {X} :
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ ap ∘ bimap lax_pure (id[F X]);

  lax_monoidal_unit_right {X} :
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ ap ∘ bimap (id[F X]) lax_pure;

  lax_monoidal_assoc {X Y Z} :
    fmap[F] (to (@tensor_assoc _ _ X Y Z)) ∘ ap ∘ bimap ap id
      ≈ ap ∘ bimap id ap ∘ to tensor_assoc
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  lax_pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.
Next Obligation. apply monoidal_unit_left. Qed.
Next Obligation. apply monoidal_unit_right. Qed.
Next Obligation. apply monoidal_assoc. Qed.

End MonoidalFunctor.

Notation "ap_iso[ F ]" := (@ap_iso _ _ _ _ F _ _ _)
  (at level 9, format "ap_iso[ F ]").
Notation "ap_functor_iso[ F ]" := (@ap_functor_iso _ _ _ _ _ F)
  (at level 9, format "ap_functor_iso[ F ]") : morphism_scope.

Notation "ap[ F ]" := (@ap _ _ _ _ F _ _ _)
  (at level 9, format "ap[ F ]").
Notation "ap_functor_nat[ F ]" := (@ap_functor_nat _ _ _ _ _ F)
  (at level 9, format "ap_functor_nat[ F ]") : morphism_scope.

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
  unfold pure.
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
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

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
  rewrite (@naturality
             _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ N))
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@naturality
                _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  simpl in X; rewrite <- X.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  pose proof (@naturality
                _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  simpl in X; rewrite X.
  simpl.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- (@naturality
                _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ N))
                (o1, o2) (o, o0) (h, h0)).
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite fmap_id.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (transform[@to _ _ _ (@ap_functor_iso _ _ _ _ _ M)]
                                (G o, G o0))).
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
  rewrite (comp_assoc
             (fmap (transform[@from _ _ _ (@ap_functor_iso _ _ _ _ _ N)]
                             (o, o0)))).
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
Next Obligation.
  rewrite monoidal_unit_left.
  rewrite monoidal_unit_left.
  unfold project_monoidal_iso; simpl.
  rewrite !comp_assoc.
  rewrite fmap_comp.
  symmetry.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  pose proof (naturality[to ap_functor_iso] (I, G X) (G I, G X)
                        (to pure_iso, id[G X])).
  simpl in X0.
  rewrite !bimap_fmap in X0.
  rewrite comp_assoc.
  rewrite X0; clear X0.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  rewrite monoidal_unit_right.
  rewrite monoidal_unit_right.
  unfold project_monoidal_iso; simpl.
  rewrite !comp_assoc.
  rewrite fmap_comp.
  symmetry.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  pose proof (naturality[to ap_functor_iso] (G X, I) (G X, G I)
                        (id[G X], to pure_iso)).
  simpl in X0.
  rewrite !bimap_fmap in X0.
  rewrite comp_assoc.
  rewrite X0; clear X0.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  pose proof (naturality[to (ap_functor_iso[M])]
                        (G X ⨂ G Y, G Z) (G (X ⨂ Y), G Z)
                        (transform (to ap_functor_iso) (X, Y), id[G Z])) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- XM; clear XM.

  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  pose proof (@monoidal_assoc _ _ _ _ G _ X Y Z) as XG; simpl in XG.
  rewrite XG; clear XG.

  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.

  pose proof (@monoidal_assoc _ _ _ _ F _ (G X) (G Y) (G Z)) as XF; simpl in XF.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ _ (bimap _ _)).
  rewrite XF; clear XF.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].

  pose proof
       (naturality[to (ap_functor_iso[M])]
                  (G X, G Y ⨂ G Z) (G X, G (Y ⨂ Z))
                  (id[G X], transform (to ap_functor_iso[N]) (Y, Z))) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  apply XM.
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
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

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
  rewrite (@naturality
             _ _ _ _ (@ap_functor_nat _ _ _ _ _ N)
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@naturality
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
Next Obligation.
  rewrite lax_monoidal_unit_left.
  rewrite lax_monoidal_unit_left.
  rewrite !comp_assoc.
  rewrite fmap_comp.
  symmetry.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  pose proof (naturality[ap_functor_nat] (I, G X) (G I, G X)
                        (lax_pure, id[G X])).
  simpl in X0.
  rewrite !bimap_fmap in X0.
  rewrite comp_assoc.
  rewrite X0; clear X0.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  rewrite lax_monoidal_unit_right.
  rewrite lax_monoidal_unit_right.
  rewrite !comp_assoc.
  rewrite fmap_comp.
  symmetry.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  pose proof (naturality[ap_functor_nat] (G X, I) (G X, G I)
                        (id[G X], lax_pure)).
  simpl in X0.
  rewrite !bimap_fmap in X0.
  rewrite comp_assoc.
  rewrite X0; clear X0.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  pose proof (naturality[ap_functor_nat[M]]
                        (G X ⨂ G Y, G Z) (G (X ⨂ Y), G Z)
                        (transform[ap_functor_nat] (X, Y), id[G Z])) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- XM; clear XM.

  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  pose proof (@lax_monoidal_assoc _ _ _ _ G _ X Y Z) as XG; simpl in XG.
  rewrite XG; clear XG.

  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.

  pose proof (@lax_monoidal_assoc _ _ _ _ F _ (G X) (G Y) (G Z)) as XF;
  simpl in XF.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ _ (bimap _ _)).
  rewrite XF; clear XF.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].

  pose proof
       (naturality[ap_functor_nat[M]]
                  (G X, G Y ⨂ G Z) (G X, G (Y ⨂ Z))
                  (id[G X], transform[ap_functor_nat[N]] (Y, Z))) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  apply XM.
Qed.

End MonoidalFunctors.

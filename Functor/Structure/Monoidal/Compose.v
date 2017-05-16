Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section MonoidalFunctors.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{D : Category}.
Context `{@Monoidal D}.
Context `{G : C ⟶ D}.

Context `{E : Category}.
Context `{@Monoidal E}.
Context `{F : D ⟶ E}.

Local Obligation Tactic := program_simpl.

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
  transitivity (F (I ⨂ G X))%object.
    transitivity (F (G X)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_iso_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I))%object.
    transitivity (F (G X))%object.
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_iso_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z))%object.
    apply ap_iso_assoc.
  apply fmap_iso.
  transitivity ((G X ⨂ G Y) ⨂ G Z)%object.
    symmetry.
    apply tensor_assoc.
  apply ap_iso_assoc.
Qed.
Next Obligation.
  rewrite monoidal_unit_left.
  rewrite monoidal_unit_left.
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
                        (G X ⨂ G Y, G Z)%object
                        (G (X ⨂ Y), G Z)%object
                        (to ap_functor_iso (X, Y), id[G Z])) as XM;
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
                  (G X, G Y ⨂ G Z)%object
                  (G X, G (Y ⨂ Z))%object
                  (id[G X], to ap_functor_iso[N] (Y, Z))) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  apply XM.
Qed.

(* Likewise, any two lax monoidal functors compose to create a lax monoidal
   functor. This is composition in the category of categories with monoidal
   structure. *)

Global Program Instance Compose_LaxMonoidalFunctor
       `(M : @LaxMonoidalFunctor D E _ _ F)
       `(N : @LaxMonoidalFunctor C D _ _ G) :
  `{@LaxMonoidalFunctor C E _ _ (F ○ G)} := {
  lax_pure := fmap lax_pure ∘ lax_pure;
  ap_functor_nat := {| transform := fun p =>
    fmap lax_ap ∘ @lax_ap _ _ _ _ F _ (G (fst p)) (G (snd p)) |}
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
  transitivity (F (I ⨂ G X))%object.
    transitivity (F (G X)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I))%object.
    transitivity (F (G X)).
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z))%object.
    apply ap_assoc.
  apply fmap_iso.
  transitivity ((G X ⨂ G Y) ⨂ G Z)%object.
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
                        (G X ⨂ G Y, G Z)%object
                        (G (X ⨂ Y), G Z)%object
                        (ap_functor_nat (X, Y), id[G Z])) as XM;
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
                  (G X, G Y ⨂ G Z)%object
                  (G X, G (Y ⨂ Z))%object
                  (id[G X], ap_functor_nat[N] (Y, Z))) as XM;
  simpl in XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  apply XM.
Qed.

End MonoidalFunctors.

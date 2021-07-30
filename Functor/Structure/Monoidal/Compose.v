Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section MonoidalFunctors.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {G : C ⟶ D}.

Context {E : Category}.
Context `{@Monoidal E}.
Context {F : D ⟶ E}.

Local Obligation Tactic := program_simpl.

(* Any two monoidal functors compose to create a monoidal functor. This is
   composition in the groupoid of categories with monoidal structure. *)

Global Program Instance Compose_MonoidalFunctor
       `(M : @MonoidalFunctor D E _ _ F)
       `(N : @MonoidalFunctor C D _ _ G) :
  `{@MonoidalFunctor C E _ _ (F ◯ G)} := {
  pure_iso := iso_compose (fmap_iso F _ _ (@pure_iso _ _ _ _ G _))
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
  rewrite (@naturality _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ N))
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@naturality _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites; reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@naturality _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ N))
             (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  pose proof (@naturality _ _ _ _ (to (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites; reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  pose proof (@naturality _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- (@naturality _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ N))
                (o1, o2) (o, o0) (h, h0)).
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  pose proof (@naturality _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ M))
                (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- (@naturality _ _ _ _ (from (@ap_functor_iso _ _ _ _ _ N))
                (o1, o2) (o, o0) (h, h0)).
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite fmap_id.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (transform[@to _ _ _ (@ap_functor_iso _ _ _ _ _ M)]
                                (G o, G o0))).
  pose proof (@iso_to_from _ _ _ (@ap_functor_iso _ _ _ _ _ M) (G o, G o0)).
  rewrites; simpl.
  rewrite !fmap_id, id_left.
  rewrite <- !fmap_comp.
  rewrite (@iso_to_from _ _ _ (@ap_functor_iso _ _ _ _ _ N) (o, o0)).
  simpl.
  rewrite !fmap_id.
  reflexivity.
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
  transitivity (F (I ⨂ G x))%object.
    transitivity (F (G x)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_iso_left.
Qed.
Next Obligation.
  transitivity (F (G x ⨂ I))%object.
    transitivity (F (G x))%object.
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_iso_right.
Qed.
Next Obligation.
  transitivity (F (G x ⨂ G y ⨂ G z))%object.
    apply ap_iso_assoc.
  apply fmap_iso.
  transitivity ((G x ⨂ G y) ⨂ G z)%object.
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
  spose (naturality[to ap_functor_iso] (I, G x) (G I, G x)
                   (to pure_iso, id[G x])) as X.
  rewrite !bimap_fmap in X.
  rewrite comp_assoc.
  rewrites.
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
  spose (naturality[to ap_functor_iso] (G x, I) (G x, G I)
                   (id[G x], to pure_iso)) as X.
  rewrite !bimap_fmap in X.
  rewrite comp_assoc.
  rewrites.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  spose (naturality[to (ap_functor_iso[M])]
                   (G x ⨂ G y, G z)%object
                   (G (x ⨂ y), G z)%object
                   (to ap_functor_iso (x, y), id[G z])) as XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrites.

  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  spose (@monoidal_assoc _ _ _ _ G _ x y z) as XG.
  rewrites.

  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.

  spose (@monoidal_assoc _ _ _ _ F _ (G x) (G y) (G z)) as XF.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ _ (bimap _ _)).
  rewrites.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].

  spose (naturality[to (ap_functor_iso[M])]
                   (G x, G y ⨂ G z)%object
                   (G x, G (y ⨂ z))%object
                   (id[G x], to ap_functor_iso[N] (y, z))) as XM.
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
  `{@LaxMonoidalFunctor C E _ _ (F ◯ G)} := {
  lax_pure := fmap lax_pure ∘ lax_pure;
  ap_functor_nat := {| transform := fun p =>
    fmap lax_ap ∘ @lax_ap _ _ _ _ F _ (G (fst p)) (G (snd p)) |}
}.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@naturality _ _ _ _ (@ap_functor_nat _ _ _ _ _ N)
                       (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  spose (@naturality _ _ _ _ (@ap_functor_nat _ _ _ _ _ M)
                     (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites; reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@naturality _ _ _ _ (@ap_functor_nat _ _ _ _ _ N)
                       (o1, o2) (o, o0) (h, h0)).
  simpl.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  spose (@naturality _ _ _ _ (@ap_functor_nat _ _ _ _ _ M)
                     (G o1, G o2) (G o, G o0) (fmap h, fmap h0)) as X.
  rewrites; reflexivity.
Qed.
Next Obligation.
  transitivity (F (I ⨂ G x))%object.
    transitivity (F (G x)).
      apply unit_left.
    apply fmap_iso.
    symmetry.
    apply unit_left.
  apply fmap_iso.
  apply pure_left.
Qed.
Next Obligation.
  transitivity (F (G x ⨂ I))%object.
    transitivity (F (G x)).
      apply unit_right.
    apply fmap_iso.
    symmetry.
    apply unit_right.
  apply fmap_iso.
  apply pure_right.
Qed.
Next Obligation.
  transitivity (F (G x ⨂ G y ⨂ G z))%object.
    apply ap_assoc.
  apply fmap_iso.
  transitivity ((G x ⨂ G y) ⨂ G z)%object.
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
  spose (naturality[ap_functor_nat] (I, G x) (G I, G x)
                   (lax_pure, id[G x])) as X.
  rewrite !bimap_fmap in X.
  rewrite comp_assoc.
  rewrites.
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
  spose (naturality[ap_functor_nat] (G x, I) (G x, G I)
                   (id[G x], lax_pure)) as X.
  rewrite !bimap_fmap in X.
  rewrite comp_assoc.
  rewrites.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  unfold fmap_iso; simpl.
  rewrite fmap_id.
  reflexivity.
Qed.
Next Obligation.
  spose (naturality[ap_functor_nat[M]]
                   (G x ⨂ G y, G z)%object
                   (G (x ⨂ y), G z)%object
                   (ap_functor_nat (x, y), id[G z])) as XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrites.

  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  spose (@lax_monoidal_assoc _ _ _ _ G _ x y z) as XG.
  rewrites.

  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.

  spose (@lax_monoidal_assoc _ _ _ _ F _ (G x) (G y) (G z)) as XF.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ _ (bimap _ _)).
  rewrites.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].

  spose (naturality[ap_functor_nat[M]]
                   (G x, G y ⨂ G z)%object
                   (G x, G (y ⨂ z))%object
                   (id[G x], ap_functor_nat[N] (y, z))) as XM.
  rewrite !bimap_fmap in XM.
  rewrite fmap_id in XM.
  apply XM.
Qed.

End MonoidalFunctors.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Monoidal.
Require Export Category.Construction.Groupoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section MonoidalFunctor.

Context `{C : Category}.
Context `{D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context `{F : C ⟶ D}.

(* A lax monoidal functor's natural transformation can be projected to a
   morphism between objects in D. This forgets the naturality of the
   transformation, which is why it is only provided as a convenience
   definition below in [LaxMonoidalFunctor]. *)

Class LaxMonoidalFunctor := {
  pure : I ~> F I;

  ap_functor_nat :
    (@functor_comp (C × C) (D × D) D (@tensor D _) (split F F))
      ~{[C × C, D]}~>
    (@functor_comp (C × C) C D F (@tensor C _));

  ap {X Y} : F X ⨂ F Y ~> F (X ⨂ Y) := transform[ap_functor_nat] (X, Y);

  pure_left {X}  : I ⨂ F X ≈ F (I ⨂ X);
  pure_right {X} : F X ⨂ I ≈ F (X ⨂ I);

  ap_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

(* The strong monoidal functor isomorphism can be projected to an isomorphism
   between objects in D. This forgets the naturality of the original natural
   isomorphism, which is why it is only provided as a convenience definition
   below in [StrongMonoidalFunctor]. *)

Program Definition project_monoidal_iso
        (iso : (@functor_comp (C × C) (D × D) D
                              (@tensor D _) (split F F))
                 ≅[[C × C, D]]
               (@functor_comp (C × C) C D F (@tensor C _)))
        (X Y : C) :
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

  ap_functor_iso :
    (@functor_comp (C × C) (D × D) D (@tensor D _) (split F F))
      ≅[[C × C, D]]
    (@functor_comp (C × C) C D F (@tensor C _));

  ap_iso {X Y} : F X ⨂ F Y ≅ F (X ⨂ Y) :=
    project_monoidal_iso ap_functor_iso X Y;

  pure_iso_left {X}  : I ⨂ F X ≈ F (I ⨂ X);
  pure_iso_right {X} : F X ⨂ I ≈ F (X ⨂ I);

  ap_iso_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.

End MonoidalFunctor.

Notation "pure[ F ]" := (@pure _ _ _ _ F _) (at level 9, format "pure[ F ]").
Notation "ap[ F ]" := (@ap _ _ _ _ F _ _ _) (at level 9, format "ap[ F ]").

Section MonoidalFunctorComposition.

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

Global Program Instance MonoidalFunctor_compose
       `(M : @MonoidalFunctor D E _ _ F)
       `(N : @MonoidalFunctor C D _ _ G) :
  `{@MonoidalFunctor C E _ _ (F ○ G)} := {
  pure_iso := compose_iso (fmap_iso F (@pure_iso _ _ _ _ G _))
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
    simpl in X1; rewrite X1.
      pose proof (@fmap_id _ _ (@tensor E H1)) as X2.
      simpl in X2; rewrite X2.
      pose proof (@fmap_respects _ _ (@tensor E H1)) as X3.
      simpl in X3; rewrite X3.
        rewrite X2.
        reflexivity.
      simpl; split;
      apply fmap_id.
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
    apply fobj_respects.
    symmetry.
    apply unit_left.
  apply fobj_respects.
  apply pure_iso_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I)).
    transitivity (F (G X)).
      apply unit_right.
    apply fobj_respects.
    symmetry.
    apply unit_right.
  apply fobj_respects.
  apply pure_iso_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z)).
    apply ap_iso_assoc.
  apply fobj_respects.
  transitivity ((G X ⨂ G Y) ⨂ G Z).
    symmetry.
    apply tensor_assoc.
  apply ap_iso_assoc.
Qed.

(* Likewise, any two lax monoidal functors compose to create a lax monoidal
   functor. This is composition in the category of categories with monoidal
   structure. *)

Global Program Instance LaxMonoidalFunctor_compose
       `(M : @LaxMonoidalFunctor D E _ _ F)
       `(N : @LaxMonoidalFunctor C D _ _ G) :
  `{@LaxMonoidalFunctor C E _ _ (F ○ G)} := {
  pure := fmap pure ∘ pure;
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
    apply fobj_respects.
    symmetry.
    apply unit_left.
  apply fobj_respects.
  apply pure_left.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ I)).
    transitivity (F (G X)).
      apply unit_right.
    apply fobj_respects.
    symmetry.
    apply unit_right.
  apply fobj_respects.
  apply pure_right.
Qed.
Next Obligation.
  transitivity (F (G X ⨂ G Y ⨂ G Z)).
    apply ap_assoc.
  apply fobj_respects.
  transitivity ((G X ⨂ G Y) ⨂ G Z).
    symmetry.
    apply tensor_assoc.
  apply ap_assoc.
Qed.

Global Program Instance StrongFunctor_compose (S : C ⟶ C)
       `{@StrongFunctor C _ S} :
  `{@StrongFunctor C _ (S ○ S)} := {
  strength := fun _ _ => fmap[S] strength ∘ strength
}.

End MonoidalFunctorComposition.

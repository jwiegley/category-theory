Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.

Generalizable All Variables.

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(* A universal arrow is an initial object in the comma category (=(c) ↓ F). *)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(* The following UMP follows directly from the nature of initial objects in a
   comma category. *)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((ttt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
  - assumption.
  - intros.
    rewrite <- id_right in e.
    rewrite <- id_right in X.
    exact (snd (@zero_unique _ arrow_initial ((ttt, d); h)
                             ((ttt, h1); e) ((ttt, v); X))).
Qed.

Definition universal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D) (η : c ~> fobj[F] d)
  (u : ∀ (d' : D) (f : c ~> fobj[F] d'), ∃! g : d ~> d', f ≈ fmap[F] g ∘ η)
  : UniversalArrow c F.
Proof.
  unshelve eapply Build_UniversalArrow. simpl. unshelve esplit.
  - simpl. unshelve esplit; [ split; [ exact ttt | exact d ] | exact η ].
  - simpl. intros [ [unit d'] f]; simpl in *.
    unshelve esplit; [ split ; [ exact ttt | exact (unique_obj (u d' f))] | ].
    rewrite id_right; simpl. exact (unique_property (u d' f)).
  - simpl. intros [[unit d']  f]; simpl in *.
    intros [[unit2 g] g_eq]. simpl in g_eq.
    intros [[unit3 h] h_eq]. split.
    + simpl. destruct unit2, unit3; reflexivity.
    + simpl. rewrite id_right in g_eq, h_eq. simpl in h_eq.
      rewrite <- (uniqueness (u d' f) _ g_eq).
      exact (uniqueness (u d' f) _ h_eq).
Defined.

Context (U : @Functor D C).

Arguments arrow : clear implicits.
Arguments arrow_obj : clear implicits.
Definition LeftAdjointFunctorFromUniversalArrows (H : forall c : C, UniversalArrow c U) 
  : @Functor C D.
Proof.
  refine
    ({|
        fobj := (fun c => arrow_obj _ _ (H c));
        fmap := (fun x y f => unique_obj (ump_universal_arrows (H x)
                                            ((arrow _ _ (H y) ∘ f))))
                  
      |}).
  - abstract(intros x y f g f_eq_g;
             apply uniqueness;
             rewrite <- (unique_property
                  (ump_universal_arrows (H x) (arrow y U (H y) ∘ g)));
             now rewrite f_eq_g).
  - abstract(intros ?; apply uniqueness; cat_simpl).
  - abstract(intros c1 c2 c3 g f; apply uniqueness;
      rewrite fmap_comp,
      <- comp_assoc,
      <- (unique_property (ump_universal_arrows (H c1) _)),
      2! comp_assoc;
      exact (compose_respects _ _
             (unique_property (ump_universal_arrows (H c2) _))
             f f (Equivalence_Reflexive _))).
Defined.

Definition AdjunctionFromUniversalArrows (H: forall c : C, UniversalArrow c U) :
  @Adjunction _ _ (LeftAdjointFunctorFromUniversalArrows H) U.
Proof.
  unshelve eapply Build_Adjunction'.
  + intros c d; unshelve eapply Isomorphism.Build_Isomorphism.
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact (fun g => (fmap[U] g) ∘ (arrow _ _ (H c))).
    * abstract(intros ? ? g1_eq_g2; rewrite g1_eq_g2; reflexivity).
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact(fun f => unique_obj (ump_universal_arrows (H c) f)).
    * abstract(intros f1 f2 f1_eq_f2; apply uniqueness; rewrite f1_eq_f2;
               apply (unique_property (ump_universal_arrows (H c) f2))).
  - abstract(intro f; symmetry; exact (unique_property (ump_universal_arrows (H c) f))).
  - abstract(simpl; intro g; apply uniqueness; reflexivity).
  + abstract(intros c1 c2 d f g;
             simpl; rewrite fmap_comp, <- 2! comp_assoc;
             apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _) _ _);
             symmetry;
             apply (unique_property (ump_universal_arrows (H c1) _))).
  + abstract(intros ? ? ? ? ?; simpl; rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.

End UniversalArrow.

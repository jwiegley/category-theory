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
Context `{G : C ⟶ C}.

Local Obligation Tactic := program_simpl.

Lemma ProductFunctor_Strong_strength_nat :
  StrongFunctor F → StrongFunctor G
    → (⨂) ○ (Id[C ∏ C]) ∏⟶ (F ∏⟶ G) ⟹ F ∏⟶ G ○ (⨂).
Proof.
  intros O P.
  natural; simplify; intros;
  simplify; simpl in *; simplify; simpl in *.
  - exact (transform[@strength_nat _ _ _ O] (x1, x0)).
  - exact (transform[@strength_nat _ _ _ P] (y, y0)).
  - destruct O, strength_nat; simpl in *.
    abstract apply (naturality (x5, x4)).
  - destruct P, strength_nat; simpl in *.
    abstract apply (naturality (y3, y4)).
Defined.

Program Definition ProductFunctor_Strong :
  StrongFunctor F -> StrongFunctor G
    -> StrongFunctor (F ∏⟶ G) := fun O P => {|
  strength_nat := ProductFunctor_Strong_strength_nat O P;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation. split; apply strength_id_left. Qed.
Next Obligation. split; apply strength_assoc. Qed.

Lemma ProductFunctor_Strong_proj1_strength_nat :
  StrongFunctor F ∏⟶ G → (⨂) ○ (Id[C]) ∏⟶ F ⟹ F ○ (⨂).
Proof.
  intro P.
  destruct P.
  natural.
    intros [x y].
    exact (fst (transform[strength_nat] ((x, I), (y, I)))).
  destruct X as [x y].
  destruct Y as [z w].
  destruct f as [f g].
  exact (fst (naturality strength_nat (x, I, (y, I)) (z, I, (w, I))
                         ((f, id), (g, id)))).
Defined.

Program Definition ProductFunctor_Strong_proj1 :
  StrongFunctor (F ∏⟶ G) -> StrongFunctor F := fun P => {|
  strength_nat := ProductFunctor_Strong_proj1_strength_nat P;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (fst (@strength_id_left _ _ _ P (X, I))).
Qed.
Next Obligation.
  pose proof (@unit_left C H I) as X0.
  pose proof (fst (naturality (@strength_nat _ _ _ P)
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
  pose proof (fst (naturality (@strength_nat _ _ _ P)
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
  exact (fst (@strength_assoc _ _ _ P (X, I) (Y, I) (Z, I))).
Qed.

Lemma ProductFunctor_Strong_proj2_strength_nat :
  StrongFunctor F ∏⟶ G → (⨂) ○ (Id[C]) ∏⟶ G ⟹ G ○ (⨂).
Proof.
  intro P.
  destruct P.
  natural.
    intros [x y].
    exact (snd (transform[strength_nat] ((I, x), (I, y)))).
  destruct X as [x y].
  destruct Y as [z w].
  destruct f as [f g].
  exact (snd (naturality strength_nat (I, x, (I, y)) (I, z, (I, w))
                         ((id, f), (id, g)))).
Defined.

Program Definition ProductFunctor_Strong_proj2 :
  StrongFunctor (F ∏⟶ G) -> StrongFunctor G := fun P => {|
  strength_nat := ProductFunctor_Strong_proj2_strength_nat P;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (snd (@strength_id_left _ _ _ P (I, X))).
Qed.
Next Obligation.
  pose proof (@unit_left C H I) as X0.
  pose proof (snd (naturality (@strength_nat _ _ _ P)
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
  pose proof (snd (naturality (@strength_nat _ _ _ P)
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
  exact (snd (@strength_assoc _ _ _ P (I, X) (I, Y) (I, Z))).
Qed.

End ProductStrong.

Theorem ProductFunctor_fst_Strong
        `{C : Category} `{@Monoidal C}
        (P : (C ∏ C) ⟶ (C ∏ C)) :
  StrongFunctor P -> StrongFunctor (ProductFunctor_fst P).
Proof.
  unshelve econstructor; simpl.
  - natural; simplify; simpl; intros; simplify.
    + exact (fst (bimap id (to unit_left)
                    ∘ transform[@strength_nat _ _ _ X] ((x, I), (y, I)))).
    + simpl in *.
      pose proof (fst (naturality (@strength_nat _ _ _ X)
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

    pose proof (fst (naturality (@strength_nat _ _ _ X)
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

    pose proof (fst (naturality (@strength_nat _ _ _ X)
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
    revert X2.
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
Qed.

Theorem ProductFunctor_snd_Strong
        `{C : Category} `{@Monoidal C}
        (P : (C ∏ C) ⟶ (C ∏ C)) :
  StrongFunctor P -> StrongFunctor (ProductFunctor_snd P).
Proof.
  unshelve econstructor; simpl.
  - natural; simplify; simpl; intros; simplify.
    + exact (snd (bimap (to unit_left) id
                    ∘ transform[@strength_nat _ _ _ X] ((I, x), (I, y)))).
    + simpl in *.
      pose proof (snd (naturality (@strength_nat _ _ _ X)
                                  (I, x1, (I, y1)) (I, x0, (I, y0))
                                  ((id, x), (id, y)))) as X0.
      simpl in X0.
      rewrite comp_assoc.
      rewrite !bimap_fmap.
      rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite id_left, id_right.
      rewrite <- comp_assoc.
      rewrite <- X0.
      rewrite comp_assoc.
      rewrite snd_comp.
      rewrite bimap_fmap.
      rewrite <- bimap_comp.
      rewrite bimap_id_id.
      rewrite id_left, id_right.
      reflexivity.
  - simpl; intros.
    pose (snd (@strength_id_left _ _ _ X (I, X0))).
    rewrite comp_assoc.
    rewrite snd_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    simpl in e.
    rewrite e; clear e.
    destruct (P (I, X0)); reflexivity.
  - simpl; intros.
    rewrite !bimap_fmap.
    rewrite comp_assoc.
    rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.

    pose proof (snd (@strength_assoc _ _ _ X (I, X0) (I, Y) (I, Z))) as X2;
    simpl in X2.

    pose proof (snd (naturality (@strength_nat _ _ _ X)
                                (I, X0, (I ⨂ I, Y ⨂ Z))
                                (I, X0, (I, Y ⨂ Z))
                                ((id[I], id[X0]),
                                 (to unit_left, id[Y ⨂ Z])))) as X3.
    simpl in X3.
    rewrite !bimap_fmap in X3.
    rewrite bimap_id_id in X3.
    rewrite <- (id_right (id[X0])).
    rewrite bimap_comp.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc (snd _)).
    rewrite <- (comp_assoc (snd _)).
    rewrite <- X3; clear X3.

    pose proof (snd (naturality (@strength_nat _ _ _ X)
                                (I ⨂ I, X0 ⨂ Y, (I, Z))
                                (I, X0 ⨂ Y, (I, Z))
                                ((to unit_left, id[X0 ⨂ Y]),
                                 (id[I], id[Z])))) as X4.
    simpl in X4.
    rewrite !bimap_fmap in X4.
    rewrite !bimap_id_id in X4.
    rewrite id_right in X4.
    rewrite <- X4; clear X4.

    rewrite !comp_assoc.
    rewrite !snd_comp.
    rewrite <- !bimap_comp.
    rewrite !id_left, id_right.
    revert X2.
    replace (snd
               (let
                   (x, y) as p
                   return
                   (((I ⨂ I) ⨂ fst p ~{ C }~> I ⨂ I ⨂ fst p) *
                    ((X0 ⨂ Y) ⨂ snd p ~{ C }~> X0 ⨂ Y ⨂ snd p)) := P (I, Z) in
                 (to tensor_assoc, to tensor_assoc)))
      with (@to C ((X0 ⨂ Y) ⨂ (snd (P (I, Z))))
                (X0 ⨂ Y ⨂ (snd (P (I, Z))))
                (@tensor_assoc C H X0 Y (snd (P (I, Z))))).
      intros.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc _ (bimap _ _)).
      rewrite X2; clear X2.
      rewrite comp_assoc.
      rewrite snd_comp.
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
    destruct (P (I, Z)); reflexivity.
Qed.

Corollary ProductFunctor_proj_Strong `{C : Category} `{@Monoidal C}
          (P : (C ∏ C) ⟶ (C ∏ C)) :
  StrongFunctor P
    -> StrongFunctor ((ProductFunctor_fst P) ∏⟶ (ProductFunctor_snd P)).
Proof.
  intros.
  exact (ProductFunctor_Strong (ProductFunctor_fst_Strong _ _)
                               (ProductFunctor_snd_Strong _ _)).
Qed.

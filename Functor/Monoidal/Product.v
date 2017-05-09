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

Lemma ProductFunctor_Monoidal_ap_functor_iso :
  MonoidalFunctor F → MonoidalFunctor G
    → (⨂) ○ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ≅[[(D ∏ C) ∏ (D ∏ C), E ∏ D]] F ∏⟶ G ○ (⨂).
Proof.
  intros O P.
  isomorphism.

  natural.
    intros [[x z] [y w]]; split.
      exact (transform[to ap_functor_iso] (x, y)).
    exact (transform[to ap_functor_iso] (z, w)).

  all:(try destruct X as [[x1 x2] [y1 y2]],
                    Y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  split.
    abstract apply (naturality (to ap_functor_iso) (x1, y1)).
  abstract apply (naturality (to ap_functor_iso) (x2, y2)).

  natural.
    intros [[x z] [y w]]; split.
      exact (transform[from ap_functor_iso] (x, y)).
    exact (transform[from ap_functor_iso] (z, w)).

  all:(try destruct X as [[x1 x2] [y1 y2]],
                    Y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  split.
    abstract apply (naturality (from ap_functor_iso) (x1, y1) (z1, w1) (f1a, f2a)).
  abstract apply (naturality (from ap_functor_iso) (x2, y2) (z2, w2) (f1b, f2b)).

  split.
    pose proof (iso_to_from (ap_functor_iso[O])).
    simpl in X; abstract apply X.
  pose proof (iso_to_from (ap_functor_iso[P])).
  simpl in X; abstract apply X.

  split.
    pose proof (iso_from_to (ap_functor_iso[O]) (x, y)).
    simpl in X; abstract apply X.
  pose proof (iso_from_to (ap_functor_iso[P]) (z, w)).
  simpl in X; abstract apply X.
Time Defined.

Time Program Definition ProductFunctor_Monoidal_prod :
        MonoidalFunctor F -> MonoidalFunctor G
          -> MonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
  pure_iso := _;
  ap_functor_iso := ProductFunctor_Monoidal_ap_functor_iso _ _;
  pure_iso_left  := _;
  pure_iso_right := _;
  ap_iso_assoc := _;
  monoidal_unit_left := _;
  monoidal_unit_right := _;
  monoidal_assoc := _
|}.
Next Obligation.
  unshelve esplit; split; apply pure_iso.
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_iso_left || apply pure_iso_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply pure_iso_left || apply pure_iso_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply ap_iso_assoc.
Qed.
Next Obligation. intros; split; apply monoidal_unit_left. Qed.
Next Obligation. intros; split; apply monoidal_unit_right. Qed.
Next Obligation. intros; split; apply monoidal_assoc. Qed.

Lemma ProductFunctor_Monoidal_proj1_ap_functor_iso :
  MonoidalFunctor F ∏⟶ G
    → (⨂) ○ F ∏⟶ F ≅[[(D ∏ D), E]] F ○ (⨂).
Proof.
  intros P.

  isomorphism.

  natural.
    intros [x y].
    exact (fst (transform[to (ap_functor_iso[P])] ((x, I), (y, I)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (fst (naturality (to (ap_functor_iso[P]))
                         (x, I, (y, I)) (z, I, (w, I))
                         ((f, id), (g, id)))).

  natural.
    intros [x y].
    exact (fst (transform[from (ap_functor_iso[P])] ((x, I), (y, I)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (fst (naturality (from (ap_functor_iso[P]))
                         (x, I, (y, I)) (z, I, (w, I))
                         ((f, id), (g, id)))).

  apply (iso_to_from (ap_functor_iso[P]) (x, I, (y, I))).
  apply (iso_from_to (ap_functor_iso[P]) (x, I, (y, I))).
Defined.

Program Definition ProductFunctor_Monoidal_proj1 :
  MonoidalFunctor (F ∏⟶ G) -> MonoidalFunctor F := fun P => {|
  pure_iso := _;
  ap_functor_iso := ProductFunctor_Monoidal_proj1_ap_functor_iso P;
  pure_iso_left  := _;
  pure_iso_right := _;
  ap_iso_assoc := _;
  monoidal_unit_left := _;
  monoidal_unit_right := _;
  monoidal_assoc := _
|}.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_iso _ _ _ _ _ P))).
  apply (fst (from (@pure_iso _ _ _ _ _ P))).
  apply (fst (iso_to_from (@pure_iso _ _ _ _ _ P))).
  apply (fst (iso_from_to (@pure_iso _ _ _ _ _ P))).
Defined.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_iso_left _ _ _ _ _ P (X, I)))).
  apply (fst (from (@pure_iso_left _ _ _ _ _ P (X, I)))).
  apply (fst (iso_to_from (@pure_iso_left _ _ _ _ _ P (X, I)))).
  apply (fst (iso_from_to (@pure_iso_left _ _ _ _ _ P (X, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_iso_right _ _ _ _ _ P (X, I)))).
  apply (fst (from (@pure_iso_right _ _ _ _ _ P (X, I)))).
  apply (fst (iso_to_from (@pure_iso_right _ _ _ _ _ P (X, I)))).
  apply (fst (iso_from_to (@pure_iso_right _ _ _ _ _ P (X, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@ap_iso_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (from (@ap_iso_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_left _ _ _ _ _ P (X, I))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_right _ _ _ _ _ P (X, I))).
Qed.
Next Obligation.
  pose proof (fst (naturality (to ap_functor_iso[P])
                              ((X ⨂ Y, I ⨂ I), (Z, I))
                              ((X ⨂ Y, I), (Z, I))
                              ((id[X ⨂ Y], to unit_left),
                               (id[Z], id[I])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (fst (naturality (to ap_functor_iso[P])
                              ((X, I), (Y ⨂ Z, I ⨂ I))
                              ((X, I), (Y ⨂ Z, I))
                              ((id[X], id[I]),
                               (id[Y ⨂ Z], to unit_left)))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  apply (fst (@monoidal_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I))).
Qed.

Lemma ProductFunctor_Monoidal_proj2_ap_functor_iso :
  MonoidalFunctor F ∏⟶ G
    → (⨂) ○ G ∏⟶ G ≅[[(C ∏ C), D]] G ○ (⨂).
Proof.
  intros P.

  isomorphism.

  natural.
    intros [x y].
    exact (snd (transform[to (ap_functor_iso[P])] ((I, x), (I, y)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (snd (naturality (to (ap_functor_iso[P]))
                         (I, x, (I, y)) (I, z, (I, w))
                         ((id, f), (id, g)))).

  natural.
    intros [x y].
    exact (snd (transform[from (ap_functor_iso[P])] ((I, x), (I, y)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (snd (naturality (from (ap_functor_iso[P]))
                         (I, x, (I, y)) (I, z, (I, w))
                         ((id, f), (id, g)))).

  apply (iso_to_from (ap_functor_iso[P]) (I, x, (I, y))).
  apply (iso_from_to (ap_functor_iso[P]) (I, x, (I, y))).
Defined.

Program Definition ProductFunctor_Monoidal_proj2 :
  MonoidalFunctor (F ∏⟶ G) -> MonoidalFunctor G := fun P => {|
  pure_iso := _;
  ap_functor_iso := ProductFunctor_Monoidal_proj2_ap_functor_iso P;
  pure_iso_left  := _;
  pure_iso_right := _;
  ap_iso_assoc := _;
  monoidal_unit_left := _;
  monoidal_unit_right := _;
  monoidal_assoc := _
|}.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_iso _ _ _ _ _ P))).
  apply (snd (from (@pure_iso _ _ _ _ _ P))).
  apply (snd (iso_to_from (@pure_iso _ _ _ _ _ P))).
  apply (snd (iso_from_to (@pure_iso _ _ _ _ _ P))).
Defined.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_iso_left _ _ _ _ _ P (I, X)))).
  apply (snd (from (@pure_iso_left _ _ _ _ _ P (I, X)))).
  apply (snd (iso_to_from (@pure_iso_left _ _ _ _ _ P (I, X)))).
  apply (snd (iso_from_to (@pure_iso_left _ _ _ _ _ P (I, X)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_iso_right _ _ _ _ _ P (I, X)))).
  apply (snd (from (@pure_iso_right _ _ _ _ _ P (I, X)))).
  apply (snd (iso_to_from (@pure_iso_right _ _ _ _ _ P (I, X)))).
  apply (snd (iso_from_to (@pure_iso_right _ _ _ _ _ P (I, X)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@ap_iso_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (from (@ap_iso_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_left _ _ _ _ _ P (I, X))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_right _ _ _ _ _ P (I, X))).
Qed.
Next Obligation.
  pose proof (snd (naturality (to ap_functor_iso[P])
                              ((I ⨂ I, X ⨂ Y), (I, Z))
                              ((I, X ⨂ Y), (I, Z))
                              ((to unit_left, id[X ⨂ Y]),
                               (id[I], id[Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (snd (naturality (to ap_functor_iso[P])
                              ((I, X), (I ⨂ I, Y ⨂ Z))
                              ((I, X), (I, Y ⨂ Z))
                              ((id[I], id[X]),
                               (to unit_left, id[Y ⨂ Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  apply (snd (@monoidal_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z))).
Qed.

Lemma ProductFunctor_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor F → LaxMonoidalFunctor G
    → (⨂) ○ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ⟹ F ∏⟶ G ○ (⨂).
Proof.
  intros O P.

  natural.
    intros [[x z] [y w]]; split.
      exact (transform[ap_functor_nat] (x, y)).
    exact (transform[ap_functor_nat] (z, w)).

  all:(try destruct X as [[x1 x2] [y1 y2]],
                    Y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  split.
    abstract apply (naturality ap_functor_nat (x1, y1)).
  abstract apply (naturality ap_functor_nat (x2, y2)).
Defined.

Program Definition ProductFunctor_LaxMonoidal_prod :
        LaxMonoidalFunctor F -> LaxMonoidalFunctor G
          -> LaxMonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_LaxMonoidal_ap_functor_nat _ _;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  unshelve esplit; apply lax_pure.
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_left || apply pure_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply pure_left || apply pure_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply ap_assoc.
Qed.
Next Obligation. intros; split; apply lax_monoidal_unit_left. Qed.
Next Obligation. intros; split; apply lax_monoidal_unit_right. Qed.
Next Obligation. intros; split; apply lax_monoidal_assoc. Qed.

Lemma ProductFunctor_LaxMonoidal_proj1_ap_functor_nat :
  LaxMonoidalFunctor F ∏⟶ G
    → (⨂) ○ F ∏⟶ F ⟹ F ○ (⨂).
Proof.
  intros P.

  natural.
    intros [x y].
    exact (fst (transform[ap_functor_nat[P]] ((x, I), (y, I)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (fst (naturality (ap_functor_nat[P])
                         (x, I, (y, I)) (z, I, (w, I))
                         ((f, id), (g, id)))).
Defined.

Program Definition ProductFunctor_LaxMonoidal_proj1 :
  LaxMonoidalFunctor (F ∏⟶ G) -> LaxMonoidalFunctor F := fun P => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_LaxMonoidal_proj1_ap_functor_nat P;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  apply (fst (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_left _ _ _ _ _ P (X, I)))).
  apply (fst (from (@pure_left _ _ _ _ _ P (X, I)))).
  apply (fst (iso_to_from (@pure_left _ _ _ _ _ P (X, I)))).
  apply (fst (iso_from_to (@pure_left _ _ _ _ _ P (X, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_right _ _ _ _ _ P (X, I)))).
  apply (fst (from (@pure_right _ _ _ _ _ P (X, I)))).
  apply (fst (iso_to_from (@pure_right _ _ _ _ _ P (X, I)))).
  apply (fst (iso_from_to (@pure_right _ _ _ _ _ P (X, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@ap_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (from (@ap_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (iso_to_from (@ap_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
  apply (fst (iso_from_to (@ap_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I)))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_left _ _ _ _ _ P (X, I))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_right _ _ _ _ _ P (X, I))).
Qed.
Next Obligation.
  pose proof (fst (naturality (ap_functor_nat[P])
                              ((X ⨂ Y, I ⨂ I), (Z, I))
                              ((X ⨂ Y, I), (Z, I))
                              ((id[X ⨂ Y], to unit_left),
                               (id[Z], id[I])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (fst (naturality (ap_functor_nat[P])
                              ((X, I), (Y ⨂ Z, I ⨂ I))
                              ((X, I), (Y ⨂ Z, I))
                              ((id[X], id[I]),
                               (id[Y ⨂ Z], to unit_left)))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  apply (fst (@lax_monoidal_assoc _ _ _ _ _ P (X, I) (Y, I) (Z, I))).
Qed.

Lemma ProductFunctor_LaxMonoidal_proj2_ap_functor_nat :
  LaxMonoidalFunctor F ∏⟶ G
    → (⨂) ○ G ∏⟶ G ⟹ G ○ (⨂).
Proof.
  intros P.

  natural.
    intros [x y].
    exact (snd (transform[ap_functor_nat[P]] ((I, x), (I, y)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (snd (naturality (ap_functor_nat[P])
                         (I, x, (I, y)) (I, z, (I, w))
                         ((id, f), (id, g)))).
Defined.

Program Definition ProductFunctor_LaxMonoidal_proj2 :
  LaxMonoidalFunctor (F ∏⟶ G) -> LaxMonoidalFunctor G := fun P => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_LaxMonoidal_proj2_ap_functor_nat P;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  apply (snd (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_left _ _ _ _ _ P (I, X)))).
  apply (snd (from (@pure_left _ _ _ _ _ P (I, X)))).
  apply (snd (iso_to_from (@pure_left _ _ _ _ _ P (I, X)))).
  apply (snd (iso_from_to (@pure_left _ _ _ _ _ P (I, X)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_right _ _ _ _ _ P (I, X)))).
  apply (snd (from (@pure_right _ _ _ _ _ P (I, X)))).
  apply (snd (iso_to_from (@pure_right _ _ _ _ _ P (I, X)))).
  apply (snd (iso_from_to (@pure_right _ _ _ _ _ P (I, X)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@ap_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (from (@ap_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (iso_to_from (@ap_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
  apply (snd (iso_from_to (@ap_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z)))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_left _ _ _ _ _ P (I, X))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_right _ _ _ _ _ P (I, X))).
Qed.
Next Obligation.
  pose proof (snd (naturality (ap_functor_nat[P])
                              ((I ⨂ I, X ⨂ Y), (I, Z))
                              ((I, X ⨂ Y), (I, Z))
                              ((to unit_left, id[X ⨂ Y]),
                               (id[I], id[Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (snd (naturality (ap_functor_nat[P])
                              ((I, X), (I ⨂ I, Y ⨂ Z))
                              ((I, X), (I, Y ⨂ Z))
                              ((id[I], id[X]),
                               (to unit_left, id[Y ⨂ Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  apply (snd (@lax_monoidal_assoc _ _ _ _ _ P (I, X) (I, Y) (I, Z))).
Qed.

End ProductMonoidal.

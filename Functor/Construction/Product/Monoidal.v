Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Product.
Require Export Category.Functor.Structure.Monoidal.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductMonoidal.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{D : Category}.
Context `{@Monoidal D}.
Context `{J : Category}.
Context `{@Monoidal J}.
Context `{K : Category}.
Context `{@Monoidal K}.

Context `{F : C ⟶ J}.
Context `{G : D ⟶ K}.

Local Obligation Tactic := program_simpl.

Lemma ProductFunctor_Monoidal_ap_functor_iso :
  MonoidalFunctor F → MonoidalFunctor G
    → (⨂) ○ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ≅[[(C ∏ D) ∏ (C ∏ D), J ∏ K]] F ∏⟶ G ○ (⨂).
Proof.
  intros O P.
  isomorphism.

  transform.
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

  transform.
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

Program Definition ProductFunctor_Monoidal :
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
    → (⨂) ○ F ∏⟶ F ≅[[(C ∏ C), J]] F ○ (⨂).
Proof.
  intros P.

  isomorphism.

  transform.
    intros [x y].
    exact (fst (transform[to (ap_functor_iso[P])] ((x, I), (y, I)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (fst (naturality (to (ap_functor_iso[P]))
                         (x, I, (y, I)) (z, I, (w, I))
                         ((f, id), (g, id)))).

  transform.
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
                              ((X ⨂ Y, I ⨂ I), (Z, I))%object
                              ((X ⨂ Y, I), (Z, I))%object
                              ((id[X ⨂ Y], to unit_left),
                               (id[Z], id[I])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (fst (naturality (to ap_functor_iso[P])
                              ((X, I), (Y ⨂ Z, I ⨂ I))%object
                              ((X, I), (Y ⨂ Z, I))%object
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
    → (⨂) ○ G ∏⟶ G ≅[[(D ∏ D), K]] G ○ (⨂).
Proof.
  intros P.

  isomorphism.

  transform.
    intros [x y].
    exact (snd (transform[to (ap_functor_iso[P])] ((I, x), (I, y)))).

  all:(try destruct X as [x y],
                    Y as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  exact (snd (naturality (to (ap_functor_iso[P]))
                         (I, x, (I, y)) (I, z, (I, w))
                         ((id, f), (id, g)))).

  transform.
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
                              ((I ⨂ I, X ⨂ Y), (I, Z))%object
                              ((I, X ⨂ Y), (I, Z))%object
                              ((to unit_left, id[X ⨂ Y]),
                               (id[I], id[Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (snd (naturality (to ap_functor_iso[P])
                              ((I, X), (I ⨂ I, Y ⨂ Z))%object
                              ((I, X), (I, Y ⨂ Z))%object
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

  transform.
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

Program Definition ProductFunctor_LaxMonoidal :
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

  transform.
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
                              ((X ⨂ Y, I ⨂ I), (Z, I))%object
                              ((X ⨂ Y, I), (Z, I))%object
                              ((id[X ⨂ Y], to unit_left),
                               (id[Z], id[I])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (fst (naturality (ap_functor_nat[P])
                              ((X, I), (Y ⨂ Z, I ⨂ I))%object
                              ((X, I), (Y ⨂ Z, I))%object
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

  transform.
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
                              ((I ⨂ I, X ⨂ Y), (I, Z))%object
                              ((I, X ⨂ Y), (I, Z))%object
                              ((to unit_left, id[X ⨂ Y]),
                               (id[I], id[Z])))); simpl in X0.
  rewrite !fmap_id in X0.
  rewrite !bimap_id_id in X0.
  rewrite !fmap_id in X0.
  rewrite id_left, id_right in X0.
  rewrite <- X0; clear X0.

  pose proof (snd (naturality (ap_functor_nat[P])
                              ((I, X), (I ⨂ I, Y ⨂ Z))%object
                              ((I, X), (I, Y ⨂ Z))%object
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

Section ProductMonoidalProj.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{D : Category}.
Context `{@Monoidal D}.
Context `{J : Category}.
Context `{@Monoidal J}.
Context `{K : Category}.
Context `{@Monoidal K}.

Variable (P : (C ∏ J) ⟶ D ∏ K).

Lemma ProductFunctor_fst_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor P
    → (⨂) ○ (ProductFunctor_fst P) ∏⟶ (ProductFunctor_fst P)
          ⟹ ProductFunctor_fst P ○ (⨂).
Proof.
  intro L.
  transform; simplify; simpl;
  intros; simplify; simpl.
    exact (fst (bimap id (to unit_left) ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((x, I), (y, I)))).
  simpl in *.
  pose proof (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
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
Defined.

Local Obligation Tactic := program_simpl.

Program Definition ProductFunctor_fst_LaxMonoidal :
  LaxMonoidalFunctor P
    -> LaxMonoidalFunctor (ProductFunctor_fst P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_fst_LaxMonoidal_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  exact (fst (@lax_pure _ _ _ _ _ L)).
Defined.
Next Obligation.
  destruct (@pure_left _ _ _ _ _ L (X, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (I ⨂ X, I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (X, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (X ⨂ I, I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (X, I) (Y, I) (Z, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (X ⨂ Y ⨂ Z, I ⨂ I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (to unit_left ∘ to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (from unit_left ∘ from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (from _)).
    rewrite iso_to_from.
    rewrite !id_left.
    rewrite iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (to _)).
    rewrite iso_from_to.
    rewrite !id_left.
    rewrite iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  unfold ProductFunctor_fst_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  pose proof (fst (@lax_monoidal_unit_left _ _ _ _ _ L (X, I))).
  simpl in X0.
  rewrite <- X0; clear X0.
  destruct (P (X, I)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_fst_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  pose proof (fst (@lax_monoidal_unit_right _ _ _ _ _ L (X, I))).
  simpl in X0.
  rewrite unit_identity.
  rewrite bimap_fmap in X0.
  rewrite <- X0; clear X0.
  destruct (P (X, I)).
  reflexivity.
Qed.
Next Obligation.
  pose proof (fst (@lax_monoidal_assoc _ _ _ _ _ L (X, I) (Y, I) (Z, I)));
  simpl in X0; revert X0.
  assert
    (fst (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (X, @I J H1)) (P (Y, @I J H1)) (P (Z, @I J H1))))
       = @to D _ _ (@tensor_assoc D H0 (fst (P (X, @I J H1)))
                                  (fst (P (Y, @I J H1))) (fst (P (Z, @I J H1))))).
    destruct (P (X, I)), (P (Y, I)), (P (Z, I)).
    reflexivity.
  srewrite H3; clear H3.
  pose proof (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                              (X, I, (Y ⨂ Z, I ⨂ I))%object
                              (X, I, (Y ⨂ Z, I))%object
                              ((id, id), (id, to unit_left)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[fst (P (X, I))] ≈ id[fst (P (X, I))] ∘ id[fst (P (X, I))]) by cat.
  intros.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X2; clear X2.
  rewrite !comp_assoc.
  rewrite !fst_comp.
  assert (id[fst (P (Z, I))] ≈ id[fst (P (Z, I))] ∘ id[fst (P (Z, I))]) by cat.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite !comp_assoc.
  apply compose_respects; [|cat].
  rewrite !bimap_fmap.
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  pose proof (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                              (X ⨂ Y, I ⨂ I, (Z, I))%object
                              (X ⨂ Y, I, (Z, I))%object
                              ((id, to unit_left), (id, id)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  rewrite <- X1; clear X1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite unit_identity.
  reflexivity.
Qed.

Lemma ProductFunctor_snd_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor P
    → (⨂) ○ (ProductFunctor_snd P) ∏⟶ (ProductFunctor_snd P)
          ⟹ ProductFunctor_snd P ○ (⨂).
Proof.
  intro L.
  transform; simplify; simpl;
  intros; simplify; simpl.
    exact (snd (bimap (to unit_left) id ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((I, x), (I, y)))).
  simpl in *.
  pose proof (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
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
Defined.

Program Definition ProductFunctor_snd_LaxMonoidal :
  LaxMonoidalFunctor P
    -> LaxMonoidalFunctor (ProductFunctor_snd P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_snd_LaxMonoidal_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  exact (snd (@lax_pure _ _ _ _ _ L)).
Defined.
Next Obligation.
  destruct (@pure_left _ _ _ _ _ L (I, X));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, I ⨂ X)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _ (to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _ (from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (I, X));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, X ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _ (to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _ (from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (I, X) (I, Y) (I, Z));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I ⨂ I, X ⨂ Y ⨂ Z)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _ (to unit_left ∘ to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _ (from unit_left ∘ from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (from _)).
    rewrite iso_to_from.
    rewrite !id_left.
    rewrite iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (to _)).
    rewrite iso_from_to.
    rewrite !id_left.
    rewrite iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  unfold ProductFunctor_snd_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  pose proof (snd (@lax_monoidal_unit_left _ _ _ _ _ L (I, X))).
  simpl in X0.
  rewrite <- X0; clear X0.
  destruct (P (I, X)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_snd_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  pose proof (snd (@lax_monoidal_unit_right _ _ _ _ _ L (I, X))).
  simpl in X0.
  rewrite unit_identity.
  rewrite bimap_fmap in X0.
  rewrite <- X0; clear X0.
  destruct (P (I, X)).
  reflexivity.
Qed.
Next Obligation.
  pose proof (snd (@lax_monoidal_assoc _ _ _ _ _ L (I, X) (I, Y) (I, Z)));
  simpl in X0; revert X0.
  assert
    (snd (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (@I C H, X)) (P (@I C H, Y)) (P (@I C H, Z))))
       = @to K _ _ (@tensor_assoc K H2 (snd (P (@I C H, X)))
                                  (snd (P (@I C H, Y))) (snd (P (@I C H, Z))))).
    destruct (P (I, X)), (P (I, Y)), (P (I, Z)).
    reflexivity.
  srewrite H3; clear H3.
  intros.
  pose proof (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                              (I, X, (I ⨂ I, Y ⨂ Z))%object
                              (I, X, (I, Y ⨂ Z))%object
                              ((id, id), (to unit_left, id)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[snd (P (I, X))] ≈ id[snd (P (I, X))] ∘ id[snd (P (I, X))]) by cat.
  rewrite X2; clear X2.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X0; clear X0.
  rewrite !comp_assoc.
  rewrite !snd_comp.
  assert (id[snd (P (I, Z))] ≈ id[snd (P (I, Z))] ∘ id[snd (P (I, Z))]) by cat.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite !comp_assoc.
  apply compose_respects; [|cat].
  rewrite !bimap_fmap.
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  pose proof (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                              (I ⨂ I, X ⨂ Y, (I, Z))%object
                              (I, X ⨂ Y, (I, Z))%object
                              ((to unit_left, id), (id, id)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  rewrite <- X1; clear X1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite unit_identity.
  reflexivity.
Qed.

Corollary ProductFunctor_proj_LaxMonoidal :
  LaxMonoidalFunctor P
    -> LaxMonoidalFunctor ((ProductFunctor_fst P) ∏⟶ (ProductFunctor_snd P)).
Proof.
  intros L.
  exact (ProductFunctor_LaxMonoidal (ProductFunctor_fst_LaxMonoidal L)
                                    (ProductFunctor_snd_LaxMonoidal L)).
Qed.

End ProductMonoidalProj.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Product.
Require Export Category.Functor.Structure.Monoidal.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Product.
Require Export Category.Structure.Monoidal.Proofs.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductMonoidal.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {J : Category}.
Context `{@Monoidal J}.
Context {K : Category}.
Context `{@Monoidal K}.

Context {F : C ⟶ J}.
Context {G : D ⟶ K}.

#[local] Obligation Tactic := program_simpl.

Program Definition ProductFunctor_Monoidal_ap_functor_iso
  (O : MonoidalFunctor F) (P : MonoidalFunctor G) :
    (⨂) ◯ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ≅[[(C ∏ D) ∏ (C ∏ D), J ∏ K]] F ∏⟶ G ◯ (⨂) :=
  {|
    to := {| transform := _; naturality := _; naturality_sym := _ |};
    from := {| transform := _; naturality := _; naturality_sym := _ |};
    iso_to_from := _;
    iso_from_to := _;
  |}.
Next Obligation.
  simpl. split;
    exact (transform[to ap_functor_iso] (_, _)).
Defined.
Next Obligation.
  simpl. split;
    apply (naturality (to ap_functor_iso) (_, _)).
Qed.
Next Obligation.
  simpl. split;
    apply (naturality_sym (to ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split; exact (transform[from ap_functor_iso] (_, _)).
Defined.
Next Obligation.
  simpl. split;
    apply (naturality (from ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split;
    apply (naturality_sym (from ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split.
  - sapply (iso_to_from (ap_functor_iso[O])).
  - sapply (iso_to_from (ap_functor_iso[P])).
Qed.
Next Obligation.
  simpl. split.
  - apply (iso_from_to (ap_functor_iso[O]) (_, _)).
  - apply (iso_from_to (ap_functor_iso[P]) (_, _)).
Qed.

Program Definition ProductFunctor_Monoidal :
  MonoidalFunctor F → MonoidalFunctor G
    → MonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
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
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_iso_left || apply pure_iso_right.
Defined.
Next Obligation.
  intros; isomorphism; split; apply ap_iso_assoc.
Qed.
Next Obligation.
  simpl.
  split; apply monoidal_unit_left.
Qed.
Next Obligation.
  simpl.
  split; apply monoidal_unit_right.
Qed.
Next Obligation.
  simpl.
  intros; split; apply monoidal_assoc.
Qed.

Program Definition ProductFunctor_Monoidal_proj1_ap_functor_iso
  (P : MonoidalFunctor F ∏⟶ G) :
    (⨂) ◯ F ∏⟶ F ≅[[(C ∏ C), J]] F ◯ (⨂) :=
  {|
    to := {| transform := _; naturality := _; naturality_sym := _ |};
    from := {| transform := _; naturality := _; naturality_sym := _ |};
    iso_to_from := _;
    iso_from_to := _;
  |}.
Next Obligation.
  exact (fst (transform[to (ap_functor_iso[P])] ((o, I), (o0, I)))).
Defined.
Next Obligation.
  simpl in *.
  epose proof (@naturality _ _ _ _ (to (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  epose proof (@naturality_sym _ _ _ _ (to (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  apply (fst (transform[from (ap_functor_iso[P])] ((_, I), (_, I)))).
Defined.
Next Obligation.
  simpl in *.
  epose proof (@naturality _ _ _ _ (from (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  epose proof (@naturality_sym _ _ _ _ (from (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  apply (iso_to_from (ap_functor_iso[P]) (_, I, (_, I))).
Qed.
Next Obligation.
  apply (iso_from_to (ap_functor_iso[P]) (_, I, (_, I))).
Qed.

Program Definition ProductFunctor_Monoidal_proj1 :
  MonoidalFunctor (F ∏⟶ G) → MonoidalFunctor F := fun P => {|
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
  apply (fst (to (@pure_iso_left _ _ _ _ _ P (x, I)))).
  apply (fst (from (@pure_iso_left _ _ _ _ _ P (x, I)))).
  apply (fst (iso_to_from (@pure_iso_left _ _ _ _ _ P (x, I)))).
  apply (fst (iso_from_to (@pure_iso_left _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_iso_right _ _ _ _ _ P (x, I)))).
  apply (fst (from (@pure_iso_right _ _ _ _ _ P (x, I)))).
  apply (fst (iso_to_from (@pure_iso_right _ _ _ _ _ P (x, I)))).
  apply (fst (iso_from_to (@pure_iso_right _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (from (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_left _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_right _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  spose (fst (naturality (to ap_functor_iso[P])
                         ((x ⨂ y, I ⨂ I), (z, I))%object
                         ((x ⨂ y, I), (z, I))%object
                         ((id[x ⨂ y], to unit_left),
                          (id[z], id[I])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (fst (naturality (to ap_functor_iso[P])
                         ((x, I), (y ⨂ z, I ⨂ I))%object
                         ((x, I), (y ⨂ z, I))%object
                         ((id[x], id[I]),
                          (id[y ⨂ z], to unit_left)))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (fst (@monoidal_assoc _ _ _ _ _ P (x, I) (y, I) (z, I))).
Qed.

Lemma ProductFunctor_Monoidal_proj2_ap_functor_iso :
  MonoidalFunctor F ∏⟶ G
    → (⨂) ◯ G ∏⟶ G ≅[[(D ∏ D), K]] G ◯ (⨂).
Proof.
  intros P.
  isomorphism.
  - transform. {
      intros [x y].
      exact (snd (transform[to (ap_functor_iso[P])] ((I, x), (I, y)))).
    }

    all:(try rename x into x0;
         try rename y into y0;
         try destruct x0 as [x y],
                      y0 as [z w],
                      f as [f g];
         try destruct A as [x y]; simpl).

    exact (snd (naturality (to (ap_functor_iso[P]))
                           (I, x, (I, y)) (I, z, (I, w))
                           ((id, f), (id, g)))).

    exact (snd (naturality_sym (to (ap_functor_iso[P]))
                               (I, x, (I, y)) (I, z, (I, w))
                               ((id, f), (id, g)))).
  - transform. {
      intros [x y].
      exact (snd (transform[from (ap_functor_iso[P])] ((I, x), (I, y)))).
    }

    all:(try rename x into x0;
         try rename y into y0;
         try destruct x0 as [x y],
                      y0 as [z w],
                      f as [f g];
         try destruct A as [x y]; simpl).

    exact (snd (naturality (from (ap_functor_iso[P]))
                           (I, x, (I, y)) (I, z, (I, w))
                           ((id, f), (id, g)))).

    exact (snd (naturality_sym (from (ap_functor_iso[P]))
                               (I, x, (I, y)) (I, z, (I, w))
                               ((id, f), (id, g)))).
  - destruct x; simpl.
    apply (iso_to_from (ap_functor_iso[P]) (I, o, (I, o0))).
  - destruct x; simpl.
    apply (iso_from_to (ap_functor_iso[P]) (I, o, (I, o0))).
Defined.

Program Definition ProductFunctor_Monoidal_proj2 :
  MonoidalFunctor (F ∏⟶ G) → MonoidalFunctor G := fun P => {|
  pure_iso            := _;
  ap_functor_iso      := ProductFunctor_Monoidal_proj2_ap_functor_iso P;
  pure_iso_left       := _;
  pure_iso_right      := _;
  ap_iso_assoc        := _;
  monoidal_unit_left  := _;
  monoidal_unit_right := _;
  monoidal_assoc      := _
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
  apply (snd (to (@pure_iso_left _ _ _ _ _ P (I, x)))).
  apply (snd (from (@pure_iso_left _ _ _ _ _ P (I, x)))).
  apply (snd (iso_to_from (@pure_iso_left _ _ _ _ _ P (I, x)))).
  apply (snd (iso_from_to (@pure_iso_left _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_iso_right _ _ _ _ _ P (I, x)))).
  apply (snd (from (@pure_iso_right _ _ _ _ _ P (I, x)))).
  apply (snd (iso_to_from (@pure_iso_right _ _ _ _ _ P (I, x)))).
  apply (snd (iso_from_to (@pure_iso_right _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (from (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_left _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_right _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  spose (snd (naturality (to ap_functor_iso[P])
                         ((I ⨂ I, x ⨂ y), (I, z))%object
                         ((I, x ⨂ y), (I, z))%object
                         ((to unit_left, id[x ⨂ y]),
                          (id[I], id[z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (snd (naturality (to ap_functor_iso[P])
                         ((I, x), (I ⨂ I, y ⨂ z))%object
                         ((I, x), (I, y ⨂ z))%object
                         ((id[I], id[x]),
                          (to unit_left, id[y ⨂ z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (snd (@monoidal_assoc _ _ _ _ _ P (I, x) (I, y) (I, z))).
Qed.

Lemma ProductFunctor_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor F → LaxMonoidalFunctor G
    → (⨂) ◯ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ⟹ F ∏⟶ G ◯ (⨂).
Proof.
  intros O P.

  transform. {
    intros [[x z] [y w]]; split.
    - exact (transform[ap_functor_nat] (x, y)).
    - exact (transform[ap_functor_nat] (z, w)).
  }

  all:(try destruct x as [[x1 x2] [y1 y2]],
                    y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  - split.
      abstract apply (naturality ap_functor_nat (x1, y1)).
    abstract apply (naturality ap_functor_nat (x2, y2)).

  - split.
      abstract apply (naturality_sym ap_functor_nat
                                     (x1, y1) (z1, w1) (f1a, f2a)).
    abstract apply (naturality_sym ap_functor_nat
                                   (x2, y2) (z2, w2) (f1b, f2b)).
Defined.

Program Definition ProductFunctor_LaxMonoidal :
  LaxMonoidalFunctor F → LaxMonoidalFunctor G
    → LaxMonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_ap_functor_nat _ _;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
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
    → (⨂) ◯ F ∏⟶ F ⟹ F ◯ (⨂).
Proof.
  intros P.

  transform. {
    intros [x y].
    exact (fst (transform[ap_functor_nat[P]] ((x, I), (y, I)))).
  }

  all:(try rename x into x0;
       try rename y into y0;
       try destruct x0 as [x y],
                    y0 as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  - exact (fst (naturality (ap_functor_nat[P])
                           (x, I, (y, I)) (z, I, (w, I))
                           ((f, id), (g, id)))).

  - exact (fst (naturality_sym (ap_functor_nat[P])
                               (x, I, (y, I)) (z, I, (w, I))
                               ((f, id), (g, id)))).
Defined.

Program Definition ProductFunctor_LaxMonoidal_proj1 :
  LaxMonoidalFunctor (F ∏⟶ G) → LaxMonoidalFunctor F := fun P => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_proj1_ap_functor_nat P;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
|}.
Next Obligation.
  apply (fst (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_left _ _ _ _ _ P (x, I)))).
  apply (fst (from (@pure_left _ _ _ _ _ P (x, I)))).
  apply (fst (iso_to_from (@pure_left _ _ _ _ _ P (x, I)))).
  apply (fst (iso_from_to (@pure_left _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@pure_right _ _ _ _ _ P (x, I)))).
  apply (fst (from (@pure_right _ _ _ _ _ P (x, I)))).
  apply (fst (iso_to_from (@pure_right _ _ _ _ _ P (x, I)))).
  apply (fst (iso_from_to (@pure_right _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  apply (fst (to (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (from (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (iso_to_from (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  apply (fst (iso_from_to (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_left _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_right _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  spose (fst (naturality (ap_functor_nat[P])
                         ((x ⨂ y, I ⨂ I), (z, I))%object
                         ((x ⨂ y, I), (z, I))%object
                         ((id[x ⨂ y], to unit_left),
                          (id[z], id[I])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (fst (naturality (ap_functor_nat[P])
                         ((x, I), (y ⨂ z, I ⨂ I))%object
                         ((x, I), (y ⨂ z, I))%object
                         ((id[x], id[I]),
                          (id[y ⨂ z], to unit_left)))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (fst (@lax_monoidal_assoc _ _ _ _ _ P (x, I) (y, I) (z, I))).
Qed.

Lemma ProductFunctor_LaxMonoidal_proj2_ap_functor_nat :
  LaxMonoidalFunctor F ∏⟶ G
    → (⨂) ◯ G ∏⟶ G ⟹ G ◯ (⨂).
Proof.
  intros P.

  transform. {
    intros [x y].
    exact (snd (transform[ap_functor_nat[P]] ((I, x), (I, y)))).
  }

  all:(try rename x into x0;
       try rename y into y0;
       try destruct x0 as [x y],
                    y0 as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  - exact (snd (naturality (ap_functor_nat[P])
                           (I, x, (I, y)) (I, z, (I, w))
                           ((id, f), (id, g)))).

  - exact (snd (naturality_sym (ap_functor_nat[P])
                               (I, x, (I, y)) (I, z, (I, w))
                               ((id, f), (id, g)))).
Defined.

Program Definition ProductFunctor_LaxMonoidal_proj2 :
  LaxMonoidalFunctor (F ∏⟶ G) → LaxMonoidalFunctor G := fun P => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_proj2_ap_functor_nat P;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
|}.
Next Obligation.
  apply (snd (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_left _ _ _ _ _ P (I, x)))).
  apply (snd (from (@pure_left _ _ _ _ _ P (I, x)))).
  apply (snd (iso_to_from (@pure_left _ _ _ _ _ P (I, x)))).
  apply (snd (iso_from_to (@pure_left _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@pure_right _ _ _ _ _ P (I, x)))).
  apply (snd (from (@pure_right _ _ _ _ _ P (I, x)))).
  apply (snd (iso_to_from (@pure_right _ _ _ _ _ P (I, x)))).
  apply (snd (iso_from_to (@pure_right _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  apply (snd (to (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (from (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (iso_to_from (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  apply (snd (iso_from_to (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_left _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_right _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  spose (snd (naturality (ap_functor_nat[P])
                         ((I ⨂ I, x ⨂ y), (I, z))%object
                         ((I, x ⨂ y), (I, z))%object
                         ((to unit_left, id[x ⨂ y]),
                          (id[I], id[z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (snd (naturality (ap_functor_nat[P])
                         ((I, x), (I ⨂ I, y ⨂ z))%object
                         ((I, x), (I, y ⨂ z))%object
                         ((id[I], id[x]),
                          (to unit_left, id[y ⨂ z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (snd (@lax_monoidal_assoc _ _ _ _ _ P (I, x) (I, y) (I, z))).
Qed.

End ProductMonoidal.

Section ProductMonoidalProj.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {J : Category}.
Context `{@Monoidal J}.
Context {K : Category}.
Context `{@Monoidal K}.

Variable (P : (C ∏ J) ⟶ D ∏ K).

Lemma ProductFunctor_fst_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor P
    → (⨂) ◯ (ProductFunctor_fst P) ∏⟶ (ProductFunctor_fst P)
          ⟹ ProductFunctor_fst P ◯ (⨂).
Proof.
  intro L.
  transform; simpl.
  intros [x y]; simpl.
  - exact (fst (bimap id (to unit_left) ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((x, I), (y, I)))).
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (x1, I, (x2, I)) (y1, I, (y2, I))
                           ((f1, id), (f2, id)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite fst_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (x1, I, (x2, I)) (y1, I, (y2, I))
                           ((f1, id), (f2, id)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite fst_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
Defined.

#[local] Obligation Tactic := program_simpl.

Program Definition ProductFunctor_fst_LaxMonoidal :
  LaxMonoidalFunctor P
    → LaxMonoidalFunctor (ProductFunctor_fst P) := fun L => {|
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
  destruct (@pure_left _ _ _ _ _ L (x, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (I ⨂ x, I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (x, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (x ⨂ I, I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (x, I) (y, I) (z, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (x ⨂ y ⨂ z, I ⨂ I ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (fst (@bimap _ _ _ P _ _ _ _ id
                       (Isomorphism.to unit_left ∘
                        Isomorphism.to unit_left))).
  - exact (fst (@bimap _ _ _ P _ _ _ _ id
                       (Isomorphism.from unit_left ∘
                        Isomorphism.from unit_left))).
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (Isomorphism.from _)).
    rewrite Isomorphism.iso_to_from.
    rewrite !id_left.
    rewrite Isomorphism.iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (Isomorphism.to _)).
    rewrite Isomorphism.iso_from_to.
    rewrite !id_left.
    rewrite Isomorphism.iso_from_to.
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
  spose (fst (@lax_monoidal_unit_left _ _ _ _ _ L (x, I))) as X.
  rewrite <- X; clear X.
  destruct (P (x, I)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_fst_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (fst (@lax_monoidal_unit_right _ _ _ _ _ L (x, I))) as X.
  rewrite unit_identity.
  rewrite bimap_fmap in X.
  rewrite <- X; clear X.
  destruct (P (x, I)).
  reflexivity.
Qed.
Next Obligation.
  spose (fst (@lax_monoidal_assoc _ _ _ _ _ L (x, I) (y, I) (z, I))) as X.
  revert X.
  assert
    (fst (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (x, @I J H1)) (P (y, @I J H1)) (P (z, @I J H1))))
       = @to D _ _ (@tensor_assoc D H0 (fst (P (x, @I J H1)))
                                  (fst (P (y, @I J H1))) (fst (P (z, @I J H1))))).
    destruct (P (x, I)), (P (y, I)), (P (z, I)).
    reflexivity.
  srewrite H3; clear H3.
  spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (x, I, (y ⨂ z, I ⨂ I))%object
                         (x, I, (y ⨂ z, I))%object
                         ((id, id), (id, to unit_left)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[fst (P (x, I))] ≈ id[fst (P (x, I))] ∘ id[fst (P (x, I))]) by cat.
  intros.
  rewrite X; clear X.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X0; clear X0.
  rewrite !comp_assoc.
  rewrite !fst_comp.
  assert (id[fst (P (z, I))] ≈ id[fst (P (z, I))] ∘ id[fst (P (z, I))]) by cat.
  rewrite X; clear X.
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
  spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (x ⨂ y, I ⨂ I, (z, I))%object
                         (x ⨂ y, I, (z, I))%object
                         ((id, to unit_left), (id, id)))) as X1.
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
    → (⨂) ◯ (ProductFunctor_snd P) ∏⟶ (ProductFunctor_snd P)
          ⟹ ProductFunctor_snd P ◯ (⨂).
Proof.
  intro L.
  transform; simpl.
  intros [x y]; simpl.
  - exact (snd (bimap (to unit_left) id ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((I, x), (I, y)))).
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (I, x1, (I, x2)) (I, y1, (I, y2))
                           ((id, f1), (id, f2)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite snd_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (I, x1, (I, x2)) (I, y1, (I, y2))
                           ((id, f1), (id, f2)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
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
    → LaxMonoidalFunctor (ProductFunctor_snd P) := fun L => {|
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
  destruct (@pure_left _ _ _ _ _ L (I, x));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, I ⨂ x)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (I, x));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, x ⨂ I)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite Isomorphism.iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (I, x) (I, y) (I, z));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I ⨂ I, x ⨂ y ⨂ z)%object)).
    isomorphism; auto.
  isomorphism.
  - exact (snd (@bimap _ _ _ P _ _ _ _
                       (Isomorphism.to unit_left ∘
                        Isomorphism.to unit_left) id)).
  - exact (snd (@bimap _ _ _ P _ _ _ _
                       (Isomorphism.from unit_left ∘
                        Isomorphism.from unit_left) id)).
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (Isomorphism.from _)).
    rewrite Isomorphism.iso_to_from.
    rewrite !id_left.
    rewrite Isomorphism.iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc _ (Isomorphism.to _)).
    rewrite Isomorphism.iso_from_to.
    rewrite !id_left.
    rewrite Isomorphism.iso_from_to.
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
  spose (snd (@lax_monoidal_unit_left _ _ _ _ _ L (I, x))) as X.
  rewrite <- X; clear X.
  destruct (P (I, x)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_snd_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (snd (@lax_monoidal_unit_right _ _ _ _ _ L (I, x))) as X.
  rewrite unit_identity.
  rewrite bimap_fmap in X.
  rewrite <- X; clear X.
  destruct (P (I, x)).
  reflexivity.
Qed.
Next Obligation.
  spose (snd (@lax_monoidal_assoc _ _ _ _ _ L (I, x) (I, y) (I, z))) as X.
  revert X.
  assert
    (snd (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (@I C H, x)) (P (@I C H, y)) (P (@I C H, z))))
       = @to K _ _ (@tensor_assoc K H2 (snd (P (@I C H, x)))
                                  (snd (P (@I C H, y))) (snd (P (@I C H, z))))).
    destruct (P (I, x)), (P (I, y)), (P (I, z)).
    reflexivity.
  srewrite H3; clear H3.
  intros.
  spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (I, x, (I ⨂ I, y ⨂ z))%object
                         (I, x, (I, y ⨂ z))%object
                         ((id, id), (to unit_left, id)))) as X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[snd (P (I, x))] ≈ id[snd (P (I, x))] ∘ id[snd (P (I, x))]) by cat.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X; clear X.
  rewrite !comp_assoc.
  rewrite !snd_comp.
  assert (id[snd (P (I, z))] ≈ id[snd (P (I, z))] ∘ id[snd (P (I, z))]) by cat.
  rewrite X; clear X.
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
  spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (I ⨂ I, x ⨂ y, (I, z))%object
                         (I, x ⨂ y, (I, z))%object
                         ((to unit_left, id), (id, id)))) as X1.
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
    → LaxMonoidalFunctor ((ProductFunctor_fst P) ∏⟶ (ProductFunctor_snd P)).
Proof.
  intros L.
  exact (ProductFunctor_LaxMonoidal (ProductFunctor_fst_LaxMonoidal L)
                                    (ProductFunctor_snd_LaxMonoidal L)).
Qed.

End ProductMonoidalProj.

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

Section ProductFunctorStrong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{@SymmetricMonoidal C _}.
Context `{@CartesianMonoidal C _}.
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

End ProductFunctorStrong.

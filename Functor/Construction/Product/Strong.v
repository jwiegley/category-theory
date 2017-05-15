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

Program Definition ProductFunctor_Strong :
  StrongFunctor F -> StrongFunctor G
    -> StrongFunctor (F ∏⟶ G) := fun O P => {|
  strength := fun _ _ => (strength, strength);
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation. split; apply strength_natural. Qed.
Next Obligation. split; apply strength_id_left. Qed.
Next Obligation. split; apply strength_assoc. Qed.

Program Definition ProductFunctor_Strong_proj1 :
  StrongFunctor (F ∏⟶ G) -> StrongFunctor F := fun P => {|
  strength := fun X Y => fst (@strength _ _ _ P (X, I) (Y, I));
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (fst (@strength_natural _ _ _ P (X, I) (Y, I) (g, id)
                                (Z, I) (W, I) (h, id))).
Defined.
Next Obligation.
  exact (fst (@strength_id_left _ _ _ P (X, I))).
Qed.
Next Obligation.
  pose proof (@unit_left C H I) as X0.
  pose proof (fst (@strength_natural _ _ _ P
                     (X, I) (X, I) (id[X], id[I])
                     (Y ⨂ Z, I)%object (Y ⨂ Z, I ⨂ I)%object
                     (id[Y ⨂ Z], from X0))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrite X1; clear X1.
  pose proof (fst (@strength_natural _ _ _ P
                     (X ⨂ Y, I)%object (X ⨂ Y, I ⨂ I)%object
                     (id[X ⨂ Y], from X0)
                     (Z, I) (Z, I) (id[Z], id[I]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrite X1; clear X1.
  exact (fst (@strength_assoc _ _ _ P (X, I) (Y, I) (Z, I))).
Qed.

Program Definition ProductFunctor_Strong_proj2 :
  StrongFunctor (F ∏⟶ G) -> StrongFunctor G := fun P => {|
  strength := fun X Y => snd (@strength _ _ _ P (I, X) (I, Y));
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (snd (@strength_natural _ _ _ P (I, X) (I, Y) (id, g)
                                (I, Z) (I, W) (id, h))).
Defined.
Next Obligation.
  exact (snd (@strength_id_left _ _ _ P (I, X))).
Qed.
Next Obligation.
  pose proof (@unit_left C H I) as X0.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, X) (I, X) (id[I], id[X])
                     (I, Y ⨂ Z)%object (I ⨂ I, Y ⨂ Z)%object
                     (from X0, id[Y ⨂ Z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrite X1; clear X1.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, X ⨂ Y)%object (I ⨂ I, X ⨂ Y)%object
                     (from X0, id[X ⨂ Y])
                     (I, Z) (I, Z) (id[I], id[Z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrite X1; clear X1.
  exact (snd (@strength_assoc _ _ _ P (I, X) (I, Y) (I, Z))).
Qed.

End ProductFunctorStrong.

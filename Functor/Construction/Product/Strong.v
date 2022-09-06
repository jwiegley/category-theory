Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Construction.Product.Monoidal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Product.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Balanced.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.

Section ProductFunctorStrong.

Context `{@CartesianMonoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Program Definition ProductFunctor_Strong
  `{!StrongFunctor F} `{!StrongFunctor G} : StrongFunctor (F ∏⟶ G) := {|
  strength := fun _ _ => (strength[F], strength[G]);
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation. split; apply strength_natural. Qed.
Next Obligation. split; apply strength_id_left. Qed.
Next Obligation. split; apply strength_assoc. Qed.

Program Definition ProductFunctor_Strong_proj1 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor F := fun P => {|
  strength := fun x y => fst (@strength _ _ _ P (x, I) (y, I));
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (fst (@strength_natural _ _ _ P (x, I) (y, I) (g, id)
                                (z, I) (w, I) (h, id))).
Defined.
Next Obligation.
  exact (fst (@strength_id_left _ _ _ P (x, I))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (fst (@strength_natural _ _ _ P
                     (x, I) (x, I) (id[x], id[I])
                     (y ⨂ z, I)%object (y ⨂ z, I ⨂ I)%object
                     (id[y ⨂ z], from X0))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (fst (@strength_natural _ _ _ P
                     (x ⨂ y, I)%object (x ⨂ y, I ⨂ I)%object
                     (id[x ⨂ y], from X0)
                     (z, I) (z, I) (id[z], id[I]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (fst (@strength_assoc _ _ _ P (x, I) (y, I) (z, I))).
Qed.

Program Definition ProductFunctor_Strong_proj2 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor G := fun P => {|
  strength := fun x y => snd (@strength _ _ _ P (I, x) (I, y));
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (snd (@strength_natural _ _ _ P (I, x) (I, y) (id, g)
                                (I, z) (I, w) (id, h))).
Defined.
Next Obligation.
  exact (snd (@strength_id_left _ _ _ P (I, x))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x) (I, x) (id[I], id[x])
                     (I, y ⨂ z)%object (I ⨂ I, y ⨂ z)%object
                     (from X0, id[y ⨂ z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x ⨂ y)%object (I ⨂ I, x ⨂ y)%object
                     (from X0, id[x ⨂ y])
                     (I, z) (I, z) (id[I], id[z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (snd (@strength_assoc _ _ _ P (I, x) (I, y) (I, z))).
Qed.

End ProductFunctorStrong.

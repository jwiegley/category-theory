Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Functor.Construction.Product.
Require Export Category.Functor.Construction.Product.Monoidal.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section ProductFunctorStrong.

Context {C : Category}.
Context `{@Monoidal C}.
Context `{@CartesianMonoidal C _}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

#[local] Obligation Tactic := program_simpl.

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
  pose proof (@unit_left C H I) as X0.
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
  StrongFunctor (F ∏⟶ G) -> StrongFunctor G := fun P => {|
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
  pose proof (@unit_left C H I) as X0.
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

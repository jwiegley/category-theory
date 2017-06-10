Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;

  t_id     : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.

Arguments TAlgebra {C} T {_} a.

Notation "t_alg[ T ]" := (@t_alg _ _ _ _ T)
  (at level 9, format "t_alg[ T ]") : morphism_scope.

Class TAlgebraHom `(T : C ⟶ C) `{@Monad C T} (a b : C)
      (F : TAlgebra T a) (G : TAlgebra T b) := {
  t_alg_hom : a ~> b;

  t_alg_hom_commutes : t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
}.

Notation "t_alg_hom[ F ]" := (@t_alg_hom _ _ _ _ _ _ _ F)
  (at level 9, format "t_alg_hom[ F ]") : morphism_scope.

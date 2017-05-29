Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  talg : T a ~> a;

  tid     : talg ∘ ret ≈ id;
  taction : talg ∘ fmap talg ≈ talg ∘ join
}.

Arguments TAlgebra {C} T {_} a.

Notation "talg[ T ]" := (@talg _ _ _ _ T)
  (at level 9, format "talg[ T ]") : morphism_scope.

Class TAlgebraHom `(T : C ⟶ C) `{@Monad C T} (a b : C)
      (F : TAlgebra T a) (G : TAlgebra T b) := {
  talg_hom : a ~> b;

  talg_hom_commutes : talg_hom ∘ talg[F] ≈ talg[G] ∘ fmap[T] talg_hom
}.

Notation "talg_hom[ F ]" := (@talg_hom _ _ _ _ _ _ _ F)
  (at level 9, format "talg_hom[ F ]") : morphism_scope.

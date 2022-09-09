Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.

Generalizable All Variables.

Section MonadDistributive.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

Class Monad_Distributive := {
  mprod {A} : N (M (N A)) ~> M (N A);

  mprod_fmap_fmap {A B} (f : A ~> B) :
    @mprod B ∘ fmap[N] (fmap[M ◯ N] f) ≈ fmap[M ◯ N] f ∘ @mprod A;
  mprod_pure {A} : @mprod A ∘ pure[N] ≈ id;
  mprod_fmap_pure {A} : @mprod A ∘ fmap[N] (ret[M] ∘ pure[N]) ≈ ret[M];
  mprod_fmap_join_fmap_mprod {A} :
    @mprod A ∘ fmap[N] (join[M] ∘ fmap[M] (@mprod A))
      ≈ join[M] ∘ fmap[M] (@mprod A) ∘ @mprod (M (N A))
}.

End MonadDistributive.

Arguments Monad_Distributive {C _} M {_} N {_ _}.

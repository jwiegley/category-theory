Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monad.

Context `{C : Category}.
Context `{M : C ⟶ C}.

Class Monad := {
  ret {a} : a ~> M a;
  join {a} : M (M a) ~> M a;

  join_fmap_join {a} : join ∘ fmap (@join a) ≈ join ∘ join;
  join_fmap_pure {a} : join ∘ fmap (@ret a) ≈ id;
  join_pure      {a} : join ∘ ret ≈ @id _ (M a);
  join_fmap_fmap {a b} (f : a ~> b) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Notation "join[ M ]" := (@join _ _ _ _ _ M _)
  (at level 9, format "join[ M ]") : category_scope.

Section MonadLib.

Context `{C : Category}.
Context `{A : @Cartesian C}.
Context `{@Closed C A}.
Context `{M : C ⟶ C}.
Context `{@Monad C M}.

Program Definition bind {a b : C} (f : a ~> M b) : M a ~> M b :=
  join ∘ fmap[M] f.

End MonadLib.

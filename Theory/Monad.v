Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monad.

Context `{M : C ⟶ C}.

Class Monad := {
  ret {x}  : x ~> M x;          (* Id    ⟹ M *)
  join {x} : M (M x) ~> M x;    (* M ○ M ⟹ M *)

  fmap_ret {x y} (f : x ~> y) : ret ∘ f ≈ fmap f ∘ ret;

  join_fmap_join {x} : join ∘ fmap (@join x) ≈ join ∘ join;
  join_fmap_ret  {x} : join ∘ fmap (@ret x) ≈ id;
  join_ret       {x} : join ∘ @ret (M x) ≈ id;

  (* This law states that join is a natural transformation. *)
  join_fmap_fmap {x y} (f : x ~> y) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Notation "ret[ M ]" := (@ret _ M _ _)
  (at level 9, format "ret[ M ]") : category_scope.
Notation "join[ M ]" := (@join _ M _ _)
  (at level 9, format "join[ M ]") : category_scope.

Section MonadLib.

Context `{@Monad C M}.

Definition bind {x y : C} (f : x ~> M y) : M x ~> M y :=
  join ∘ fmap[M] f.

End MonadLib.

Notation "m >>= f" := (bind f m) (at level 42, right associativity) : morphism_scope.
Notation "f >> g" := (f >>= fun _ => g)%morphism
  (at level 81, right associativity) : morphism_scope.

Require Import Category.Functor.Opposite.

Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).

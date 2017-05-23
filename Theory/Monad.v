Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monad.

Context {C : Category}.
Context {M : C ⟶ C}.

Class Monad := {
  ret {a}  : a ~> M a;          (* Id    ⟹ M *)
  join {a} : M (M a) ~> M a;    (* M ○ M ⟹ M *)

  fmap_ret {a b} (f : a ~> b) : ret ∘ f ≈ fmap f ∘ ret;
  join_fmap_join {a} : join ∘ fmap (@join a) ≈ join ∘ join;
  join_fmap_ret  {a} : join ∘ fmap (@ret a) ≈ id;
  join_ret       {a} : join ∘ @ret (M a) ≈ id;

  (* This law states that join is a natural transformation from [fmap . fmap]
     to [fmap]. *)
  join_fmap_fmap {a b} (f : a ~> b) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Notation "ret[ M ]" := (@ret _ M _ _)
  (at level 9, format "ret[ M ]") : category_scope.
Notation "join[ M ]" := (@join _ M _ _)
  (at level 9, format "join[ M ]") : category_scope.

Section MonadLib.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.

Program Definition bind {a b : C} (f : a ~> M b) : M a ~> M b :=
  join ∘ fmap[M] f.

End MonadLib.

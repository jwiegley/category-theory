Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monad.

Context `{C : Category}.
Context `{M : C ⟶ C}.

Class Monad := {
  ret {a}  : a ~> M a;          (* Id    ⟹ M *)
  join {a} : M (M a) ~> M a;    (* M ○ M ⟹ M *)

  join_fmap_join {a} : join ∘ fmap (@join a) ≈ join ∘ join;
  join_fmap_pure {a} : join ∘ fmap (@ret a) ≈ id;
  join_pure      {a} : join ∘ ret ≈ @id _ (M a);
  join_fmap_fmap {a b} (f : a ~> b) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

(* Monads are monoid (objects) in the (monoidal) category of endofunctors
   which is monoidal with respect to functor composition. *)

Definition Endofunctors `(C : Category) := ([C, C]).

Program Definition Monad_is_a_Monoid_in_the_category_of_endofunctors
        (m : @Monoid (Endofunctors C) Composition_Monoidal M) : Monad := {|
  ret  := transform[mempty[m]];
  join := transform[mappend[m]]
|}.
Next Obligation.
  pose proof (@mappend_assoc _ _ _ m a) as X; simpl in X.
  autorewrite with categories in X.
  symmetry; assumption.
Qed.
Next Obligation.
  pose proof (@mempty_right _ _ _ m a) as X; simpl in X.
  autorewrite with categories in X.
  assumption.
Qed.
Next Obligation.
  pose proof (@mempty_left _ _ _ m a) as X; simpl in X.
  autorewrite with categories in X.
  assumption.
Qed.
Next Obligation.
  symmetry.
  apply (@natural_transformation _ _ _ _ (@mappend _ _ _ m)).
Qed.

End Monad.

Notation "ret[ M ]" := (@ret _ M _ _)
  (at level 9, format "ret[ M ]") : category_scope.
Notation "join[ M ]" := (@join _ M _ _)
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

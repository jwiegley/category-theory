Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidMonad.

Context `{C : Category}.
Context `{M : C ⟶ C}.

(* Monads are monoid (objects) in the (monoidal) category of endofunctors
   which is monoidal with respect to functor composition. *)

Definition Endofunctors `(C : Category) := ([C, C]).

Program Definition Monoid_Monad
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

End MonoidMonad.

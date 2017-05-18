Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Structure.Monoid.
Require Export Category.Structure.Monoidal.Composition.
Require Export Category.Instance.Nat.

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

Theorem Monoid_Monad :
  @Monoid (Endofunctors C) Composition_Monoidal M <--> Monad.
Proof.
  split; intros m.
  - refine {| join := transform[mappend[m]]
            ; ret  := transform[mempty[m]] |}; intros.
    + symmetry.
      apply (@naturality _ _ _ _ (@mempty _ _ _ m)).
    + pose proof (@mappend_assoc _ _ _ m a) as X; simpl in X.
      autorewrite with categories in X.
      symmetry; assumption.
    + pose proof (@mempty_right _ _ _ m a) as X; simpl in X.
      autorewrite with categories in X.
      assumption.
    + pose proof (@mempty_left _ _ _ m a) as X; simpl in X.
      autorewrite with categories in X.
      assumption.
    + symmetry.
      apply (@naturality _ _ _ _ (@mappend _ _ _ m)).
  - unshelve (refine {| mempty  := _
                      ; mappend := _ |}).
    + transform; intros.
        exact ret.
      simpl.
      symmetry.
      apply fmap_ret.
    + transform; intros.
        exact join.
      simpl.
      symmetry.
      apply join_fmap_fmap.
    + simpl; intros; cat.
      apply join_ret.
    + simpl; intros; cat.
      apply join_fmap_ret.
    + simpl; intros; cat.
      symmetry.
      apply join_fmap_join.
Defined.

End MonoidMonad.

Require Import Lib.
Require Export Monad.
Require Export Adjunction.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section MonadAdjunction.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.
Context `{J : F ⊣ U}.

(* Every adjunction gives rise to a monad. *)

Program Definition Monad_Adjunction : @Monad D (U ○ F) := {|
  ret  := @unit _ _ _ _ J;
  join := fun a => fmap (@counit _ _ _ _ J (F a))
|}.
Obligation 1.
  unfold counit.
  rewrite <- !fmap_comp.
  rewrite <- adj_right_nat_l; cat.
  rewrite <- adj_right_nat_r; cat.
Qed.
Obligation 2.
  unfold unit, counit.
  rewrite <- !fmap_comp.
  rewrite <- adj_right_nat_l; cat.
  rewrite adj_right_left; cat.
Qed.
Obligation 3.
  unfold unit, counit.
  rewrite <- adj_left_nat_r; cat.
  rewrite adj_left_right; cat.
Qed.
Obligation 4.
  unfold unit, counit.
  rewrite <- !fmap_comp.
  rewrite <- adj_right_nat_r; cat.
  rewrite <- adj_right_nat_l; cat.
Qed.

End MonadAdjunction.

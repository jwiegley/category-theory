Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Theory.Monad.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionMonad.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.

(* Every adjunction gives rise to a monad. However, for the reverse direction,
   just knowing that the monad is formed from the product of two functors is
   not enough information, since one could always just compose [Id] to some
   monad [M], and this would not give an adjoint. *)

Theorem Adjunction_Monad : F ⊣ U -> @Monad D (U ○ F).
Proof.
  intros.
  unshelve econstructor; simpl; intros.
  - exact unit.
  - exact (fmap counit).
  - unfold unit.
    rewrite <- adj_left_nat_l; cat.
    rewrite <- adj_left_nat_r; cat.
  - unfold counit.
    rewrite <- !fmap_comp.
    rewrite <- adj_right_nat_l; cat.
    rewrite <- adj_right_nat_r; cat.
  - rewrite <- fmap_comp.
    rewrite counit_fmap_unit; cat.
  - apply fmap_counit_unit.
  - rewrite <- !fmap_comp.
    unfold counit.
    rewrite <- adj_right_nat_r; cat.
    rewrite <- adj_right_nat_l; cat.
Defined.

End AdjunctionMonad.

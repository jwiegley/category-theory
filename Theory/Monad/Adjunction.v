Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.Natural.Transformation.
Require Export Category.Theory.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionMonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Every adjunction gives rise to a monad. However, for the reverse direction,
   just knowing that the monad is formed from the product of two functors is
   not enough information, since one could always just compose [Id] to some
   monad [M], and this would not give an adjoint. *)

Theorem Adjunction_Monad : F ∹ U -> @Monad D (U ○ F).
Proof.
  intros.
  unshelve econstructor; simpl; intros.
  - exact (transform[unit] _).
  - exact (fmap (transform[counit] _)).
  - symmetry.
    apply (naturality[unit]).
  - rewrite <- !fmap_comp.
    apply fmap_respects.
    symmetry.
    apply (naturality[counit]).
  - rewrite <- !fmap_comp.
    srewrite (@counit_fmap_unit); cat.
  - simpl.
    srewrite (@fmap_counit_unit); cat.
  - rewrite <- !fmap_comp.
    srewrite (naturality[counit]); cat.
Qed.

End AdjunctionMonad.

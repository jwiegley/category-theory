Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Theory.Adjunction.
Require Export Category.Adjunction.Natural.Transformation.

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

Theorem Adjunction_Monad : F ⊣ U -> @Monad D (U ◯ F).
Proof.
  intros.
  unshelve econstructor; simpl; intros.
  - apply (to (adj[X])); simpl.
    exact id.
  - apply fmap.
    apply (from (adj[X])); simpl.
    exact id.
  - rewrite <- to_adj_nat_r.
    rewrite <- to_adj_nat_l.
    cat.
  - simpl.
    rewrite <- !fmap_comp.
    apply fmap_respects.
    rewrite <- from_adj_nat_r.
    rewrite <- from_adj_nat_l.
    cat.
  - rewrite <- !fmap_comp; simpl.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    destruct X, adj; simpl in *.
    rewrite iso_from_to.
    exact fmap_id.
  - rewrite <- to_adj_nat_r; simpl.
    rewrite id_right.
    destruct X, adj; simpl in *.
    rewrite iso_to_from.
    reflexivity.
  - rewrite <- !fmap_comp; simpl.
    apply fmap_respects.
    rewrite <- from_adj_nat_r.
    rewrite <- from_adj_nat_l.
    cat.
Qed.

Theorem Adjunction_Nat_Monad : F ∹ U -> @Monad D (U ◯ F).
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

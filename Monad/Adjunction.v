Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The monad induced by an adjunction. *)

(* nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   Every adjunction F ⊣ U, with F : D ⟶ C (left adjoint) and U : C ⟶ D (right
   adjoint), induces a monad on the domain category D whose endofunctor is the
   composite U ◯ F. Its unit is the adjunction unit, ret = η : Id ⟹ U ◯ F, and
   its multiplication is the counit whiskered on both sides by the adjoints,
   join = U ε F : U F U F ⟹ U F, i.e. join_X = fmap[U] (ε (F X)) = U(ε_{F X}).
   The monad laws are exactly the triangle (zig-zag) identities of the
   adjunction: the unit laws are counit_fmap_unit (ε F ∘ F η = id) transported
   through U and fmap_counit_unit (U ε ∘ η U = id), while associativity is
   naturality of ε. Dually, F ◯ U is a comonad on C.

   Two proofs are given below, one for each presentation of an adjunction in
   this library: [Adjunction_Monad] works from the hom-set (transpose) form
   F ⊣ U, building ret and join from the transposes ⌊id⌋ and fmap[U] ⌈id⌉; and
   [Adjunction_Nat_Monad] works from the counit/unit form F ∹ U, reading off η
   and U ε directly. Both yield the same monad U ◯ F.

   The converse — that every monad arises from an adjunction — also holds, via
   the Kleisli (initial) and Eilenberg–Moore (terminal) resolutions (see
   Monad/Kleisli.v and Monad/Eilenberg/Moore.v). But the bare composite U ◯ F
   does not by itself remember an adjunction: one could compose Id with an
   arbitrary monad M and recover no adjoint, so a presentation of the monad
   alone, without the adjunction data, is not enough to reconstruct F and U. *)

Section AdjunctionMonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Theorem Adjunction_Monad : F ⊣ U → @Monad D (U ◯ F).
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

Theorem Adjunction_Nat_Monad : F ∹ U → @Monad D (U ◯ F).
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
    apply fmap_respects.
    symmetry.
    apply (naturality[counit]).
Qed.

End AdjunctionMonad.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Balanced.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SymmetricMonoidal.

Context {C : Category}.

Class SymmetricMonoidal := {
  symmetric_is_balanced : @BalancedMonoidal C;

  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_balanced.

Context `{SymmetricMonoidal}.

Corollary braid_symmetry {x y} :
  to (@braid _ _ x y) ≈ from (@braid _ _ y x).
Proof.
  rewrite <- id_right.
  rewrite <- (@iso_to_from _ _ _ braid).
  rewrite comp_assoc.
  rewrite braid_invol.
  now rewrite id_left.
Qed.

Lemma hexagon_rotated {x y z} :
  tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ braid ∘ tensor_assoc ∘ braid.
Proof.
  rewrite <- (id_right (id ⨂ braid ∘ tensor_assoc ∘ braid)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc; rewrite <- (comp_assoc _ tensor_assoc braid); rewrite <- (comp_assoc _ (tensor_assoc ∘ braid) _).
  rewrite hexagon_to_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite braid_invol.
  cat.
Qed.

Lemma bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ braid ≈ braid ∘ f ⨂ g.
Proof.
  spose (fst braid_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

Lemma braid_bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  braid ∘ g ⨂ f ∘ braid ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_invol.
  cat.
Qed.

End SymmetricMonoidal.

Program Definition balanced_twist_id_is_symmetric `{B : @BalancedMonoidal C}
  (to_twist : ∀ x, to twist ≈ to (@iso_id _ x)) :
  @SymmetricMonoidal C := {|
  symmetric_is_balanced := B;
|}.
Next Obligation.
  pose proof (@balanced_to_commutes _ _ x y).
  rewrite <- to_twist.
  rewrite <- X; clear X.
  comp_left.
  rewrite <- id_left at 1.
  comp_right.
  rewrite !to_twist.
  now rewrite bimap_id_id.
Qed.

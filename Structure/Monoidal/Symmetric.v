Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SymmetricMonoidal.

Context `{@Monoidal C}.

Class SymmetricMonoidal := {
  symmetric_is_braided : BraidedMonoidal;
  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

Corollary braid_symmetry `{SymmetricMonoidal} {x y} :
  to (@braid _ _ _ x y) ≈ from (@braid _ _ _ y x).
Proof.
  rewrite <- id_right.
  rewrite <- (@iso_to_from _ _ _ braid).
  rewrite comp_assoc.
  rewrite braid_invol.
  now rewrite id_left.
Qed.

Corollary hexagon_rotated `{SymmetricMonoidal} {x y z} :
  tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ braid ∘ tensor_assoc ∘ braid.
Proof.
  rewrite <- (id_right (id ⨂ braid ∘ tensor_assoc ∘ braid)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc; rewrite <- (comp_assoc _ tensor_assoc braid); rewrite <- (comp_assoc _ (tensor_assoc ∘ braid) _).
  rewrite hexagon_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite braid_invol.
  cat.
Qed.

Corollary bimap_braid `{SymmetricMonoidal} {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ braid ≈ braid ∘ f ⨂ g.
Proof.
  spose (fst braid_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

Corollary braid_bimap_braid `{SymmetricMonoidal} {x y z w} (f : x ~> z) (g : y ~> w) :
  braid ∘ g ⨂ f ∘ braid ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_invol.
  cat.
Qed.

End SymmetricMonoidal.

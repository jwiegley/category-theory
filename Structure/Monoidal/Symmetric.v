Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SymmetricMonoidal.

Context `{@Monoidal C}.

Class SymmetricMonoidal := {
  twist {x y} : x ⨂ y ≅ y ⨂ x;
  twist_natural : natural (@twist);

  twist_invol {x y} : twist ∘ twist ≈ id[x ⨂ y];

  hexagon_identity {x y z} :
    tensor_assoc ∘ twist ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ twist ∘ tensor_assoc ∘ twist ⨂ id
}.

Corollary hexagon_rotated `{SymmetricMonoidal} {x y z} :
  tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ twist ∘ tensor_assoc ∘ twist.
Proof.
  rewrite <- (id_right (id ⨂ twist ∘ tensor_assoc ∘ twist)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc; rewrite <- (comp_assoc _ tensor_assoc twist); rewrite <- (comp_assoc _ (tensor_assoc ∘ twist) _).
  rewrite hexagon_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite twist_invol.
  cat.
Qed.

Corollary bimap_twist `{SymmetricMonoidal} {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ twist ≈ twist ∘ f ⨂ g.
Proof.
  spose (fst twist_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

Corollary twist_bimap_twist `{SymmetricMonoidal} {x y z w} (f : x ~> z) (g : y ~> w) :
  twist ∘ g ⨂ f ∘ twist ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_twist.
  rewrite comp_assoc.
  rewrite twist_invol.
  cat.
Qed.

End SymmetricMonoidal.

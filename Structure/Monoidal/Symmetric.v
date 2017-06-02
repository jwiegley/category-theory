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
  twist {X Y} : X ⨂ Y ≅ Y ⨂ X;
  twist_natural : natural (@twist);

  twist_invol {X Y} : twist ∘ twist ≈ id[X ⨂ Y];

  hexagon_identity {X Y Z} :
    tensor_assoc ∘ twist ∘ tensor_assoc
      << (X ⨂ Y) ⨂ Z ~~> Y ⨂ (Z ⨂ X) >>
    id ⨂ twist ∘ tensor_assoc ∘ twist ⨂ id
}.

Corollary bimap_twist `{SymmetricMonoidal} {X Y Z W} (f : X ~> Z) (g : Y ~> W) :
  twist ∘ g ⨂ f ∘ twist ≈ f ⨂ g.
Proof.
  pose proof (fst twist_natural _ _ f _ _ g); simpl in X0.
  normal.
  rewrite <- comp_assoc.
  rewrites.
  rewrite comp_assoc.
  rewrite twist_invol; cat.
Qed.

End SymmetricMonoidal.

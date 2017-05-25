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

Section BraidedMonoidal.

Context `{@Monoidal C}.

Class BraidedMonoidal := {
  braid {X Y} : X ⨂ Y ≅ Y ⨂ X;
  braid_natural : natural (@braid);

  hexagon_identity {X Y Z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (X ⨂ Y) ⨂ Z ~~> Y ⨂ (Z ⨂ X) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id
}.

End BraidedMonoidal.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Binoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Premonoidal.

Context {C : Category}.

(*
Class Presemigroupoidal := {
  presemigroupoidal_is_binoidal : @Binoidal C;

  tensor_assoc {x y z} : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z);  (* alpha *)

  (* alpha is a central isomorphism. *)

  tensor_assoc_to_central {x y z} : central (to (@tensor_assoc x y z));
  tensor_assoc_from_central {x y z} : central (from (@tensor_assoc x y z));

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    g ⊗ (h ⊗ i) ∘ tensor_assoc
      << (x ⊗ z) ⊗ v ~~> y ⊗ w ⊗ u >>
    tensor_assoc ∘ (g ⊗ h) ⊗ i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    (g ⊗ h) ⊗ i ∘ tensor_assoc⁻¹
      << x ⊗ z ⊗ v ~~> (y ⊗ w) ⊗ u >>
    tensor_assoc⁻¹ ∘ g ⊗ (h ⊗ i);

  (* The above observe the following coherence conditions *)

  pentagon_identity {x y z w} :
    id ⊗ tensor_assoc ∘ tensor_assoc ∘ tensor_assoc ⊗ id
      << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
    tensor_assoc ∘ tensor_assoc
}.
#[export] Existing Instance presemigroupoidal_is_binoidal.
*)

Class Premonoidal := {
  premonoidal_is_binoidal : @Binoidal C;

  I : C;

  tensor_assoc {x y z} : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z);  (* alpha *)

  unit_right {x} : x ⊗ I ≅ x;  (* lambda *)
  unit_left  {x} : I ⊗ x ≅ x;  (* rho *)

  unit_left_to_central {x} : central (to (@unit_left x));
  unit_left_from_central {x} : central (from (@unit_left x));

  unit_right_to_central {x} : central (to (@unit_right x));
  unit_right_from_central {x} : central (from (@unit_right x));

  tensor_assoc_to_central {x y z} : central (to (@tensor_assoc x y z));
  tensor_assoc_from_central {x y z} : central (from (@tensor_assoc x y z));

  (* alpha, lambda and rho are all central isomorphisms. *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⊗ x ~~> y >> unit_left ∘ id ⊗ g;
  from_unit_left_natural {x y} (g : x ~> y) :
    id ⊗ g ∘ unit_left⁻¹ << x ~~> I ⊗ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⊗ I ~~> y >> unit_right ∘ g ⊗ id;
  from_unit_right_natural {x y} (g : x ~> y) :
    g ⊗ id ∘ unit_right⁻¹ << x ~~> y ⊗ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    g ⊗ (h ⊗ i) ∘ tensor_assoc
      << (x ⊗ z) ⊗ v ~~> y ⊗ w ⊗ u >>
    tensor_assoc ∘ (g ⊗ h) ⊗ i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    (g ⊗ h) ⊗ i ∘ tensor_assoc⁻¹
      << x ⊗ z ⊗ v ~~> (y ⊗ w) ⊗ u >>
    tensor_assoc⁻¹ ∘ g ⊗ (h ⊗ i);

  (* The above observe the following coherence conditions *)

  triangle_identity {x y} :
    unit_right ⊗ id
      << (x ⊗ I) ⊗ y ~~> x ⊗ y >>
    id ⊗ unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    id ⊗ tensor_assoc ∘ tensor_assoc ∘ tensor_assoc ⊗ id
      << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
    tensor_assoc ∘ tensor_assoc
}.
#[export] Existing Instance premonoidal_is_binoidal.

End Premonoidal.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Naturality.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidalProofs.

Context `{M : @Monoidal C}.

Lemma tensor_id_left_inj {X Y} (f g : X ~> Y) :
  id[I] ⨂ f ≈ id[I] ⨂ g -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_left).
  rewrite !comp_assoc.
  rewrite !to_unit_left_natural.
  rewrite X0.
  reflexivity.
Qed.

Lemma tensor_id_right_inj {X Y} (f g : X ~> Y) :
  f ⨂ id[I] ≈ g ⨂ id[I] -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_right).
  rewrite !comp_assoc.
  rewrite !to_unit_right_natural.
  rewrite X0.
  reflexivity.
Qed.

(* The following proofs are from the book "Tensor Categories", by Pavel
   Etingof, Shlomo Gelaki, Dmitri Nikshych, and Victor Ostrik. *)

(* Proposition 2.2.2 *)

Proposition id_unit_left {X} :
  id ⨂ unit_left ≈ @unit_left _ _ (I ⨂ X).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_left ∘ id ⨂ unit_left
            << I ⨂ (I ⨂ X) ~~> X >>
          unit_left ∘ unit_left).
    rewrite to_unit_left_natural; reflexivity.

  (* "Since lX is an isomorphism, the first identity follows." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_left).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

Proposition id_unit_right {X} :
  unit_right ⨂ id ≈ @unit_right _ _ (X ⨂ I).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_right ∘ unit_right ⨂ id
            << (X ⨂ I) ⨂ I ~~> X >>
          unit_right ∘ unit_right).
    rewrite to_unit_right_natural; reflexivity.

  (* "The second one follows similarly from naturality of r." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_right).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

(* Proposition 2.2.4 *)

Lemma bimap_id_unit_left {X Y Z} :
  id ⨂ (unit_left ⨂ id)
    << X ⨂ ((I ⨂ Y) ⨂ Z) ~~> X ⨂ (Y ⨂ Z) >>
  id ⨂ unit_left ∘ id ⨂ tensor_assoc.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (to_tensor_assoc_natural (id[X]) (@unit_left _ _ Y) (id[Z])) as X0.
  assert (X1 : ∀ X Y Z W (f g : (X ⨂ Y) ⨂ Z ~> W),
             f ≈ g -> f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
    intros; rewrite X2; reflexivity.
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_to_from, id_right in X0.
  rewrite X0; clear X0.
  rewrite comp_assoc; normal.

  pose proof (to_tensor_assoc_natural
                (@unit_right _ _ X) (id[Y]) (id[Z])) as X0.
  rewrite bimap_id_id in X0.
  rewrite triangle_identity in X0.
  rewrite triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_right in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : (X ⨂ I ⨂ Y) ⨂ Z ~{ C }~> X ⨂ Y ⨂ Z),
             f ∘ tensor_assoc ⨂ id ≈ g ∘ tensor_assoc ⨂ id
             -> f ≈ g).
    intros.
    assert (∀ X Y Z W V (f g : ((X ⨂ Y) ⨂ Z) ⨂ V ~> W),
               f ≈ g -> f ∘ (tensor_assoc⁻¹ ⨂ id[V]) ≈
                        g ∘ (tensor_assoc⁻¹ ⨂ id[V])).
      intros; rewrite X4; reflexivity.
    apply X3 in X2.
    normal.
    rewrite !iso_to_from in X2.
    rewrite !bimap_id_id, !id_right in X2.
    assumption.
  apply X2 in X0; clear X2.
  rewrite X0; clear X0.

  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_left {X Y} :
  unit_left ⨂ id
    << (I ⨂ X) ⨂ Y ~~> X ⨂ Y >>
  unit_left ∘ tensor_assoc.
Proof.
  (* "Setting X = 1 and applying the functor L−1 to the lower right triangle,
     1 we obtain commutativity of the triangle (2.12)." *)
  pose proof (@bimap_id_unit_left I X Y).
  normal.
  apply tensor_id_left_inj in X0.
  assumption.
Qed.

Theorem inverse_triangle_identity {X Y} :
  id ⨂ unit_left
    << X ⨂ (I ⨂ Y) ~~> X ⨂ Y >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Theorem inverse_pentagon_identity {X Y Z W} :
  tensor_assoc⁻¹ ⨂ id[W] ∘ tensor_assoc⁻¹ ∘ id[X] ⨂ tensor_assoc⁻¹
      << X ⨂ (Y ⨂ (Z ⨂ W)) ~~> ((X ⨂ Y) ⨂ Z) ⨂ W >>
  tensor_assoc⁻¹ ∘ tensor_assoc⁻¹.
Proof.
  apply (iso_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  apply (iso_epic tensor_assoc).
  rewrite iso_from_to.
  rewrite <- !comp_assoc.
  rewrite <- pentagon_identity.
  normal.
  rewrite iso_from_to; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to; normal.
  rewrite iso_from_to; normal.
  reflexivity.
Qed.

Lemma bimap_unit_right_id {X Y Z} :
  (id ⨂ unit_right) ⨂ id
    << (X ⨂ (Y ⨂ I)) ⨂ Z ~~> (X ⨂ Y) ⨂ Z >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹ ⨂ id.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (from_tensor_assoc_natural
                (id[X]) (@unit_right _ _ Y) (id[Z])) as X0.
  assert (X1 : ∀ X Y Z W (f g : X ⨂ (Y ⨂ Z) ~> W),
             f ≈ g -> f ∘ tensor_assoc ≈ g ∘ tensor_assoc).
    intros; rewrite X2; reflexivity.
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_from_to, id_right in X0.
  rewrite X0; clear X0.
  rewrite comp_assoc; normal.

  pose proof (from_tensor_assoc_natural
                (id[X]) (id[Y]) (@unit_left _ _ Z)) as X0.
  rewrite bimap_id_id in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- inverse_pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_left in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : X ⨂ ((Y ⨂ I) ⨂ Z) ~{ C }~> (X ⨂ Y) ⨂ Z),
             f ∘ id ⨂ tensor_assoc⁻¹ ≈ g ∘ id ⨂ tensor_assoc⁻¹
             -> f ≈ g).
    intros.
    assert (∀ X Y Z W V (f g : X ⨂ (Y ⨂ (Z ⨂ V)) ~> W),
               f ≈ g -> f ∘ (id[X] ⨂ tensor_assoc) ≈
                        g ∘ (id[X] ⨂ tensor_assoc)).
      intros; rewrite X4; reflexivity.
    apply X3 in X2.
    normal.
    rewrite !iso_from_to in X2.
    rewrite !bimap_id_id, !id_right in X2.
    assumption.
  apply X2 in X0; clear X2.
  rewrite X0; clear X0.

  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_right {X Y} :
  id ⨂ unit_right
    << X ⨂ (Y ⨂ I) ~~> X ⨂ Y >>
  unit_right ∘ tensor_assoc⁻¹.
Proof.
  pose proof (@bimap_unit_right_id X Y I).
  normal.
  apply tensor_id_right_inj in X0.
  assumption.
Qed.

Theorem bimap_triangle_right {X Y} :
  unit_right
    << (X ⨂ Y) ⨂ I ~~> X ⨂ Y >>
  bimap id unit_right ∘ to tensor_assoc.
Proof.
  rewrite triangle_identity_right.
  rewrite <- comp_assoc.
  rewrite iso_from_to; cat.
Qed.

Theorem bimap_triangle_left {X Y} :
  unit_left
    << I ⨂ (X ⨂ Y) ~~> X ⨂ Y >>
  bimap unit_left id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Corollary unit_identity :
  to (@unit_left _ _ I) ≈ to (@unit_right _ _ I).
Proof.
  pose proof (@bimap_id_unit_left I I I).
  pose proof (@triangle_identity _ _ I I).
  normal.
  rewrite id_unit_left in X0.
  rewrite <- X0 in X; clear X0.
  apply tensor_id_left_inj in X.
  apply tensor_id_right_inj in X.
  apply X.
Qed.

End MonoidalProofs.

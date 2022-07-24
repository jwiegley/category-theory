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

Lemma tensor_id_left_inj {x y} (f g : x ~> y) :
  id[I] ⨂ f ≈ id[I] ⨂ g -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_left).
  rewrite !comp_assoc.
  rewrite !to_unit_left_natural.
  rewrites; reflexivity.
Qed.

Lemma tensor_id_right_inj {x y} (f g : x ~> y) :
  f ⨂ id[I] ≈ g ⨂ id[I] -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_right).
  rewrite !comp_assoc.
  rewrite !to_unit_right_natural.
  rewrites; reflexivity.
Qed.

(* The following proofs are from the book "Tensor Categories", by Pavel
   Etingof, Shlomo Gelaki, Dmitri Nikshych, and Victor Ostrik. *)

(* Proposition 2.2.2 *)

Proposition id_unit_left {x} :
  id ⨂ unit_left ≈ @unit_left _ _ (I ⨂ x).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_left ∘ id ⨂ unit_left
            << I ⨂ (I ⨂ x) ~~> x >>
            unit_left ∘ unit_left)
    by (rewrite to_unit_left_natural; reflexivity).

  (* "Since lX is an isomorphism, the first identity follows." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_left).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

Proposition id_unit_right {x} :
  unit_right ⨂ id ≈ @unit_right _ _ (x ⨂ I).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_right ∘ unit_right ⨂ id
            << (x ⨂ I) ⨂ I ~~> x >>
          unit_right ∘ unit_right)
    by (rewrite to_unit_right_natural; reflexivity).

  (* "The second one follows similarly from naturality of r." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_right).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

(* Proposition 2.2.4 *)

Lemma bimap_id_unit_left {x y z} :
  id ⨂ (unit_left ⨂ id)
    << x ⨂ ((I ⨂ y) ⨂ z) ~~> x ⨂ (y ⨂ z) >>
  id ⨂ unit_left ∘ id ⨂ tensor_assoc.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (to_tensor_assoc_natural (id[x]) (@unit_left _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : (x ⨂ y) ⨂ z ~> w),
             f ≈ g -> f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
  { intros; rewrites; reflexivity. }
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_to_from, id_right in X0.
  rewrites.
  rewrite comp_assoc; normal.

  pose proof (to_tensor_assoc_natural
                (@unit_right _ _ x) (id[y]) (id[z])) as X0.
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

  assert (X2 : ∀ (f g : (x ⨂ I ⨂ y) ⨂ z ~{ C }~> x ⨂ y ⨂ z),
             f ∘ tensor_assoc ⨂ id ≈ g ∘ tensor_assoc ⨂ id
             -> f ≈ g).
    intros.
    assert (X3 : ∀ x y z w v (f g : ((x ⨂ y) ⨂ z) ⨂ v ~> w),
               f ≈ g -> f ∘ (tensor_assoc⁻¹ ⨂ id[v]) ≈
                        g ∘ (tensor_assoc⁻¹ ⨂ id[v])).
      intros; rewrites; reflexivity.
    apply X3 in X.
    normal.
    rewrite !iso_to_from in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_left {x y} :
  unit_left ⨂ id
    << (I ⨂ x) ⨂ y ~~> x ⨂ y >>
  unit_left ∘ tensor_assoc.
Proof.
  (* "Setting x = 1 and applying the functor L−1 to the lower right triangle,
     1 we obtain commutativity of the triangle (2.12)." *)
  pose proof (@bimap_id_unit_left I x y).
  normal.
  apply tensor_id_left_inj in X.
  assumption.
Qed.

Theorem inverse_triangle_identity {x y} :
  id ⨂ unit_left
    << x ⨂ (I ⨂ y) ~~> x ⨂ y >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Theorem inverse_pentagon_identity {x y z w} :
  tensor_assoc⁻¹ ⨂ id[w] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ tensor_assoc⁻¹
      << x ⨂ (y ⨂ (z ⨂ w)) ~~> ((x ⨂ y) ⨂ z) ⨂ w >>
  tensor_assoc⁻¹ ∘ tensor_assoc⁻¹.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  apply (iso_to_epic tensor_assoc).
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

Lemma bimap_unit_right_id {x y z} :
  (id ⨂ unit_right) ⨂ id
    << (x ⨂ (y ⨂ I)) ⨂ z ~~> (x ⨂ y) ⨂ z >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹ ⨂ id.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (from_tensor_assoc_natural
                (id[x]) (@unit_right _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : x ⨂ (y ⨂ z) ~> w),
             f ≈ g -> f ∘ tensor_assoc ≈ g ∘ tensor_assoc).
    intros; rewrites; reflexivity.
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_from_to, id_right in X0.
  rewrites.
  rewrite comp_assoc; normal.

  pose proof (from_tensor_assoc_natural
                (id[x]) (id[y]) (@unit_left _ _ z)) as X0.
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

  assert (X2 : ∀ (f g : x ⨂ ((y ⨂ I) ⨂ z) ~{ C }~> (x ⨂ y) ⨂ z),
             f ∘ id ⨂ tensor_assoc⁻¹ ≈ g ∘ id ⨂ tensor_assoc⁻¹
             -> f ≈ g).
    intros.
    assert (X3 : ∀ x y z w v (f g : x ⨂ (y ⨂ (z ⨂ v)) ~> w),
               f ≈ g -> f ∘ (id[x] ⨂ tensor_assoc) ≈
                        g ∘ (id[x] ⨂ tensor_assoc)).
      intros; rewrites; reflexivity.
    apply X3 in X.
    normal.
    rewrite !iso_from_to in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_right {x y} :
  id ⨂ unit_right
    << x ⨂ (y ⨂ I) ~~> x ⨂ y >>
  unit_right ∘ tensor_assoc⁻¹.
Proof.
  pose proof (@bimap_unit_right_id x y I).
  normal.
  apply tensor_id_right_inj in X.
  assumption.
Qed.

Theorem bimap_triangle_right {x y} :
  unit_right
    << (x ⨂ y) ⨂ I ~~> x ⨂ y >>
  bimap id unit_right ∘ to tensor_assoc.
Proof.
  rewrite triangle_identity_right.
  rewrite <- comp_assoc.
  rewrite iso_from_to; cat.
Qed.

Theorem bimap_triangle_left {x y} :
  unit_left
    << I ⨂ (x ⨂ y) ~~> x ⨂ y >>
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

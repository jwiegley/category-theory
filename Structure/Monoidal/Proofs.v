Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   These are the derived unit-coherence lemmas of a monoidal category: the
   consequences of the triangle and pentagon axioms (and the naturality of
   the unitors and associator) that Mac Lane's coherence theorem guarantees
   without making them part of the data. They are sometimes called Kelly's
   lemmas, after G. M. Kelly, "On MacLane's conditions for coherence of
   natural associativities, commutativities, etc." (J. Algebra 1, 1964),
   which showed that several of the original Mac Lane axioms are redundant.
   What is established here:

     - left/right tensoring by id[I] is injective on morphisms;
     - id ⨂ λ ≈ λ and ρ ⨂ id ≈ ρ at the appropriate objects
       (Etingof et al., Proposition 2.2.2);
     - the variant triangle identities relating each unitor to the
       associator (e.g. λ ⨂ id ≈ λ ∘ α);
     - the pentagon identity in the inverse (α⁻¹) direction;
     - λ_I ≈ ρ_I, the two unitors agree on the unit object
       (Kelly 1964; [unit_identity]).

   Orientation note: as in [Structure/Monoidal.v], the associator is taken
   as α : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z), following nLab. Some sources use the
   opposite orientation; the statements below differ from those only by
   inverses. *)

Section MonoidalProofs.

Context `{M : @Monoidal C}.

(* Left tensoring by id[I] reflects equality of morphisms: it is a faithful
   operation because λ (unit_left) is a natural isomorphism. Used to cancel a
   leading [id[I] ⨂ -] when deriving the variant triangle identities. *)

Lemma tensor_id_left_inj {x y} (f g : x ~> y) :
  id[I] ⨂ f ≈ id[I] ⨂ g → f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_left).
  rewrite !comp_assoc.
  rewrite !to_unit_left_natural.
  rewrites; reflexivity.
Qed.

(* The mirror of [tensor_id_left_inj]: right tensoring by id[I] is faithful,
   since ρ (unit_right) is a natural isomorphism. *)

Lemma tensor_id_right_inj {x y} (f g : x ~> y) :
  f ⨂ id[I] ≈ g ⨂ id[I] → f ≈ g.
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

(* The left unitor is compatible with the tensor on the unit side:
   id[I] ⨂ λ_x ≈ λ_{I ⨂ x}. Following Etingof et al., this is read off from
   naturality of λ (the square below) together with λ being an isomorphism. *)

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

(* The mirror of [id_unit_left] for the right unitor:
   ρ_x ⨂ id[I] ≈ ρ_{x ⨂ I}, from naturality of ρ and ρ being an iso. *)

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

(* Helper diagram for the variant left triangle identity. It expresses the
   commutativity of the "lower right triangle" obtained by pasting the
   associator-naturality square against the pentagon and the triangle axiom;
   [triangle_identity_left] is recovered from it by specializing x = I and
   cancelling the leading [id[I] ⨂ -] via [tensor_id_left_inj]. *)

Lemma bimap_id_unit_left {x y z} :
  id ⨂ (unit_left ⨂ id)
    << x ⨂ ((I ⨂ y) ⨂ z) ~~> x ⨂ (y ⨂ z) >>
  id ⨂ unit_left ∘ id ⨂ tensor_assoc.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (to_tensor_assoc_natural (id[x]) (@unit_left _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : (x ⨂ y) ⨂ z ~> w),
             f ≈ g → f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
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
             → f ≈ g). {
    intros.
    assert (X3 : ∀ x y z w v (f g : ((x ⨂ y) ⨂ z) ⨂ v ~> w),
               f ≈ g → f ∘ (tensor_assoc⁻¹ ⨂ id[v]) ≈
                        g ∘ (tensor_assoc⁻¹ ⨂ id[v])). {
      intros; rewrites; reflexivity.
    }
    apply X3 in X.
    normal.
    rewrite !iso_to_from in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  }
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* Variant triangle identity, the unit-on-the-left form: λ ⨂ id ≈ λ ∘ α.
   This is Kelly's lemma λ_x ⨂ id_y ≈ λ_{x ⨂ y} ∘ α_{I,x,y}, a derived
   coherence consequence (not part of the monoidal data). *)

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

(* The original triangle axiom (ρ ⨂ id ≈ id ⨂ λ ∘ α) rewritten across the
   inverse associator: id ⨂ λ ≈ (ρ ⨂ id) ∘ α⁻¹. Just the axiom post-composed
   with α⁻¹ and simplified, so no new content beyond [triangle_identity]. *)

Theorem inverse_triangle_identity {x y} :
  id ⨂ unit_left
    << x ⨂ (I ⨂ y) ~~> x ⨂ y >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

(* The pentagon axiom in the inverse (α⁻¹) direction, obtained by inverting
   both sides of [pentagon_identity] and reversing the composition order:
   (α⁻¹ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ α⁻¹) ≈ α⁻¹ ∘ α⁻¹. Used by [bimap_unit_right_id]. *)

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

(* Right-handed mirror of [bimap_id_unit_left]: the helper diagram from which
   [triangle_identity_right] is recovered. Built by pasting the inverse
   associator-naturality square against the inverse pentagon and the inverse
   triangle identity, then cancelling the trailing [- ⨂ id]. *)

Lemma bimap_unit_right_id {x y z} :
  (id ⨂ unit_right) ⨂ id
    << (x ⨂ (y ⨂ I)) ⨂ z ~~> (x ⨂ y) ⨂ z >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹ ⨂ id.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (from_tensor_assoc_natural
                (id[x]) (@unit_right _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : x ⨂ (y ⨂ z) ~> w),
             f ≈ g → f ∘ tensor_assoc ≈ g ∘ tensor_assoc). {
    intros; rewrites; reflexivity.
  }
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
             → f ≈ g). {
    intros.
    assert (X3 : ∀ x y z w v (f g : x ⨂ (y ⨂ (z ⨂ v)) ~> w),
               f ≈ g → f ∘ (id[x] ⨂ tensor_assoc) ≈
                        g ∘ (id[x] ⨂ tensor_assoc)). {
      intros; rewrites; reflexivity.
    }
    apply X3 in X.
    normal.
    rewrite !iso_from_to in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  }
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

(* Variant triangle identity, the unit-on-the-right form: id ⨂ ρ ≈ ρ ∘ α⁻¹.
   The Kelly lemma ρ_{x ⨂ y} ≈ (id_x ⨂ ρ_y) ∘ α_{x,y,I}, here stated across
   α⁻¹; the right-handed companion of [triangle_identity_left]. *)

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

(* [triangle_identity_right] solved for ρ across the forward associator:
   ρ ≈ (id ⨂ ρ) ∘ α. The α/α⁻¹ pair cancels, so this restates the previous
   lemma with α on the right rather than α⁻¹. *)

Theorem bimap_triangle_right {x y} :
  unit_right
    << (x ⨂ y) ⨂ I ~~> x ⨂ y >>
  bimap id unit_right ∘ to tensor_assoc.
Proof.
  rewrite triangle_identity_right.
  rewrite <- comp_assoc.
  rewrite iso_from_to; cat.
Qed.

(* The left companion of [bimap_triangle_right]: λ ≈ (λ ⨂ id) ∘ α⁻¹, i.e.
   [triangle_identity_left] solved for λ across the inverse associator. *)

Theorem bimap_triangle_left {x y} :
  unit_left
    << I ⨂ (x ⨂ y) ~~> x ⨂ y >>
  bimap unit_left id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

(* Kelly's lemma (Kelly 1964): the two unitors agree on the unit object,
   λ_I ≈ ρ_I : I ⨂ I ~> I. This is the canonical derived coherence fact, and
   it underlies, e.g., the commutativity of End(I) via Eckmann-Hilton. It is
   obtained here by combining the helper diagram [bimap_id_unit_left] at
   x = y = I with the triangle axiom and [id_unit_left], then cancelling the
   id[I]-tensorings on both sides. *)

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

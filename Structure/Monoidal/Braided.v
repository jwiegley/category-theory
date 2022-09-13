Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section BraidedMonoidal.

Context {C : Category}.

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

Coercion braided_is_monoidal : BraidedMonoidal >-> Monoidal.

Context `{BraidedMonoidal}.

Theorem Yang_Baxter_equation {a b c : C} :
  braid ⨂ id[a] ∘ tensor_assoc⁻¹
    ∘ id[b] ⨂ braid ∘ tensor_assoc
    ∘ braid ⨂ id[c] ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ id[c] ⨂ braid
        ∘ tensor_assoc ∘ braid ⨂ id[b]
        ∘ tensor_assoc⁻¹ ∘ id[a] ⨂ braid.
Proof.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite iso_to_from, id_right.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite (@comp_assoc _ _ _ _ _ _ tensor_assoc⁻¹).
  rewrite iso_to_from, id_left.
  destruct H.
  simpl in *.
  specialize (braid_natural0 a _ id _ _ (braid0 b c)).
  rewrite bimap_id_id in braid_natural0.
  rewrite id_right in braid_natural0.
  rewrite braid_natural0.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

End BraidedMonoidal.

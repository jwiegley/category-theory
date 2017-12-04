Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Cartesian.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Proofs.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section GroupObject.

Context {C : Category}.
Context `{@Monoidal C}.
Context `{@CartesianMonoidal C _}.

Class GroupObject (grp : C) := {
  monoid_structure :> MonoidObject grp;
  inverse : grp ~> grp;

  (* inverse g⁻¹ ⨂ g ≈ I *)
  left_inverse : mappend ∘ bimap inverse id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (* g ⨂ g⁻¹ ≈ I *)
  right_inverse : mappend ∘ bimap id inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.

Context (grp : C).
Context `{@GroupObject grp}.

Lemma mempty_left_diagonal : mappend ∘ id ⨂ (mempty ∘ eliminate) ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  rewrite mempty_right.
  apply proj_left_diagonal.
Qed.

Lemma mempty_right_diagonal : mappend ∘ (mempty ∘ eliminate) ⨂ id ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite mempty_left.
  apply proj_right_diagonal.
Qed.

Lemma inverse_unique
  (X : C) (f : X ~> grp) (f_inv : X ~> grp)
  (f_left_inverse : mappend ∘ f_inv ⨂ f ∘ ∆ X ≈ mempty ∘ eliminate)
  : f_inv ≈ inverse ∘ f.
Proof.
  rewrite <- id_left.
  rewrite <- mempty_left_diagonal.
  rewrite <- comp_assoc.
  rewrite <- (diagonal_natural _ _ f_inv); simpl.
  rewrite comp_assoc; rewrite <- (comp_assoc mappend _ _).
  rewrite <- bimap_comp.
  rewrite <- (comp_assoc _ eliminate _).
  rewrite (unit_terminal (eliminate ∘ f_inv) (eliminate ∘ f)).
  rewrite (comp_assoc _ eliminate _).
  rewrite <- right_inverse.
  rewrite <- !comp_assoc.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ _ f).
  rewrite <- (diagonal_natural _ _ f); simpl.
  rewrite (comp_assoc _ (f ⨂ f) _).
  rewrite <- bimap_comp.
  rewrite id_left.
  rewrite <- (id_right f_inv).
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite comp_assoc.
  rewrite <- comp_assoc.
  rewrite diagonal_tensor_assoc.
  rewrite <- (comp_assoc tensor_assoc _ _); rewrite (comp_assoc _ tensor_assoc _); rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to; rewrite id_right.
  rewrite <- comp_assoc; rewrite (comp_assoc _ _ (∆ X)).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (mappend ⨂ id) _ _).
  rewrite <- bimap_comp.
  rewrite (comp_assoc mappend (f_inv ⨂ f) _).
  rewrite f_left_inverse.
  rewrite (unit_terminal eliminate (eliminate ∘ (inverse ∘ f))).
  rewrite (comp_assoc _ eliminate _).
  rewrite bimap_comp.
  rewrite <- (comp_assoc _ _ (∆ X)).
  assert ((inverse ∘ f) ⨂ (inverse ∘ f) ≈ map (inverse ∘ f)) as h.
    simpl. reflexivity.
  rewrite h.
  rewrite (diagonal_natural _ _ (inverse ∘ f)).
  simpl.
  rewrite !comp_assoc.
  rewrite mempty_right_diagonal.
  cat.

  (*
    f_inv
  = id ∘ f_inv
  = (mappend ∘ bimap id (mempty ∘ eliminate) ∘ ∆ grp) ∘ f_inv
  = mappend ∘ bimap id (mempty ∘ eliminate) ∘ (∆ grp ∘ f_inv)
  = mappend ∘ bimap id (mempty ∘ eliminate) ∘ (bimap f_inv f_inv ∘ ∆ X)
  = mappend ∘ (bimap id (mempty ∘ eliminate) ∘ (bimap f_inv f_inv ∘ ∆ X))
  = mappend ∘ bimap (id ∘ f_inv) (mempty ∘ eliminate ∘ f_inv) ∘ ∆ X
  = mappend ∘ bimap f_inv (mempty ∘ eliminate ∘ f) ∘ ∆ X
  = mappend ∘ bimap f_inv (mappend ∘ bimap id inverse ∘ ∆ grp ∘ f) ∘ ∆ X
  = mappend ∘ bimap id mappend ∘ bimap f_inv (bimap id inverse ∘ ∆ grp ∘ f) ∘ ∆ X
  = (mappend ∘ bimap id mappend) ∘ (bimap f_inv (bimap id inverse ∘ ∆ grp ∘ f) ∘ ∆ X)
  = (mappend ∘ bimap mappend id) ∘ (bimap f_inv (bimap id inverse ∘ ∆ grp ∘ f) ∘ ∆ X)
  = (mappend ∘ bimap mappend id) ∘ (bimap f_inv (bimap f (inverse ∘ f) ∘ ∆ X) ∘ ∆ X)
  = (mappend ∘ bimap mappend id) ∘ (bimap (bimap f_inv f ∘ ∆ X) (inverse ∘ f) ∘ ∆ X)
  = mappend ∘ (bimap mappend id ∘ bimap (bimap f_inv f ∘ ∆ X) (inverse ∘ f)) ∘ ∆ X
  = mappend ∘ bimap (mappend ∘ bimap f_inv f ∘ ∆ X) (inverse ∘ f) ∘ ∆ X
  = mappend ∘ bimap (empty ∘ eliminate) (inverse ∘ f) ∘ ∆ X
  = mappend ∘ bimap (empty ∘ eliminate ∘ (inverse ∘ f)) (inverse ∘ f) ∘ ∆ X
  = mappend ∘ bimap (empty ∘ eliminate ∘ (inverse ∘ f)) (id ∘ (inverse ∘ f)) ∘ ∆ X
  = mappend ∘ (bimap (empty ∘ eliminate) id ∘ bimap (inverse ∘ f) (inverse ∘ f)) ∘ ∆ X
  = mappend ∘ bimap (empty ∘ eliminate) id ∘ (bimap (inverse ∘ f) (inverse ∘ f)) ∘ ∆ X)
  = mappend ∘ bimap (empty ∘ eliminate) id ∘ (bimap (inverse ∘ f) (inverse ∘ f) ∘ ∆ X)
  = mappend ∘ bimap (empty ∘ eliminate) id ∘ (∆ grp ∘ inverse ∘ f)
  = (mappend ∘ bimap (empty ∘ eliminate) id ∘ ∆ grp) ∘ inverse ∘ f
  = id ∘ inverse ∘ f
  = inverse ∘ f
    (modulo associators)
  *)
Qed.

Lemma mappend_inverse : mappend ∘ inverse ⨂ inverse ≈ inverse ∘ mappend ∘ twist.
Proof.
  rewrite <- (comp_assoc inverse mappend twist).
  apply inverse_unique.
  rewrite bimap_comp.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite mappend_assoc.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc; rewrite <- (comp_assoc _ (id ⨂ mappend) _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc mappend _ _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite diagonal_twist2.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ tensor_assoc (tensor_assoc ⁻¹)).
  rewrite iso_to_from; rewrite id_right.
  rewrite <- (comp_assoc _ (inverse ⨂ _) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite hexagon_rotated.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (inverse ⨂ twist) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite twist_invol.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to; rewrite id_right.
  rewrite <- (bimap_id_left_right ∆grp ∆grp).
  rewrite !comp_assoc; rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- bimap_id_id.
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc mappend (inverse ⨂ _) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite <- (comp_assoc _ twist _).
  rewrite <- bimap_twist.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ ((inverse ⨂ id) ⨂ id) _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite <- (comp_assoc _ (mappend ⨂ id) _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite !comp_assoc.
  rewrite left_inverse.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  rewrite mempty_left.
  rewrite <- (comp_assoc _ (eliminate ⨂ id) twist).
  rewrite bimap_twist.
  rewrite comp_assoc.
  rewrite unit_left_twist.

  rewrite <- (id_left inverse).
  rewrite bimap_comp.
  rewrite comp_assoc; rewrite <- (comp_assoc _ _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  rewrite comp_assoc.
  rewrite triangle_identity_right.
  rewrite comp_assoc; rewrite <- (comp_assoc _ _ tensor_assoc).
  rewrite iso_from_to; rewrite id_right.
  rewrite <- (comp_assoc _ _ (∆grp ⨂ id[grp])).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ unit_right _).
  rewrite <- to_unit_right_natural.
  rewrite !comp_assoc.
  rewrite left_inverse.
  rewrite <- !comp_assoc.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(* TODO: inverse ∘ inverse = id *)

End GroupObject.

Notation "inverse [ G ]" := (@inverse _ _ _ G)
  (at level 9, format "inverse [ G ]") : category_scope.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.

Generalizable All Variables.

Section CartesianMonoid.

Context `{@CartesianMonoidal C}.
Context (mon : C).
Context `{@MonoidObject C _ grp}.

Lemma mempty_right_diagonal : mappend ∘ id ⨂ (mempty ∘ eliminate) ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  rewrite mempty_right.
  apply proj_left_diagonal.
Qed.

Lemma mempty_left_diagonal : mappend ∘ (mempty ∘ eliminate) ⨂ id ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite mempty_left.
  apply proj_right_diagonal.
Qed.

End CartesianMonoid.

Section GroupProofs.

Context `{@CartesianMonoidal C}.
Context (grp : C).
Context `{@GroupObject C _ grp}.

(* This proof is analogous to the following
   proof that y = x⁻¹ for an
   element y with yx = I:

     y = yI
       = y(xx⁻¹)
       = (yx)x⁻¹
       = (yx)x⁻¹
       = Ix⁻¹
       = x⁻¹ *)
Lemma left_inverse_unique
  (X : C) (f : X ~> grp) (f_inv : X ~> grp)
  (f_left_inverse : mappend ∘ f_inv ⨂ f ∘ ∆ X ≈ mempty ∘ eliminate) :
  f_inv ≈ inverse[grp] ∘ f.
Proof.
  rewrite <- (id_left f_inv).
  (* ... = yI *)
  rewrite <- mempty_right_diagonal.
  rewrite <- (comp_assoc _ ∆grp f_inv).
  rewrite <- (diagonal_natural _ _ f_inv); simpl.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (_ ⨂ _) (_ ⨂ _)).
  rewrite <- bimap_comp.
  rewrite <- (comp_assoc _ eliminate _).
  rewrite (unit_terminal (eliminate ∘ f_inv) (eliminate ∘ f)).
  rewrite !comp_assoc.
  (* ... = y(xx⁻¹) *)
  rewrite <- right_inverse.
  assert (mappend ∘ id ⨂ inverse[grp] ∘ ∆grp ∘ f ≈ mappend ∘ (id ⨂ inverse[grp] ∘ ∆grp ∘ f)) as R by cat;
    rewrite R; clear R.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  (* ... = (yx)x⁻¹ *)
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ _ f).
  rewrite <- (diagonal_natural _ _ f); simpl.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite <- (id_right f_inv).
  rewrite bimap_comp.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (id ⨂ ∆X) (∆X)).
  rewrite diagonal_tensor_assoc.
  rewrite <- (comp_assoc tensor_assoc _ _); rewrite (comp_assoc _ tensor_assoc _); rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to; rewrite id_right.
  rewrite !comp_assoc; rewrite <- 2!(comp_assoc mappend _ _).
  rewrite <- 2!bimap_comp; rewrite id_right.
  rewrite !comp_assoc.
  (* ... = Ix⁻¹ *)
  rewrite f_left_inverse.
  rewrite (unit_terminal eliminate (eliminate ∘ (inverse[grp] ∘ f))).
  rewrite !comp_assoc; rewrite <- 2!(comp_assoc _ inverse[grp] f).
  rewrite bimap_comp.
  rewrite <- (comp_assoc _ _ ∆X).
  assert ((inverse[grp] ∘ f) ⨂ (inverse[grp] ∘ f) ≈ map (inverse[grp] ∘ f)) as R
    by reflexivity; rewrite R; clear R.
  rewrite <- (comp_assoc _ _ ∆X).
  rewrite (diagonal_natural _ _ (inverse[grp] ∘ f)).
  simpl.
  rewrite !comp_assoc.
  (* ... = x⁻¹ *)
  rewrite mempty_left_diagonal.
  cat.
Qed.

(* This proof is analogous to the following
   proof y⁻¹x⁻¹ = (xy)⁻¹: Calculate

     (y⁻¹x⁻¹)(xy) = y⁻¹(x⁻¹(xy))
                  = y⁻¹((x⁻¹x)y)
                  = y⁻¹(Iy)
                  = y⁻¹y
                  = I

   Then use the lemma above. *)
Lemma mappend_inverse : mappend ∘ inverse[grp] ⨂ inverse[grp] ≈ inverse[grp] ∘ mappend ∘ braid.
Proof.
  rewrite <- (comp_assoc inverse[grp] mappend braid).
  apply left_inverse_unique.
  (* (y⁻¹x⁻¹)(xy) = ... *)
  rewrite bimap_comp.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  (* ... = y⁻¹(x⁻¹(xy)) *)
  rewrite mappend_assoc.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc; rewrite <- (comp_assoc _ (id ⨂ mappend) _).
  rewrite <- bimap_comp; rewrite id_left.
  (* ... = y⁻¹((x⁻¹x)y) *)
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc mappend _ _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite diagonal_braid2.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ tensor_assoc (tensor_assoc ⁻¹)).
  rewrite iso_to_from; rewrite id_right.
  rewrite <- (comp_assoc _ (inverse[grp] ⨂ _) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite hexagon_rotated.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (inverse[grp] ⨂ braid) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite braid_invol.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to; rewrite id_right.
  rewrite <- (bimap_id_left_right ∆grp ∆grp).
  rewrite !comp_assoc; rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- bimap_id_id.
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc; rewrite <- (comp_assoc mappend (inverse[grp] ⨂ _) _).
  rewrite <- bimap_comp; rewrite id_right.
  rewrite <- (comp_assoc _ braid _).
  rewrite <- bimap_braid.
  rewrite !comp_assoc; rewrite <- (comp_assoc _ ((inverse[grp] ⨂ id) ⨂ id) _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite <- (comp_assoc _ (mappend ⨂ id) _).
  rewrite <- bimap_comp; rewrite id_left.
  rewrite !comp_assoc.
  (* ... = y⁻¹(Iy) *)
  rewrite left_inverse.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  (* ... = y⁻¹y *)
  rewrite mempty_left.
  rewrite <- (comp_assoc _ (eliminate ⨂ id) braid).
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite unit_left_braid.
  rewrite <- (id_left inverse[grp]).
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
  (* ... = I *)
  rewrite left_inverse.
  rewrite <- !comp_assoc.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End GroupProofs.

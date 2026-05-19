Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.Cospan.SCFA.

Generalizable All Variables.

(** * [Hypergraph (CospanCat C HP)] : the full hypergraph instance

    Building on [cospan_scfa] from [SCFA.v], we discharge the eight
    coherence axioms of the [Hypergraph] class.

    The four UNIT axioms ([scfa_unit_{mu/eta/delta/epsilon}]) follow by
    initiality: every morphism out of [0] is unique, so any cospan with
    apex containing [0] or [0+0] is canonically determined.

    The four TENSOR axioms ([scfa_tensor_{mu/eta/delta/epsilon}]) reduce
    to C-level identities relating the codiagonal/zero structure of
    [X+Y] to the same structure on [X] and [Y] composed through the
    middle-swap [mid_swap X Y]. *)

Section CospanHypergraphInstance.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** ** Unit coherence (cheaper) *)

(** [scfa_mu (scfa I) ≈ to unit_left] : at the cospan level, both
    [mor_as_cospan (id▽id : 0+0 → 0)] and [mor_as_cospan (to coprod_zero_l)]
    are equal because all morphisms with codomain [0] are equal by
    initiality. *)
Lemma cospan_scfa_unit_mu :
  cospan_equiv
    (cospan_scfa_mu (@Cospan_unit_obj C H_Ini))
    (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini
                          (@Cospan_unit_obj C H_Ini)))).
Proof.
  unfold cospan_scfa_mu, Cospan_unit_obj.
  apply mor_as_cospan_proper.
  (* (id ▽ id : 0+0 → 0) ≈ (to coprod_zero_l : 0+0 → 0) = (zero ▽ id) *)
  unfold to, coprod_zero_l; simpl.
  apply (snd (merge_inv _ _ _ _)).
  split.
  - apply (@zero_unique C H_Ini _ _ _).
  - reflexivity.
Defined.

(** [scfa_eta (scfa I) ≈ id[I]] : both are morphisms in/out of 0; trivial. *)
Lemma cospan_scfa_unit_eta :
  cospan_equiv
    (cospan_scfa_eta (@Cospan_unit_obj C H_Ini))
    (cospan_id (@Cospan_unit_obj C H_Ini)).
Proof.
  unfold cospan_scfa_eta, Cospan_unit_obj.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_proper.
    apply (@zero_unique C H_Ini _ _ id[initial_obj]). }
  apply mor_as_cospan_id.
Defined.

(** [scfa_delta (scfa I) ≈ from unit_left] : analogous to mu, but with
    backward cospans. *)
Lemma cospan_scfa_unit_delta :
  cospan_equiv
    (cospan_scfa_delta (@Cospan_unit_obj C H_Ini))
    (mor_as_cospan (from (@coprod_zero_l C H_Coc H_Ini
                            (@Cospan_unit_obj C H_Ini)))).
Proof.
  unfold cospan_scfa_delta, Cospan_unit_obj, mor_as_cospan; simpl.
  (* Build_CospanArrow 0 id (id▽id : 0+0 → 0)
     vs Build_CospanArrow (0+0) (from coprod_zero_l) id.
     Apex iso: phi = iso_sym coprod_zero_l : 0 ≅ 0+0.
     to phi = from coprod_zero_l ✓.
     to phi ∘ (id▽id) ≈ id[0+0] by initiality (0+0 → 0+0 from 0 source). *)
  exists (iso_sym (@coprod_zero_l C H_Coc H_Ini (@Cospan_unit_obj C H_Ini))).
  simpl; split.
  - apply id_right.
  - (* from coprod_zero_l ∘ (id ▽ id) ≈ id[0+0]
       By coprod_ext: ∘ inl gives inr ≈ inl in 0 → 0+0 (initiality);
                      ∘ inr gives inr ≈ inr (reflexivity).      *)
    apply coprod_ext.
    + rewrite <- comp_assoc.
      rewrite inl_merge.
      rewrite id_right.
      rewrite id_left.
      apply (@zero_unique C H_Ini _ _ _).
    + rewrite <- comp_assoc.
      rewrite inr_merge.
      rewrite id_right.
      rewrite id_left.
      unfold from, coprod_zero_l; simpl.
      reflexivity.
Defined.

(** [scfa_epsilon (scfa I) ≈ id[I]]. *)
Lemma cospan_scfa_unit_epsilon :
  cospan_equiv
    (cospan_scfa_epsilon (@Cospan_unit_obj C H_Ini))
    (cospan_id (@Cospan_unit_obj C H_Ini)).
Proof.
  unfold cospan_scfa_epsilon, Cospan_unit_obj, cospan_id; simpl.
  (* Build_CospanArrow 0 id zero vs Build_CospanArrow 0 id id.
     Use iso_id, but show zero ≈ id at 0 → 0 by initiality. *)
  exists iso_id; simpl; split.
  - cat.
  - rewrite id_left.
    apply (@zero_unique C H_Ini _ _ _).
Defined.

(** ** Tensor coherence: [scfa_tensor_eta]

    Both [scfa_eta (X⨂Y)] and [canonical_tensor_eta (scfa X) (scfa Y)]
    reduce to [mor_as_cospan zero : 0 → X+Y] after lifting through
    [mor_as_cospan_compose] and [cospan_tensor_mor_as_cospan]. *)

Lemma cospan_scfa_tensor_eta (X Y : C) :
  cospan_equiv
    (cospan_scfa_eta (X + Y))
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_eta X) (cospan_scfa_eta Y))
       (mor_as_cospan (from (@coprod_zero_l C H_Coc H_Ini
                               (@Cospan_unit_obj C H_Ini))))).
Proof.
  unfold cospan_scfa_eta, Cospan_tensor_obj.
  (* RHS: cospan_tensor (mor_as_cospan zero) (mor_as_cospan zero)
        ≈ mor_as_cospan (cover zero zero).
     Then compose with mor_as_cospan (from coprod_zero_l)
        ≈ mor_as_cospan ((cover zero zero) ∘ from coprod_zero_l). *)
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  (* C-level: (cover zero zero : 0+0 → X+Y) ∘ (from coprod_zero_l : 0 → 0+0) ≈ zero *)
  (* from coprod_zero_l = inr : 0 → 0+0.  cover zero zero ∘ inr = inr ∘ zero = zero. *)
  unfold from, coprod_zero_l; simpl.
  rewrite cover_inr.
  apply (@zero_unique C H_Ini _ _ _).
Defined.

(** ** Tensor coherence: [scfa_tensor_epsilon]

    [scfa_epsilon (X⨂Y) ≈ canonical_tensor_epsilon] :
    both reduce to [mor_as_cospan_back (zero : 0 → X+Y)]. *)

Lemma cospan_scfa_tensor_epsilon (X Y : C) :
  cospan_equiv
    (cospan_scfa_epsilon (X + Y))
    (cospan_compose HP
       (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini
                             (@Cospan_unit_obj C H_Ini))))
       (cospan_tensor (cospan_scfa_epsilon X) (cospan_scfa_epsilon Y))).
Proof.
  unfold cospan_scfa_epsilon, Cospan_tensor_obj.
  apply cospan_equiv_sym.
  (* Inner: cospan_tensor (back zero_X) (back zero_Y) ≈ back (cover zero_X zero_Y). *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan_back.
    - apply cospan_equiv_refl. }
  (* Now: compose (mor_as_cospan (to coprod_zero_l)) (back (cover zero zero)).
     Apply cospan_compose_forward_iso_back with g = cover zero zero, phi = coprod_zero_l. *)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_forward_iso_back HP
              (cover (zero : 0 ~{C}~> X) (zero : 0 ~{C}~> Y))
              (@coprod_zero_l C H_Coc H_Ini 0%object)). }
  (* Result: mor_as_cospan_back ((cover zero zero) ∘ from coprod_zero_l).
     LHS target: mor_as_cospan_back (zero : 0 → X+Y).
     Need: (cover zero zero) ∘ from coprod_zero_l ≈ zero in C. *)
  apply mor_as_cospan_back_proper.
  unfold from, coprod_zero_l; simpl.
  rewrite cover_inr.
  symmetry.
  apply (@zero_unique C H_Ini _ _ _).
Defined.

End CospanHypergraphInstance.

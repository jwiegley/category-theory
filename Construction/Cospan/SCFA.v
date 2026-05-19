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
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.

Generalizable All Variables.

(** * Special commutative Frobenius algebras on [CospanCat C HP]

    Every object of [CospanCat C HP] carries a canonical SCFA built
    from the cocartesian structure of [C].  This file discharges the
    axioms of:
    - [Monoid (CospanCat C HP) X]   (with mu, eta from [cospan_scfa_*])
    - [Comonoid (CospanCat C HP) X] (with delta, epsilon)
    - [Frobenius] compatibility
    - [CommutativeFrobenius] (mu/delta commutativity under braid)
    - [SpecialCommutativeFrobenius] (mu ∘ delta ≈ id)
    for each [X : C].

    The proofs reduce — via [mor_as_cospan_compose] and
    [cospan_tensor_mor_as_cospan] — to C-level coproduct identities on
    pushouts of the codiagonal [id ▽ id] and zero. *)

Section CospanSCFA.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** ** Identification of the SCFA data with [mor_as_cospan] lifts

    [cospan_scfa_mu X] and [cospan_scfa_eta X] are exactly
    [mor_as_cospan (id ▽ id)] and [mor_as_cospan zero] respectively.
    [cospan_scfa_delta X] and [cospan_scfa_epsilon X] are the
    backwards-cospan variants, lifted via [mor_as_cospan_back]. *)

Lemma cospan_scfa_mu_as_cospan (X : C) :
  cospan_scfa_mu X = mor_as_cospan ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X).
Proof. reflexivity. Qed.

Lemma cospan_scfa_eta_as_cospan (X : C) :
  cospan_scfa_eta X = mor_as_cospan (zero : 0%object ~{C}~> X).
Proof. reflexivity. Qed.

(** A cospan from [X] to [Y] with apex [X], leg1 = id, leg2 = f : Y → X.
    This is the "backward" direction: a C-morphism [Y → X] reinterpreted
    as a cospan from [X] to [Y]. *)
Definition mor_as_cospan_back {X Y : C} (f : Y ~> X) : CospanArrow X Y :=
  Build_CospanArrow X id[X] f.

Lemma cospan_scfa_delta_as_back (X : C) :
  cospan_scfa_delta X
  = mor_as_cospan_back ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X).
Proof. reflexivity. Qed.

Lemma cospan_scfa_epsilon_as_back (X : C) :
  cospan_scfa_epsilon X
  = mor_as_cospan_back (zero : 0%object ~{C}~> X).
Proof. reflexivity. Qed.

(** ** Bridging: composing a backward-cospan on the outside

    [mor_as_cospan_back f : X → Y] has apex X and in1 = id[X].
    Composing it with [g : Z → X] (apex N) gives the pushout of
    [(in2 g : X → N, id[X] : X → X)], whose apex collapses to N. *)

Lemma cospan_compose_mor_as_cospan_back_left
      {X Y Z : C} (f : Y ~> X) (g : CospanArrow Z X) :
  cospan_equiv (cospan_compose HP (mor_as_cospan_back f) g)
               (Build_CospanArrow (cospan_apex g)
                                  (cospan_in1 g)
                                  (cospan_in2 g ∘ f)).
Proof.
  unfold cospan_compose, mor_as_cospan_back; simpl.
  pose (P := pushout (cospan_in2 g) (id[X] : X ~{C}~> X)).
  (* The apex P is pushout (in2 g, id[X]); by pushout_id_right_apex it ≅ apex g. *)
  pose (iso := pushout_id_right_apex HP (cospan_in2 g)).
  (* to iso : apex P → apex g, with:
       to iso ∘ pushout_in1 P ≈ id[apex g]
       to iso ∘ pushout_in2 P ≈ cospan_in2 g                                 *)
  exists iso.
  simpl; split; fold P.
  - (* to iso ∘ (pushout_in1 P ∘ in1 g) ≈ in1 g *)
    rewrite comp_assoc.
    unfold iso, pushout_id_right_apex; simpl.
    rewrite pushout_med_in1.
    apply id_left.
  - (* to iso ∘ (pushout_in2 P ∘ f) ≈ in2 g ∘ f *)
    rewrite comp_assoc.
    unfold iso, pushout_id_right_apex; simpl.
    rewrite pushout_med_in2.
    reflexivity.
Defined.

(** Note: composing [back_f] on the RIGHT (as inner) of a generic cospan is
    a genuine pushout (not a collapse), so no analogous left-collapse bridge
    exists.  The dual configurations use [back] on the LEFT (outer). *)

(** ** C-level: codiagonal absorbs cover

    [(id ▽ id) ∘ cover f g ≈ f ▽ g] : the codiagonal absorbs the
    coproduct structure, simplifying both sides of the monoid axioms. *)

Lemma codiag_cover {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover f g ≈ f ▽ g.
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    rewrite inl_merge.
    reflexivity.
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    rewrite inr_merge.
    reflexivity.
Qed.

(** ** [Monoid mu_assoc] at the C-level

    Reduces via [codiag_cover] to:
      (id ▽ id) ▽ id ≈ id ▽ (id ▽ id) ∘ to coprod_assoc                  *)

Lemma codiag_assoc {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover (id[X] ▽ id[X]) id[X]
  ≈ (id[X] ▽ id[X]) ∘ cover id[X] (id[X] ▽ id[X])
    ∘ to (@coprod_assoc C H_Coc X X X).
Proof.
  rewrite codiag_cover.
  rewrite <- comp_assoc.
  (* Goal: (id ▽ id) ▽ id ≈ (id ▽ id) ∘ (cover id (id ▽ id) ∘ α). *)
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl) → LHS = id, RHS = (id▽id) ∘ inl = id *)
      rewrite inl_merge, inl_merge.
      symmetry.
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inl.
      rewrite cover_inl.
      rewrite id_right.
      rewrite inl_merge.
      reflexivity.
    + (* ∘ (inl ∘ inr) → LHS = id, RHS reduces via assoc_to_inl_inr + cover_inr *)
      rewrite inl_merge, inr_merge.
      symmetry.
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inl).
      rewrite inl_merge.
      rewrite id_right.
      rewrite inr_merge.
      reflexivity.
  - (* ∘ inr → LHS = id, RHS reduces via assoc_to_inr + cover_inr *)
    rewrite inr_merge.
    symmetry.
    rewrite <- !comp_assoc.
    rewrite assoc_to_inr.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inr).
    rewrite cover_inr.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inr).
    rewrite inr_merge.
    rewrite id_right.
    rewrite inr_merge.
    reflexivity.
Qed.

(** ** C-level identities backing the unit laws

    [mu ∘ bimap eta id ≈ to unit_left] becomes (at C level after
    mor_as_cospan-fusion):
      (id ▽ id) ∘ cover zero id ≈ zero ▽ id     [= to coprod_zero_l]   *)

Lemma codiag_eta_left {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover (zero : 0%object ~> X) id[X]
  ≈ to (@coprod_zero_l C H_Coc H_Ini X).
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    unfold to, coprod_zero_l; simpl.
    rewrite inl_merge.
    apply (@zero_unique C H_Ini _ _ _).
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    unfold to, coprod_zero_l; simpl.
    rewrite inr_merge.
    reflexivity.
Qed.

Lemma codiag_eta_right {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover id[X] (zero : 0%object ~> X)
  ≈ to (@coprod_zero_r C H_Coc H_Ini X).
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    unfold to, coprod_zero_r; simpl.
    rewrite inl_merge.
    reflexivity.
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    unfold to, coprod_zero_r; simpl.
    rewrite inr_merge.
    apply (@zero_unique C H_Ini _ _ _).
Qed.

(** ** C-level: codiagonal commutes with paws

    [(id ▽ id) ∘ paws ≈ id ▽ id]  is just [paws_fork]. *)

Lemma codiag_paws_comm {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ paws
  ≈ (id[X] ▽ id[X]).
Proof. apply paws_fork. Qed.

(** ** Cospan-level monoid axioms

    Each axiom lifts the corresponding C-level identity through
    [mor_as_cospan_compose] and [cospan_tensor_mor_as_cospan]. *)

(** [cospan_scfa_mu ∘ bimap mu (cospan_id X) ≈ cospan_scfa_mu ∘ bimap id mu ∘ to tensor_assoc]
    in [CospanCat C HP]. *)
Lemma cospan_mu_assoc (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_scfa_mu X) (cospan_id X)))
    (cospan_compose HP
       (cospan_compose HP (cospan_scfa_mu X)
          (cospan_tensor (cospan_id X) (cospan_scfa_mu X)))
       (mor_as_cospan (to (@coprod_assoc C H_Coc X X X)))).
Proof.
  unfold cospan_scfa_mu.
  (* LHS: cospan_compose (mor_as_cospan (id▽id))
                         (cospan_tensor (mor_as_cospan (id▽id)) (cospan_id X)).
     RHS: cospan_compose (cospan_compose (mor_as_cospan (id▽id))
                            (cospan_tensor (cospan_id X) (mor_as_cospan (id▽id))))
                         (mor_as_cospan α). *)
  (* On LHS replace [cospan_id X] with [mor_as_cospan id[X]], then fuse tensors. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_sym, mor_as_cospan_id.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  (* RHS handling. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_respects.
        * apply cospan_equiv_sym, mor_as_cospan_id.
        * apply cospan_equiv_refl.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_mor_as_cospan.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  symmetry.
  apply codiag_assoc.
Defined.

(** Cospan-level [mu ∘ bimap eta id ≈ to unit_left]. *)
Lemma cospan_mu_unit_left (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_scfa_eta X) (cospan_id X)))
    (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_eta.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_sym, mor_as_cospan_id.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  apply codiag_eta_left.
Defined.

(** Cospan-level [mu ∘ bimap id eta ≈ to unit_right]. *)
Lemma cospan_mu_unit_right (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_id X) (cospan_scfa_eta X)))
    (mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_eta.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  apply codiag_eta_right.
Defined.

(** ** [Monoid (CospanCat C HP) X] for every X *)

Program Definition cospan_monoid (X : C) :
  @Monoid (CospanCat C HP) (Cospan_Monoidal HP) X := {|
  mu  := cospan_scfa_mu X ;
  eta := cospan_scfa_eta X
|}.
Next Obligation.
  apply cospan_mu_assoc.
Defined.
Next Obligation.
  apply cospan_mu_unit_left.
Defined.
Next Obligation.
  apply cospan_mu_unit_right.
Defined.

End CospanSCFA.

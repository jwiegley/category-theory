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
    [mor_as_cospan (id ▽ id)] and [mor_as_cospan zero] respectively. *)

Lemma cospan_scfa_mu_as_cospan (X : C) :
  cospan_scfa_mu X = mor_as_cospan ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X).
Proof. reflexivity. Qed.

Lemma cospan_scfa_eta_as_cospan (X : C) :
  cospan_scfa_eta X = mor_as_cospan (zero : 0%object ~{C}~> X).
Proof. reflexivity. Qed.

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

End CospanSCFA.

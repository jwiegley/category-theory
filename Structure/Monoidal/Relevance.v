Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section RelevanceMonoidal.

Context {C : Category}.

Class RelevanceMonoidal := {
  relevance_is_symmetric : @SymmetricMonoidal C;

  diagonal {x} : x ~> x ⨂ x;
  diagonal_natural : natural (@diagonal);

  (* These properties are given by Kosta Došen and Zoran Petrić in their 2007
     publication, "Relevance Categories and Partial Functions". *)

  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  diagonal_tensor_assoc {x} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal x;

  braid_diagonal {x} :
    braid ∘ diagonal ≈ @diagonal x;

  braid2 {x y z w} : (x ⨂ y) ⨂ (z ⨂ w) ~> (x ⨂ z) ⨂ (y ⨂ w) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  diagonal_braid2 {x y} :
    @diagonal (x ⨂ y) ≈ braid2 ∘ diagonal ⨂ diagonal
}.
#[export] Existing Instance relevance_is_symmetric.

Coercion relevance_is_symmetric : RelevanceMonoidal >-> SymmetricMonoidal.

Context `{RelevanceMonoidal}.

Lemma braid2_natural : natural (@braid2 _).
Proof.
  unfold braid2; simpl; intros; normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  comp_right.
  comp_left.
  normal.
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  normal.
  bimap_right.
  spose (fst braid_natural _ _ h _ _ i) as X.
  normal; assumption.
Qed.

Notation "∆ x" := (@diagonal _ x)
  (at level 9, format "∆ x") : morphism_scope.

Definition fork {x y z} (f : x ~> y) (g : x ~> z) :
  x ~> y ⨂ z := f ⨂ g ∘ ∆x.

#[export] Program Instance fork_respects {x y z : C} :
  Proper (equiv ==> equiv ==> equiv) (@fork x y z).
Next Obligation.
  proper.
  unfold fork.
  rewrites.
  reflexivity.
Qed.

End RelevanceMonoidal.

Notation "∆ x" := (@diagonal _ _ x)
  (at level 9, format "∆ x") : morphism_scope.

Infix "△" := fork (at level 28) : morphism_scope.

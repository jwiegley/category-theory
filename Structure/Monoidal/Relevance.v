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

(* nLab: https://ncatlab.org/nlab/show/relevance+monoidal+category
   Wikipedia: (no dedicated article; see Symmetric monoidal category and
   Relevance logic / structural rule of contraction)

   A relevance (relevant) monoidal category is a symmetric monoidal category
   equipped with a natural diagonal (copying/contraction) map

       ∆x : x ~> x ⨂ x

   satisfying coherence laws that make every object a cocommutative
   cosemigroup — coassociative and cocommutative comultiplication, but with
   no counit x ~> I. Modelling-wise this is the categorical counterpart of
   relevance logic: a substructural logic with the contraction rule (copying,
   the diagonal) but without weakening (projection/deletion, which would be a
   counit). Adding both diagonals and projections would make the category
   cartesian; adding projections alone would make it semicartesian.

   The axioms below follow Kosta Došen and Zoran Petrić, "Relevant Categories
   and Partial Functions" (2007), arXiv:math/0504133, in this library's
   notation:

       naturality:    (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f             (f : x ~> y)
       unit:          ∆I ≈ unit_left⁻¹                   (I ≅ I ⨂ I)
       coassoc:       id ⨂ ∆ ∘ ∆ ≈ α ∘ ∆ ⨂ id ∘ ∆
       cocomm:        braid ∘ ∆ ≈ ∆                       (σ_{x,x} ∘ ∆ = ∆)
       tensor-compat: ∆(x ⨂ y) ≈ braid2 ∘ (∆ ⨂ ∆)

   where braid2 is the middle-four interchange iso permuting the inner two
   factors of (x ⨂ y) ⨂ (z ⨂ w) to (x ⨂ z) ⨂ (y ⨂ w). *)

Class RelevanceMonoidal := {
  (* The underlying symmetric monoidal structure (braiding + symmetry). *)
  relevance_is_symmetric : @SymmetricMonoidal C;

  (* The diagonal / copying map ∆x : x ~> x ⨂ x (the contraction rule). *)
  diagonal {x} : x ~> x ⨂ x;
  (* Naturality: (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f, so ∆ is a natural transformation
     from the identity functor to the squaring functor x ↦ x ⨂ x. *)
  diagonal_natural : natural (@diagonal);

  (* Unit: the diagonal at the monoidal unit is the canonical iso I ≅ I ⨂ I,
     here unit_left⁻¹ : I ~> I ⨂ I. *)
  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  (* Coassociativity: copying-then-copying-the-left equals
     copying-then-copying-the-right, modulo the associator. *)
  diagonal_tensor_assoc {x} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal x;

  (* Cocommutativity / symmetry compatibility: swapping the two copies leaves
     the diagonal unchanged, σ_{x,x} ∘ ∆x ≈ ∆x. *)
  braid_diagonal {x} :
    braid ∘ diagonal ≈ @diagonal x;

  (* The middle-four interchange iso (a definitional abbreviation, not an
     axiom): permutes the inner factors of (x ⨂ y) ⨂ (z ⨂ w) into
     (x ⨂ z) ⨂ (y ⨂ w), built from the associator and braiding. *)
  braid2 {x y z w} : (x ⨂ y) ⨂ (z ⨂ w) ~> (x ⨂ z) ⨂ (y ⨂ w) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  (* Tensor compatibility: copying a tensor is copying each factor then
     regrouping via braid2, ∆(x ⨂ y) ≈ braid2 ∘ (∆x ⨂ ∆y). *)
  diagonal_braid2 {x y} :
    @diagonal (x ⨂ y) ≈ braid2 ∘ diagonal ⨂ diagonal
}.
#[export] Existing Instance relevance_is_symmetric.

Coercion relevance_is_symmetric : RelevanceMonoidal >-> SymmetricMonoidal.

Context `{RelevanceMonoidal}.

(* The middle-four interchange braid2 is natural in all four arguments; this
   is what makes the tensor-compatibility axiom diagonal_braid2 coherent. *)
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
  spose (braid_natural _ _ h _ _ i) as X.
  normal; assumption.
Qed.

Notation "∆ x" := (@diagonal _ x)
  (at level 9, format "∆ x") : morphism_scope.

(* The fork (split) combinator: copy x with the diagonal, then run f and g on
   the two copies, ⟨f, g⟩ = (f ⨂ g) ∘ ∆x. In a cartesian category this is the
   pairing map; here the diagonal supplies the copying without a counit. *)
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

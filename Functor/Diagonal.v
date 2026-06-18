Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** The diagonal functor Δ : C ⟶ [J, C] (and the binary Δ : C ⟶ C ∏ C). *)

(* nLab: https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   For a fixed index category J, the diagonal functor Δ[J] : C ⟶ [J, C] sends
   each object c : C to the constant functor Δ[J](c) : J ⟶ C, which takes every
   object of J to c and every morphism of J to id[c]; and it sends each
   morphism f : c ~> c' to the natural transformation Δ[J](c) ⟹ Δ[J](c') whose
   component at every j : J is f itself (naturality is f ∘ id ≈ id ∘ f). When J
   is the discrete two-object category this recovers the binary diagonal
   Δ : C ⟶ C ∏ C with c ↦ (c, c); Diagonal_Product_Two below witnesses that
   agreement.

   The diagonal is the universal source of cones: a cone over a diagram
   F : J ⟶ C with apex c is exactly a natural transformation Δ[J](c) ⟹ F. When
   the relevant universal cones exist, Δ is sandwiched by the limit and colimit
   functors as colim ⊣ Δ ⊣ lim (C is J-cocomplete iff Δ has a left adjoint and
   J-complete iff Δ has a right adjoint); for the binary case this is the
   familiar (-) + (-) ⊣ Δ ⊣ (-) × (-). *)

#[export]
Program Instance Diagonal {C : Category} (J : Category) : C ⟶ [J, C] := {
  fobj := fun x =>
    {| fobj := fun _ => x
     ; fmap := fun _ _ _ => id[x] |};
  fmap := fun _ _ f =>
    {| transform := fun _ => f |}
}.

Section Diagonal_Product.

#[local] Set Transparent Obligations.

#[export]
Program Instance Diagonal_Product `(C : Category) : C ⟶ C ∏ C.

End Diagonal_Product.

Notation "Δ[ J ]( c )" := (Diagonal J c) (at level 0, format "Δ[ J ]( c )") : functor_scope.

Require Import Category.Instance.One.

Notation "Δ( c )" := (Diagonal _ c) (at level 0, format "Δ( c )") : functor_scope.
Notation "=( c )" := (Diagonal 1 c) (at level 0, format "=( c )") : functor_scope.

Definition Δ {C J : Category} := @Diagonal C J.

(* Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   Wikipedia: "In category theory, a branch of mathematics, the diagonal
   functor C → C × C is given by Δ(a) = ⟨a, a⟩, which maps objects as well as
   morphisms. This functor can be employed to give a succinct alternate
   description of the product of objects within the category C: a product a ×
   b is a universal arrow from Δ to ⟨a, b⟩. The arrow comprises the projection
   maps."

  "More generally, in any functor category Cᴶ (here J should be thought of as
  a small index category), for each object a in C, there is a constant functor
  with fixed object a : Δ(a) ∈ Cᴶ. The diagonal functor Δ : C → Cᴶ assigns to
  each object of C the functor Δ(a), and to each morphism f : a → b in C the
  obvious natural transformation η in Cᴶ (given by ηⱼ = f). In the case that J
  is a discrete category with two objects, the diagonal functor C → C × C is
  recovered." *)

Require Import Category.Instance.Two.Discrete.

Theorem Diagonal_Product_Two (C : Category) :
  (∀ x, Diagonal_Product C x ≅ (Diagonal Two_Discrete x TwoDX,
                                Diagonal Two_Discrete x TwoDY)) *
  (∀ x y (f : x ~> y),
     fmap[Diagonal_Product C] f
       ≈ (transform[fmap[Diagonal Two_Discrete] f] TwoDX,
          transform[fmap[Diagonal Two_Discrete] f] TwoDY)).
Proof.
  split; intros.
  - isomorphism; simpl; intros; try exact (id, id); cat.
  - reflexivity.
Qed.

#[export]
Instance Transform_Const `(x ~{C}~> y) : Δ(x) ⟹ Δ(y).
Proof. construct; auto; cat_simpl. Qed.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Monoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   A monoidal category is a category equipped with a tensor product and a
   unit object that are associative and unital up to coherent isomorphism.
   The data are a unit object I, a tensor bifunctor ⊗ : C ∏ C ⟶ C, and three
   natural isomorphisms,

       lambda  : I ⊗ x ≅ x              ([unit_left]),
       rho     : x ⊗ I ≅ x              ([unit_right]),
       alpha   : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)   ([tensor_assoc]),

   the left unitor, the right unitor, and the associator respectively. The
   associator direction (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z) follows nLab; the opposite
   orientation appears in some sources and differs only by inverses.

   Naturality of each isomorphism is recorded explicitly, in both the forward
   (to) and inverse (from) directions, so rewriting and dualization work
   either way. For lambda this is the square g ∘ λ ≈ λ ∘ (id ⊗ g), and
   similarly for rho and alpha.

   Two coherence conditions govern the interaction of these isomorphisms:

       triangle:  (ρ ⊗ id) ≈ (id ⊗ λ) ∘ α   on   (x ⊗ I) ⊗ y
       pentagon:  (id ⊗ α) ∘ α ∘ (α ⊗ id) ≈ α ∘ α
                                              on  ((x ⊗ y) ⊗ z) ⊗ w

   The triangle identity relates the unitors to the associator across the
   unit; the pentagon identity makes the two reassociations of a fourfold
   tensor agree. By Mac Lane's coherence theorem these two laws force every
   formal diagram built from α, λ, ρ to commute. *)

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;                        (* unit_obj *)
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;  (* lambda *)
  unit_right {x} : x ⨂ I ≅ x;  (* rho *)

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions:
     the triangle identity (unitors vs. associator) and the pentagon
     identity (the two reassociations of a fourfold tensor agree). *)

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Naturality.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context {C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {X} : I ⨂ X ≅ X;  (* lambda *)
  unit_right {X} : X ⨂ I ≅ X;  (* rho *)

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {X Y} (g : X ~> Y) :
    g ∘ unit_left << I ⨂ X ~~> Y >> unit_left ∘ bimap id g;
  from_unit_left_natural {X Y} (g : X ~> Y) :
    bimap id g ∘ unit_left⁻¹ << X ~~> I ⨂ Y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {X Y} (g : X ~> Y) :
    g ∘ unit_right << X ⨂ I ~~> Y >> unit_right ∘ bimap g id;
  from_unit_right_natural {X Y} (g : X ~> Y) :
    bimap g id ∘ unit_right⁻¹ << X ~~> Y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {X Y Z W V U} (g : X ~> Y) (h : Z ~> W) (i : V ~> U) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (X ⨂ Z) ⨂ V ~~> Y ⨂ W ⨂ U >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {X Y Z W V U} (g : X ~> Y) (h : Z ~> W) (i : V ~> U) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << X ⨂ Z ⨂ V ~~> (Y ⨂ W) ⨂ U >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions *)

  triangle_identity {X Y} :
    bimap unit_right id
      << (X ⨂ I) ⨂ Y ~~> X ⨂ Y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {X Y Z W} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((X ⨂ Y) ⨂ Z) ⨂ W ~~> X ⨂ (Y ⨂ (Z ⨂ W)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "X ⨂ Y" := (@tensor _ _ (X%object, Y%object))
  (at level 30, right associativity) : object_scope.
Notation "X ⨂[ M ] Y" := (fobj[@tensor _ M] (X, Y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.

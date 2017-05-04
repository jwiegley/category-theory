Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Functor.Product.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ∏ C ⟶ C
    where "x ⨂ y" := (tensor (x, y));

  I : C;

  unit_left  {X} : I ⨂ X ≅ X;
  unit_right {X} : X ⨂ I ≅ X;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z)
}.

Notation "X ⨂ Y" := (tensor (X, Y)) (at level 30, right associativity).

Class SymmetricMonoidal `{Monoidal} := {
  swap {X Y} : X ⨂ Y ≅ Y ⨂ X
}.

End Monoidal.

Notation "X ⨂ Y" := (@tensor _ _ (X, Y)) (at level 30, right associativity).

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal `{C : Category} :
  @Monoidal ([C, C]) := {|
  tensor := _;
  I := Id
|}.
Next Obligation.
  functor; simpl.
  - intros [X Y].
    exact (functor_comp X Y).
  - intros [F G] [F' G'] [N M]; simpl in *.
    natural; simpl; intros.
    + exact (transform[N] (G' X) ∘ fmap[F] (transform[M] X)).
    + simpl.
      rewrite <- natural_transformation.
      rewrite comp_assoc.
      rewrite <- fmap_comp.
      rewrite <- natural_transformation.
      rewrite <- !comp_assoc.
      rewrite <- natural_transformation.
      rewrite comp_assoc.
      rewrite <- fmap_comp.
      rewrite <- natural_transformation.
      reflexivity.
  - proper; simplify; simpl in *.
    rewrite a, b.
    reflexivity.
  - simplify; simpl in *.
    rewrite !fmap_id; cat.
  - simplify; simpl in *.
    rewrite <- !comp_assoc.
    apply compose_respects.
      reflexivity.
    rewrite <- !natural_transformation.
    rewrite fmap_comp.
    rewrite comp_assoc.
    reflexivity.
Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition Product_Monoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} : @Monoidal C := {|
  tensor := ProductFunctor C;
  I := One
|}.

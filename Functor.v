Require Import Lib.
Require Export Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Class Functor `(_ : Category C) `(_ : Category D) := {
  fobj : C -> D;
  fmap {X Y : C} (f : X ~> Y) : fobj X ~> fobj Y;

  fmap_respects : ∀ X Y,
    Proper (@eqv _ _ X Y ==> @eqv _ _ (fobj X) (fobj Y)) fmap;

  fmap_id {X : C} : fmap (@id C _ X) ≈ id;
  fmap_comp {X Y Z : C} (f : Y ~> Z) (g : X ~> Y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

Arguments Functor C {_} D {_}.

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (Functor C D) (at level 90, right associativity).

Hint Rewrite @fmap_id : categories.

Program Instance parametric_morphism_fmap `(_ : Functor C D) (a b : C) :
  Proper (eqv ==> eqv) (@fmap C _ D _ _ a b) := fmap_respects a b.

(* The Identity [Functor] *)

Definition Identity `{Category C} : C ⟶ C.
  apply Build_Functor with
    (fobj := fun X => X)
    (fmap := fun X X f => f); cat.
Defined.

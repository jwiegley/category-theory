Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ⟶ [C, C]           (* uncurried = C ∏ C ⟶ C *)
    where "x ⨂ y" := (tensor x y);

  munit : C;

  unit_left  {X} : munit ⨂ X ≅ X;
  unit_right {X} : X ⨂ munit ≅ X;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z)
}.

End Monoidal.

Infix "⨂" := (@tensor _ _) (at level 30, right associativity).

Section MonoidalFunctor.

Context `{C : Category}.
Context `{D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context `{F : C ⟶ D}.

Class LaxMonoidalFunctor := {
  pure : munit ~> F munit;
  ap {X Y} : F X ⨂ F Y ~> F (X ⨂ Y)
}.

Class StrongMonoidalFunctor := {
  pure_iso : munit ≅ F munit;
  ap_iso {X Y} : F X ⨂ F Y ≅ F (X ⨂ Y)
}.

Definition StrongMonoidalFunctor_Is_Lax (S : StrongMonoidalFunctor) :
  LaxMonoidalFunctor := {|
  pure := to (@pure_iso S);
  ap := fun X Y => to (@ap_iso S X Y)
|}.

End MonoidalFunctor.

Class StrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  strength {X Y} : X ⨂ F Y ≅ F (X ⨂ Y)
}.

Class RightStrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  right_strength {X Y} : F X ⨂ Y ≅ F (X ⨂ Y)
}.

(* A strong lax monoidal functor is called an "applicative functor" in
   Haskell. *)

Set Warnings "-non-primitive-record".

Class StrongLaxMonoidalFunctor
      `{C : Category}
      `{@Monoidal C}
      (F : C ⟶ C)
      `{@StrongFunctor _ _ F}
      `{@LaxMonoidalFunctor _ _ _ _ F}.

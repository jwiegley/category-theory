Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Terminal.
Require Export Category.Construction.Opposite.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Dinatural.

Context `{C : Category}.
Context `{@Terminal C}.
Context `{@Terminal (C^op)}.
Context `{D : Category}.
Context `{F : C^op ∏ C ⟶ D}.
Context `{G : C^op ∏ C ⟶ D}.

Definition prod_split {X Y Z W} (f : X ~{C^op}~> Z) (g : Y ~{C}~> W) :
  (X, Y) ~{ (C ^op) ∏ C }~> (Z, W) := (f, g).
Arguments prod_split {_ _ _ _} _ _ /.

Infix "⋆⋆⋆" := prod_split (at level 100) : category_scope.

Class Dinatural := {
  ditransform {X} : F (X, X) ~> G (X, X);

  dinaturality {X Y} (f : X ~{C}~> Y) :
    fmap[G] (op f ⋆⋆⋆ id) ∘ ditransform ∘ fmap[F] (id ⋆⋆⋆ f)
        ≈ fmap[G] (id ⋆⋆⋆ f) ∘ ditransform ∘ fmap[F] (op f ⋆⋆⋆ id)
}.

Global Program Instance Dinatural_Setoid : Setoid Dinatural.

End Dinatural.

Notation "ditransform[ F ]" := (@ditransform _ _ _ _ F)
  (at level 9, format "ditransform[ F ]") : category_scope.

(* Dinatural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion ditransform : Dinatural >-> Funclass.

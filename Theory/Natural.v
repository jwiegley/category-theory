Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Natural.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : C ⟶ D}.
Context `{G : C ⟶ D}.

Class Natural := {
  transform {X} : F X ~> G X;

  naturality {X Y} (f : X ~> Y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f
}.

Global Program Instance Natural_Setoid : Setoid Natural.

End Natural.

Arguments transform {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ _ _ _.

Bind Scope natural_scope with Natural.
Delimit Scope natural_type_scope with natural_type.
Delimit Scope natural_scope with natural.
Open Scope natural_type_scope.
Open Scope natural_scope.

Notation "F ⟹ G" := (@Natural _ _ F%functor G%functor)
  (at level 90, right associativity) : natural_type_scope.

Notation "transform[ F ]" := (@transform _ _ _ _ F%natural)
  (at level 9, only parsing, format "transform[ F ]") : morphism_scope.
Notation "naturality[ F ]" := (@naturality _ _ _ _ F%natural)
  (at level 9, only parsing, format "naturality[ F ]") : morphism_scope.

Ltac natural :=
  unshelve (refine {| transform := _ |}; simpl; intros).

Ltac constructive :=
  isomorphism; simpl; intros;
  [ natural; simpl; intros
  | natural; simpl; intros
  | .. ]; simpl; intros.

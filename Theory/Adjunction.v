Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Adjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class Adjunction := {
  unit   : Id ⟹ U ○ F;
  counit : F ○ U ⟹ Id;

  counit_fmap_unit {X} :
    transform[counit] (F X) ∘ fmap[F] (transform[unit] X) ≈ id;
  fmap_counit_unit {X} :
    fmap[U] (transform[counit] X) ∘ transform[unit] (U X) ≈ id
}.

End Adjunction.

Arguments Adjunction {C D} F%functor U%functor.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.

Notation "unit[ A ]" := (@unit _ _ _ _ A)
  (at level 9, format "unit[ A ]") : morphism_scope.
Notation "counit[ A ]" := (@counit _ _ _ _ A)
  (at level 9, format "counit[ A ]") : morphism_scope.

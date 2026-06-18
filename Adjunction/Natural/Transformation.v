Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.

Generalizable All Variables.

(** The counit/unit (natural-transformation) characterization of an
    adjunction. *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U between F : D ⟶ C (the left adjoint) and U : C ⟶ D
   (the right adjoint) is given here in counit/unit form: a unit
   η : Id ⟹ U ◯ F and a counit ε : F ◯ U ⟹ Id satisfying the two triangle
   (zig-zag) identities. Componentwise these are

     ε (F X) ∘ fmap[F] (η X) ≈ id[F X]   (counit_fmap_unit), i.e. εF ∘ Fη = 1_F,
     fmap[U] (ε X) ∘ η (U X) ≈ id[U X]   (fmap_counit_unit), i.e. Uε ∘ ηU = 1_U.

   This is the data of an adjunction with which the hom-set form
   [Category.Adjunction.Hom] and the universal-morphism form
   [Category.Theory.Adjunction] are shown equivalent: the transposes of the
   identities recover η and ε, and conversely η, ε with these identities
   reconstruct the natural hom-set isomorphism. *)

Section AdjunctionTransform.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class Adjunction_Transform := {
  unit   : Id ⟹ U ◯ F;
  counit : F ◯ U ⟹ Id;

  counit_fmap_unit {X} :
    transform[counit] (F X) ∘ fmap[F] (transform[unit] X) ≈ id;
  fmap_counit_unit {X} :
    fmap[U] (transform[counit] X) ∘ transform[unit] (U X) ≈ id
}.

End AdjunctionTransform.

Arguments Adjunction_Transform {C D} F%_functor U%_functor.

Declare Scope adjunction_scope.
Declare Scope adjunction_type_scope.
Bind Scope adjunction_scope with Adjunction_Transform.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ∹ G" := (@Adjunction_Transform _ _ F G)
  (at level 59) : adjunction_type_scope.

Notation "unit[ A ]" := (@unit _ _ _ _ A)
  (at level 9, format "unit[ A ]") : morphism_scope.
Notation "counit[ A ]" := (@counit _ _ _ _ A)
  (at level 9, format "counit[ A ]") : morphism_scope.

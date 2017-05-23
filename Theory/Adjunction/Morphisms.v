Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionMorphisms.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Another way to define an adjunction is by providing the unit and counit
   morphisms. *)

Class AdjunctionMorphisms := {
  unit' {a : D} : a ~> U (F a);
  counit' {a : C} : F (U a) ~> a;

  unit_nat {X Y} (f : X ~> Y) :
    fmap[U] (fmap[F] f) ∘ @unit' X ≈ @unit' Y ∘ f;
  counit_nat {X Y} (f : X ~> Y) :
    f ∘ @counit' X ≈ @counit' Y ∘ fmap[F] (fmap[U] f);

  counit_fmap_unit' {X} : counit' ∘ fmap[F] unit' ≈ @id C (F X);
  fmap_counit_unit' {X} : fmap[U] counit' ∘ unit' ≈ @id D (U X)
}.

Program Definition adj_from_unit_conuit {A : AdjunctionMorphisms} : F ⊣ U := {|
  adj_iso := fun a b =>
    {| to   := {| morphism := fun f => fmap f ∘ @unit' A a |}
     ; from := {| morphism := fun f => @counit' A b ∘ fmap f |} |}
|}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite unit_nat.
  rewrite comp_assoc.
  rewrite fmap_counit_unit'; cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- counit_nat.
  rewrite <- comp_assoc.
  rewrite counit_fmap_unit'; cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite unit_nat.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- counit_nat.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

End AdjunctionMorphisms.

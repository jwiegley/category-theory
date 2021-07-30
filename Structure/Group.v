Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Structure.Monoidal.Cartesian.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section GroupObject.

Context {C : Category}.
Context `{@Monoidal C}.
Context `{@CartesianMonoidal C _}.

Class GroupObject (grp : C) := {
  is_monoid :> MonoidObject grp;
  inverse : grp ~> grp;

  (* g⁻¹ ⨂ g ≈ I *)
  left_inverse : mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (* g ⨂ g⁻¹ ≈ I *)
  right_inverse : mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.

End GroupObject.

Notation "'inverse' [ G ]" := (@inverse _ _ _ G _)
  (at level 9, format "inverse [ G ]") : category_scope.

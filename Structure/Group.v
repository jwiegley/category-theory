Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section GroupObject.

Context `{@CartesianMonoidal C}.

Class GroupObject (grp : C) := {
  groupobject_is_monoid : MonoidObject grp;
  inverse : grp ~> grp;

  (* g⁻¹ ⨂ g ≈ I *)
  left_inverse : mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (* g ⨂ g⁻¹ ≈ I *)
  right_inverse : mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.
#[export] Existing Instance groupobject_is_monoid.

End GroupObject.

Notation "'inverse' [ G ]" := (@inverse _ _ G _)
  (at level 9, format "inverse [ G ]") : category_scope.

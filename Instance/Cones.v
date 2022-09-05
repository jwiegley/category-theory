Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Definition Cones `(F : J ⟶ C) : Category := {|
  obj     := Cone F;
  hom     := fun N L => { u : vertex_obj[N] ~> vertex_obj[L]
                        & ∀ j, vertex_map[L] ∘ u ≈ @vertex_map _ _ F N j };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _);
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite X0; auto.
Qed.

Definition Cocones `(F : J ⟶ C) := Cones (F^op).

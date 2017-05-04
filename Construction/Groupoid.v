Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Groupoid.

Context `{C : Category}.

Program Instance id_iso `{C : Category} {X : C} : X ≅ X := {
  to := id;
  from := id
}.

Program Instance compose_iso `{C : Category}
        {X Y Z : C} `(f : Y ≅ Z) `(g : X ≅ Y) : X ≅ Z := {
  to := to f ∘ to g;
  from := from g ∘ from f
}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Qed.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Definition Groupoid : Category := {|
  ob      := @ob C;
  hom     := @Isomorphism C;
  homset  := @isomorphism_setoid C;
  id      := @id_iso C;
  compose := @compose_iso C
|}.

End Groupoid.

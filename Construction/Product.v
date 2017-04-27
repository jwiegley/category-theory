Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Product.

Context `{C : Category}.
Context `{D : Category}.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Instance Product : Category := {
  ob      := C * D;
  hom     := fun X Y => (fst X ~> fst Y) * (snd X ~> snd Y);
  homset  := fun _ _ => {| equiv := fun f g => fst f ≈ fst g ∧ snd f ≈ snd g |} ;
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g)
}.

End Product.

Notation "C ∏ D" := (@Product C D) (at level 90).

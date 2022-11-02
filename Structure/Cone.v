Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

Class ConeFrom `(c : obj[C]) `(F : J ⟶ C) := {
    vertex_map {x : J} : c ~{C}~> F x;
    cone_coherence {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ @vertex_map x ≈ @vertex_map y
  }.


Class Cone `(F : J ⟶ C) := {
  vertex_obj : C;
  coneFrom : ConeFrom vertex_obj F
}.

Coercion vertex_obj : Cone >-> obj.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ L ]" := (@vertex_map _ _ _ _ (@coneFrom _ _ _ L) _)
  (at level 9, format "vertex_map[ L ]") : category_scope.

Notation "Cone[ N ] F" := (ConeFrom N F)(* . { ψ : Cone F | vertex_obj[ψ] = N } *)
  (at level 9, format "Cone[ N ] F") : category_scope.

Definition Cocone `(F : J ⟶ C) := Cone (F^op).


Require Import Lib.
Require Export Functor.
Require Export Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Natural.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : C ⟶ D}.
Context `{G : C ⟶ D}.

Class Natural := {
  transform {X} : F X ~> G X;

  natural_transformation {X Y} (f : X ~> Y) :
    fmap f ∘ transform ≈ transform ∘ fmap f
}.

End Natural.

Notation "F ⟹ G" := (@Natural _ _ F G) (at level 90, right associativity).

Notation "transform[ F  ]" := (@transform _ _ _ _ F) (at level 9).

(* Natural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion transform : Natural >-> Funclass.

Section Nat.

Context `{C : Category}.
Context `{D : Category}.

Program Definition nat_identity `{F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.
Obligation 1. cat. Qed.

Program Definition nat_compose `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := fun X => transform[f] X ∘ transform[g] X
|}.
Obligation 1.
  intros.
  rewrite comp_assoc.
  rewrite natural_transformation.
  rewrite <- comp_assoc.
  rewrite natural_transformation.
  rewrite comp_assoc.
  reflexivity.
Qed.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Global Program Instance Nat : Category := {
  ob      := C ⟶ D;
  hom     := @Natural C D;
  id      := @nat_identity;
  compose := @nat_compose
}.
Obligation 1.
  destruct f.
Admitted.
Obligation 2.
  destruct f.
Admitted.
Obligation 3.
  destruct f.
Admitted.

End Nat.

Notation "[ C , D ]" := (@Nat C D) (at level 90, right associativity).

Require Import Coq.
Require Import Opposite.

Definition Copresheaves (C : Category) := [C, Coq].
Definition Presheaves   (C : Category) := [C^op, Coq].

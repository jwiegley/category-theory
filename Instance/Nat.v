Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Nat.

Context `{C : Category}.
Context `{D : Category}.

Program Definition nat_cequiv `{F : C ⟶ D} `{G : C ⟶ D} : crelation (F ⟹ G) :=
  fun n m => ∀ A, transform[n] A ≋ transform[m] A.

Hint Unfold nat_cequiv.

Global Program Definition nat_cequiv_equivalence `{F : C ⟶ D} `{G : C ⟶ D} :
  CRelationClasses.Equivalence (@nat_cequiv F G).
Proof.
  equivalence.
  transitivity (transform[y] A).
    apply X.
  apply X0.
Defined.

Global Program Instance nat_CSetoid `{F : C ⟶ D} `{G : C ⟶ D} :
  CSetoid (F ⟹ G) := {
  cequiv := nat_cequiv;
  setoid_cequiv := nat_cequiv_equivalence
}.

Global Program Definition nat_identity `{F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.

Hint Unfold nat_identity.

Global Program Definition nat_compose `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := fun X => transform[f] X ∘ transform[g] X
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite natural_transformation.
  rewrite <- comp_assoc.
  rewrite natural_transformation.
  rewrite comp_assoc.
  reflexivity.
Qed.

Hint Unfold nat_compose.

Global Program Definition nat_compose_respects
       `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D} :
  CMorphisms.Proper (cequiv ===> cequiv ===> cequiv) (@nat_compose F G K).
Proof.
  proper.
  autounfold.
  unfold cequiv in *; simpl in *.
  autounfold in *; simpl in *.
  intros.
  rewrite X, X0.
  reflexivity.
Defined.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Global Program Instance Nat : Category := {
  ob      := C ⟶ D;
  hom     := @Natural C D;
  id      := @nat_identity;
  compose := @nat_compose;

  compose_respects := @nat_compose_respects
}.
Next Obligation.
  simplify equiv; intros.
  simplify equiv; cat.
Qed.
Next Obligation.
  simplify equiv; intros.
  simplify equiv; cat.
Qed.
Next Obligation.
  simplify equiv; intros.
  simplify equiv; cat.
Qed.

End Nat.

Notation "[ C , D ]" := (@Nat C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "F ⊚ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Hint Unfold nat_compose.
Hint Unfold nat_identity.
Hint Unfold nat_cequiv.

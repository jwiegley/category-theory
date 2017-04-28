Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Nat.

Context `{C : Category}.
Context `{D : Category}.

Program Definition nat_equiv `{F : C ⟶ D} `{G : C ⟶ D} : relation (F ⟹ G) :=
  fun n m =>
    let setoid := {| equiv := fun X Y : ∀ X, F X ~> G X =>
                                forall A, X A ≈ Y A|} in
    @equiv _ setoid (transform[n]) (transform[m]).
Next Obligation. equivalence; transitivity (y A); auto. Qed.

Global Program Definition nat_equiv_equivalence `{F : C ⟶ D} `{G : C ⟶ D} :
  Equivalence (@nat_equiv F G).
Proof.
  equivalence.
  transitivity (y A); auto.
Qed.

Global Program Instance nat_Setoid `{F : C ⟶ D} `{G : C ⟶ D} :
  Setoid (F ⟹ G) := {
  equiv := nat_equiv;
  setoid_equiv := nat_equiv_equivalence
}.

Global Program Definition nat_identity `{F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.

Global Program Definition nat_compose `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := fun X => transform[f] X ∘ transform[g] X
|}.
Obligation 1.
  rewrite comp_assoc.
  rewrite natural_transformation.
  rewrite <- comp_assoc.
  rewrite natural_transformation.
  rewrite comp_assoc.
  reflexivity.
Qed.

Global Program Definition nat_compose_respects
       `{F : C ⟶ D} `{G : C ⟶ D} `{K : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@nat_compose F G K).
Proof. proper. Qed.

Hint Unfold nat_compose.
Hint Unfold nat_identity.
Hint Unfold nat_equiv.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Global Program Instance Nat : Category := {
  ob      := C ⟶ D;
  hom     := @Natural C D;
  id      := @nat_identity;
  compose := @nat_compose;

  compose_respects := @nat_compose_respects
}.

End Nat.

Notation "[ C , D ]" := (@Nat C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "F ⊚ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Hint Unfold nat_compose.
Hint Unfold nat_identity.
Hint Unfold nat_equiv.

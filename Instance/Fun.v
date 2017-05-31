Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Fun.

Context {C : Category}.
Context {D : Category}.

Program Definition nat_equiv {F : C ⟶ D} {G : C ⟶ D} : crelation (F ⟹ G) :=
  fun n m => ∀ A, transform[n] A ≈ transform[m] A.

Hint Unfold nat_equiv.

Global Program Definition nat_equiv_equivalence {F : C ⟶ D} {G : C ⟶ D} :
  Equivalence (@nat_equiv F G).
Proof.
  equivalence.
  transitivity (transform[y] A).
    apply X.
  apply X0.
Qed.

Global Program Instance nat_Setoid {F : C ⟶ D} {G : C ⟶ D} :
  Setoid (F ⟹ G) := {
  equiv := nat_equiv;
  setoid_equiv := nat_equiv_equivalence
}.

Global Program Definition nat_identity {F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.

Hint Unfold nat_identity.

Global Program Definition nat_compose {F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := fun X => transform[f] X ∘ transform[g] X
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  apply nat_compose_obligation_1.
Qed.

Hint Unfold nat_compose.

Global Program Definition nat_compose_respects
       {F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@nat_compose F G K).
Proof. proper. Qed.

(* Fun is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Global Program Definition Fun : Category := {|
  ob      := C ⟶ D;
  hom     := @Transform C D;
  id      := @nat_identity;
  compose := @nat_compose;

  compose_respects := @nat_compose_respects
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "F ⊙ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Hint Unfold nat_compose.
Hint Unfold nat_identity.
Hint Unfold nat_equiv.

Arguments nat_equiv {_ _ _ _} _ _ /.

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_identity ⊙ N ≈[Fun] N.
Proof. unfold nat_identity, nat_compose; simpl; intros; cat. Qed.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ⊙ nat_identity ≈[Fun] N.
Proof. unfold nat_identity, nat_compose; simpl; intros; cat. Qed.

Theorem Functor_Setoid_Nat_Iso `(F : C ⟶ D) (G : C ⟶ D) :
  F ≅[Fun] G <--> @equiv _ Functor_Setoid F G.
Proof.
  split; intros; simpl.
    given (iso : ∀ x : C, F x ≅ G x). {
      intros; isomorphism; simpl; intros.
      - apply X.
      - apply (X⁻¹).
      - srewrite (iso_to_from X); cat.
      - srewrite (iso_from_to X); cat.
    }
    exists iso; simpl in *; intros.
    rewrite <- comp_assoc.
    rewrite (naturality[to X]).
    rewrite comp_assoc.
    srewrite (iso_from_to X); cat.
  destruct X.
  isomorphism; simpl; intros.
  - transform; simpl; intros.
    + apply x.
    + rewrite e; simpl.
      rewrite !comp_assoc.
      rewrite iso_to_from; cat.
    + rewrite e; simpl.
      rewrite !comp_assoc.
      rewrite iso_to_from; cat.
  - transform; simpl; intros.
    + apply x.
    + rewrite e; simpl.
      rewrite <- !comp_assoc.
      rewrite iso_to_from; cat.
    + rewrite e; simpl.
      rewrite <- !comp_assoc.
      rewrite iso_to_from; cat.
  - rewrite fmap_id.
    apply iso_to_from.
  - rewrite fmap_id.
    apply iso_from_to.
Qed.

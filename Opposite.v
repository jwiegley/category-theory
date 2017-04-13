Require Import Lib.
Require Export Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Reserved Notation "C ^op" (at level 90).

Program Instance Opposite `(_ : Category C) : Category C := {
  hom     := fun x y => @hom C _ y x;
  id      := @id C _;
  compose := fun _ _ _ f g => g ∘ f
}.
Obligation 1.
  intros ??????.
  rewrite H0, H1.
  reflexivity.
Defined.
Obligation 2. cat. Qed.
Obligation 3. cat. Qed.
Obligation 4.
  rewrite comp_assoc.
  reflexivity.
Qed.

Notation "C ^op" := (@Opposite _ C) (at level 90) : category_scope.

Open Scope equiv_scope.

(* jww (2017-04-13): Need to define equivalence of categories. *)
Lemma op_involutive `{C : Category ob} : (C^op)^op === C.
Proof.
  unfold Opposite.
  induction C.
  unfold Opposite_obligation_1.
Admitted.

Definition obj `(_ : Category C) := C.

Coercion obj : Category >-> Sortclass.

Definition op `{C : Category ob} : ∀ {X Y : ob},
  (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. intros; assumption. Defined.

Definition unop `{C : Category ob} : ∀ {X Y : ob},
  (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.

(*
Require Export Functor.

(* jww (2017-04-13): Right now this loops indefinitely. *)
Program Instance Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op := {
    fobj := @fobj C D F;
    fmap := fun X Y f => @fmap C D F Y X (op f)
}.
Obligation 1. unfold op. apply functor_id_law. Qed.
Obligation 2. unfold op. apply functor_compose_law. Qed.

(* jww (2014-08-10): Until I figure out how to make C^op^op implicitly unify
   with C, I need a way of undoing the action of Opposite_Functor. *)

Program Instance Reverse_Opposite_Functor `(F : C^op ⟶ D^op) : C ⟶ D := {
    fobj := @fobj _ _ F;
    fmap := fun X Y f => unop (@fmap _ _ F Y X f)
}.
Obligation 1.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_id_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e X). auto.
Qed.
Obligation 2.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_compose_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e Z Y X g f).
  auto.
Qed.

Lemma op_functor_involutive `(F : Functor)
  : Reverse_Opposite_Functor (Opposite_Functor F) = F.
Proof.
  unfold Reverse_Opposite_Functor.
  unfold Opposite_Functor.
  destruct F.
  apply fun_irrelevance.
  auto.
Qed.
*)
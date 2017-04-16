Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Construct.Opposite.
Require Import Category.Functor.Bifunctor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(** This is the Yoneda embedding. *)
Program Instance Yoneda `(C : Category) : C ⟶ [C^op, Sets] := Hom (C^op).
Obligation 1. apply op_involutive. Defined.

(* jww (2017-04-15):  TODO
Program Instance YonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C^op} :
  C A ⟹ F ≃ F A.
Obligation 1.
  intros.
  destruct X.
  apply transform.
  simpl.
  destruct C.
Admitted.
Obligation 2.
  intros.
  simpl.
  pose (@fmap C Sets F A).
  apply Build_Natural with (transform := fun Y φ => h Y φ X).
  intros.
  inversion F. simpl.
  intro e.
  unfold h.
Admitted.
Obligation 3.
Admitted.
(*
  pose (f := fun (_ : unit) => e).
  destruct C.
  destruct F. simpl.
  rewrite functor_id_law0.
  crush.
Qed.
Obligation 4.
  extensionality e.
  destruct e.
  simpl.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct C as [ob0 uhom0 hom0 id0].
  destruct F.
  simpl.
  assert (fmap0 A f g (transport0 A (id0 A)) =
          (fmap0 A f g ∘ transport0 A) (id0 A)).
    crush. rewrite H. clear H.
  rewrite naturality0.
  crush.
Qed.
*)
*)
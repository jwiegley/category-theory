Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Theory.Bifunctor.
Require Import Category.Construct.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Definition Presheaves   (C : Category) := [C^op, Sets].
Definition Copresheaves (C : Category) := [C, Sets].

Program Instance fobj_setoid `{C : Category} `{F : C ⟶ Sets} {A : C} :
  Setoid (F A).

(** This is the Yoneda embedding. *)
(* Program Instance Yoneda `{C : Category} : C ⟶ [C^op, Sets] := HomFunctor (C^op). *)
(* Obligation 1. apply op_involutive. Defined. *)

(* Program Definition nat_fobj_setoid_morphism (C : Category) (F : C ⟶ Sets) (A : C) : *)
(*   SetoidMorphism (@nat_Setoid C Sets (Hom(A,─)) F) (@fobj_setoid C F A) := {| *)
(*   morphism := _ *)
(* |}. *)
(* Obligation 1. *)
(*   destruct X; simpl in *. *)
(*   unfold Basics.compose in *. *)
(*   apply transform, id. *)
(* Defined. *)
(* Obligation 2. *)
(*   repeat intro. *)
(*   unfold nat_fobj_setoid_morphism_obligation_1. *)
(*   destruct x, y; simpl in *. *)
(*   unfold Basics.compose in *; simpl in *. *)
(*   unfold nat_equiv in H. *)
(*   unfold equiv in H; simpl in H. *)
(*   specialize (H A id). *)
(*   simpl in *. *)
(*   Set Printing All. *)
(*   eapply H. *)
(*   rewrite H. *)
(*   destruct H. *)
(*   apply H. *)
(*   rewrite H. *)

(*
Program Instance YonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C} :
  [C, Sets] (Hom(A,─)) F ≅[Sets] F A.
Next Obligation.
  eapply {| morphism := _ |}.
  Unshelve.
  - intros.
    apply X, id.
  - repeat intro.
    destruct x, y; simpl in *.
    unfold nat_equiv in X; simpl in X.
    rewrite X.
    reflexivity.
Defined.
Next Obligation.
  eapply {| morphism := _ |}.
  Unshelve.
  - intros.
    pose (@fmap C Sets F A).
    eapply {| transform := fun Y =>
                {| morphism := _ |} |}.
  - repeat intro; simpl in *.
    reflexivity.
    Unshelve.
    + simpl; unfold Basics.compose; intros.
      rewrite fmap_comp.
Defined.
Admitted.
Next Obligation.
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
Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Export Category.Instance.One.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Slice `(C : Category) `(c : C) : Category := {
  ob      := { a : C & a ~> c };
  hom     := fun x y => (` x) ~> (` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
}.

Notation "C ̸ c" := (@Slice C c) (at level 90).

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Identity ↓ Select c). *)

Program Instance Comma_Slice `(C : Category) `(c : C) :
  C̸c ≅[Cat] (Identity ↓ Select c) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  exists (X, tt); simpl.
  assumption.
Defined.
Next Obligation.
  exists o.
  assumption.
Defined.
Next Obligation.
  unfold Comma_Slice_obligation_1.
  simpl; intros.
  destruct X, x, u; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold Comma_Slice_obligation_1.
  simpl; intros.
  destruct X; simpl.
  reflexivity.
Qed.

Program Instance Coslice `(C : Category) `(c : C) : Category := {
  ob      := { a : C & c ~> a };
  hom     := fun x y => (` x) ~> (` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
}.

Notation "C ̸co c" := (@Coslice C c) (at level 90).

Program Instance Comma_Coslice `(C : Category) `(c : C) :
  C ̸co c ≅[Cat] (Select c ↓ Identity) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  exists (tt, X); simpl.
  assumption.
Defined.
Next Obligation.
  exists o.
  assumption.
Defined.
Next Obligation.
  unfold Comma_Slice_obligation_1.
  simpl; intros.
  destruct X, x, u; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold Comma_Slice_obligation_1.
  simpl; intros.
  destruct X; simpl.
  reflexivity.
Qed.

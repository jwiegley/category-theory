Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This instance must appear in a separate file, because the Closed structure
   makes use of isomorphisms in [Sets]. *)

Program Instance Sets_Closed : @Closed Sets _ := {
  Exp := fun X Y =>
            {| carrier := SetoidMorphism X Y
             ; is_csetoid := @SetoidMorphism_Setoid X Y
             |};
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    {| morphism := fun x =>
                         {| morphism := fun y => f (x, y) |} |} |}
     ; from := {| morphism := fun f =>
                    {| morphism := fun p => f (fst p) (snd p) |} |}
     |}
}.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  simplify equiv; intros.
  apply proper_morphism.
  split; simpl; intuition.
Qed.
Next Obligation.
  proper; destruct x, y; simpl in *.
  simplify equiv in all; intros.
  simplify equiv; intros.
  apply X.
Qed.
Next Obligation.
  proper.
  destruct x, y; simpl in *.
  destruct X; simpl in *.
  destruct f; simpl in *.
  unfold CMorphisms.Proper, CMorphisms.respectful in proper_morphism.
  simplify equiv in proper_morphism.
  rewrite (proper_morphism _ _ c3).
  destruct (morphism c1).
  apply proper_morphism0; assumption.
Qed.
Next Obligation.
  proper.
  simplify equiv; intros.
  destruct x0, x, y; simpl in *.
  unfold CMorphisms.Proper, CMorphisms.respectful in *.
  simplify equiv in X.
  apply X.
Qed.
Next Obligation.
  simplify equiv; intros.
  simplify equiv; intros.
  simplify equiv; intros.
  reflexivity.
Qed.
Next Obligation.
  simplify equiv; intros.
  simplify equiv; intros.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.
Next Obligation.
  simplify equiv; intros.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

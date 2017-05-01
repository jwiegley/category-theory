Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Sets.
Require Export Category.Instance.Sets.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This instance must appear in a separate file, because the Closed structure
   makes use of isomorphisms in [Sets]. *)

Program Instance Sets_Closed : @Closed Sets _ := {
  Exp := fun X Y =>
            {| carrier := SetoidMorphism X Y
             ; is_setoid := @SetoidMorphism_Setoid X Y
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
  apply proper_morphism.
  split; simpl; intuition.
Qed.
Next Obligation.
  proper.
  destruct x, y; simpl in *.
  destruct f; simpl in *.
  unfold Proper, respectful in proper_morphism.
  rewrite (proper_morphism _ _ a).
  destruct (morphism c1).
  apply proper_morphism0; assumption.
Qed.

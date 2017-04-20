Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

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
  simpl; split; intuition.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  simpl; split; intuition.
Qed.
Next Obligation. proper. Qed.
Next Obligation.
  proper; destruct f; simpl.
  destruct x, y; simpl in *.
  pose proof (proper_morphism c c1 H3) as HA.
  simpl in HA; rewrite HA; clear HA.
  destruct (morphism c1); simpl.
  apply proper_morphism0; auto.
Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.

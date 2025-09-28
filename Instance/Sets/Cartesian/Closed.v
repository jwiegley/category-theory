Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(* This instance must appear in a separate file, because the Closed structure
   makes use of isomorphisms in [Sets]. *)

#[export]
Program Instance Sets_Closed : @Closed Sets _ := {
  exponent_obj := fun x y =>
    {| carrier := SetoidMorphism x y
     ; is_setoid := @SetoidMorphism_Setoid x y |};

  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    {| morphism := fun x =>
                         {| morphism := fun y => f (x, y) |} |} |}
     ; from := {| morphism := fun f =>
                    {| morphism := fun p => f (fst p) (snd p) |} |} |}
}.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; simpl in *.
  destruct f; simpl in *.
  unfold Proper, respectful, SetoidMorphism_equiv in proper_morphism.
  rewrite (proper_morphism _ _ X).
  destruct (morphism y).
  apply proper_morphism0; assumption.
Qed.

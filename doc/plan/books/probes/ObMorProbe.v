(* PROBE for QA finding E1 (#929): how many natural transformations between the
   object-functor ob and the morphism-functor mor on Cat?

   #929 as filed miscounts these.  The correct counts come from co-Yoneda:
   ob = Cat(1, -) and mor = Cat(2, -), where 1 is the terminal category and 2
   the walking arrow.  So
       Nat(ob, mor) = Nat(Cat(1,-), Cat(2,-)) ~= Cat(2, 1)   -- ONE functor
       Nat(mor, ob) = Nat(Cat(2,-), Cat(1,-)) ~= Cat(1, 2)   -- TWO functors
   i.e. one transformation ob ==> mor and two mor ==> ob, THREE in total.

   This probe checks the two counting facts the argument turns on, at the level
   of the shapes themselves: there is exactly one map from the walking arrow to
   the point, and exactly two points of the walking arrow. *)

Require Import Coq.Init.Datatypes.

(* Objects of the walking arrow 2, and of the terminal category 1. *)
Inductive Two := TZero | TOne.
Inductive One := Star.

(* Cat(2,1) on objects: every functor 2 -> 1 sends both objects to Star, so the
   object-map is unique. *)
Theorem two_to_one_unique :
  forall f g : Two -> One, forall t : Two, f t = g t.
Proof. intros f g t. destruct (f t), (g t). reflexivity. Qed.

(* Cat(1,2) on objects: a functor 1 -> 2 is a choice of object of 2, and there
   are exactly two such choices. *)
Theorem one_to_two_two_choices :
  forall f : One -> Two, (f Star = TZero) \/ (f Star = TOne).
Proof. intro f. destruct (f Star). - left. reflexivity. - right. reflexivity. Qed.

Theorem one_to_two_choices_differ : TZero <> TOne.
Proof. discriminate. Qed.

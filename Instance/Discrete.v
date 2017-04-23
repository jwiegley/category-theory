Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Coq.MSets.MSetInterface.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module Discrete (O : DecidableType) (S : WSetsOn O).

(* Local Obligation Tactic := simpl; intros; intuition. *)

Fixpoint In' (f : O.t * O.t) (l : list (O.t * O.t)) : Prop :=
    match l with
      | nil => False
      | (x, y) :: m => (O.eq (fst f) x /\ O.eq (snd f) y) \/ In f m
    end.

Fixpoint Subset' (X Y : O.t) (l : list (O.t * O.t)) : list (O.t * O.t) :=
  filter (fun p => if O.eq_dec (fst p) X
                   then if O.eq_dec (snd p) Y
                        then true
                        else false
                   else false) l.
Arguments Subset' X Y l : simpl never.

(*
  repeat (
    match goal with
    | [ H : { _ | _ }%type |- _ ] => destruct H
    | [ |- { _ | _ }%type ] => econstructor
    | [ H : { _ | _  & _ }%type |- _ ] => destruct H
    | [ |- { _ | _  & _ }%type ] => econstructor
    | [ H : _ //\\ _ |- _ ] => destruct H
    | [ |- _ //\\ _ ] => econstructor
    end; simpl in *; intuition; eauto).
  destruct f.
*)

Program Instance Discrete (Obs : S.t) (Homs : list (O.t * O.t)) : Category := {
  ob  := { x : O.t | S.In x Obs };
  hom := fun X Y =>
    { f : list (O.t * O.t)
    | ∀ h, In' h f <-> In' h ((X, Y) :: Subset' X Y  Homs) }%type;
  homset := fun X Y =>
    {| equiv := fun f g => ∀ h, In' h f <-> In' h g |}%type;
  id := fun X => exist _ ((X, X) :: nil) _
}.
Next Obligation.
  equivalence.
Admitted.
Next Obligation.
  firstorder.
  induction Homs; simpl in *; auto.
  destruct a; simpl in *.
  destruct (O.eq_dec t1 X); intuition.
  destruct (O.eq_dec t2 X); intuition.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

End Discrete.

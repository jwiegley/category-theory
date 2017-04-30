Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Local Ltac crush :=
  repeat (
    match goal with
    | [ H : _ ∧ _ |- _ ] => destruct H
    | [ H : _ ∨ _ |- _ ] => destruct H
    end; subst; auto).

(* The category 2 has two objects, their identity morphisms, and one morphism
   from the first object to the second (here denoted false and true). *)

Program Instance _2 : Category := {
  ob      := bool;
  hom     := fun x y => ((x = y) + ((x = false) * (y = true)))%type;
  homset  := fun x y => {| equiv := fun f g => f = g |};
  id      := fun x => Datatypes.inl (eq_refl x);
  compose := fun _ _ _ f g =>
    match f with
    | Datatypes.inl H =>
      match g with
      | Datatypes.inl H0 => Datatypes.inl (eq_trans H0 H)
      | Datatypes.inr H0 =>
        Datatypes.inr
          match H0 with
          | pair H1 H2 => pair H1 (eq_trans (eq_sym H) H2)
          end
      end
    | Datatypes.inr H =>
      Datatypes.inr
        match g with
        | Datatypes.inl H0 =>
          match H with
          | pair H1 H2 => pair (eq_trans H0 H1) H2
          end
        | Datatypes.inr H0 =>
          match H with
          | pair _ H2 =>
            match H0 with
            | pair H3 _ => pair H3 H2
            end
          end
        end
    end
}.
Next Obligation.
  equivalence; congruence.
Qed.
Next Obligation.
  destruct f.
    reflexivity.
  destruct p; subst.
  reflexivity.
Qed.
Next Obligation.
  destruct f.
    subst; simpl.
    reflexivity.
  destruct p; subst.
  reflexivity.
Qed.
Next Obligation.
  destruct f, g, h;
  subst; simpl; intuition;
  subst; simpl; auto.
Qed.

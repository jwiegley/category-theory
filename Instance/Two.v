Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
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
  hom     := fun x y => x = y ∨ (x = false ∧ y = true);
  homset  := fun x y => {| equiv := proof_eq |};
  id      := fun x => or_introl (eq_refl x);
  compose := fun _ _ _ f g =>
               match f with
               | or_introl H =>
                 match g with
                 | or_introl H0 => or_introl (eq_trans H0 H)
                 | or_intror H0 =>
                   or_intror
                     match H0 with
                     | conj H1 H2 => conj H1 (eq_trans (eq_sym H) H2)
                     end
                 end
               | or_intror H =>
                 or_intror
                   match g with
                   | or_introl H0 =>
                     match H with
                     | conj H1 H2 => conj (eq_trans H0 H1) H2
                     end
                   | or_intror H0 =>
                     match H with
                     | conj _ H2 =>
                       match H0 with
                       | conj H3 _ => conj H3 H2
                       end
                     end
                   end
               end
}.
Next Obligation. crush. Qed.
Next Obligation. crush. Qed.
Next Obligation. crush. Qed.

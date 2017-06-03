Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Pending.Finite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(*
Program Definition Span_Structure : Concrete_Structure := {|
  obs  := 3;
  arrs := [set (0, 0); (1, 1); (2, 2); (1, 0); (1, 2)]
|}.
Next Obligation.
  destruct n; intuition idtac.
  destruct n; intuition idtac.
  destruct n; intuition idtac.
  repeat (apply le_S_n in H).
  mini_omega.
Qed.
Next Obligation.
  destruct n, m, o; intuition idtac;
  try (inversion H4; subst; discriminate);
  try (inversion H0; subst; discriminate);
  destruct n, m; intuition idtac;
  try (inversion H4; subst; discriminate);
  try (inversion H0; subst; discriminate);
  destruct m, o; intuition idtac;
  try (inversion H4; subst; discriminate);
  try (inversion H0; subst; discriminate);
  destruct o; intuition idtac;
  try (inversion H4; subst; discriminate);
  try (inversion H0; subst; discriminate).
Qed.

Definition Span_Category := Concrete Span_Structure.

Program Definition Span {C : Category} {S x y : C} (f : S ~> x) (g : S ~> y) :
  Span_Category ⟶ C := {|
  fobj := fun z =>
    match proj1_sig z with
    | 0%nat => x
    | 1%nat => S
    | 2%nat => y
    | _ => _
    end;
  fmap := fun z w h => _
|}.
*)

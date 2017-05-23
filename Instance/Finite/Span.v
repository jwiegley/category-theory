Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Finite.

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

Program Definition Span {C : Category} {S X Y : C} (f : S ~> X) (g : S ~> Y) :
  Span_Category ⟶ C := {|
  fobj := fun x =>
    match proj1_sig x with
    | 0%nat => X
    | 1%nat => S
    | 2%nat => Y
    | _ => _
    end;
  fmap := fun x y f => _
|}.
*)

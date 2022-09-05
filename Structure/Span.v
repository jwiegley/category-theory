Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Roof.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Span (C : Category) := Roof ⟶ C.

Definition Cospan (C : Category) := Roof^op ⟶ C.

Program Definition ASpan {C : Category} {S x y : C} (f : S ~> x) (g : S ~> y) :
  Roof ⟶ C := {|
  fobj := fun z => match z with
    | RNeg  => x
    | RZero => S
    | RPos  => y
    end;
  fmap := fun z w _ => match z, w with
    | RNeg,  RNeg  => id[x]
    | RZero, RNeg  => f
    | RZero, RZero => id[S]
    | RZero, RPos  => g
    | RPos,  RPos  => id[y]
    | _,      _      => _
    end
|}.
Next Obligation.
  destruct z, w; simpl; intuition idtac; auto with roof_laws.
Defined.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation.
  proper.
  destruct x0, y0; simpl; auto with roof_laws; reflexivity.
Qed.
Next Obligation.
  destruct x0; reflexivity.
Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with roof_laws;
  rewrite ?id_left, ?id_right;
  reflexivity.
Qed.

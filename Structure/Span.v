Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.
Require Export Category.Instance.Roof.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Span (C : Category) := Roof ⟶ C.

Definition Cospan (C : Category) := Roof^op ⟶ C.

Program Definition ASpan {C : Category} {S X Y : C} (f : S ~> X) (g : S ~> Y) :
  Roof ⟶ C := {|
  fobj := fun x => match x with
    | RNeg  => X
    | RZero => S
    | RPos  => Y
    end;
  fmap := fun x y _ => match x, y with
    | RNeg,  RNeg  => id[X]
    | RZero, RNeg  => f
    | RZero, RZero => id[S]
    | RZero, RPos  => g
    | RPos,  RPos  => id[Y]
    | _,      _      => _
    end
|}.
Next Obligation.
  destruct x, y; simpl; intuition idtac; auto with roof_laws.
Defined.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation.
  proper.
  destruct X0, Y0; simpl; auto with roof_laws; reflexivity.
Qed.
Next Obligation.
  destruct X0; reflexivity.
Qed.
Next Obligation.
  destruct X0, Y0, Z; simpl; auto with roof_laws;
  rewrite ?id_left, ?id_right;
  reflexivity.
Qed.

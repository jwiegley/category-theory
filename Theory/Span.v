Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive Trinary : Type := TrNeg | TrZero | TrPos.

Inductive TrinaryHom : Trinary -> Trinary -> Type :=
  | IdNeg   : TrinaryHom TrNeg  TrNeg
  | ZeroNeg : TrinaryHom TrZero TrNeg
  | IdZero  : TrinaryHom TrZero TrZero
  | ZeroPos : TrinaryHom TrZero TrPos
  | IdPos   : TrinaryHom TrPos  TrPos.

Lemma TrNeg_TrZero_absurd : TrinaryHom TrNeg TrZero -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction TrNeg_TrZero_absurd.

Lemma TrPos_TrZero_absurd : TrinaryHom TrPos TrZero -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction TrPos_TrZero_absurd.

Lemma TrNeg_TrPos_absurd : TrinaryHom TrNeg TrPos -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction TrNeg_TrPos_absurd.

Lemma TrPos_TrNeg_absurd : TrinaryHom TrPos TrNeg -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction TrPos_TrNeg_absurd.

Program Definition Trinary_Category : Category := {|
  ob  := Trinary;
  hom := TrinaryHom;
  (* Any hom that typechecks is valid. *)
  homset := fun x y => {| equiv := fun (f g : TrinaryHom x y) => True |};
  id := fun x => match x return TrinaryHom x x with
    | TrNeg  => IdNeg
    | TrZero => IdZero
    | TrPos  => IdPos
    end
|}.
Next Obligation.
  destruct A, B, C;
  try constructor;
  try inversion f;
  try inversion g.
Defined.

Definition Span {C : Category} := Trinary_Category ⟶ C.

Program Definition ASpan {C : Category} {S X Y : C} (f : S ~> X) (g : S ~> Y) :
  Span := {|
  fobj := fun x => match x with
    | TrNeg  => X
    | TrZero => S
    | TrPos  => Y
    end;
  fmap := fun x y _ => match x, y with
    | TrNeg,  TrNeg  => id[X]
    | TrZero, TrNeg  => f
    | TrZero, TrZero => id[S]
    | TrZero, TrPos  => g
    | TrPos,  TrPos  => id[Y]
    | _,      _      => _
    end
|}.
Next Obligation.
  destruct x, y; simpl; intuition idtac; auto.
Defined.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation.
  proper.
  destruct X0, Y0; simpl; auto; reflexivity.
Qed.
Next Obligation.
  destruct X0; reflexivity.
Qed.
Next Obligation.
  destruct X0, Y0, Z; simpl; auto;
  rewrite ?id_left, ?id_right;
  reflexivity.
Qed.

Definition Cospan {C : Category} := Trinary_Category ⟶ C^op.

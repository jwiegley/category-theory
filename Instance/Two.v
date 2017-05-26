Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive TwoObj : Type := TwoX | TwoY.

Inductive TwoHom : TwoObj -> TwoObj -> Type :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition caseTwoXX (p : TwoHom TwoX TwoX) :
  forall
    (P : TwoHom TwoX TwoX -> Type)
    (PTwoIdX : P TwoIdX), P p :=
  match p with
  | TwoIdX => fun _ P => P
  end.

Definition caseTwoYY (p : TwoHom TwoY TwoY) :
  forall
    (P : TwoHom TwoY TwoY -> Type)
    (PTwoIdY : P TwoIdY), P p :=
  match p with
  | TwoIdY => fun _ P => P
  end.

Definition caseTwoXY (p : TwoHom TwoX TwoY) :
  forall
    (P : TwoHom TwoX TwoY -> Type)
    (PTwoIdY : P TwoXY), P p :=
  match p with
  | TwoXY => fun _ P => P
  end.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 =>
  match goal with
    [ H : TwoHom TwoY TwoX |- _ ] =>
    contradiction (TwoHom_Y_X_absurd H)
  end : two_laws.

(* The category 2 has two objects, their identity morphisms, and one morphism
   from the first object to the second (here denoted false and true). *)

Program Definition _2 : Category := {|
  ob      := TwoObj;
  hom     := TwoHom;
  homset  := fun x y => {| equiv := eq |};
  id      := fun x => match x with
    | TwoX => TwoIdX
    | TwoY => TwoIdY
    end;
  compose := fun x y z (f : TwoHom y z) (g : TwoHom x y) =>
    match x, y, z with
    | TwoX, TwoX, TwoX => TwoIdX
    | TwoY, TwoY, TwoY => TwoIdY
    | TwoX, TwoX, TwoY => TwoXY
    | TwoX, TwoY, TwoY => TwoXY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct X, Y; auto with two_laws; intuition.
  - pattern f.
    apply caseTwoXX; reflexivity.
  - pattern f.
    apply caseTwoXY; reflexivity.
  - pattern f.
    apply caseTwoYY; reflexivity.
Qed.
Next Obligation.
  destruct X, Y; auto with two_laws; intuition.
  - pattern f.
    apply caseTwoXX; reflexivity.
  - pattern f.
    apply caseTwoXY; reflexivity.
  - pattern f.
    apply caseTwoYY; reflexivity.
Qed.
Next Obligation.
  destruct X, Y, Z, W; auto with two_laws; intuition.
Qed.
Next Obligation.
  destruct X, Y, Z, W; auto with two_laws; intuition.
Qed.

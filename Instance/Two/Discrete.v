Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive TwoDObj : Type := TwoDX | TwoDY.

Inductive TwoDHom : TwoDObj -> TwoDObj -> Type :=
  | TwoDIdX : TwoDHom TwoDX TwoDX
  | TwoDIdY : TwoDHom TwoDY TwoDY.

Definition caseTwoDXX (p : TwoDHom TwoDX TwoDX) :
  forall
    (P : TwoDHom TwoDX TwoDX -> Type)
    (PTwoDIdX : P TwoDIdX), P p :=
  match p with
  | TwoDIdX => fun _ P => P
  end.

Definition caseTwoDYY (p : TwoDHom TwoDY TwoDY) :
  forall
    (P : TwoDHom TwoDY TwoDY -> Type)
    (PTwoDIdY : P TwoDIdY), P p :=
  match p with
  | TwoDIdY => fun _ P => P
  end.

Lemma TwoDHom_X_Y_absurd : TwoDHom TwoDX TwoDY -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 =>
  match goal with
    [ H : TwoDHom TwoDX TwoDY |- _ ] =>
    contradiction (TwoDHom_X_Y_absurd H)
  end : two_laws.

Lemma TwoDHom_Y_X_absurd : TwoDHom TwoDY TwoDX -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 =>
  match goal with
    [ H : TwoDHom TwoDY TwoDX |- _ ] =>
    contradiction (TwoDHom_Y_X_absurd H)
  end : two_laws.

(* The discrete category 2 has two objects and their identity morphisms. *)

Program Definition Two_Discrete : Category := {|
  ob      := TwoDObj;
  hom     := TwoDHom;
  homset  := fun x y => {| equiv := eq |};
  id      := fun x => match x with
    | TwoDX => TwoDIdX
    | TwoDY => TwoDIdY
    end;
  compose := fun x y z (f : TwoDHom y z) (g : TwoDHom x y) =>
    match x, y, z with
    | TwoDX, TwoDX, TwoDX => TwoDIdX
    | TwoDY, TwoDY, TwoDY => TwoDIdY
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
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct X, Y; auto with two_laws; intuition.
    pattern f.
    apply caseTwoDXX; reflexivity.
  pattern f.
  apply caseTwoDYY; reflexivity.
Qed.
Next Obligation.
  destruct X, Y; auto with two_laws; intuition.
    pattern f.
    apply caseTwoDXX; reflexivity.
  pattern f.
  apply caseTwoDYY; reflexivity.
Qed.
Next Obligation.
  destruct X, Y, Z, W; auto with two_laws; intuition.
Qed.
Next Obligation.
  destruct X, Y, Z, W; auto with two_laws; intuition.
Qed.

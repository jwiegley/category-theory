Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This is the category of three objects and two arrows, from the first object
   to the other two (as well as the three identity morphisms):

                x
              /   \
           f /     \ g
            /       \
           v         v
          y           z

  This is used to build diagrams that identify spans and pullbacks. *)

Inductive RoofObj : Type := RNeg | RZero | RPos.

Inductive RoofHom : RoofObj -> RoofObj -> Type :=
  | IdNeg   : RoofHom RNeg  RNeg
  | ZeroNeg : RoofHom RZero RNeg
  | IdZero  : RoofHom RZero RZero
  | ZeroPos : RoofHom RZero RPos
  | IdPos   : RoofHom RPos  RPos.

Definition caseRoofNegNeg (p : RoofHom RNeg RNeg) :
  forall
    (P : RoofHom RNeg RNeg -> Type)
    (PIdNeg : P IdNeg), P p :=
  match p with
  | IdNeg => fun _ P => P
  end.

Definition caseRoofZeroNeg (p : RoofHom RZero RNeg) :
  forall
    (P : RoofHom RZero RNeg -> Type)
    (PZeroNeg : P ZeroNeg), P p :=
  match p with
  | ZeroNeg => fun _ P => P
  end.

Definition caseRoofZeroZero (p : RoofHom RZero RZero) :
  forall
    (P : RoofHom RZero RZero -> Type)
    (PIdZero : P IdZero), P p :=
  match p with
  | IdZero => fun _ P => P
  end.

Definition caseRoofZeroPos (p : RoofHom RZero RPos) :
  forall
    (P : RoofHom RZero RPos -> Type)
    (PZeroPos : P ZeroPos), P p :=
  match p with
  | ZeroPos => fun _ P => P
  end.

Definition caseRoofPosPos (p : RoofHom RPos RPos) :
  forall
    (P : RoofHom RPos RPos -> Type)
    (PIdPos : P IdPos), P p :=
  match p with
  | IdPos => fun _ P => P
  end.

Lemma RNeg_RZero_absurd : RoofHom RNeg RZero -> False.
Proof. inversion 1. Qed.

Hint Extern 4 => contradiction RNeg_RZero_absurd : roof_laws.

Lemma RPos_RZero_absurd : RoofHom RPos RZero -> False.
Proof. inversion 1. Qed.

Hint Extern 4 => contradiction RPos_RZero_absurd : roof_laws.

Lemma RNeg_RPos_absurd : RoofHom RNeg RPos -> False.
Proof. inversion 1. Qed.

Hint Extern 4 => contradiction RNeg_RPos_absurd : roof_laws.

Lemma RPos_RNeg_absurd : RoofHom RPos RNeg -> False.
Proof. inversion 1. Qed.

Hint Extern 4 => contradiction RPos_RNeg_absurd : roof_laws.

Program Definition Roof : Category := {|
  ob  := RoofObj;
  hom := RoofHom;
  (* Any hom that typechecks is valid. *)
  homset := fun x y => {| equiv := fun (f g : RoofHom x y) => True |};
  id := fun x => match x return RoofHom x x with
    | RNeg  => IdNeg
    | RZero => IdZero
    | RPos  => IdPos
    end
|}.
Next Obligation.
  destruct A, B, C;
  try constructor;
  try inversion f;
  try inversion g.
Defined.

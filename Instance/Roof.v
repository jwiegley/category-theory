Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This is the category of three objects and two arrows from the first object
   to the other two (and three identity morphisms):

                x
              /   \
             /     \
            /       \
           /         \
          v           v
            y       z

  This is used to build diagrams that identify spans and pullbacks. *)

Inductive RoofObj : Type := RNeg | RZero | RPos.

Inductive RoofHom : RoofObj -> RoofObj -> Type :=
  | IdNeg   : RoofHom RNeg  RNeg
  | ZeroNeg : RoofHom RZero RNeg
  | IdZero  : RoofHom RZero RZero
  | ZeroPos : RoofHom RZero RPos
  | IdPos   : RoofHom RPos  RPos.

Lemma RNeg_RZero_absurd : RoofHom RNeg RZero -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction RNeg_RZero_absurd.

Lemma RPos_RZero_absurd : RoofHom RPos RZero -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction RPos_RZero_absurd.

Lemma RNeg_RPos_absurd : RoofHom RNeg RPos -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction RNeg_RPos_absurd.

Lemma RPos_RNeg_absurd : RoofHom RPos RNeg -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 => contradiction RPos_RNeg_absurd.

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

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

Definition RoofHom_inv_t : forall x y, RoofHom x y -> Prop.
Proof.
  intros [] [] f.
  exact (f = IdNeg).
  exact False.          (* Unused, any Prop is ok here *)
  exact False.          (* Unused, any Prop is ok here *)
  exact (f = ZeroNeg).
  exact (f = IdZero).
  exact (f = ZeroPos).
  exact False.          (* Unused, any Prop is ok here *)
  exact False.          (* Unused, any Prop is ok here *)
  exact (f = IdPos).
Defined.

Corollary RoofHom_inv x y f : RoofHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma RNeg_RNeg_id (f : RoofHom RNeg RNeg) : f = IdNeg.
Proof. exact (RoofHom_inv _ _ f). Qed.

Lemma RZero_RPos_id (f : RoofHom RZero RPos) : f = ZeroPos.
Proof. exact (RoofHom_inv _ _ f). Qed.

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
  obj    := RoofObj;
  hom    := RoofHom;
  (* Any hom that typechecks is valid. *)
  homset := fun x y => {| equiv := fun (f g : RoofHom x y) => True |};
  id     := fun x => match x return RoofHom x x with
    | RNeg  => IdNeg
    | RZero => IdZero
    | RPos  => IdPos
    end
|}.
Next Obligation.
  destruct x, y, z;
  try constructor;
  try inversion f;
  try inversion g.
Defined.

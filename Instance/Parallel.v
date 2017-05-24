Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This is the category with two objects and two parallel arrows between them
   (and two identity morphisms):

       --- f --->
     x            y
       --- g --->

  This is used to build diagrams that identify equalizers. *)

Inductive ParObj : Type := ParX | ParY.

Inductive ParHom : bool -> ParObj -> ParObj -> Type :=
  | ParIdX : ParHom true ParX ParX
  | ParIdY : ParHom true ParY ParY
  | ParOne : ParHom true ParX ParY
  | ParTwo : ParHom false ParX ParY.

Definition caseParXX (p : ParHom true ParX ParX) :
  forall
    (P : ParHom true ParX ParX -> Type)
    (PParIdX : P ParIdX), P p :=
  match p with
  | ParIdX => fun _ P => P
  end.

Definition caseParYY (p : ParHom true ParY ParY) :
  forall
    (P : ParHom true ParY ParY -> Type)
    (PParIdY : P ParIdY), P p :=
  match p with
  | ParIdY => fun _ P => P
  end.

Definition caseParOne (p : ParHom true ParX ParY) :
  forall
    (P : ParHom true ParX ParY -> Type)
    (PParOne : P ParOne), P p :=
  match p with
  | ParOne => fun _ P => P
  end.

Definition caseParTwo (p : ParHom false ParX ParY) :
  forall
    (P : ParHom false ParX ParY -> Type)
    (PParTwo : P ParTwo), P p :=
  match p with
  | ParTwo => fun _ P => P
  end.

Lemma ParHom_Id_false_absurd : ∀ x, ParHom false x x -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 =>
  match goal with
    [ H : ParHom false ?X ?X |- _ ] =>
    contradiction (ParHom_Id_false_absurd X H)
  end : parallel_laws.

Lemma ParHom_Y_X_absurd : ∀ b, ParHom b ParY ParX -> False.
Proof. inversion 1. Qed.

Local Hint Extern 4 =>
  match goal with
    [ H : ParHom ?B ParY ParX |- _ ] =>
    contradiction (ParHom_Y_X_absurd B H)
  end : parallel_laws.

Local Ltac reduce :=
  repeat match goal with
  | [ H : ParObj |- _ ] => destruct H
  | [ H : bool   |- _ ] => destruct H
  end; auto.

Set Transparent Obligations.

Program Definition Parallel : Category := {|
  ob  := ParObj;
  hom := fun X Y => { b : bool & ParHom b X Y };
  (* Any hom that typechecks is valid. *)
  homset := fun x y =>
    {| equiv := fun (f g : { b : bool & ParHom b x y }) => ``f = ``g |};
  id := fun x => match x with
    | ParX => (true; ParIdX)
    | ParY => (true; ParIdY)
    end;
  compose := fun x y z (f : { b : bool & ParHom b y z })
                       (g : { b : bool & ParHom b x y }) =>
    match x, y, z with
    | ParX, ParX, ParX => (true; ParIdX)
    | ParY, ParY, ParY => (true; ParIdY)
    | ParX, ParY, ParY => _
    | ParX, ParX, ParY => _
    | _,    _,    _    => _
    end
|}.
Next Obligation. equivalence; reduce. Qed.
Next Obligation. exact (f; X0). Defined.
Next Obligation. reduce; intuition. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  proper.
  destruct X, Y, Z; simpl in *; intuition.
Defined.
Next Obligation.
  destruct X, Y; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct X, Y; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct X, Y, Z, W; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct X, Y, Z, W; simpl in *;
  destruct f; intuition.
Qed.

Require Import Category.Theory.Functor.

Program Definition APair {C : Category} {X Y : C} (f g : X ~> Y) :
  Parallel ⟶ C := {|
  fobj := fun x => match x with
    | ParX => X
    | ParY => Y
    end;
  fmap := fun x y h => match x, y with
    | ParX, ParX => id[X]
    | ParY, ParY => id[Y]
    | ParX, ParY =>
      match ``h with
      | true  => f
      | false => g
      end
    | ParY, ParX => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
    end
|}.
Next Obligation.
  proper; reduce; simpl in *; intuition.
Qed.
Next Obligation. destruct X0; simpl; cat. Qed.
Next Obligation. destruct X0, Y0, Z; simpl; auto with parallel_laws; cat. Qed.

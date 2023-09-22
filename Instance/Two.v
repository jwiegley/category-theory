Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Inductive TwoObj : Set := TwoX | TwoY.

Inductive TwoHom : TwoObj → TwoObj → Set :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoIdX).
  - exact (f = TwoXY).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = TwoIdY).
Defined.

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(* The category 2 has two objects, their identity morphisms, and one morphism
   from the first object to the second (here denoted false and true). *)

Program Definition _2 : Category := {|
  obj     := TwoObj;
  hom     := TwoHom;
  homset  := Morphism_equality;
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
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.

Require Import Category.Instance.Sets.

Program Definition _2_as_Set : _2 ⟶ Sets := {|
  fobj := fun x =>
    match x with
    | TwoX => {| carrier := False |}
    | TwoY => {| carrier := True |}
    end;
  fmap := fun x y f =>
    match x, y with
    | TwoY, TwoY => _
    | _, _       => _
    end
|}.
Next Obligation.
  construct.
  - repeat intro.
    contradiction.
  - equivalence.
Defined.
Next Obligation.
  construct.
  - repeat intro.
    exact True.
  - equivalence.
Defined.
Next Obligation.
  construct; auto.
Defined.
Next Obligation.
  construct; auto.
  - destruct x, y; simpl in *; auto with two_laws.
  - proper.
    destruct x, y; simpl in *; auto with two_laws.
Qed.
Next Obligation.
  destruct x; simpl in *; auto with two_laws.
  contradiction.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; auto with two_laws.
  contradiction.
Qed.

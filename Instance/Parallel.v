Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(* This is the category with two objects and two parallel arrows between them
   (and two identity morphisms):

       --- f --->
     x            y
       --- g --->

  This is used to build diagrams that identify equalizers. *)

Inductive ParObj : Type := ParX | ParY.

Inductive ParHom : bool → ParObj → ParObj → Type :=
  | ParIdX : ParHom true ParX ParX
  | ParIdY : ParHom true ParY ParY
  | ParOne : ParHom true ParX ParY
  | ParTwo : ParHom false ParX ParY.

Definition ParHom_inv_t : ∀ b x y, ParHom b x y → Prop.
Proof.
  intros [] [] [] f.
  - exact (f = ParIdX).
  - exact (f = ParOne).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = ParIdY).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = ParTwo).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact False.          (* Unused, any Prop is ok here *)
Defined.

Corollary ParHom_inv b x y f : ParHom_inv_t b x y f.
Proof. destruct f; reflexivity. Qed.

Lemma ParHom_Id_false_absurd : ∀ x, ParHom false x x → False.
Proof. inversion 1. Qed.

#[local] Hint Extern 4 =>
  match goal with
    [ H : ParHom false ?X ?X |- _ ] =>
    contradiction (ParHom_Id_false_absurd X H)
  end : parallel_laws.

Lemma ParHom_Y_X_absurd : ∀ b, ParHom b ParY ParX → False.
Proof. inversion 1. Qed.

#[local] Hint Extern 4 =>
  match goal with
    [ H : ParHom ?B ParY ParX |- _ ] =>
    contradiction (ParHom_Y_X_absurd B H)
  end : parallel_laws.

#[local] Ltac reduce :=
  repeat match goal with
  | [ H : ParObj |- _ ] => destruct H
  | [ H : bool   |- _ ] => destruct H
  end; auto.

Set Transparent Obligations.

Program Definition Parallel : Category := {|
  obj     := ParObj;
  hom     := fun x y => ∃ b : bool, ParHom b x y;
  (* Any hom that typechecks is valid. *)
  homset  := fun x y =>
    {| equiv := fun (f g : ∃ b : bool, ParHom b x y) => ``f = ``g |};
  id      := fun x => match x with
    | ParX => (true; ParIdX)
    | ParY => (true; ParIdY)
    end;
  compose := fun x y z (f : ∃ b : bool, ParHom b y z)
                       (g : ∃ b : bool, ParHom b x y) =>
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
  destruct x, y, z; simpl in *; intuition.
Defined.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition.
Qed.

Require Import Category.Theory.Functor.

Program Definition APair {C : Category} {x y : C} (f g : x ~> y) :
  Parallel ⟶ C := {|
  fobj := fun z => match z with
    | ParX => x
    | ParY => y
    end;
  fmap := fun z w h => match z, w with
    | ParX, ParX => id[x]
    | ParY, ParY => id[y]
    | ParX, ParY =>
      match ``h with
      | true  => f
      | false => g
      end
    | ParY, ParX => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
    end
|}.
Next Obligation. proper; reduce; simpl; intuition. Qed.
Next Obligation. destruct x0; simpl; cat. Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with parallel_laws; cat.
Qed.

(* A contravariant functor on this category is given by a pair of sets G0,G1
   and a pair of function source, target: G_1\to G_0. Identities are sent to
   identities.

   In other words, a presheaf on the category 0⟹1 is a graph. *)

Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Program Definition Presheaf_Graph : Parallel^op ⟶ Sets := {|
  fobj := fun z => match z with
    | ParX => {| carrier := nat |}       (* vertices *)
    | ParY => {| carrier := nat * nat |} (* edges *)
    end;
  fmap := fun z w h => match z, w with
    | ParX, ParX => id
    | ParY, ParY => id
    | ParX, ParY => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
    | ParY, ParX =>
      match ``h with
      | true  => {| morphism := fst |} (* source *)
      | false => {| morphism := snd |} (* target *)
      end
    end
|}.
Next Obligation.
  construct.
  - exact eq.
  - exact eq_equivalence.
Defined.
Next Obligation.
  construct.
  - exact eq.
  - exact eq_equivalence.
Defined.
Next Obligation.
  proper.
  simpl in H; subst.
  destruct x, y; simpl; auto.
  exfalso.
  now apply ParHom_Y_X_absurd in e.
Qed.
Next Obligation.
  destruct x; simpl; auto.
Qed.
Next Obligation.
  destruct x, y, z; simpl; auto.
  - exfalso.
    now apply ParHom_Y_X_absurd in X0.
  - exfalso.
    now apply ParHom_Y_X_absurd in X.
  - exfalso.
    now apply ParHom_Y_X_absurd in X.
  - exfalso.
    now apply ParHom_Y_X_absurd in X0.
Qed.

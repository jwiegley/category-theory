Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The walking parallel pair *)

(* nLab: https://ncatlab.org/nlab/show/parallel+morphisms
   nLab: https://ncatlab.org/nlab/show/walking+parallel+pair
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   This is the "walking parallel pair" (also called the free quiver), the
   category with two objects and two parallel non-identity arrows between them
   (plus the two identity morphisms):

       --- f --->
     x            y
       --- g --->

   There are no arrows y → x, and no non-identity arrows x → x or y → y, so
   composition is trivial: composing the only non-identity arrows f, g : x → y
   with an identity yields that same arrow.

   A functor [Parallel ⟶ C] is exactly a parallel pair of morphisms in C; its
   limit is their equalizer and its colimit their coequalizer.  This is the
   shape category used to build the diagrams that identify (co)equalizers. *)

Inductive ParObj : Set := ParX | ParY.

Inductive ParHom : bool → ParObj → ParObj → Set :=
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

Local Set Warnings "-intuition-auto-with-star".

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
Next Obligation. reduce; intuition; auto with *. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  proper.
  destruct x, y, z; simpl in *; intuition; auto with *.
Defined.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition; auto with *.
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
Next Obligation. proper; reduce; simpl; intuition; auto with *. Qed.
Next Obligation. destruct x0; simpl; cat. Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with parallel_laws; cat.
Qed.

(* A presheaf on this category, i.e. a contravariant functor [Parallel^op ⟶
   Sets], is given by a pair of sets G0, G1 and a pair of functions source,
   target : G1 → G0.  Identities are sent to identities.

   nLab: https://ncatlab.org/nlab/show/quiver
   Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)

   In other words, a presheaf on the parallel-pair category x ⇉ y is a graph
   (quiver): G0 is the set of vertices, G1 the set of edges, and the two arrows
   send an edge to its source and target. *)

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

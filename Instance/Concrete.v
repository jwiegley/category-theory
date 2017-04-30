Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Concrete.

Variable A : Type.
Hypothesis Aeq_dec : forall x y : A, {x = y} + {x <> y}.

Definition Aeq (x y : A) := if Aeq_dec x y then True else False.

Program Instance Aeq_equivalence : Equivalence Aeq.
Next Obligation.
  unfold Aeq; intros.
  destruct (Aeq_dec _ _); auto.
Qed.
Next Obligation.
  unfold Aeq; intros.
  destruct (Aeq_dec _ _).
    subst.
    apply Aeq_equivalence_obligation_1.
  contradiction.
Qed.
Next Obligation.
  unfold Aeq; intros.
  destruct (Aeq_dec _ _).
    subst.
    apply H0.
  contradiction.
Qed.

Fixpoint In' (f : A * A) (l : list (A * A)) : Prop :=
    match l with
      | nil => False
      | (x, y) :: m => (Aeq (fst f) x /\ Aeq (snd f) y) \/ In f m
    end.

Fixpoint Subset' (X Y : A) (l : list (A * A)) : list (A * A) :=
  filter (fun p => if Aeq_dec (fst p) X
                   then if Aeq_dec (snd p) Y
                        then true
                        else false
                   else false) l.
Arguments Subset' X Y l : simpl never.

Lemma Subset'_cons X Y x xs :
  Subset' X Y (x :: xs)
    = if Aeq_dec (fst x) X
      then if Aeq_dec (snd x) Y
           then x :: Subset' X Y xs
           else Subset' X Y xs
      else Subset' X Y xs.
Proof.
  induction xs; unfold Subset'; simpl;
  destruct (Aeq_dec (fst x) X);
  destruct (Aeq_dec (snd x) Y); auto.
Qed.

Lemma In_Subset'_inv X Y x y xs :
  In (x, y) (Subset' X Y xs) -> Aeq x X ∧ Aeq y Y.
Proof.
  induction xs; simpl; intros; [tauto|].
  rewrite Subset'_cons in H.
  destruct (Aeq_dec (fst a) X);
  destruct (Aeq_dec (snd a) Y); auto.
  destruct H; subst; simpl; auto.
  split; reflexivity.
Qed.

(* A concrete category has a fixed set of objects (of some decidable type, to
   differentiate them), and a fixed set of arrows between those objects. A
   frequent use of these is as index categories to build diagrams. *)

Program Instance Concrete (Obs : set A) (Homs : list (A * A)) : Category := {
  ob  := { x : A | In x Obs };
  hom := fun X Y =>
    { f : list (A * A)
    | ∀ h, In' h f <-> In' h ((X, Y) :: Subset' X Y  Homs) }%type;
  homset := fun X Y =>
    {| cequiv := fun f g => ∀ h, In' h f <-> In' h g |}%type;
  id := fun X => exist _ ((X, X) :: nil) _
}.
Next Obligation.
  equivalence.
  - apply H1; assumption.
  - apply H1; assumption.
  - apply H2, H1; assumption.
  - apply H1, H2; assumption.
Qed.
Next Obligation.
  firstorder.
  apply In_Subset'_inv in H0.
  constructor; auto.
Qed.
Next Obligation. firstorder. Defined.
Next Obligation.
  proper; simpl in *.
  unfold Concrete_obligation_3; simpl.
  simplify equiv; simpl.
  destruct x, x0, y, y0; simpl in *.
  firstorder.
Qed.

End Concrete.

Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.

Module ConcreteInstances.

Import ListNotations.

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Concrete_0 := Concrete False _ [] [].

Program Instance Map_0 `(C : Category) : Concrete_0 ⟶ C.

Program Instance Initial_0 : @Initial Cat := {
  Zero := Concrete_0;
  zero := Map_0
}.
Next Obligation.
  simplify equiv; intros.
  constructive;
  try destruct X;
  try contradiction;
  simplify equiv; intros;
  destruct A0;
  contradiction.
Qed.

Program Instance Initial_0_is_0 : @Zero Cat Initial_0 ≅ _0.
Next Obligation.
  simplify equiv; intros.
  constructive; try contradiction;
  simplify equiv; intros;
  contradiction.
Qed.
Next Obligation.
  simplify equiv; intros.
  constructive;
  try destruct X;
  try contradiction;
  simplify equiv; intros;
  destruct A; contradiction.
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Concrete_1 := Concrete unit _ [tt] [].
Next Obligation. destruct x, y; auto. Defined.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.
Next Obligation. simplify equiv; intros; intuition. Qed.

Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  simplify equiv; intros.
  constructive; simpl;
  try destruct (f X), (g X);
  try destruct x, x0;
  unfold Concrete_obligation_3, Concrete_1_obligation_1.
  all:swap 2 3; simpl.
  - eexists [(tt, tt)]; intros; intuition.
  - eexists [(tt, tt)]; intros; intuition.
Admitted.

(*
jww (2017-04-29): TODO
Program Instance Terminal_1_is_1 : @One Cat Terminal_1 ≅ _1.
Next Obligation.
  simplify equiv.
  constructive; intuition;
  simplify equiv; intuition.
Qed.
Next Obligation.
  simplify equiv.
  constructive; intuition;
  simplify equiv; intuition;
  unfold Concrete_obligation_3, Concrete_1_obligation_1.
  destruct X; simpl.
  eexists (exist _ [(tt, x)] _).
  Unshelve. Focus 2. intuition.
  eexists (exist _ [(x, tt)] _).
  Unshelve. Focus 2. intuition.
  simpl; intuition.
Qed.
*)

(* The 2 category has two objects, their identity morphisms, and a morphism
   from the first to the second object. *)

Definition Concrete_2 :=
  Concrete bool Bool.bool_dec [false; true] [(false, true)].

(* The 3 category has three objects, their identity morphisms, and morphisms
   from the first to the second object, the second to the third, and the first
   to the third (required by composition). *)

Inductive three : Set := One_ | Two_ | Three_.

Definition three_dec (x y : three) : {x = y} + {x ≠ y}.
Proof.
  destruct x, y; intuition;
  solve [ left; reflexivity
        | right; intros; discriminate ].
Qed.

Definition Concrete_3 :=
  Concrete three three_dec [One_; Two_; Three_]
           [(One_, Two_); (Two_, Three_); (One_, Three_)].

End ConcreteInstances.

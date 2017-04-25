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
    {| equiv := fun f g => ∀ h, In' h f <-> In' h g |}%type;
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
  proper; simpl in *;
  destruct x, x0, y, y0; simpl in *;
  firstorder.
Qed.
Next Obligation.
  firstorder; simpl in *.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H4 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (a, a0))); firstorder.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H3 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (a, a0))); firstorder.
  - destruct f.
      contradiction.
    pose proof (proj1 (H (a, a0))); firstorder.
Qed.
Next Obligation.
  firstorder; simpl in *.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H4 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (a, a0))); firstorder.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H3 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (a, a0))); firstorder.
  - destruct f.
      contradiction.
    pose proof (proj1 (H (a, a0))); firstorder.
Qed.

End Concrete.

Module ConcreteInstances.

Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Import ListNotations.

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Concrete_0 := Concrete False _ [] [].

Program Instance Map_0 `(C : Category) : Concrete_0 ⟶ C.

Program Instance Initial_0 : @Initial Cat := {
  Zero := Concrete_0;
  zero := Map_0
}.
Next Obligation.
  intros.
  destruct X.
  contradiction.
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Concrete_1 := Concrete unit _ [tt] [].
Next Obligation. destruct x, y; auto. Defined.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  intros.
  destruct (f X), (g X), x, x0.
  eexists (exist _ [(tt, tt)] _).
  Unshelve. 2:split; auto.
  eexists (exist _ [(tt, tt)] _).
  Unshelve. 2:split; auto.
  simpl; intuition.
Qed.

(* The 2 category has two objects, their identity morphisms, and a morphism
   from the first to the second object. *)

Definition Concrete_2 :=
  Concrete bool Bool.bool_dec [true; false] [(true, false)].

(* The 3 category has three objects, their identity morphisms, and morphisms
   from the first to the second object, the second to the third, and the first
   to the third (required by composition). *)

Inductive three : Set := One_ | Two_ | Three_.

Definition three_dec (x y : three) : {x = y} + {x ≠ y}.
Proof.
  destruct x, y; intuition;
  solve [ left; reflexivity
        | right; intros; discriminate ].
Defined.

Definition Concrete_3 :=
  Concrete three three_dec [One_; Two_; Three_]
           [(One_, Two_); (Two_, Three_); (One_, Three_)].

End ConcreteInstances.

Require Import Coq.Init.Datatypes.
Require Setoid.

Close Scope nat_scope.

(* Pose the axiom of extensionality.  This is not needed when we work with
   general categories, where we can make use of setoid equivalences to achieve
   the same thing. *)

Axiom ext_eq : forall {T1 T2 : Type} (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Type) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
Proof.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Hint Resolve ext_eq.
Hint Resolve ext_eqS.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.

(* Simple identity. *)

Definition id {X} (a : X) : X := a.

(* Function composition. *)

Definition compose {A B C}
  (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 69, right associativity).

Theorem comp_id_left : forall {A B} (f : A -> B),
  id ∘ f = f.
Proof. reflexivity. Qed.

Theorem comp_id_right : forall {A B} (f : A -> B),
  f ∘ id = f.
Proof. reflexivity. Qed.

Theorem comp_assoc : forall {A B C D} (f : C -> D) (g : B -> C) (h : A -> B),
  f ∘ g ∘ h = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Theorem uncompose : forall {A B C} (f : B -> C) (g : A -> B) (x : A) (y : C),
  (f ∘ g) x = f (g x).
Proof. reflexivity. Qed.

Ltac uncompose k :=
    rewrite <- uncompose with (f := k);
    repeat (rewrite <- comp_assoc).

(* Some utility functions. *)

Definition flip {X Y Z} (f : X -> Y -> Z) (y : Y) (x : X) : Z := f x y.

Definition call {X Y} (f : X -> Y) (x : X) : Y := f x.

Theorem flip_call : forall {X Y} (f : X -> Y) (x : X),
  f x = flip call x f.
Proof. reflexivity. Qed.
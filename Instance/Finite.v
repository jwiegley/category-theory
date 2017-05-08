Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.ListSet.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Ltac mini_omega :=
  match goal with
  | [ |- ?X = ?X ∨ _ ] => left; reflexivity
  | [ H : (_ < 0)%nat |- _ ] =>
    pose proof (Nat.nlt_0_r _ H); contradiction
  | [ H : (S _ <= 0)%nat |- _ ] =>
    pose proof (Nat.nle_succ_0 _ H); contradiction
  | [ H : (S _ < 1)%nat |- _ ] =>
    unfold lt in H;
    pose proof (le_S_n _ _ H);
    mini_omega
  end.

Local Obligation Tactic :=
  timeout 1 program_simpl;
  intros; simpl;
  try solve [ mini_omega
            | proper
            | apply proof_irrelevance ].

Definition prod_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct (Nat.eq_dec n n1).
    destruct (Nat.eq_dec n0 n2).
      left.
      congruence.
    right.
    congruence.
  right.
  congruence.
Defined.

Local Notation "[set ]" := (empty_set _).
Local Notation "[set a ; .. ; b ]" :=
  (set_add prod_dec a%nat .. (set_add prod_dec b%nat [set]) ..).

(* This record establishes the structure of a concrete category's objects and
   arrows, in terms of fixed sets of natural numbers. It's main practical use
   is for building diagrams. *)

Record Concrete_Structure := {
  obs  : nat;
  arrs : set (nat * nat);

  identity_property :
    ∀ (n : nat | (n < obs)%nat), set_In (`n, `n) arrs;

  composition_property :
    ∀ (n : nat | (n < obs)%nat)
      (m : nat | (m < obs)%nat)
      (o : nat | (o < obs)%nat),
     set_In (`m, `o) arrs ->
     set_In (`n, `m) arrs ->
     set_In (`n, `o) arrs
}.

(* A concrete category has a fixed set of objects (of some decidable type, to
   differentiate them), and a fixed set of arrows between those objects. A
   frequent use of these is as index categories to build diagrams. *)

Program Definition Concrete `(S : Concrete_Structure) : Category := {|
  ob      := { n : nat | n < obs S }%nat;
  hom     := fun x y => set_In (`x, `y) (arrs S);
  homset  := fun _ _ => {| equiv := eq |};
  id      := identity_property S;
  compose := composition_property S
|}.

Module ConcreteInstances.

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Structure_0 : Concrete_Structure := {|
  obs  := 0;
  arrs := empty_set (nat * nat)
|}.

Program Definition Concrete_0 := Concrete Structure_0.

Program Instance Map_0 `(C : Category) : Concrete_0 ⟶ C.

Program Instance Initial_0 : @Initial Cat := {
  Zero := Concrete_0;
  zero := Map_0
}.
Next Obligation.
  constructive;
  try destruct X;
  try contradiction;
  try destruct A0;
  mini_omega.
Qed.

Program Instance Initial_0_is_0 : @Zero Cat Initial_0 ≅ _0.
Next Obligation.
  constructive; try contradiction;
  contradiction.
Qed.
Next Obligation.
  constructive;
  try destruct X;
  try contradiction;
  try destruct A;
  pose proof (Nat.nlt_0_r _ l);
  contradiction.
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Structure_1 : Concrete_Structure := {|
  obs  := 1;
  arrs := [set (0, 0)]
|}.
Next Obligation. destruct n; mini_omega. Defined.
Next Obligation. destruct n, m, o; mini_omega. Defined.

Program Definition Concrete_1 := Concrete Structure_1.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => 0%nat;
  fmap := fun _ _ _ => id
}.

Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  constructive;
  try destruct (f X), (g X);
  try destruct x, x0;
  simpl in *; auto;
  try mini_omega;
  apply proof_irrelevance.
Qed.

Program Instance Terminal_1_is_1 : @One Cat Terminal_1 ≅ _1.
Next Obligation.
  constructive; intuition;
  intuition.
Qed.
Next Obligation.
  constructive; intuition;
  intuition;
  try apply proof_irrelevance;
  destruct X; simpl;
  destruct x; mini_omega.
Qed.

(* The 2 category has two objects, their identity morphisms, and a morphism
   from the first to the second object. *)

Program Definition Structure_2 : Concrete_Structure := {|
  obs  := 2;
  arrs := [set (0, 0); (1, 1); (0, 1)]
|}.
Next Obligation.
  destruct n; auto.
  destruct n; auto.
  apply le_S_n in H.
  apply le_S_n in H.
  mini_omega.
Defined.
Next Obligation.
  intuition; try congruence.
  - left; congruence.
  - left; congruence.
  - right; left; congruence.
  - right; right; left; congruence.
Defined.

Definition Concrete_2 := Concrete Structure_2.

(* The 3 category has three objects, their identity morphisms, and morphisms
   from the first to the second object, the second to the third, and the first
   to the third (required by composition). *)

Local Obligation Tactic := intros.

Program Definition Structure_3 : Concrete_Structure := {|
  obs  := 3;
  arrs := [set (0, 0); (1, 1); (2, 2)
          ;    (0, 1); (1, 2); (0, 2) ]
|}.
Next Obligation.
  destruct n.
  destruct x; simpl; try congruence.
    intuition.
  destruct x; simpl; intuition.
  destruct x; simpl; intuition.
  apply le_S_n in l.
  apply le_S_n in l.
  apply le_S_n in l.
  mini_omega.
Defined.
Next Obligation.
  destruct n, m, o;
  destruct x, x0, x1; simpl in *; try congruence;
  repeat
    match goal with
    | [ H : _ ∨ _ |- _ ] => destruct H
    end; try congruence; intuition.
  - left; congruence.
  - left; congruence.
  - right; right; left; congruence.
  - right; left; congruence.
  - right; right; right; left; congruence.
  - right; left; congruence.
  - right; right; right; right; left; congruence.
Defined.

Definition Concrete_3 := Concrete Structure_3.

End ConcreteInstances.

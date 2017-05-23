Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Import ListNotations.

Inductive set_In {n} (a : Fin.t n * Fin.t n) : list (Fin.t n * Fin.t n) -> Type :=
  | In_head xs : set_In a (a :: xs)
  | In_tail x xs :
      set_In a xs
        -> (Fin.eqb (fst a) (fst x) && Fin.eqb (snd a) (snd x))%bool = false
        -> set_In a (x :: xs).

Inductive MethodType {n} : Fin.t n -> Fin.t n -> Type :=
  Method x y : MethodType x y.

Ltac mini_omega :=
  match goal with
  | [ x : Fin.t 0 |- _ ] => refine (case0 (fun x => _) x)
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

Definition prod_dec {n} (x y : Fin.t n * Fin.t n) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct (Fin.eq_dec t t1), (Fin.eq_dec t0 t2).
  - left; congruence.
  - right; congruence.
  - right; congruence.
  - right; congruence.
Defined.

Notation "[set ]" := (empty_set _).
Notation "[set a ; .. ; b ]" :=
  (set_add prod_dec a%nat .. (set_add prod_dec b%nat [set]) ..).

(* This record establishes the structure of a concrete category's objects and
   arrows, in terms of fixed sets of natural numbers. It's main practical use
   is for building diagrams. *)

Record Concrete_Structure := {
  obs  : nat;
  arrs : set (Fin.t obs * Fin.t obs);

  identity_property : ∀ x, set_In (x, x) arrs;

  composition_property : ∀ x y z,
     set_In (y, z) arrs ->
     set_In (x, y) arrs ->
     set_In (x, z) arrs
}.

(* A concrete category has a fixed set of objects (of some decidable type, to
   differentiate them), and a fixed set of arrows between those objects. A
   frequent use of these is as index categories to build diagrams. *)

Program Definition Concrete (S : Concrete_Structure) :
  Category := {|
  ob      := Fin.t (obs S);
  hom     := fun x y => { m : MethodType x y & set_In (x, y) (arrs S) };
  homset  := fun x y => {| equiv := fun _ _ => True |};
  id      := fun x => (Method x x; identity_property S x);
  compose := fun x y z f g =>
    (Method x z; composition_property S x y z (projT2 f) (projT2 g))
|}.

Module ConcreteInstances.

Local Obligation Tactic := cat_simpl; try mini_omega.

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Structure_0 : Concrete_Structure := {|
  obs  := 0;
  arrs := [set]
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

Program Instance Initial_0_is_0 : @Zero Cat Initial_0 ≅ 0.
Next Obligation. exact Id. Qed.
Next Obligation. exact Id. Qed.
Next Obligation.
  constructive;
  try destruct X;
  try contradiction;
  try destruct A;
  try mini_omega; auto.
Qed.
Next Obligation.
  constructive;
  try destruct X;
  try contradiction;
  try destruct A;
  try mini_omega; auto.
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Structure_1 : Concrete_Structure := {|
  obs  := 1;
  arrs := [set (F1, F1)]
|}.
Next Obligation.
  refine (@caseS' 0 x (fun x => set_In (x, x) [(F1, F1)]) _ _).
    constructor.
  intros.
  mini_omega.
Defined.
Next Obligation.
  refine (@caseS' 0 x (fun x => set_In (x, z) [(F1, F1)]) _ _).
    refine (@caseS' 0 z (fun z => set_In (F1, z) [(F1, F1)]) _ _).
      constructor.
    intros; mini_omega.
  intros; mini_omega.
Defined.

Program Definition Concrete_1 := Concrete Structure_1.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => F1;
  fmap := fun _ _ _ => id
}.

(*
Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  constructive; auto.
    refine (@caseS' 0 (f X) (fun x => {_ : MethodType x (g X) & set_In (f X, g X) [(F1, F1)]}) _ _).
      refine (@caseS' 0 (g X) (fun x => {_ : MethodType F1 x & set_In (f X, g X) [(F1, F1)]}) _ _).
        exists (Method F1 F1).
        constructor.
    assert (f X = F1).
      clear.
      destruct f; simpl in *.
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
*)

End ConcreteInstances.

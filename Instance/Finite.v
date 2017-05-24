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
Unset Transparent Obligations.

Import ListNotations.

(* This record establishes the structure of a concrete category's objects and
   arrows, in terms of fixed sets of natural numbers. It's main practical use
   is for building diagrams. *)

Record Concrete_Structure := {
  obs  : nat;
  arrs : Fin.t obs -> Fin.t obs -> nat
}.

(* A concrete category has a fixed set of objects (of some decidable type, to
   differentiate them), and a fixed set of arrows between those objects. A
   frequent use of these is as index categories to build diagrams. *)

Import EqNotations.

Inductive Morphism (S : Concrete_Structure) :
  Fin.t (obs S) -> Fin.t (obs S) -> Type :=
  | Named x y         : Fin.t (arrs S x y) -> Morphism S x y
  | Identity x        : Morphism S x x
  | Composition x y z : Morphism S y z -> Morphism S x y -> Morphism S x z.

Fixpoint denote (S : Concrete_Structure) `(c : Morphism S a b) :
  ∀ {C : Category}
    (typ : Fin.t (obs S) -> C)
    (arr : ∀ x y, Fin.t (arrs S x y) -> typ x ~{C}~> typ y),
    typ a ~{C}~> typ b := fun _ typ arr =>
  match c with
  | Identity _ _            => id
  | Composition _ _ _ _ f g => denote S f typ arr ∘ denote S g typ arr
  | Named _ x y f           => arr x y f
  end.

Corollary denote_comp S typ arr x y z (f : Morphism S y z) (g : Morphism S x y) :
  denote S f typ arr ∘ denote S g typ arr ≈
    denote S (Composition S x y z f g) typ arr.
Proof. reflexivity. Qed.

Program Definition Concrete (S : Concrete_Structure) :
  Category := {|
  ob      := Fin.t (obs S);
  hom     := Morphism S;
  homset  := fun _ _ => {| equiv := fun f g =>
    ∀ {C : Category}
      (typ : Fin.t (obs S) -> C)
      (arr : ∀ x y, Fin.t (arrs S x y) -> typ x ~{C}~> typ y),
      denote S f typ arr ≈ denote S g typ arr |};
  id      := Identity S;
  compose := Composition S
|}.
Next Obligation.
  equivalence.
  transitivity (denote S y typ arr); auto.
Qed.

Module ConcreteInstances.

(* Local Obligation Tactic := cat_simpl; try mini_omega. *)

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Structure_0 : Concrete_Structure := {|
  obs  := 0;
  arrs := fun _ _ => 0%nat
|}.

Program Definition Concrete_0 := Concrete Structure_0.

Program Instance Map_0 `(C : Category) : Concrete_0 ⟶ C.
Next Obligation. inversion H. Qed.
Next Obligation. inversion X. Qed.
Next Obligation. inversion X. Qed.
Next Obligation. inversion X. Qed.
Next Obligation. inversion X. Qed.

Program Instance Initial_0 : @Initial Cat := {
  Zero := Concrete_0;
  zero := Map_0
}.
Next Obligation.
  constructive.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact A0.
  refine (case0 (fun _ => _) _). exact A0.
Qed.

Program Instance Initial_0_is_0 : @Zero Cat Initial_0 ≅ 0.
Next Obligation. exact Id. Qed.
Next Obligation. exact Id. Qed.
Next Obligation.
  constructive;
  refine (case0 (fun _ => _) _); try exact X; try exact A.
Qed.
Next Obligation.
  constructive;
  refine (case0 (fun _ => _) _); try exact X; try exact A.
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Structure_1 : Concrete_Structure := {|
  obs  := 1;
  arrs := fun _ _ => 0%nat
|}.

Program Definition Concrete_1 := Concrete Structure_1.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => F1;
  fmap := fun _ _ _ => id
}.

Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  constructive; auto; simpl.
  - pattern (f X); apply caseS'.
      pattern (g X); apply caseS'.
        apply Identity.
      apply case0.
    apply case0.
  - assert (f X = f Y).
      pattern (f X); apply caseS'.
        pattern (f Y); apply caseS'.
          reflexivity.
        apply case0.
      apply case0.
    pose (fmap[f] f0).
    rewrite <- H in h.
    destruct (fmap[g] f0); simpl.
    unfold Structure_1, denote; simpl.
  - exact F1.
  - refine (caseS' (fmap[g] f0) (fun x => F1 = x) (reflexivity _) _).
    refine (case0 (fun _ => _)).
  - unfold Structure_1_obligation_1.
    refine (caseS' (fmap[g] id) (fun x => F1 = x) (reflexivity _) _).
    refine (case0 (fun _ => _)).
  - refine (caseS' (fmap[f] id) (fun x => F1 = x) (reflexivity _) _).
    refine (case0 (fun _ => _)).
Qed.

Program Instance Terminal_1_is_1 : @One Cat Terminal_1 ≅ _1.
Next Obligation.
  functor; simpl; intros; reflexivity.
Defined.
Next Obligation.
  functor; simpl; intros; reflexivity.
Defined.
Next Obligation.
  constructive; intuition.
Qed.
Next Obligation.
  constructive; intuition;
  unfold Structure_1_obligation_1; simpl.
  - refine (caseS' X (fun x => x = F1) (reflexivity _) _).
    refine (case0 (fun _ => _)).
  - refine (caseS' X (fun x => x = f) _ _).
      refine (caseS' f (fun x => F1 = x) _ _).
        reflexivity.
      refine (case0 (fun _ => _)).
    refine (case0 (fun _ => _)).
  - refine (caseS' A (fun x => x = F1) _ _).
      reflexivity.
    refine (case0 (fun _ => _)).
  - refine (caseS' A (fun x => x = F1) _ _).
      reflexivity.
    refine (case0 (fun _ => _)).
Qed.

(* The 2 category has two objects, their identity morphisms, and a morphism
   from the first to the second object. *)

Program Definition Structure_2 : Concrete_Structure := {|
  obs  := 2;
  card := _
|}.
Next Obligation.
  destruct H.
    destruct H0.
      exact 0%nat.
    exact 1%nat.
  exact 0%nat.
Defined.
Next Obligation.
  unfold Structure_2_obligation_1 in *; simpl in *.
  destruct x.
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

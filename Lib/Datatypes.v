Set Warnings "-notation-overridden".

Require Export Category.Lib.Setoid.
Require Export Category.Lib.Tactics.

Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The only inductive types from the standard library used in this development
   are products and sums, so we must show how they interact with constructive
   setoids. *)

Program Instance prod_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A * B) := {
  equiv := fun x y => equiv (fst x) (fst y) * equiv (snd x) (snd y)
}.

Program Instance pair_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv ==> equiv) (@pair A B).

Program Instance fst_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@fst A B).

Program Instance snd_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@snd A B).

Corollary let_fst {x y} (A : x * y) `(f : x -> z) :
  (let (x, _) := A in f x) = f (fst A).
Proof. destruct A; auto. Qed.

Corollary let_snd {x y} (A : x * y) `(f : y -> z) :
  (let (_, y) := A in f y) = f (snd A).
Proof. destruct A; auto. Qed.

Corollary let_projT1 {A P} (S : @sigT A P) `(f : A -> z) :
  (let (x, _) := S in f x) = f (projT1 S).
Proof. destruct S; auto. Qed.

Corollary let_projT2 {A P} (S : @sigT A P) `(f : forall x, P x -> z) :
  (let (x, y) := S in f x y) = f (projT1 S) (projT2 S).
Proof. destruct S; auto. Qed.

Program Instance sum_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A + B) := {
  equiv := fun x y =>
    match x with
    | inl x =>
      match y with
      | inl y => equiv x y
      | inr y => False
      end
    | inr x =>
      match y with
      | inl y => False
      | inr y => equiv x y
      end
    end
}.
Next Obligation.
  equivalence; destruct x, y; try destruct z; intuition.
Qed.

Program Instance inl_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inl A B).

Program Instance inr_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inr A B).

(* Products can be compared for boolean equality if their members can be. *)
Definition prod_eqb {A B} (A_eqb : A -> A -> bool) (B_eqb : B -> B -> bool)
           (x y : A * B) : bool :=
  A_eqb (fst x) (fst y) && B_eqb (snd x) (snd y).

(* Products can be compared for decidable equality if their members can be. *)
Program Definition prod_eq_dec {A B}
        (A_eq_dec : forall x y : A, {x = y} + {x ≠ y})
        (B_eq_dec : forall x y : B, {x = y} + {x ≠ y})
        (x y : A * B) : {x = y} + {x ≠ y} :=
  match A_eq_dec (fst x) (fst y) with
  | in_left =>
    match B_eq_dec (snd x) (snd y) with
    | in_left  => in_left
    | in_right => in_right
    end
  | in_right => in_right
  end.
Next Obligation. congruence. Qed.

Lemma peano_rect' : ∀ P : N → Type, P 0%N → (∀ n : N, P (N.succ n)) → ∀ n : N, P n.
Proof.
  intros.
  induction n using N.peano_rect.
    apply X.
  apply X0.
Defined.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Pos_eq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Pos_eq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Pos_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma N_eq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (N.eq_dec x y); auto.
Qed.

Lemma N_eq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (N_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma prod_eq_dec' :
  ∀ (A B : Type) (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
    (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y)
    (x y : A ∧ B), x = y \/ x ≠ y.
Proof.
  intros.
  destruct x, y; simpl.
  destruct (A_eq_dec a a0); subst.
    destruct (B_eq_dec b b0); subst.
      left; reflexivity.
    right; congruence.
  right; congruence.
Qed.

Lemma prod_eq_dec_refl (A B : Type) n
      (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y)
      (B_eq_dec : ∀ x y : B, x = y ∨ x ≠ y) :
  prod_eq_dec A_eq_dec B_eq_dec n n = left (@eq_refl (A ∧ B) n).
Proof.
  destruct (prod_eq_dec _ _ n n).
    refine (K_dec_on_type (A ∧ B) n (prod_eq_dec' _ _ A_eq_dec B_eq_dec n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl (A ∧ B) n)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma length_remove A (A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y) x xs :
  (length (remove A_eq_dec x xs) <= length xs)%nat.
Proof.
  induction xs; auto.
  simpl.
  destruct (A_eq_dec x a); subst.
    apply PeanoNat.Nat.le_le_succ_r, IHxs.
  simpl.
  apply le_n_S, IHxs.
Qed.

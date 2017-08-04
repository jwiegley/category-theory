Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.

Generalizable All Variables.

Section Expr.

Definition obj_idx := positive.
Definition arr_idx := positive.

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : Set :=
  | Identity (o : obj_idx) : Term
  | Morph    (x y : obj_idx) (a : arr_idx) : Term
  (* With induction-recursion, the [m] argument would be unnecessary. *)
  | Compose  (m : obj_idx) (f : Term) (g : Term) : Term.

Function term_beq (f g : Term) : bool :=
  match f, g with
  | Identity x, Identity y => Eq_eqb x y
  | Morph x y a, Morph x' y' a' =>
    Eq_eqb x x' &&& Eq_eqb y y' &&& Eq_eqb a a'
  | Compose m f g, Compose m' f' g' =>
    Eq_eqb m m' &&& term_beq f f' &&& term_beq g g'
  | _, _ => false
  end.

Lemma term_beq_eq (f g : Term) :
  term_beq f g = true -> f = g.
Proof.
  generalize dependent g.
  induction f, g; simpl; intros;
  equalities; try discriminate.
  f_equal; intuition.
Qed.

Function term_dom (e : Term) : obj_idx :=
  match e with
  | Identity x    => x
  | Morph x _ _   => x
  | Compose _ _ g => term_dom g
  end.

Function term_cod (e : Term) : obj_idx :=
  match e with
  | Identity y    => y
  | Morph _ y _   => y
  | Compose _ f _ => term_cod f
  end.

Fixpoint term_size (t : Term) : nat :=
  match t with
  | Identity _    => 1%nat
  | Morph _ _ _   => 1%nat
  | Compose _ f g => 1%nat + term_size f + term_size g
  end.

(*
Inductive NormalForm : obj_idx -> obj_idx -> Term -> Term -> Type :=
  | NFIdentity : ∀ x, NormalForm x x (Identity x) (Identity x)
  | NFMorph : ∀ x y f, NormalForm x y (Morph x y f) (Morph x y f)
  | NFCompose_Id_Left : ∀ x y f f',
      NormalForm x y f f' ->
      NormalForm x y (Compose y (Identity y) f) f'
  | NFCompose_Id_Right : ∀ x y f f',
      NormalForm x y f f' ->
      NormalForm x y (Compose x f (Identity x)) f'
  | NFCompose_Morph : ∀ x y z f g g',
      NormalForm y z g g' ->
      NormalForm x z (Compose z (Morph y z f) g)
                     (Compose z (Morph y z f) g')
  | NFCompose_Assoc : ∀ x y z w f f' g g' h h',
      NormalForm z w f f' ->
      NormalForm y z g g' ->
      NormalForm x y h h' ->
      NormalForm x w (Compose y (Compose z f g) h)
                     (Compose z f' (Compose y g' h')).

Definition term_append (t : Term) : ∃ t' x y, NormalForm x y t t'.
Proof.
  induction t.
  - do 3 eexists; econstructor.
  - do 3 eexists; econstructor.
  - equalities.
    destruct t1; simpl.
    + inversion n0; subst.
      exists t2, o, o.
      apply NFCompose_Id_Left.
      admit.
    + exists (Compose m (Morph x1 y a) t2).
      admit.
    + exists (Compose m0 t1_1 (Compose m t1_2 t2)).
      constructor.

Program Fixpoint term_append (t u : Term) :
  ∃ t' m, NormalForm (Compose m t u) t'  :=
  match t with
  | Compose m g h =>
    match term_append h u with
    | (t'; (u'; h')) => _ term_append g t'
    end
  | Identity o    => _ u
  | Morph x y a   =>
    match u with
    | Identity _ => _ t
    | _ => _ (Compose x t u)
    end
  end.
Next Obligation.
  eexists; eexists.
  econstructor; eauto.
*)

Function term_append (t u : Term) : Term :=
  match t with
  | Compose m g h => term_append g (term_append h u)
  | Identity _    => u
  | Morph x y a   =>
    match u with
    | Identity _ => t
    | _ => Compose x t u
    end
  end.

Functional Scheme term_append_scheme :=
  Induction for term_append Sort Type.

Definition term_normal (t : Term) : Term :=
  term_append t (Identity (term_dom t)).

Definition term_equiv (f g : Term) := term_normal f = term_normal g.

Example normalize_term_ex1 :
  term_normal
    (Compose
       1 (Compose
            1 (Compose 1 (Morph 1 1 1) (Identity 1))
              (Compose 1 (Morph 1 1 3) (Morph 1 1 4)))
         (Compose
            1 (Compose 1 (Identity 1) (Identity 1))
              (Compose 1 (Morph 1 1 7) (Morph 1 1 8))))%positive
    = (Compose 1 (Morph 1 1 1)
         (Compose 1 (Morph 1 1 3)
            (Compose 1 (Morph 1 1 4)
               (Compose 1 (Morph 1 1 7) (Morph 1 1 8)))))%positive.
Proof. reflexivity. Qed.

Inductive Expr : Set :=
  | Top
  | Bottom
  | Equiv (x y : obj_idx) (f g : Term)
  (* | Not   (p : Expr) *)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Fixpoint expr_size (t : Expr) : nat :=
  match t with
  | Top           => 1%nat
  | Bottom        => 1%nat
  | Equiv _ _ f g => 1%nat + term_size f + term_size g
  (* | Not p         => 1%nat + expr_size p *)
  | And p q       => 1%nat + expr_size p + expr_size q
  | Or p q        => 1%nat + expr_size p + expr_size q
  | Impl p q      => 1%nat + expr_size p + expr_size q
  end.

Remark all_exprs_have_size e : (0 < expr_size e)%nat.
Proof. induction e; simpl; omega. Qed.

End Expr.

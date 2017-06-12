Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.ilist.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Vectors.Vector.
Require Import Coq.NArith.NArith.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Solver.

Context {C : Category}.

Set Decidable Equality Schemes.

Open Scope N_scope.

Inductive Term : N -> N -> Type :=
  | Identity : ∀ x, Term x x
  | Morph    : ∀ x y, N -> Term x y
  | Compose  : ∀ x y z, Term y z -> Term x y -> Term x z.

(*
Inductive Subterm : Term -> Term -> Prop :=.
  (* | Compose1 : forall x y z t1 t2, Subterm _ t1 (Compose x y z t1 t2) *)
  (* | Compose2 : forall x y z t1 t2, Subterm _ t2 (Compose x y z t1 t2). *)

Lemma Subterm_wf : well_founded Subterm.
Proof.
  constructor; intros.
  inversion H; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H0; subst; clear H0;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.
*)

(*
Program Fixpoint typeDenote (e : Term x y) (tenv : nat -> C * C) : ∃ x y : C, Type :=
  match e with
  | Morph n => let '(d, c) := tenv n in (d; (c; @hom C d c))
  | Identity => _
  | Compose f g =>
    let '(x; (y; g')) := typeDenote g tenv in
    let '(y; (z; f')) := typeDenote f tenv in
    (x; (z; g' ∘ f'))
  end.
*)

Fixpoint eval `(e : Term x y)
         (objs : N -> C) (arrs : N -> ∀ a b : N, objs a ~> objs b) :
  objs x ~> objs y :=
  match e with
  | Morph x y n       => arrs n x y
  | Identity x        => @id C (objs x)
  | Compose x y z f g => eval f objs arrs ∘ eval g objs arrs
  end.

(*
Program Instance typeDenote_setoid (t : type) : Setoid (typeDenote t) :=
  match t with
  | ArrT x y => @homset C x y
  end.
*)

Definition Equiv {x y} (f g : Term x y) : Type :=
  ∀ objs arrs, eval f objs arrs ≈ eval g objs arrs.
Arguments Equiv {_} _ _ /.

(*
Definition R {t} := symprod (Term t) (Term t) Subterm Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

(* Program Fixpoint decision {v} (p : Term v * Term v) {wf (R (t:=_)) p} : *)
(*   { b : bool & b = true -> Equiv (fst p) (snd p) } := *)

Local Obligation Tactic := intros.

Program Fixpoint decision (n : nat) {v} (p : Term v * Term v) {struct n} :
  { b : bool & b = true -> Equiv (fst p) (snd p) } :=
  match p, n with
  | (s, t), 0%nat => existT _ false _
  | (s, t), S n =>
    match s in Term v' return v = v' -> _ with
    | Identity _ => fun _ => existT _ false _
    | Morph i f => fun _ =>
      match t with
      | Identity _  => existT _ false _
      | Morph j g   => existT _ (Nat.eqb i j) _
      | Compose h k => existT _ false _
      end
    | Compose f g => fun _ =>
      match t with
      | Identity _  => existT _ false _
      | Morph j g   => existT _ false _
      | Compose h k => existT _ (`1 (decision n (f, h)) &&&
                                 `1 (decision n (g, k))) _
      end
    end eq_refl
  end.
Next Obligation. simpl; intros; discriminate. Defined.
Next Obligation. simpl; intros; discriminate. Defined.
Next Obligation. simpl; intros; discriminate. Defined.
Next Obligation. simpl; intros; discriminate. Qed.
Next Obligation. simpl; intros; discriminate. Qed.
Next Obligation.
  simpl; intros; discriminate.
Next Obligation. intros; discriminate. Qed.
Next Obligation.
  intros; discriminate.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  destruct x; simpl in *.
  unfold eq_rect in *; simpl in *.
Admitted.
(* Next Obligation. *)
(*   apply wf_symprod; *)
(*   apply Subterm_wf. *)
(* Defined. *)

Example speed_test :
  ` (leq (Meet (Var 0) (Var 1), Join (Var 0) (Var 1))) = true.
Proof. reflexivity. Qed.

Notation "s ≲ t" := (leq (s, t)) (at level 30).

Definition leq_correct {t u : Term} (Heq : ` (t ≲ u) = true) :
  forall env, 〚t〛env ≤ 〚u〛env := proj2_sig (leq (t, u)) Heq.

End Lattice.

Notation "〚 t 〛 env" := (@eval _ _ t env) (at level 9).
Notation "s ≲ t" := (@leq _ _ _ _ (s, t)) (at level 30).

Import ListNotations.

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac allVars xs e :=
  match e with
  | ?e1 ⊓ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | ?e1 ⊔ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | _ => addToList e xs
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => O
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(S n)
  end.

Ltac reifyTerm env t :=
  match t with
  | ?X1 ⊓ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Meet r1 r2)
  | ?X1 ⊔ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Join r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Var n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : nat => x)
    | (?x, ?xs'') =>
      let f := loop (S n) xs'' in
      constr:(fun m : nat => if m =? n then x else f m)
    end in
  loop 0 xs.

Ltac reify :=
  match goal with
  | [ |- ?S ≤ ?T ] =>
    let xs  := allVars tt S in
    let xs' := allVars xs T in
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in
    let env := functionalize xs' in
    (* pose xs'; *)
    (* pose env; *)
    (* pose r1; *)
    (* pose r2; *)
    change (〚r1〛env ≤ 〚r2〛env)
  end.

Ltac lattice := reify; apply leq_correct; vm_compute; auto.

Example sample_1 `{LOSet A} : forall a b : A,
  a ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma running_example `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof.
  intros a b.
  rewrite meet_consistent.
  rewrite meet_associative.
  rewrite join_commutative.
  rewrite meet_absorptive.
  reflexivity.
Qed.

Lemma running_example' `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma median_inequality `{LOSet A} : forall x y z : A,
  (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x).
Proof. intros; lattice. Qed.
*)

End Solver.

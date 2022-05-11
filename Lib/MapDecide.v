Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMaps.

Require Import Category.Lib.
Require Import Category.Lib.Nomega.
Require Import Category.Lib.FMapExt.

Generalizable All Variables.
Set Transparent Obligations.

(* For the time being, this module is fixed to maps from [N * N -> N]. *)

Module PO := PairOrderedType N_as_OT N_as_OT.
Module M  := FMapList.Make(PO).
Module Import FMapExt := FMapExt PO M.

(**************************************************************************
 * Data type for representing partial results, taken from Chlipala's CPDT
 *)

Inductive partial (P : Prop) : Set :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Declare Scope partial_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

(**************************************************************************
 * A term language for theorems involving FMaps
 *)

Record environment := {
  vars : positive -> N
}.

Inductive term :=
  | Var   : positive -> term
  | Value : N -> term.

Definition term_beq (x y : term) : bool :=
  match x, y with
  | Var x,   Var y   => (x =? y)%positive
  | Value x, Value y => (x =? y)%N
  | _, _ => false
  end.

Lemma term_beq_sound x y : term_beq x y = true -> x = y.
Proof.
  induction x, y; simpl; intros; intuition.
  - apply Pos.eqb_eq in H; subst; reflexivity.
  - apply N.eqb_eq in H; subst; reflexivity.
Defined.

Program Definition term_eq_dec (x y : term) : {x = y} + {x ≠ y} :=
  match x, y with
  | Var x,   Var y   => if Pos.eq_dec x y then left _ else right _
  | Value x, Value y => if N.eq_dec   x y then left _ else right _
  | _, _ => right _
  end.
Next Obligation.
  intuition; subst.
  destruct y.
    specialize (H0 p p); intuition.
  specialize (H n n); intuition.
Defined.
Next Obligation.
  split; unfold not; intros ? ? H1;
  destruct H1; discriminate.
Defined.
Next Obligation.
  split; unfold not; intros ? ? H1;
  destruct H1; discriminate.
Defined.

Definition subst_all {A} (f : A -> term -> term -> A) :
  A -> list (term * term) -> A :=
  fold_right (fun '(v, v') rest => f rest v v').

Definition subst_term (x v v' : term) : term :=
  if term_beq x v then v' else x.

Definition term_denote env (x : term) : N :=
  match x with
  | Var n => vars env n
  | Value n => n
  end.

Inductive map_expr : Set :=
  | Empty : map_expr
  | Add   : term -> term -> term -> map_expr -> map_expr.

Fixpoint subst_map_expr (t : map_expr) (v v' : term) : map_expr :=
  match t with
  | Empty => Empty
  | Add x y f m =>
    Add (subst_term x v v')
        (subst_term y v v')
        (subst_term f v v')
        (subst_map_expr m v v')
  end.

Fixpoint map_expr_denote env (m : map_expr) : M.t N :=
  match m with
  | Empty => M.empty N
  | Add x y f m' => M.add (term_denote env x, term_denote env y)
                          (term_denote env  f) (map_expr_denote env m')
  end.

Inductive formula :=
  | Top    : formula
  | Bottom : formula
  | Maps   : term -> term -> term -> map_expr -> formula
  | Impl   : formula -> formula -> formula.

Fixpoint subst_formula (t : formula) (v v' : term) : formula :=
  match t with
  | Top => Top
  | Bottom => Bottom
  | Maps x y f m =>
    Maps (subst_term x v v')
         (subst_term y v v')
         (subst_term f v v')
         (subst_map_expr m v v')
  | Impl p q => Impl (subst_formula p v v') (subst_formula q v v')
  end.

Fixpoint formula_denote env (t : formula) : Prop :=
  match t with
  | Top => True
  | Bottom => False
  | Maps x y f m =>
    M.MapsTo (term_denote env x, term_denote env y)
             (term_denote env f) (map_expr_denote env m)
  | Impl p q => formula_denote env p -> formula_denote env q
  end.

(**************************************************************************
 * Compute structural size of formulas, for well-founded recursion
 *)

Fixpoint map_expr_size (t : map_expr) : nat :=
  match t with
  | Empty       => 1%nat
  | Add _ _ _ m => 1%nat + map_expr_size m
  end.

Lemma map_expr_size_subst_map_expr v v' m :
  map_expr_size (subst_map_expr m v v') = map_expr_size m.
Proof. induction m; simpl; auto. Qed.

Lemma map_expr_size_subst_all_map_expr defs m :
  map_expr_size (subst_all subst_map_expr m defs) = map_expr_size m.
Proof.
  induction defs; simpl; auto.
  destruct a.
  now rewrite map_expr_size_subst_map_expr.
Qed.

Fixpoint formula_size (t : formula) : nat :=
  match t with
  | Top          => 1%nat
  | Bottom       => 1%nat
  | Maps _ _ _ m => 1%nat + map_expr_size m
  | Impl p q     => 1%nat + formula_size p + formula_size q
  end.

Lemma formula_size_subst_formula v v' m :
  formula_size (subst_formula m v v') = formula_size m.
Proof.
  induction m; simpl; auto.
  now rewrite map_expr_size_subst_map_expr.
Qed.

Lemma formula_size_subst_all_formula defs m :
  formula_size (subst_all subst_formula m defs) = formula_size m.
Proof.
  induction defs; simpl; auto.
  destruct a.
  now rewrite formula_size_subst_formula.
Qed.

(**************************************************************************
 * Substitution of variables throughout a formula
 *)

Definition substitution (x y : term) : option (term * term) :=
  match x, y with
  | Var n, Var m => if Pos.eq_dec n m then None else Some (x, y)
  | Var _, _     => Some (x, y)
  | _ ,    Var _ => Some (y, x)
  | _,     _     => None
  end.

Fixpoint substitutions (xs : list (term * term)) : list (term * term) :=
  match xs with
  | nil => nil
  | cons (x, y) xs =>
    match substitution x y with
    | Some p => cons p (substitutions xs)
    | None => substitutions xs
    end
  end.

Lemma term_denote_subst_term env v v' t :
  term_denote env v = term_denote env v'
    -> term_denote env (subst_term t v v') = term_denote env t.
Proof.
  unfold subst_term; intros.
  destruct term_beq eqn:?; auto.
  apply term_beq_sound in Heqb.
  congruence.
Qed.

Lemma term_denote_substitution {env t0 t1 t2 t3} :
  substitution t0 t1 = Some (t2, t3)
    -> term_denote env t0 = term_denote env t1
    -> term_denote env t2 = term_denote env t3.
Proof.
  intros.
  destruct t0, t1; simpl in H;
  try (destruct (Pos.eq_dec _ _); [discriminate|]);
  now inversion_clear H.
Qed.

Lemma term_substitution_eq env t xs :
  Forall (fun '(v, v') => term_denote env v = term_denote env v') xs
    → term_denote env (subst_all subst_term t (substitutions xs)) =
      term_denote env t.
Proof.
  induction xs as [|[] ?]; simpl; intros; auto.
  inversion H.
  destruct (substitution t0 t1) eqn:?; intuition.
  destruct p; simpl.
  rewrite term_denote_subst_term; auto.
  now apply (term_denote_substitution Heqo).
Qed.

Lemma map_expr_denote_subst_map_expr env v v' m :
  term_denote env v = term_denote env v'
    -> map_expr_denote env (subst_map_expr m v v') = map_expr_denote env m.
Proof.
  induction m; simpl; auto; intros.
  rewrite IHm; auto.
  now rewrite !term_denote_subst_term.
Qed.

Lemma map_expr_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> map_expr_denote env (subst_all subst_map_expr t (substitutions xs)) =
       map_expr_denote env t.
Proof.
  induction xs as [|[] ?]; simpl; intros; auto.
  inversion H.
  destruct (substitution t0 t1) eqn:?; intuition.
  destruct p; simpl.
  rewrite map_expr_denote_subst_map_expr; auto.
  now apply (term_denote_substitution Heqo).
Qed.

Lemma formula_denote_subst_formula env v v' t :
  term_denote env v = term_denote env v'
    -> formula_denote env (subst_formula t v v') = formula_denote env t.
Proof.
  induction t; simpl; auto; intros.
    rewrite map_expr_denote_subst_map_expr,
            !term_denote_subst_term; auto.
  rewrite IHt1, IHt2; auto.
Qed.

Lemma formula_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> formula_denote env (subst_all subst_formula t (substitutions xs)) =
       formula_denote env t.
Proof.
  induction xs as [|[] ?]; simpl; intros; auto.
  inversion H.
  destruct (substitution t0 t1) eqn:?; intuition.
  destruct p; simpl.
  rewrite formula_denote_subst_formula; auto.
  now apply (term_denote_substitution Heqo).
Qed.

(**************************************************************************
 * Code for removing conflicted map entries
 *)

Definition conflicted (x y : term) : bool :=
  match x, y with
  | Value n, Value n' => negb (N.eqb n n')
  | _, _ => false
  end.

Fixpoint remove_conflicts (x y f : term) (m : map_expr) : map_expr :=
  match m with
  | Empty => Empty
  | Add x' y' f' m' =>
    if (conflicted x x' || conflicted y y' || conflicted f f')%bool
    then remove_conflicts x y f m'
    else Add x' y' f' (remove_conflicts x y f m')
  end.

Lemma terms_not_conflicted env x y :
  term_denote env x = term_denote env y
    -> conflicted y x = false.
Proof.
  destruct x, y; simpl; auto.
  intros; subst.
  rewrite N.eqb_refl; reflexivity.
Qed.

(**************************************************************************
 * Computational decision procedure for map membership
 *)

Import ListNotations.

Program Definition formula_forward (t : formula) env (hyp : formula)
        (cont : ∀ env' defs,
            [formula_denote env' (subst_all subst_formula t defs)]) :
  [formula_denote env hyp -> formula_denote env t] :=
  match hyp with
  | Top => Reduce (cont env [])
  | Bottom => Yes
  | Maps x y f m =>
    let fix go n : [formula_denote env (Maps x y f n)
                    -> formula_denote env t] :=
        match n with
        | Empty => Yes
        | Add x' y' f' m' =>
          cont env (substitutions [(x, x'); (y, y'); (f, f')]) && go m'
        end in Reduce (go (remove_conflicts x y f m))
  | Impl _ _ => Reduce (cont env [])
  end.
Next Obligation.
  contradiction.
Defined.
Next Obligation.
  simplify_maps.
  match goal with [ H : _ /\ _ |- _ ] => destruct H end.
  simpl in *.
  pose proof (formula_substitution_eq env t [(x, x'); (y, y'); (f, f')]).
  let Hr := match goal with [ H : _ -> _ = _ |- _ ] => H end in
  simpl in Hr; rewrite <- Hr; auto.
Defined.
Next Obligation.
  match goal with [ H : M.MapsTo _ _ _ -> _ |- _ ] => apply H; clear H end.
  induction m; simpl in *; auto.
  destruct (conflicted x t0) eqn:?;
  destruct (conflicted y t1) eqn:?;
  destruct (conflicted f t2) eqn:?;
  simpl; simplify_maps;
  try destruct H1;
  simpl in *;
  try pose proof (terms_not_conflicted _ _ _ H);
  try pose proof (terms_not_conflicted _ _ _ H0);
  try pose proof (terms_not_conflicted _ _ _ H2);
  try congruence;
  rewrite ?H, ?H0, ?H2;
  simplify_maps.
Defined.

Fixpoint map_contains env (x y : N) (m : map_expr) : option term :=
  match m with
  | Empty => None
  | Add x' y' f' m' =>
    if (N.eqb x (term_denote env x') &&
        N.eqb y (term_denote env y'))%bool
    then Some f'
    else map_contains env x y m'
  end.

Lemma map_contains_MapsTo env x y f m :
  Some f = map_contains env x y m
    -> M.MapsTo (x, y) (term_denote env f) (map_expr_denote env m).
Proof.
  induction m; simpl; intros.
    discriminate.
  simplify_maps.
  destruct ((x =? term_denote env t)%N &&
            (y =? term_denote env t0)%N)%bool eqn:?.
    inversion_clear H.
    clear IHm.
    apply andb_true_iff in Heqb.
    destruct Heqb.
    apply N.eqb_eq in H.
    apply N.eqb_eq in H0.
    intuition.
  right.
  apply andb_false_iff in Heqb.
  destruct Heqb;
  apply N.eqb_neq in H0;
  intuition.
Qed.

Program Fixpoint formula_backward (t : formula) env {measure (formula_size t)} :
  [formula_denote env t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Maps x y f m =>
    match map_contains env (term_denote env x) (term_denote env y) m with
    | Some f' => Reduce (term_eq_dec f' f)
    | None => No
    end
  | Impl p q =>
    formula_forward q env p
      (fun env' defs' => formula_backward (subst_all subst_formula q defs') env')
  end.
Next Obligation.
  apply map_contains_MapsTo; auto.
Defined.
Next Obligation.
  rewrite formula_size_subst_all_formula; simpl; lia.
Defined.

Definition formula_tauto : ∀ env t, [formula_denote env t].
Proof.
  intros; refine (Reduce (formula_backward t env)); auto.
Defined.

Lemma formula_sound env t :
  (if formula_tauto env t then True else False) -> formula_denote env t.
Proof.
  unfold formula_tauto; destruct t, (formula_backward _ env); tauto.
Qed.

(**************************************************************************
 * Environment management tactics
 *)

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

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    lazymatch xs' with
    | tt => constr:(fun _ : positive => 0%N)
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop (1%positive) xs.

Ltac allVar xs e :=
  match e with
  | N0 => xs
  | Npos _ => xs
  | _ => addToList e xs
  end.

Ltac allVars xs e :=
  match e with
  | M.MapsTo (?X, ?Y) ?F _ =>
    let xs := allVar xs X in
    let xs := allVar xs Y in
    allVar xs F
  | M.In (?X, ?Y) _ =>
    let xs := allVar xs X in
    allVar xs Y
  | ?P -> ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | _ => xs
  end.

(**************************************************************************
 * Reflection tactics
 *)

Ltac reifyValue env t :=
  match t with
  | N0 => constr:(Value N0)
  | Npos ?X =>
    constr:(Value (Npos X))
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  end.

Ltac reifyMapTerm env t :=
  match t with
  | M.empty _ => constr:(Empty)
  | M.add (?X, ?Y) ?F ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let f := reifyValue env F in
    let m := reifyMapTerm env M in
    constr:(Add x y f m)
  end.

Ltac reifyTerm env t :=
  match t with
  | True => constr:(Top)
  | False => constr:(Bottom)
  | M.MapsTo (?X, ?Y) ?F ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let f := reifyValue env F in
    let m := reifyMapTerm env M in
    constr:(Maps x y f m)
  | ?P -> ?Q =>
    let p := reifyTerm env P in
    let q := reifyTerm env Q in
    constr:(Impl p q)
  end.

Ltac gather_vars :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    pose xs
  end.

Ltac reify' :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1
  end.

Ltac reify :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    change (formula_denote {| vars := env |} r1)
  end.

(**************************************************************************
 * User interface tactics
 *)

Ltac solve_map := reify; apply formula_sound; vm_compute; auto.

#[global]
Program Instance sigT_proper {A : Type} :
  Proper (pointwise_relation A Basics.arrow ==> Basics.arrow) (@sigT A).
Next Obligation.
  proper.
  destruct X0.
  apply X in x1.
  exists x0.
  assumption.
Defined.

Lemma find_mapsto_iff_ex {elt k m} :
  (∃ v : elt, M.MapsTo (elt:=elt) k v m) ->
  (∃ v : elt, M.find (elt:=elt) k m = Some v).
Proof.
  apply sigT_proper.
  intros ??.
  apply F.find_mapsto_iff.
  assumption.
Defined.

Ltac prepare_maps :=
  repeat lazymatch goal with
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex, in_mapsto_iffT
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ H : M.find _ (M.empty _) = Some _ |- _ ] => inversion H
  | [ H : M.find _ _ = Some ?F |- _ ] =>
    apply F.find_mapsto_iff in H; revert H
  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)
  end.

Ltac map_decide := prepare_maps; solve_map.

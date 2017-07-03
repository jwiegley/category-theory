Set Warnings "-notation-overridden".

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

Definition partialOut {P : Prop} (x : partial P) :=
  match x return (match x with
                  | Proved _ _  => P
                  | Uncertain _ => True
                  end) with
  | Proved _ pf => pf
  | Uncertain _ => I
  end.

Notation "[ P ]" := (partial P) : type_scope.

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

Lemma term_beq_neq_sound x y : term_beq x y = false -> x ≠ y.
Proof.
  induction x, y; simpl; intros; try discriminate.
  - apply Pos.eqb_neq in H.
    contradict H.
    inversion H; subst; reflexivity.
  - apply N.eqb_neq in H.
    contradict H.
    inversion H; subst; reflexivity.
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
  split; unfold not; intros;
  destruct H1; discriminate.
Defined.
Next Obligation.
  split; unfold not; intros;
  destruct H1; discriminate.
Defined.

Definition subst_term (x v v' : term) : term :=
  if term_beq x v then v' else x.

Fixpoint subst_all_term (x : term) (xs : list (term * term)) : term :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_term (subst_term x v v') xs
  end.

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

Fixpoint subst_all_map_expr (x : map_expr) (xs : list (term * term)) : map_expr :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_map_expr (subst_map_expr x v v') xs
  end.

Lemma subst_all_map_expr_Empty defs :
  subst_all_map_expr Empty defs = Empty.
Proof.
  induction defs; simpl; auto.
  destruct a; auto.
Qed.

Lemma subst_all_map_expr_Add defs x y f m :
  subst_all_map_expr (Add x y f m) defs =
  Add (subst_all_term x defs) (subst_all_term y defs)
      (subst_all_term f defs) (subst_all_map_expr m defs).
Proof.
  generalize dependent m.
  generalize dependent f.
  generalize dependent y.
  generalize dependent x.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Fixpoint map_expr_denote env (m : map_expr) : M.t N :=
  match m with
  | Empty => M.empty N
  | Add x y f m' => M.add (term_denote env x, term_denote env y)
                          (term_denote env  f) (map_expr_denote env m')
  end.

Inductive formula :=
  | Maps : term -> term -> term -> map_expr -> formula
  | Impl : formula -> formula -> formula.

Fixpoint subst_formula (t : formula) (v v' : term) : formula :=
  match t with
  | Maps x y f m =>
    Maps (subst_term x v v')
         (subst_term y v v')
         (subst_term f v v')
         (subst_map_expr m v v')
  | Impl p q => Impl (subst_formula p v v') (subst_formula q v v')
  end.

Fixpoint subst_all_formula (x : formula) (xs : list (term * term)) : formula :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_formula (subst_formula x v v') xs
  end.

Lemma subst_all_formula_Maps defs x y f m :
  subst_all_formula (Maps x y f m) defs =
  Maps (subst_all_term x defs) (subst_all_term y defs)
       (subst_all_term f defs) (subst_all_map_expr m defs).
Proof.
  generalize dependent m.
  generalize dependent f.
  generalize dependent y.
  generalize dependent x.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_all_formula_Impl defs p q :
  subst_all_formula (Impl p q) defs =
  Impl (subst_all_formula p defs) (subst_all_formula q defs).
Proof.
  generalize dependent q.
  generalize dependent p.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Fixpoint formula_denote env (t : formula) : Prop :=
  match t with
  | Maps x y f m =>
    M.MapsTo (term_denote env x, term_denote env y)
             (term_denote env f) (map_expr_denote env m)
  | Impl p q => formula_denote env p -> formula_denote env q
  end.

Fixpoint map_expr_size (t : map_expr) : nat :=
  match t with
  | Empty => 1%nat
  | Add _ _ _ m => 1%nat + map_expr_size m
  end.

Fixpoint formula_size (t : formula) : nat :=
  match t with
  | Maps _ _ _ m => 1%nat + map_expr_size m
  | Impl p q => formula_size p + formula_size q
  end.

Lemma all_formulas_have_size t : (0 < formula_size t)%nat.
Proof. induction t; simpl; omega. Qed.

Lemma map_expr_size_subst_all_map_expr defs m :
  map_expr_size (subst_all_map_expr m defs) = map_expr_size m.
Proof.
  induction m; simpl.
  - rewrite subst_all_map_expr_Empty; simpl; auto.
  - rewrite subst_all_map_expr_Add; simpl; auto.
Qed.

Lemma formula_size_subst_all_formula defs q :
  formula_size (subst_all_formula q defs) = formula_size q.
Proof.
  induction q; simpl.
  - rewrite subst_all_formula_Maps; simpl; auto.
    rewrite map_expr_size_subst_all_map_expr; auto.
  - rewrite subst_all_formula_Impl; simpl; auto.
Qed.

(**************************************************************************
 * Computational decision procedure
 *)

Definition conflicted (x y : term) : bool :=
  match x, y with
  | Value n, Value n' => negb (N.eqb n n')
  | _, _ => false
  end.

Definition substitution (x y : term) : option (term * term) :=
  match x, y with
  | Var n, Var m => if Pos.eq_dec n m then None else Some (x, y)
  | Var _, _  => Some (x, y)
  | _ , Var _ => Some (y, x)
  | _, _ => None
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

Fixpoint remove_conflicts (x y f : term) (m : map_expr) : map_expr :=
  match m with
  | Empty => Empty
  | Add x' y' f' m' =>
    if (conflicted x x' || conflicted y y' || conflicted f f')%bool
    then remove_conflicts x y f m'
    else Add x' y' f' (remove_conflicts x y f m')
  end.

Lemma term_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
  → term_denote env (subst_all_term t (substitutions xs)) =
    term_denote env t.
Proof.
  generalize dependent t.
  induction xs; simpl; intros; auto.
  inversion H; subst; clear H.
  destruct a as [x y]; simpl in *.
  destruct t; simpl; intros.
  - destruct x, y; simpl in *; intros; auto.
    + destruct (Pos.eq_dec p0 p1); simpl; auto.
        rewrite IHxs; auto.
      unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        rewrite IHxs; auto.
      apply Pos.eqb_neq in n0; rewrite n0; simpl; auto.
      apply IHxs; auto.
    + unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        apply IHxs; auto.
      apply Pos.eqb_neq in n0; rewrite n0; simpl; auto.
      apply IHxs; auto.
    + unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        apply IHxs; auto.
      apply Pos.eqb_neq in n0; rewrite n0; simpl; auto.
      apply IHxs; auto.
    + apply IHxs; auto.
  - destruct x, y; simpl in *; intros; try apply IHxs; auto.
    destruct (Pos.eq_dec p p0); simpl; apply IHxs; auto.
Qed.

Lemma map_expr_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> map_expr_denote env (subst_all_map_expr t (substitutions xs)) =
       map_expr_denote env t.
Proof.
  induction t; simpl; intros.
  - rewrite subst_all_map_expr_Empty; simpl; auto.
  - rewrite subst_all_map_expr_Add; simpl; intros.
    rewrite !term_substitution_eq; auto.
    rewrite IHt; auto.
Qed.

Lemma formula_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> formula_denote env (subst_all_formula t (substitutions xs)) =
       formula_denote env t.
Proof.
  induction t; simpl; intros.
  - rewrite subst_all_formula_Maps; simpl; intros.
    rewrite !term_substitution_eq; auto.
    rewrite map_expr_substitution_eq; auto.
  - rewrite subst_all_formula_Impl; simpl; intros.
    intuition.
    rewrite H0, H1; auto.
Qed.

Lemma terms_not_conflicted env x y :
  term_denote env x = term_denote env y
    -> conflicted y x = false.
Proof.
  destruct x, y; simpl; auto.
  intros; subst.
  rewrite N.eqb_refl; reflexivity.
Qed.

(* The only job of formula_forward at the moment is to accumulate variable
   definitions. *)
Program Definition formula_forward (t : formula) env (hyp : formula)
        (cont : ∀ env' defs, [formula_denote env' (subst_all_formula t defs)]) :
  [formula_denote env hyp -> formula_denote env t] :=
  match hyp with
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
  simplify_maps.
  destruct H2.
  simpl in *.
  pose proof (formula_substitution_eq env t [(x, x'); (y, y'); (f, f')]).
  simpl in H4.
  rewrite H4 in H; auto.
Defined.
Next Obligation.
  apply H; clear H.
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

Fixpoint map_contains env (x y : term) (m : map_expr) : option term :=
  match m with
  | Empty => None
  | Add x' y' f' m' =>
    if (N.eqb (term_denote env x) (term_denote env x') &&
        N.eqb (term_denote env y) (term_denote env y'))%bool
    then Some f'
    else map_contains env x y m'
  end.

Lemma map_contains_MapsTo env x y f m :
  Some f = map_contains env x y m
    -> M.MapsTo (term_denote env x, term_denote env y)
                (term_denote env f) (map_expr_denote env m).
Proof.
  induction m; simpl; intros.
    discriminate.
  simplify_maps.
  destruct ((term_denote env x =? term_denote env t)%N &&
            (term_denote env y =? term_denote env t0)%N)%bool eqn:?.
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
  | Maps x y f m =>
    match map_contains env x y m with
    | Some f' => Reduce (term_eq_dec f' f)
    | None => No
    end
  | Impl p q =>
    formula_forward q env p
      (fun env' defs' => formula_backward (subst_all_formula q defs') env')
  end.
Next Obligation.
  apply map_contains_MapsTo; auto.
Defined.
Next Obligation.
  rewrite formula_size_subst_all_formula; simpl.
  apply Nat.lt_add_pos_l, all_formulas_have_size.
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

(**************************************************************************
 * Some helper lemmas and a "traditional" FMap theorem solver
 *)

Lemma mapsto_inv : ∀ elt f g (fg : elt) x y z m,
  M.MapsTo (f, g) fg (M.add (x, y) z m) ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.MapsTo (f, g) fg m.
Proof.
  intros.
  apply add_mapsto_iffT in H.
  destruct H; simpl in *; intuition.
Defined.

Lemma find_add_inv : ∀ f g (fg : N) x y z m,
  M.find (f, g) (M.add (x, y) z m) = Some fg ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.find (f, g) m = Some fg.
Proof.
  intros.
  destruct (N.eq_dec x f).
    destruct (N.eq_dec y g).
      destruct (N.eq_dec z fg).
        subst; left; intuition.
      contradiction n.
      rewrite F.add_eq_o in H.
        inversion_clear H.
        reflexivity.
      simpl; intuition.
    rewrite F.add_neq_o in H; intuition.
  rewrite F.add_neq_o in H; intuition.
Defined.

Ltac destruct_maps :=
  repeat match goal with
  | [ H : M.find (?X, ?Y) (M.empty _) = Some ?F |- _ ] =>
    inversion H
  | [ H : M.find (?X, ?Y) (M.add _ _ _) = Some ?F |- _ ] =>
    apply find_add_inv in H;
    (destruct H as [[? [? ?]]|]; [subst; try nomega|])
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    vm_compute; eexists; reflexivity

  | [ H : M.find _ _ = Some _ |- _ ] =>
    apply F.find_mapsto_iff in H
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex

  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)

  | [ H : M.MapsTo (?X, ?Y) ?F (M.add _ _ _) |- _ ] =>
    apply mapsto_inv in H; destruct H as [[? [? ?]]|]

  | [ H : ?X = ?Y |- context[M.MapsTo (?Y, _)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ?Y)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo _ ?Y] ] =>
    rewrite <- H; cbn

  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
      exists F
    end
  | [ |- M.MapsTo (?X, ?Y) ?F (M.add (?X, ?Y) ?F _) ] =>
    simplify_maps
  | [ |- M.MapsTo _ _ (M.add _ _ _) ] =>
    simplify_maps; right; split; [idtac|]
  end;
  try congruence.

(**************************************************************************
 * Proof of concept examples
 *)

Example formula_backward_example (x y z w : N) :
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty)))
       {| vars := fun p =>
           if (p =? 1)%positive then x else
           if (p =? 2)%positive then y else
           if (p =? 3)%positive then z else
           if (p =? 4)%positive then w else 9%N |}
  then True else False.
Proof. vm_compute; constructor. Qed.

Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

Delimit Scope fmap_scope with fmap.

Notation "[map ]" := (M.empty _) (at level 9, only parsing) : fmap_scope.
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing) : fmap_scope.
Notation "[map  a ; .. ; b ]" := (a .. (b [map]%fmap) ..) (only parsing) : fmap_scope.

Example big_problem : ∀ f g h fg gh fgh : N,
  let big :=
    [map (0, 0) +=> 0
    ;    (1, 1) +=> 1
    ;    (2, 2) +=> 2
    ;    (3, 3) +=> 3

    ;    (4, 0) +=> 4
    ;    (1, 4) +=> 4

    ;    (5, 1) +=> 5
    ;    (2, 5) +=> 5

    ;    (6, 2) +=> 6
    ;    (3, 6) +=> 6

    ;    (7, 0) +=> 7
    ;    (2, 7) +=> 7

    ;    (8, 1) +=> 8
    ;    (3, 8) +=> 8

    ;    (9, 0) +=> 9
    ;    (3, 9) +=> 9

    ;    (5, 4) +=> 7
    ;    (6, 5) +=> 8
    ;    (6, 7) +=> 9
    ;    (8, 4) +=> 9 ]%N%fmap in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  intros.
  unfold big in *; clear big.
(*
  Time destruct_maps; try nomega. (* takes 30s *)
  Undo.
*)
  Time map_decide.                (* takes 0.017s *)
Qed.

Print Assumptions big_problem.

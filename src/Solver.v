Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
(* Require Import Coq.Relations.Relations. *)
(* Require Import Coq.Classes.RelationClasses. *)
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
(* Require Import Coq.Vectors.Vector. *)
Require Import Coq.NArith.NArith.

Generalizable All Variables.

Definition obj_idx := N.
Definition arr_idx := N.

Set Universe Polymorphism.

Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
  equiv := fun x y => match x, y with
    | Some x, Some y => x ≈ y
    | None, None => True
    | _, _ => False
    end
}.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Qed.

Program Definition index_eq_dec (n m : index) : {n = m} + {n ≠ m} :=
  match index_eq n m with
  | true  => left (index_eq_prop n m _)
  | false => right _
  end.
Next Obligation.
  intro; subst.
  induction m; simpl in Heq_anonymous; auto.
  discriminate.
Qed.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> ∀ p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Defined.

Lemma Neq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (N.eq_dec x y); auto.
Defined.

Lemma Neq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (Neq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
    reflexivity.
  contradiction.
Qed.

Corollary index_eq_dec' : ∀ x y : index, x = y \/ x ≠ y.
Proof. intros; destruct (index_eq_dec x y); auto. Defined.

Lemma index_eq_dec_refl n : index_eq_dec n n = left (@eq_refl _ n).
Proof.
  destruct (index_eq_dec n n).
    refine (K_dec_on_type index n (index_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl index n)) _ _).
    reflexivity.
  contradiction.
Defined.

Unset Universe Polymorphism.

Open Scope N_scope.

Set Decidable Equality Schemes.

Inductive Term : Type :=
  | Identity : N -> Term
  | Morph    : N -> Term
  | Compose  : Term -> Term -> Term.

Lemma Term_eq_dec' : ∀ x y : Term, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Term_eq_dec x y); auto.
Defined.

Lemma Term_eq_dec_refl n : Term_eq_dec n n = left (@eq_refl _ n).
Proof.
  destruct (Term_eq_dec n n).
    refine (K_dec_on_type Term n (Term_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl _ n)) _ _).
    reflexivity.
  contradiction.
Qed.

Inductive Subterm : Term -> Term -> Prop :=
  | Compose1 : ∀ t1 t2, Subterm t1 (Compose t1 t2)
  | Compose2 : ∀ t1 t2, Subterm t2 (Compose t1 t2).

Definition Subterm_inv_t : ∀ x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Compose ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Compose ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | _ => exact False
  end.
Defined.

Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl; intuition;
  rewrite Term_eq_dec_refl;
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym; intuition;
  destruct (Term_eq_dec _ _);
  try (rewrite e || rewrite <- e);
  try (rewrite e0 || rewrite <- e0);
  try congruence; intuition.
Qed.

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

Section Symmetric_Product2.

  Variable A : Type.
  Variable leA : A -> A -> Prop.

  Inductive symprod2 : A * A -> A * A -> Prop :=
    | left_sym2 :
      ∀ x x':A, leA x x' -> ∀ y:A, symprod2 (x, y) (x', y)
    | right_sym2 :
      ∀ y y':A, leA y y' -> ∀ x:A, symprod2 (x, y) (x, y')
    | both_sym2 :
      ∀ (x x':A) (y y':A),
        leA x x' ->
        leA y y' ->
        symprod2 (x, y) (x', y').

  Lemma Acc_symprod2 :
    ∀ x:A, Acc leA x -> ∀ y:A, Acc leA y -> Acc symprod2 (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros y H2.
    induction H2 as [x1 H3 IHAcc1].
    apply Acc_intro; intros y H5.
    inversion_clear H5; auto with sets.
    apply IHAcc; auto.
    apply Acc_intro; trivial.
  Defined.

  Lemma wf_symprod2 :
    well_founded leA -> well_founded symprod2.
  Proof.
    red.
    destruct a.
    apply Acc_symprod2; auto with sets.
  Defined.

End Symmetric_Product2.

Program Fixpoint eval (C : Category) (e : Term)
        (objs : obj_idx -> C)
        (arrs : arr_idx -> ∃ a b : obj_idx, option (objs a ~> objs b)) :
  ∃ a b : obj_idx, option (objs a ~> objs b) :=
  match e with
  | Morph n => arrs n
  | Identity x => (x; (x; Some (@id C (objs x))))
  | Compose f g =>
    let f' := eval C f objs arrs in
    let g' := eval C g objs arrs in
    match f', g' with
    | (yf; (z; Some f')), (x; (yg; Some g')) =>
      match N.eq_dec yf yg with
      | left _  => (x; (z; Some (f' ∘ g')))
      | right _ => (0; (0; None))
      end
    | _, _ => (0; (0; None))
    end
  end.

Program Definition Equiv (p : Term * Term) : Type.
Proof.
  refine (∀ (C : Category) objs arrs, _).
  refine (
    match eval C (fst p) objs arrs, eval C (snd p) objs arrs with
    | (fx; (fy; Some f)), (gx; (gy; Some g)) =>
      match N.eq_dec fx gx, N.eq_dec fy gy with
      | left _, left _ => f ≈ _ g
      | _, _ => False
      end
    | (_; (_; None)), (_; (_; None)) => True
    | _, _ => False
    end).
  subst.
  auto.
Defined.
Arguments Equiv _ /.

Definition R := symprod2 Term Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Local Obligation Tactic := intros; try discriminate.

Definition Compose' (a b : Term) : Term :=
  match a, b with
  | Identity _, g => g
  | f, Identity _ => f
  | Compose f g, Compose h k => Compose (Compose (Compose f g) h) k
  | _, _ => Compose a b
  end.

Theorem Compose'_ok : ∀ a b, Equiv (Compose' a b, Compose a b).
Proof.
  simpl; intros.
  destruct a.
  - destruct b; simpl.
    unfold eval_obligation_1; simpl.
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym; simpl.
    unfold EqdepFacts.internal_eq_rew_r_dep,
           EqdepFacts.internal_eq_sym_involutive,
           EqdepFacts.internal_eq_sym_internal.
    (* jww (2017-06-12): We get stuck here. *)
    destruct (N.eq_dec n n0).

(*
Program Fixpoint normalize (p : Term) {wf (Subterm) p} :
  { t : Term & ∀ C, Equiv C (p, t) } :=
  match p with
  | Identity x  => existT _ p _
  | Morph x y f => existT _ p _

  | Compose f (Identity x)  =>
    match N.eq_dec (TermDom f) x with
    | left _  => existT _ f _
    | right _ => existT _ p _
    end
  | Compose (Identity x) g  =>
    match N.eq_dec x (TermCod g) with
    | left _  => existT _ g _
    | right _ => existT _ p _
    end
  | Compose f (Compose g h) =>
    match N.eq_dec (TermDom f) (TermCod g) with
    | left _  => existT _ (Compose (Compose f g) h) _
    | right _ => existT _ p _
    end

  | Compose f g => existT _ p _
  end.
Next Obligation.
  simpl; intros; subst; simpl.
  destruct (N.eq_dec x x); auto.
  unfold eq_rect.
  destruct e.
  reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  destruct (arrs f x y).
  unfold eq_rect.
    reflexivity.
  constructor.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (eval C f objs arrs).
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
    rewrite id_right; reflexivity.
  constructor.
Admitted.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec x (TermDom f)); auto.
  destruct (eval C f objs arrs).
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
    destruct e.
    rewrite id_right; reflexivity.
  constructor.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (eval C g objs arrs).
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
    rewrite id_left; reflexivity.
  constructor.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) x); auto.
  destruct (eval C g objs arrs).
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
    destruct e.
    rewrite id_left; reflexivity.
  constructor.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) (TermDom f)); auto.
  unfold eval_obligation_1; simpl.
  destruct (eval C f objs arrs); auto.
  destruct (N.eq_dec (TermCod h) (TermDom g)); auto.
  destruct (eval C g objs arrs); auto.
  destruct (eval C h objs arrs); auto.
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
  destruct e, e0.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) (TermDom f)); auto.
  unfold eval_obligation_1; simpl.
  destruct (eval C f objs arrs); auto.
  destruct (N.eq_dec (TermCod h) (TermDom g)); auto.
  destruct (eval C g objs arrs); auto.
  destruct (eval C h objs arrs); auto.
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
  destruct e, e0.
  reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) (TermDom f)); auto.
  unfold eval_obligation_1; simpl.
  destruct (eval C f objs arrs); auto.
  destruct (eval C g objs arrs); auto.
  unfold eq_ind_r, eq_ind, eq_rect, eq_sym; simpl.
  destruct e.
  reflexivity.
Defined.
Next Obligation.
  split; intros.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) (TermDom f)); auto.
  unfold eval_obligation_1; simpl.
  - unfold not; intros.
    inversion H5.
  - unfold not; intros.
    inversion H5.
  - split; intros.
    + unfold not; intros.
      inversion H5.
    + unfold not; intros.
      inversion H5.
Defined.
Next Obligation.
  split; intros.
  simpl; intros; subst; simpl.
  repeat rewrite Neq_dec_refl.
  unfold eval_obligation_1; simpl.
  destruct (N.eq_dec (TermCod g) (TermDom f)); auto.
  unfold eval_obligation_1; simpl.
  - unfold not; intros.
    inversion H4.
  - unfold not; intros.
    inversion H4.
  - split; intros.
    + unfold not; intros.
      inversion H4.
    + unfold not; intros.
      inversion H4.
Defined.
Next Obligation.
  apply measure_wf.
  apply Subterm_wf.
Defined.

Eval vm_compute in `1 (normalize (Compose (Morph 0 0 0) (Identity 0))).
*)

Program Fixpoint check_equiv (p : Term * Term) {wf (R) p} : bool :=
  match p with (s, t) =>
    match s with
    | Identity x =>
      match t with
      | Identity y  => N.eqb x y
      | Morph g     => false
      | Compose h k => false
      end
    | Morph f =>
      match t with
      | Identity _  => false
      | Morph g     => N.eqb f g
      | Compose h k => false
      end
    | Compose f g =>
      match t with
      | Identity _  => false
      | Morph g     => false
      | Compose h k => check_equiv (f, h) &&& check_equiv (g, k)
      end
    end
  end.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  apply measure_wf.
  apply wf_symprod2.
  apply Subterm_wf.
Defined.

Theorem check_equiv_sound : ∀ p : Term * Term,
  check_equiv p = true -> ∀ C, Equiv C p.
Proof.
  intros [] H C objs arrs; simpl in *.
  induction t; simpl in *.
  - destruct t0; simpl in *; try discriminate.
    destruct (N.eq_dec n n0); subst.
      unfold eq_rect_r, eq_rect, eq_sym; simpl.
      reflexivity.
    apply N.eqb_eq in H; subst.
    contradiction.
  - destruct t0; simpl in *; try discriminate.
    apply N.eqb_eq in H; subst.
    destruct (arrs n0) as [x [y [f|]]].
      rewrite !Neq_dec_refl.
      unfold eq_rect_r, eq_rect, eq_sym; simpl.
      reflexivity.
    constructor.
  - destruct t0; simpl in *; try discriminate.
    destruct t1; simpl in *; try discriminate.
    + destruct t2; simpl in *; try discriminate.
Admitted.

(*
Next Obligation.
  subst.
  simpl; intros; subst.
  repeat destruct (N.eq_dec _ _); simpl; auto.
  unfold eq_rect; simpl.
  destruct e.
  reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst.
  apply N.eqb_eq in H; subst.
  repeat destruct (N.eq_dec _ _); simpl; auto.
  unfold eq_rect; simpl; subst.
  destruct (arrs g _ _); reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst.
  repeat destruct (decision _ _); simpl in *;
  destruct x, x0; try discriminate;
  specialize (e eq_refl C objs arrs);
  specialize (e0 eq_refl C objs arrs);
  repeat destruct (N.eq_dec _ _); simpl; auto;
  unfold eval_obligation_1 in *; simpl in *;
  clear decision;
  destruct (eval C f objs arrs),
           (eval C g objs arrs),
           (eval C k objs arrs),
           (eval C h objs arrs);
  unfold eq_ind_r, eq_ind, eq_sym, eq_rect in *; simpl in *;
  auto; try tauto.
    destruct e5, e2, e1, e6, e3.
    rewrite e.
    apply compose_respects.
      reflexivity.
    rewrite e0; clear.
    (* Avoid the use of JMeq_eq, since otherwise [dependent destruction e4]
       would solve this goal. *)
    assert (K_dec_on_type :
              ∀ (x:N) (P:x = x -> Type),
                P (eq_refl x) -> ∀ p:x = x, P p).
      intros.
      elim (@Eqdep_dec.eq_proofs_unicity_on N _) with x (eq_refl x) p.
        trivial.
      intros.
      destruct (N.eq_dec x y); auto.
    exact (
      K_dec_on_type
        (TermCod k)
        (fun x =>
           Setoid.equiv
             match x in (_ = y) return (objs (TermDom k) ~{ C }~> objs y)
             with eq_refl => h2
             end h2)
        (Setoid.setoid_refl _ _) e4).
  clear -e3 e4 e5 n.
  congruence.
Admitted.
*)

Example speed_test (C : Category) :
  `1 (check_equiv
      (`1 (simplify (Compose (Morph 2 3 0) (Compose (Morph 1 2 1) (Morph 0 1 2)))),
       `1 (simplify (Compose (Compose (Morph 2 3 0) (Morph 1 2 1)) (Morph 0 1 2))))) = true.
Proof. reflexivity. Qed.

Definition decision_correct {t u : Term}
        (Heq : `1 (decision (`1 (normalize t), `1 (normalize u))) = true) :
  ∀ C, Equiv C (`1 (normalize t), `1 (normalize u)) :=
  `2 (decision (`1 (normalize t), `1 (normalize u))) Heq.

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
  (* jww (2017-06-12): TODO *)
  | ?e1 ∘ ?e2 =>
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
  (* jww (2017-06-12): TODO *)
  | ?X1 ∘ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Compose r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Morph n)
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
  | [ |- ?S ≈ ?T ] =>
    let xs  := allVars tt S in
    let xs' := allVars xs T in
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in
    let objs := functionalize xs' in
    let arrs := functionalize xs' in
    (* pose xs'; *)
    (* pose env; *)
    (* pose r1; *)
    (* pose r2; *)
    (* jww (2017-06-12): TODO *)
    change (eval r1 objs arrs ≈ eval r2 objs arrs)
  end.

Ltac categorical := reify; apply decision_correct; vm_compute; auto.

Example sample_1 {C : Category} :
  ∀ (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y),
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h.
Proof. Fail intros; categorical. Abort.

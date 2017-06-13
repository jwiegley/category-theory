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
Next Obligation. intuition; discriminate. Defined.
Next Obligation. intuition; discriminate. Defined.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Defined.

Program Definition index_eq_dec (n m : index) : {n = m} + {n ≠ m} :=
  match index_eq n m with
  | true  => left (index_eq_prop n m _)
  | false => right _
  end.
Next Obligation.
  intro; subst.
  induction m; simpl in Heq_anonymous; auto.
  discriminate.
Defined.

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
Defined.

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
  | Morph    : N -> N -> N -> Term
  | Compose  : Term -> Term -> Term.

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x _ _ => x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph _ x _ => x
  | Compose f _ => TermCod f
  end.

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
Defined.

Inductive Subterm : Term -> Term -> Prop :=
  | Compose1 : ∀ t1 t2, Subterm t1 (Compose t1 t2)
  | Compose2 : ∀ t1 t2, Subterm t2 (Compose t1 t2).

Definition Subterm_inv_t : ∀ x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Compose ?Y _ ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Compose ?Y _ ?Z) |- Prop ] =>
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

(*
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
Defined.
*)

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
  Qed.

  Lemma wf_symprod2 :
    well_founded leA -> well_founded symprod2.
  Proof.
    red.
    destruct a.
    apply Acc_symprod2; auto with sets.
  Defined.

End Symmetric_Product2.

Program Fixpoint eval (C : Category) (dom cod : obj_idx) (e : Term)
        (objs : obj_idx -> C)
        (arrs : arr_idx -> ∀ x y : obj_idx, option (objs x ~> objs y))
        {struct e} :
  TermDom e = dom ->
  TermCod e = cod ->
  option (objs dom ~> objs cod) := fun Hdom Hcod =>
    match e with
    | Identity x  => Some (@id C (objs x))
    | Morph x y n => _ (arrs n x y)
    | Compose f g =>
      match N.eq_dec (TermDom f) (TermCod g) with
      | left _ =>
        match eval C (TermCod g) cod f objs arrs _ Hcod,
              eval C dom (TermCod g) g objs arrs Hdom _ with
        | Some f', Some g' => Some (f' ∘ g')
        | _, _ => None
        end
      | right _ => None
      end
    end.

Program Definition Equiv (p : Term * Term) : Type :=
  ∀ (C : Category) objs arrs dom cod f Hdom Hcod,
    eval C dom cod (fst p) objs arrs Hdom Hcod = Some f
      -> ∃ g Hdom' Hcod', eval C dom cod (snd p) objs arrs Hdom' Hcod' = Some g
           ∧ f ≈ g.
Arguments Equiv _ /.

Definition R := symprod2 Term Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Local Obligation Tactic := intros; try discriminate.

Section Reduction.

Context {C : Category}.

Variable (objs : obj_idx -> C).
Variable (arrs : arr_idx -> ∀ x y : obj_idx, option (objs x ~> objs y)).

Definition Compose' (a b : Term) : Term :=
  match a, b with
  | Identity _, g => g
  | f, Identity _ => f
  | Compose f g, Compose h k => Compose (Compose (Compose f g) h) k
  | _, _ => Compose a b
  end.

Lemma Identity_dom_cod dom cod x f Hdom Hcod :
  eval C dom cod (Identity x) objs arrs Hdom Hcod = Some f
    -> dom = cod ∧ dom = x.
Proof.
  intros.
  inversion Hdom.
  inversion Hcod.
  subst; intuition.
Qed.

Theorem eval_dom cod f (Hdom : TermDom f = TermDom f) Hcod :
  eval C (TermDom f) cod f objs arrs Hdom Hcod =
  eval C (TermDom f) cod f objs arrs eq_refl Hcod.
Proof.
  replace Hdom with (@eq_refl _ (TermDom f)).
    reflexivity.
  apply (Eqdep_dec.UIP_dec N.eq_dec).
Qed.

Theorem eval_cod dom f Hdom (Hcod : TermCod f = TermCod f) :
  eval C dom (TermCod f) f objs arrs Hdom Hcod =
  eval C dom (TermCod f) f objs arrs Hdom eq_refl.
Proof.
  replace Hcod with (@eq_refl _ (TermCod f)).
    reflexivity.
  apply (Eqdep_dec.UIP_dec N.eq_dec).
Qed.

Corollary eval_dom_cod
        f (Hdom : TermDom f = TermDom f) (Hcod : TermCod f = TermCod f) :
  eval C (TermDom f) (TermCod f) f objs arrs Hdom Hcod =
  eval C (TermDom f) (TermCod f) f objs arrs eq_refl eq_refl.
Proof. rewrite eval_dom, eval_cod; reflexivity. Qed.

Lemma Identity_eval x f Hdom Hcod :
  eval C x x (Identity x) objs arrs Hdom Hcod = Some f ->
  f ≈ @id C (objs x).
Proof.
  pose proof (eval_dom_cod (Identity x) Hdom Hcod).
  simpl TermDom in H; simpl TermCod in H; rewrite H; clear H.
  simpl; inversion_clear 1; reflexivity.
Qed.

Corollary Compose'_Identity_Left x g : Compose' (Identity x) g = g.
Proof. reflexivity. Qed.

Lemma Compose'_Identity_Right f x :
  TermDom f = x -> Compose' f (Identity x) = f.
Proof. destruct f; simpl; intros; subst; auto. Qed.

Theorem Compose_eval dom mid cod a b :
  ∀ f Hmid_f Hcod_f, eval C mid cod a objs arrs Hmid_f Hcod_f = Some f ->
  ∀ g Hdom_g Hmid_g, eval C dom mid b objs arrs Hdom_g Hmid_g = Some g ->
  ∀ fg Hdom_fg Hcod_fg,
    eval C dom cod (Compose a b) objs arrs Hdom_fg Hcod_fg = Some fg ->
  fg ≈ f ∘ g.
Proof.
  intros; subst;
  destruct a, b;
  simpl TermDom in *;
  simpl TermCod in *; subst;
  match goal with
    [ H : eval _ ?N ?M (Compose ?F ?G) _ _ ?HD ?HC = Some ?FG |- _ ] =>
    let Hdc := fresh "Hdc" in
    pose proof (eval_dom_cod (Compose F G) HD HC) as Hdc;
    simpl TermDom in Hdc; simpl TermCod in Hdc;
    rewrite Hdc in H; clear Hdc
  end.
  - inversion_clear H.
    inversion_clear H0.
    simpl in H1.
    rewrite Neq_dec_refl in H1.
    inversion_clear H1.
    cat.
Admitted.

Theorem Compose'_ok dom cod a b (val : objs dom ~{ C }~> objs cod) Hdom Hcod :
  eval C dom cod (Compose a b) objs arrs Hdom Hcod = Some val
    -> ∃ val' Hdom' Hcod',
         eval C dom cod (Compose' a b) objs arrs Hdom' Hcod' = Some val'
           ∧ val ≈ val'.
Proof.
  intros.
  destruct a, b;
  simpl TermDom in *;
  simpl TermCod in *;
  simpl Compose' in *; subst.
  - simpl in H.
    destruct (N.eq_dec cod dom); simpl in H.
      destruct e; simpl in H.
      exists id.
      exists eq_refl.
      exists eq_refl.
      inversion_clear H.
      simpl.
      cat.
    discriminate.
  - admit.
Admitted.

Theorem Compose'_eval dom mid cod a b :
  ∀ f Hmid_f Hcod_f, eval C mid cod a objs arrs Hmid_f Hcod_f = Some f ->
  ∀ g Hdom_g Hmid_g, eval C dom mid b objs arrs Hdom_g Hmid_g = Some g ->
  ∀ fg Hdom_fg Hcod_fg,
    eval C dom cod (Compose' a b) objs arrs Hdom_fg Hcod_fg = Some fg ->
  fg ≈ f ∘ g.
Proof.
  intros; subst;
  destruct a, b;
  simpl TermDom in *;
  simpl TermCod in *; subst;
  match goal with
    [ H : eval _ ?N ?M (Compose' ?F ?G) _ _ ?HD ?HC = Some ?FG |- _ ] =>
    let Hdc := fresh "Hdc" in
    pose proof (eval_dom_cod (Compose' F G) HD HC) as Hdc;
    simpl TermDom in Hdc; simpl TermCod in Hdc;
    rewrite Hdc in H; clear Hdc
  end;
  simpl Compose' in *.
  - inversion_clear H.
    inversion_clear H0.
    inversion_clear H1.
    cat.
  - inversion_clear H.
    rewrite H0 in H1; inversion_clear H1.
    cat.
  - inversion_clear H.
    rewrite H0 in H1; inversion_clear H1.
    cat.
  - inversion_clear H0.
    rewrite H in H1; inversion_clear H1.
    cat.
  - eapply Compose_eval; eauto.
  - eapply Compose_eval; eauto.
  - inversion_clear H0.
    rewrite H in H1; inversion_clear H1.
    cat.
  - eapply Compose_eval; eauto.
  - admit.
Admitted.

Program Fixpoint check_equiv (p : Term * Term) {wf (R) p} : bool :=
  match p with (s, t) =>
    match s with
    | Identity x =>
      match t with
      | Identity y  => N.eqb x y
      | Morph _ _ g => false
      | Compose h k => false
      end
    | Morph _ _ f =>
      match t with
      | Identity _  => false
      | Morph _ _ g => N.eqb f g
      | Compose h k => false
      end
    | Compose f g =>
      match t with
      | Identity _  => false
      | Morph _ _ g => false
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
  check_equiv p = true -> Equiv p.
Proof.
  unfold check_equiv, Equiv; intros; subst.
  destruct p as [s t]; simpl in *.
  induction s; simpl in *.
  - destruct t; simpl in *.
    + inversion_clear H0.
      exists id.
      simpl in H.
      (* jww (2017-06-13): check_equiv is not reducing yet *)
      compute in H.
      destruct (N.eq_dec n0 n); subst.
        exists eq_refl.
        exists eq_refl.
        simpl; cat.
      (* jww (2017-06-13): H should prove this branch for us. *)
      admit.
Admitted.

(*
Example speed_test (C : Category) :
  `1 (check_equiv
      (`1 (simplify (Compose (Morph 2 3 0) (Compose (Morph 1 2 1) (Morph 0 1 2)))),
       `1 (simplify (Compose (Compose (Morph 2 3 0) (Morph 1 2 1)) (Morph 0 1 2))))) = true.
Proof. reflexivity. Defined.
*)

Definition decision_correct {t u : Term}
        (Heq : check_equiv (t, u) = true) : Equiv (t, u) :=
  check_equiv_sound (t, u) Heq.

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

Example sample_1 :
  ∀ (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y),
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h.
Proof. Fail intros; categorical. Abort.

End Reduction.

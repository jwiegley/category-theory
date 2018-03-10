Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Lib.Equality.

Program Instance positive_EqDec : EqDec.EqDec positive := {
  eq_dec := Eq_eq_dec
}.

Program Instance positive_Setoid : Setoid positive := {
  equiv := Eq_eq;
  setoid_equiv := eq_equivalence
}.

Generalizable All Variables.

Program Instance Equality_EqDec `{Equality A} : EqDec A := {
  eq_dec := Eq_eq_dec
}.
Program Instance option_EqDec `{EqDec A} : EqDec (option A) := {
  eq_dec := _
}.
Next Obligation.
  destruct x, y.
  - destruct (eq_dec a a0); subst.
      now left.
    right.
    intros.
    inversion H0.
    contradiction.
  - now right.
  - now right.
  - now left.
Defined.

Require Import Solver.Env.

Instance obj_idx_Equality : Equality obj_idx := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Instance arr_idx_Setoid : Setoid arr_idx := {
  equiv := Eq_eq;
  setoid_equiv := eq_equivalence
}.

Inductive Term {A : Type} : Type :=
  | Ident : Term
  | Morph (a : A) : Term
  | Comp (f : Term) (g : Term) : Term.

Arguments Term : clear implicits.

Fixpoint term_map {A B : Type} (f : A -> B) (t : Term A) : Term B :=
  match t with
  | Ident    => Ident
  | Morph a  => Morph (f a)
  | Comp l r => Comp (term_map f l) (term_map f r)
  end.

Fixpoint term_size `(t : Term A) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.

Inductive Expr {A : Type} : Type :=
  | Top
  | Bottom
  | Equiv (x y : obj_idx) (f g : Term A)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Arguments Expr : clear implicits.

Fixpoint expr_size `(t : Expr A) : nat :=
  match t with
  | Top           => 1%nat
  | Bottom        => 1%nat
  | Equiv _ _ f g => 1%nat + term_size f + term_size g
  | And p q       => 1%nat + expr_size p + expr_size q
  | Or p q        => 1%nat + expr_size p + expr_size q
  | Impl p q      => 1%nat + expr_size p + expr_size q
  end.

Remark all_exprs_have_size {A} e : (0 < expr_size (A:=A) e)%nat.
Proof. induction e; simpl; omega. Qed.

Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.

Program Definition TermF : Coq ⟶ Coq := {|
  fmap := @term_map
|}.
Next Obligation.
  proper.
  induction x1; simpl; auto.
    now rewrite H.
  now rewrite IHx1_1, IHx1_2.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0_1, IHx0_2.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0_1, IHx0_2.
Qed.

Require Import Category.Theory.EndoFunctor.

Global Program Instance TermF_Map : EndoFunctor TermF :=
  Functor_EndoFunctor (F:=TermF).

Require Import Category.Theory.Natural.Transformation.

(** This is a more lawful way of saying that Term is Foldable. *)

Fixpoint arrows {a} (t : Term a) : list a :=
  match t with
  | Ident    => nil
  | Morph a  => [a]
  | Comp f g => arrows f ++ arrows g
  end.

Program Instance Term_list_Foldable : TermF ⟹ listF := {
  transform := fun _ => arrows
}.
Next Obligation.
  induction x0; simpl; auto.
  rewrite <- IHx0_1, <- IHx0_2.
  now rewrite List.map_app.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  rewrite IHx0_1, IHx0_2.
  now rewrite List.map_app.
Qed.

(** This is the same as saying that Term is Traversable.

    For the moment this is too painful to do generally, so we just do it for
    the few cases that we need. *)

Fixpoint Term_option_sequence {a} (x : Term (option a)) : option (Term a) :=
  match x with
  | Ident => Some Ident
  | Morph a => map[optionF] Morph a
  | Comp f g =>
    match Term_option_sequence f with
    | None => None
    | Some f' =>
      match Term_option_sequence g with
      | None => None
      | Some g' =>
        Some (Comp f' g')
      end
    end
  end.

Program Instance Term_option_Traversable :
  TermF ○ optionF ⟹ optionF ○ TermF := {
  transform := fun _ => Term_option_sequence
}.
Next Obligation.
  intros.
  induction x0; simpl; auto.
  - destruct a; auto.
  - rewrite <- IHx0_1, <- IHx0_2.
    clear IHx0_1 IHx0_2.
    do 2 destruct (Term_option_sequence _); auto.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  - destruct a; auto.
  - rewrite IHx0_1, IHx0_2.
    clear IHx0_1 IHx0_2.
    do 2 destruct (Term_option_sequence _); auto.
Qed.

(** The category of syntactic terms. *)

Definition Term_equiv `{Setoid A} (f g : Term A) : Type :=
  arrows f ≈ arrows g.
Arguments Term_equiv {A _} f g /.

Program Instance Term_equivalence `{Setoid A} : Equivalence Term_equiv.
Next Obligation. intuition. Qed.
Next Obligation. intros; now rewrite X, X0. Qed.

Instance Term_Setoid `{Setoid A} : Setoid (Term A) := {|
  equiv := Term_equiv;
  setoid_equiv := Term_equivalence
|}.

Program Instance Comp_Proper `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@Comp A).
Next Obligation.
  proper.
  simpl in *.
  now rewrite X, X0.
Qed.

Program Definition Terms (A : Type) `{Setoid A} :
  Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term A;
  homset := fun _ _ => Term_Setoid;
  id := fun _ => Ident;
  compose := fun _ _ _ => Comp
|}.
Next Obligation. now rewrite List.app_nil_r. Defined.
Next Obligation. now rewrite List.app_assoc. Defined.
Next Obligation. now rewrite List.app_assoc. Defined.

(** The denotation Functor from syntactic terms over environment indices. *)

Section Denote.

Context `{Env}.

Import EqNotations.

Fixpoint termD_work dom (e : Term arr_idx) :
  option (∃ cod, objs dom ~> objs cod) :=
  match e with
  | Ident => Some (dom; @id _ (objs dom))
  | Morph a =>
    match arrs a with
    | Some (x; (y; f)) =>
      match Eq_eq_dec x dom with
      | Specif.left edom =>
        Some (y; rew [fun x => objs x ~> objs y] edom in f)
      | _ => None
      end
    | _ => None
    end
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition termD dom cod (e : Term arr_idx) : option (objs dom ~> objs cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Lemma termD_Ident {x} : termD x x Ident = Some id.
Proof.
  unfold termD; simpl; intros.
  now rewrite Pos_eq_dec_refl.
Defined.

Lemma termD_Morph {f dom cod f'} :
  arrs f = Some (dom; (cod; f')) ↔ termD dom cod (Morph f) = Some f'.
Proof.
  unfold termD; simpl; split; intros.
    rewrite H0.
    now rewrite !Pos_eq_dec_refl.
  destruct (arrs f) eqn:?; [|discriminate].
  destruct s, s.
  destruct (BinPos.Pos.eq_dec x dom); subst; [|discriminate].
  destruct (BinPos.Pos.eq_dec x0 cod); subst; [|discriminate].
  inversion H0; subst; clear H0.
  reflexivity.
Defined.

Equations Term_cod (dom : obj_idx) (e : Term arr_idx) : option obj_idx :=
  Term_cod dom Ident := Some dom;
  Term_cod dom (Morph a) <= arrs a => {
    | Some (existT d (existT cod _)) <= eq_dec dom d => {
        | Specif.left _ => Some cod;
        | _ => None
      };
    | None => None
  };
  Term_cod dom (Comp f g) <= Term_cod dom g => {
    | Some mid => Term_cod mid f;
    | None => None
  }.

Ltac inv H := inversion H; subst; try clear H.

Ltac desh :=
  lazymatch goal with
  | [ H : match Pos.eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (Pos.eq_dec n m)
  | [ H : match Eq_eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (Eq_eq_dec n m)
  | [ H : match eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (eq_dec n m)
  | [ H : match ?t with _ => _ end = _ |- _ ] =>
    destruct t eqn:?
  | [ H : match ?t with _ => _ end _ _ = _ |- _ ] =>
    destruct t eqn:?
  | [ H : context[match Pos.eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (Pos.eq_dec n m)
  | [ H : context[match Eq_eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (Eq_eq_dec n m)
  | [ H : context[match eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (eq_dec n m)
  | [ H : context[match ?t with _ => _ end] |- _ ] =>
    destruct t eqn:?
  | [ H : context[match ?t with _ => _ end _ _] |- _ ] =>
    destruct t eqn:?
  end;
  repeat lazymatch goal with
  | [ H : Some _ = Some _ |- _ ] => inversion H; subst; try clear H
  | [ H : (?X; _) = (?X; _) |- _ ] =>
    try apply (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec) in H
  | [ H : { _ : _ & _ } |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in
    destruct H as [x e]
  end;
  simpl in H; simpl; simplify; simpl_eq;
  try rewrite eq_dec_refl in *;
  try rewrite Eq_eq_dec_refl in *;
  try rewrite Pos_eq_dec_refl in *;
  subst;
  try (discriminate + contradiction).

Ltac desg :=
  lazymatch goal with
  | [ |- context[match Pos.eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (Pos.eq_dec n m)
  | [ |- context[match Eq_eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (Eq_eq_dec n m)
  | [ |- context[match eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (eq_dec n m)
  | [ |- context[match ?t with _ => _ end] ] =>
    destruct t eqn:?
  | [ |- context[match ?t with _ => _ end _ _] ] =>
    destruct t eqn:?
  end;
  repeat lazymatch goal with
  | [ H : { _ : _ & _ } |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in
    destruct H as [x e]
  end;
  simpl in H; simpl; simplify; simpl_eq;
  try rewrite eq_dec_refl in *;
  try rewrite Eq_eq_dec_refl in *;
  try rewrite Pos_eq_dec_refl in *;
  subst;
  try (discriminate + contradiction).

Lemma Term_cod_Some_inv {f dom cod f'} :
  termD_work dom f = Some (cod; f') -> Term_cod dom f = Some cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl; intros.
  - rewrite Term_cod_equation_1.
    now inv H0.
  - rewrite Term_cod_equation_2.
    unfold Term_cod_obligation_2.
    unfold Term_cod_obligation_1.
    now desh; desh.
  - rewrite Term_cod_equation_3.
    unfold Term_cod_obligation_3.
    desh; desh.
    desg; rewrite (IHf2 _ _ _ Heqo) in Heqo1.
      inv Heqo1.
      apply (IHf1 _ _ _ Heqo0).
    discriminate.
Defined.

Lemma Term_cod_Some {f dom cod} :
  Term_cod dom f = Some cod -> ∃ f', termD dom cod f = Some f'.
Proof.
  unfold termD.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl; intros.
  - rewrite Term_cod_equation_1 in H0.
    inv H0.
    exists id.
    now equalities.
  - rewrite Term_cod_equation_2 in H0.
    unfold Term_cod_obligation_2 in H0.
    unfold Term_cod_obligation_1 in H0.
    desh; desh.
    exists e0.
    now equalities.
  - rewrite Term_cod_equation_3 in H0.
    unfold Term_cod_obligation_3 in H0.
    desh.
    destruct (IHf1 _ _ H0); clear IHf1.
    destruct (IHf2 _ _ Heqo); clear IHf2.
    repeat desh.
    now exists (x ∘ x0).
Defined.

Lemma Term_cod_None {f dom} :
  Term_cod dom f = None -> ∀ cod, termD dom cod f = None.
Proof.
  unfold termD.
  generalize dependent dom.
  induction f; simpl; intros.
  - inversion H0.
  - rewrite Term_cod_equation_2 in H0.
    unfold Term_cod_obligation_2 in H0.
    unfold Term_cod_obligation_1 in H0.
    unfold termD; simpl.
    now desh; cat; desh; desg; desh.
  - rewrite Term_cod_equation_3 in H0.
    unfold Term_cod_obligation_3 in H0.
    desh.
      clear IHf2.
      specialize (IHf1 _ H0).
      destruct (Term_cod_Some Heqo); clear Heqo.
      unfold termD in e.
      repeat desh; repeat desg; auto.
      now specialize (IHf1 cod); desh.
    specialize (IHf2 _ Heqo).
    repeat desh; repeat desg; auto.
    now specialize (IHf2 x); desh.
Defined.

Lemma termD_Comp {f g dom cod} :
  termD dom cod (Comp f g) =
    match Term_cod dom g with
    | Some mid =>
      match termD dom mid g with
      | Some g' =>
        match termD mid cod f with
        | Some f' => Some (f' ∘ g')
        | None => None
        end
      | None => None
      end
    | None => None
    end.
Proof.
  unfold termD; simpl; intros.
  generalize dependent cod.
  generalize dependent dom.
  induction g; simpl; intros.
  - rewrite Term_cod_equation_1.
    rewrite Pos_eq_dec_refl.
    desg; desh; auto.
    now desg.
  - rewrite Term_cod_equation_2.
    unfold Term_cod_obligation_2.
    desg; repeat (cat; desh).
    + unfold Term_cod_obligation_1.
      desg; rewrite Heqo1; desg; auto.
        now inv Heqo0.
      now desh.
    + unfold Term_cod_obligation_1.
      now desg; desg; desh.
    + unfold Term_cod_obligation_1.
      now desg.
  - rewrite Term_cod_equation_3.
    unfold Term_cod_obligation_3.
    repeat desg;
    repeat desh; auto.
    + apply Term_cod_Some_inv in Heqo4.
      rewrite Heqo4 in Heqo2; inv Heqo2.
      apply Term_cod_Some_inv in Heqo5.
      rewrite Heqo5 in Heqo0; inv Heqo0.
      contradiction.
    + apply Term_cod_Some_inv in Heqo.
      rewrite Heqo in Heqo1; inv Heqo1.
      apply Term_cod_Some_inv in Heqo3.
      congruence.
    + apply Term_cod_Some_inv in Heqo.
      congruence.
Defined.

Lemma termD_Comp_impl {f g dom mid cod f' g'} :
  termD mid cod f = Some f'
    -> termD dom mid g = Some g'
    -> termD dom cod (Comp f g) = Some (f' ∘ g').
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Lemma termD_Comp_None_right {f g dom} :
  termD_work dom g = None
    -> termD_work dom (Comp f g) = None.
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Lemma termD_rect
      (P : Term arr_idx -> ∀ dom cod, objs dom ~> objs cod -> Type) :
     (∀ dom, termD dom dom Ident = Some id -> P Ident dom dom id)
  -> (∀ a dom cod f', arrs a = Some (dom; (cod; f'))
        -> termD dom cod (Morph a) = Some f'
        -> P (Morph a) dom cod f')
  -> (∀ f mid cod f', termD mid cod f = Some f'
        -> P f mid cod f'
        -> ∀ g dom g', termD dom mid g = Some g'
        -> P g dom mid g' -> P (Comp f g) dom cod (f' ∘ g'))
  -> ∀ f dom cod f', termD dom cod f = Some f'
       -> P f dom cod f'.
Proof.
  unfold termD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    apply X.
    simpl.
    now rewrite Pos_eq_dec_refl.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct (Pos.eq_dec x dom); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    inversion H0; subst.
    apply X0.
      now rewrite Heqo.
    simpl.
    rewrite Heqo.
    rewrite Pos_eq_dec_refl.
    now rewrite Pos_eq_dec_refl.
  - destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst; simpl in *.
    specialize (IHf1 x cod h0).
    specialize (IHf2 dom x h).
    rewrite Heqo0, Pos_eq_dec_refl in IHf1.
    rewrite Heqo, Pos_eq_dec_refl in IHf2.
    specialize (IHf1 eq_refl).
    specialize (IHf2 eq_refl).
    specialize (X1 f1 x cod h0).
    rewrite Heqo0, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf1 f2 dom h).
    rewrite Heqo, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf2).
    inversion H0; subst.
    apply X1.
Defined.

Definition option_ex_equiv {dom}
           (x y : option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) :=
  match x, y with
  | Some (cf; f), Some (cg; g) =>
    match eq_dec cf cg with
    | Specif.left H => f ≈ rew <- [fun x => _ ~> objs x] H in g
    | _ => False
    end
  | None, None => True
  | _, _ => False
  end.

Program Instance option_ex_Setoid {dom} :
  Setoid (option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) := {
  equiv := option_ex_equiv
}.
Next Obligation.
  unfold option_ex_equiv.
  equivalence.
  - destruct x; cat.
    now rewrite eq_dec_refl.
  - destruct x, y; cat; desh.
    now rewrite eq_dec_refl.
  - destruct x, y, z; cat; repeat desh.
      now transitivity e0.
    contradiction.
Qed.

Lemma app_eq_unit_type {A : Type} (x y : list A) (a : A) :
  (x ++ y)%list = [a]%list
    -> x = []%list ∧ y = [a]%list ∨ x = [a]%list ∧ y = []%list.
Proof.
  generalize dependent y.
  induction x; simpl; intuition idtac.
  inv H0.
  rewrite H3.
  apply List.app_eq_nil in H3.
  destruct H3.
  now subst; right.
Qed.

Lemma list_equiv_arrows `{Setoid A} (xs : list A) :
  list_equiv xs [] -> xs = nil.
Proof.
  induction xs; simpl; intros; tauto.
Qed.

Lemma arrows_nil {dom cod f f'} :
  arrows f = []%list
    -> termD_work dom f = Some (cod; f')
    -> ∃ H : dom = cod,
        f' ≈ rew [fun x => _ ~> objs x] H in @id cat (objs dom).
Proof.
  clear; intros.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl in *; intros.
  - inv H1.
    exists eq_refl.
    reflexivity.
  - desh.
  - repeat desh.
    apply List.app_eq_nil in H0.
    destruct H0.
    firstorder idtac.
    destruct (X _ _ _ Heqo); subst.
    destruct (X0 _ _ _ Heqo0); subst.
    exists eq_refl.
    rewrite e1, e2; cat.
Qed.

Lemma arrows_termD_nil {f} :
  arrows f = []%list
    -> ∀ dom, termD_work dom f ≈ Some (dom; id).
Proof.
  clear; intros.
  generalize dependent dom.
  induction f; simpl in *; intros; auto.
  - rewrite eq_dec_refl; cat.
  - discriminate.
  - apply List.app_eq_nil in H0.
    destruct H0.
    firstorder idtac.
    repeat desg.
    + specialize (X dom).
      specialize (X0 x).
      rewrite Heqo in X.
      rewrite Heqo0 in X0.
      simpl in X, X0.
      desh.
      rewrite eq_dec_refl in X.
      rewrite X, X0; cat.
    + destruct (arrows_nil H0 Heqo0); subst.
      destruct (arrows_nil H1 Heqo); subst.
      contradiction.
    + specialize (X0 x).
      rewrite Heqo0 in X0.
      simpl in X0.
      contradiction.
    + specialize (X dom).
      rewrite Heqo in X.
      simpl in X.
      contradiction.
Qed.

Definition unarrows `(fs : list A) : Term A :=
  List.fold_right (fun f rest => Comp (Morph f) rest) Ident fs.

Import ListNotations.

Fixpoint arrowsD_work dom (fs : list arr_idx) :
  option (∃ cod, objs dom ~> objs cod) :=
  match fs with
  | nil => Some (dom; @id _ (objs dom))
  | a :: fs =>
    match arrs a with
    | Some (x; (y; f)) =>
      match fs with
      | nil =>
        match Eq_eq_dec x dom with
        | Specif.left edom =>
          Some (y; rew [fun x => objs x ~> objs y] edom in f)
        | _ => None
        end
      | _ =>
        match arrowsD_work dom fs with
        | Some (mid; g) =>
          match Eq_eq_dec mid x with
          | Specif.left emid =>
            (* jww (2017-08-06): This associates the wrong way, which doesn't
               technically matter, but does make the normalized results look
               funny. At some point, the correct orientation should be
               done. *)
            Some (y; f ∘ rew [fun y => objs dom ~> objs y] emid in g)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Definition arrowsD dom cod (fs : list arr_idx) :
  option (objs dom ~> objs cod) :=
  match arrowsD_work dom fs with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint exprAD (e : Expr arr_idx) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => arrowsD x y (arrows f) ≈ arrowsD x y (arrows g)
  | And p q       => exprAD p ∧ exprAD q
  | Or p q        => exprAD p + exprAD q
  | Impl p q      => exprAD p -> exprAD q
  end.

Lemma arrowsD_rect'
      (P : ∀ dom cod, objs dom ~> objs cod -> list arr_idx -> Type) :
     Proper (forall_relation (fun dom =>
             forall_relation (fun cod =>
               @equiv _ (@homset cat (objs dom) (objs cod))
                 ==> eq ==> arrow)%signature)) P
  -> (∀ dom, P dom dom id [])
  -> (∀ f mid cod f', arrs f = Some (mid; (cod; f'))
        -> ∀ g dom g', arrowsD dom mid g = Some g'
        -> P dom mid g' g -> P dom cod (f' ∘ g') (f :: g))
  -> ∀ f dom cod f', arrowsD dom cod f = Some f'
       -> P dom cod f' f.
Proof.
  unfold arrowsD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    now apply X0.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct f.
      destruct (Pos.eq_dec x dom); [|discriminate].
      destruct (Pos.eq_dec x0 cod); [|discriminate].
      inversion H0; subst.
      simpl.
      specialize (X1 a dom cod h Heqo [] dom id).
      simpl in X1.
      rewrite Pos_eq_dec_refl in X1.
      specialize (X1 eq_refl (X0 _)).
      eapply X; eauto; cat.
    destruct (arrowsD_work dom (a0 :: f)) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x1 x); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    specialize (IHf dom x h0).
    rewrite Heqo0, Eq_eq_dec_refl in IHf.
    specialize (IHf eq_refl).
    specialize (X1 a x cod h Heqo (a0 :: f) dom h0).
    rewrite Heqo0, Eq_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf).
    inversion H0; subst.
    eapply X; eauto; cat.
Defined.

(**
Template for using this:

  pattern f, dom, cod, f', H0.
  refine (arrowsD_rect (fun dom cod f' f => _) _ _ _ _ _ _ _ _); intros.
  - proper.
  -
  -
*)

Lemma arrowsD_rect
      (P : ∀ (f : list arr_idx) dom cod (f' : objs dom ~> objs cod), Type) :
     Proper (eq ==>
             forall_relation (fun dom =>
             forall_relation (fun cod =>
               @equiv _ (@homset cat (objs dom) (objs cod))
                 ==> arrow)%signature)) P
  -> (∀ dom (H : arrowsD dom dom [] = Some id), P [] dom dom id)
  -> (∀ f mid cod f', arrs f = Some (mid; (cod; f'))
        -> ∀ g dom g' (H : arrowsD dom mid g = Some g'),
           P g dom mid g'
        -> ∀ fg' (Hfg : arrowsD dom cod (f :: g) = Some fg'),
           P (f :: g) dom cod fg')
  -> ∀ f dom cod f' (H : arrowsD dom cod f = Some f'),
       P f dom cod f'.
Proof.
  unfold arrowsD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    apply X0; simpl.
    now rewrite Pos_eq_dec_refl.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct f.
      destruct (Pos.eq_dec x dom); [|discriminate].
      destruct (Pos.eq_dec x0 cod); [|discriminate].
      inversion H0; subst.
      simpl.
      specialize (X1 a dom cod h Heqo [] dom id).
      simpl in X1.
      rewrite Pos_eq_dec_refl in X1.
      simpl in X0.
      specialize (X0 dom).
      rewrite Pos_eq_dec_refl in X0.
      specialize (X1 eq_refl (X0 eq_refl)).
      rewrite Heqo in X1.
      rewrite Pos_eq_dec_refl in X1.
      rewrite Pos_eq_dec_refl in X1.
      simpl in X1.
      eapply X; eauto; cat.
    destruct (arrowsD_work dom (a0 :: f)) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x1 x); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    specialize (IHf dom x h0).
    rewrite Heqo0, Eq_eq_dec_refl in IHf.
    specialize (IHf eq_refl).
    specialize (X1 a x cod h Heqo (a0 :: f) dom h0).
    rewrite Heqo0, Eq_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf).
    inversion H0; subst.
    apply X1; clear X1 X0 IHf.
    simpl in *.
    rewrite Heqo; clear Heqo.
    destruct (arrs a0) eqn:?; [|discriminate].
    destruct s, s.
    destruct f.
      destruct (Pos.eq_dec x0 dom); [|discriminate].
      subst.
      inversion Heqo0; subst; clear Heqo0.
      rewrite Pos_eq_dec_refl.
      eapply Eqdep_dec.inj_pair2_eq_dec in H3; [ | apply Eq_eq_dec ].
      subst.
      rewrite Pos_eq_dec_refl.
      reflexivity.
    destruct (arrowsD_work dom (a1 :: f)); [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x2 x0); [|discriminate].
    subst.
    inversion Heqo0; subst; clear Heqo0.
    rewrite Pos_eq_dec_refl.
    eapply Eqdep_dec.inj_pair2_eq_dec in H3; [ | apply Eq_eq_dec ].
    subst.
    rewrite Pos_eq_dec_refl.
    reflexivity.
Defined.

Ltac destruct_arrows :=
  lazymatch goal with
  | [ H : context[match arrs ?t with _ => _ end] |- _ ] =>
    destruct (arrs t) as [[? []]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : context[match arrowsD_work ?o ?t with _ => _ end] |- _ ] =>
    destruct (arrowsD_work o t) as [[]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : context[match termD_work ?o ?t with _ => _ end] |- _ ] =>
    destruct (termD_work o t) as [[]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
  | [ H : (?x; ?f) = (?y; ?g) |- _ ] => inversion H; subst
  end;
  try (equalities; let n := numgoals in guard n < 2);
  simpl_eq.

Theorem arrowsD_compose {xs ys dom cod f} :
  arrowsD_work dom (xs ++ ys) = Some (cod; f) ->
  ∃ mid g h, f ≈ g ∘ h ∧
    arrowsD_work mid xs = Some (cod; g) ∧
    arrowsD_work dom ys = Some (mid; h).
Proof.
  generalize dependent ys.
  generalize dependent cod.
  generalize dependent dom.
  induction xs; simpl; intros.
    simpl in H.
    exists cod.
    exists id.
    exists f.
    split; cat.
  destruct_arrows.
  destruct ys eqn:?.
    exists dom.
    exists f.
    exists id.
    rewrite app_nil_r in H0.
    split; cat.
    assert (
      match arrowsD_work dom (xs ++ a0 :: l) with
      | Some s =>
        match s with
        | (mid; g) =>
          match BinPos.Pos.eq_dec mid x with
          | Specif.left emid =>
            Some (x0; (h ∘ match emid with eq_refl => g end))
          | _ =>
            @None (@sigT obj_idx
                         (fun cod : obj_idx =>
                            @hom _ (objs dom) (objs cod)))
          end
        end
      | None => None
      end = Some (existT _ cod f)) by (destruct xs; auto).
  clear H0.
  destruct_arrows.
  specialize (IHxs _ _ _ _ Heqo0).
Admitted.
(*
  destruct_arrows.
  destruct xs.
  - simpl in a2.
    inversion a2; subst.
    exists _, h, x2.
    split.
    + rewrite a1.
      rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H2).
      cat.
    + split.
      * equalities.
      * simpl in b0.
        destruct_arrows.
  - exists _, (h ∘ x1), x2.
    split.
    + rewrite a1; cat.
    + split.
      * rewrite a2.
        equalities.
      * simpl in b0.
        destruct_arrows.
Qed.
*)

Theorem arrowsD_sound {p dom cod f} :
  arrowsD dom cod (arrows p) = Some f ->
  ∃ f', f ≈ f' ∧ termD dom cod p = Some f'.
Proof.
  unfold termD, arrowsD.
  generalize dependent cod.
  generalize dependent dom.
  induction p; simpl; intros; repeat equalities; simpl_eq.
  - now desh.
  - now desh.
  - repeat desh.
    now exists f.
  - repeat desh.
    pose proof (arrowsD_compose Heqo).
    destruct X, s, s, p, p.
    specialize (IHp1 x cod x0).
    rewrite e0 in IHp1.
    rewrite Eq_eq_dec_refl in IHp1.
    specialize (IHp1 (reflexivity _)).
    destruct IHp1, p.
    specialize (IHp2 dom x x1).
    rewrite e1 in IHp2.
    rewrite Eq_eq_dec_refl in IHp2.
    specialize (IHp2 (reflexivity _)).
    destruct IHp2, p.
    repeat desh.
    exists (x2 ∘ x3).
    split; auto.
    now rewrite e, e2, e4.
Qed.

Theorem arrowsD_compose_r {xs ys dom mid cod g h} :
  arrowsD_work mid xs = Some (cod; g) ->
  arrowsD_work dom ys = Some (mid; h) ->
  ∃ f, f ≈ g ∘ h ∧
    arrowsD_work dom (xs ++ ys) = Some (cod; f).
Proof.
  intros.
  generalize dependent ys.
  generalize dependent cod.
  generalize dependent dom.
  induction xs; simpl; intros.
    destruct_arrows; cat.
  repeat destruct_arrows.
  destruct (arrowsD_work mid xs) eqn:?;
  [|destruct xs; [|discriminate]; equalities].
  destruct s, xs; equalities.
    (* jww (2017-08-07): I have the feeling this branch of the proof is
       longer than it needs to be. *)
    inversion H; subst.
    simpl in Heqo0.
    inversion Heqo0; subst.
    specialize (IHxs dom h x1 h1 eq_refl _ H1).
    equalities.
    simpl in *.
    destruct ys; simpl in *.
      inversion H1; subst.
      equalities'; auto.
Admitted.
(*
      equalities'; auto.
      rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H5).
      exists g.
      simpl; cat.
    destruct_arrows.
    destruct ys.
      equalities.
      inversion H0; subst.
      inversion H1; subst.
      inversion H5; subst.
      equalities'; auto.
      rewrite Eq_eq_dec_refl; simpl.
      exists (h0 ∘ h2).
      simpl; cat.
      rewrite (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H6).
      reflexivity.
    destruct_arrows.
    equalities'; auto.
    destruct (Eq_eq_dec x4 x2); [|discriminate]; subst.
    inversion H0; subst.
    inversion H1; subst.
    inversion H5; subst.
    equalities'; auto.
    rewrite Eq_eq_dec_refl.
    exists (h0 ∘ (h2 ∘ h3)).
    simpl; cat.
    rewrite (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H6).
    reflexivity.
  destruct (IHxs dom h x h1 eq_refl _ H1); clear IHxs.
  destruct p.
  inversion H; simpl in *; subst.
  destruct_arrows.
  destruct (xs ++ ys) eqn:?.
    equalities'; auto.
    destruct (Eq_eq_dec x2 dom); [|discriminate].
    destruct e1.
    inversion H0; subst.
    inversion e0; subst.
    equalities'; auto.
    rewrite Eq_eq_dec_refl.
    exists (h0 ∘ h2).
    split; cat.
    rewrite <- comp_assoc.
    rewrite <- e.
    now rewrite (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H5).
  destruct_arrows; equalities.
  inversion H0; subst.
  inversion e0; subst.
  equalities'; auto.
  rewrite Eq_eq_dec_refl.
  exists (h0 ∘ (h2 ∘ h3)).
  simpl; cat.
  rewrite <- comp_assoc.
  rewrite (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H5).
  now rewrite <- e.
Qed.
*)

Theorem arrowsD_sound_r {p dom cod f} :
  termD dom cod p = Some f ->
  ∃ f', f ≈ f' ∧ arrowsD dom cod (arrows p) = Some f'.
Proof.
  unfold termD, arrowsD.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; desh.
  - exists id; intuition.
  - repeat desh.
    exists f; intuition.
  - repeat desh.
    specialize (IHp1 cod x e0).
    rewrite Heqo1 in IHp1.
    rewrite Eq_eq_dec_refl in IHp1.
    specialize (IHp1 (reflexivity _)).
    destruct IHp1, p.
    specialize (IHp2 x dom e).
    rewrite Heqo0 in IHp2.
    rewrite Eq_eq_dec_refl in IHp2.
    specialize (IHp2 (reflexivity _)).
    destruct IHp2, p.
    repeat desh.
    destruct (arrowsD_compose_r Heqo2 Heqo); cat.
      now rewrite e1, e3, p.
    rewrite H0.
    equalities.
Qed.

Lemma arrows_decide {x y f f' g g'} :
  termD x y f = Some f' ->
  termD x y g = Some g' ->
  list_beq Eq_eqb (arrows f) (arrows g) = true -> f' ≈ g'.
Proof.
  intros.
  destruct (arrowsD_sound_r H0), p.
  destruct (arrowsD_sound_r H1), p.
  apply list_beq_eq in H2.
    rewrite H2 in e0.
    rewrite e, e1.
    rewrite e0 in e2.
    now inversion_clear e2.
  apply Eq_eqb_eq.
Qed.

Lemma arrowsD_apply dom cod (f g : Term arr_idx) :
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  arrowsD dom cod (arrows f) ||| false = true ->
  arrowsD dom cod (arrows f) = arrowsD dom cod (arrows g) ->
  termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  destruct (arrowsD dom cod (arrows f)) eqn:?; [|discriminate].
  destruct (arrowsD_sound Heqo), p.
  rewrite e0; clear e0.
  red.
  symmetry in H2.
  apply arrowsD_sound in H2.
  equalities.
  rewrite H2.
  rewrite <- e0, <- e.
  reflexivity.
Qed.

Fixpoint exprD (e : Expr arr_idx) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Lemma exprAD_sound (e : Expr arr_idx) : exprAD e ↔ exprD e.
Proof.
  induction e; simpl; split; intros; firstorder auto.
  - destruct (arrowsD x y (arrows f)) eqn:?.
      destruct (arrowsD x y (arrows g)) eqn:?; [|contradiction].
      destruct (arrowsD_sound Heqo), p.
      destruct (arrowsD_sound Heqo0) ,p.
      now rewrite e0, e2, <- e, <- e1.
    destruct (arrowsD x y (arrows g)) eqn:?; [contradiction|].
    destruct (termD x y f) eqn:?.
      destruct (arrowsD_sound_r Heqo1), p.
      rewrite Heqo in e0.
      discriminate.
    destruct (termD x y g) eqn:?; auto.
    destruct (arrowsD_sound_r Heqo2), p.
    rewrite Heqo0 in e0.
    discriminate.
  - destruct (termD x y f) eqn:?.
      destruct (termD x y g) eqn:?; [|contradiction].
      destruct (arrowsD_sound_r Heqo), p.
      destruct (arrowsD_sound_r Heqo0), p.
      now rewrite e0, e2, <- e, <- e1.
    destruct (termD x y g) eqn:?; [contradiction|].
    destruct (arrowsD x y (arrows f)) eqn:?.
      destruct (arrowsD_sound Heqo1), p.
      rewrite Heqo in e0.
      discriminate.
    destruct (arrowsD x y (arrows g)) eqn:?; auto.
    destruct (arrowsD_sound Heqo2), p.
    rewrite Heqo0 in e0.
    discriminate.
Qed.

Lemma termD_arrows dom cod x :
  termD dom cod x ≈ arrowsD dom cod (arrows x).
Proof.
  destruct (termD _ _ _) eqn:?,
           (arrowsD _ _ _) eqn:?.
  - apply arrowsD_sound in Heqo0.
    destruct Heqo0; cat.
    f_equiv.
    rewrite Heqo in H0.
    inv H0.
    now symmetry.
  - apply arrowsD_sound_r in Heqo.
    destruct Heqo; cat.
    rewrite H0 in Heqo0.
    discriminate.
  - apply arrowsD_sound in Heqo0.
    destruct Heqo0; cat.
    rewrite H0 in Heqo.
    discriminate.
  - reflexivity.
Qed.

Lemma list_equiv_arr (xs ys : list arr_idx) : list_equiv xs ys -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs; simpl; intros; desh; intuition auto.
  rewrite a1.
  f_equal.
  now apply IHxs.
Qed.

Definition list_equiv_termD (x y : Term arr_idx) :
  list_equiv (arrows x) (arrows y)
    -> ∀ dom cod, termD dom cod x ≈ termD dom cod y.
Proof.
  intros.
  apply list_equiv_arr in X.
  rewrite !termD_arrows.
  now rewrite X.
Qed.

Program Instance termD_work_Proper {dom} :
  Proper (equiv ==> equiv) (@termD_work dom).
Next Obligation.
  repeat intro.
  pose proof (list_equiv_termD _ _ X).
  unfold termD in *.
  specialize (X0 dom).
  destruct (termD_work dom x) eqn:?; cat.
    specialize (X0 x0).
    rewrite Eq_eq_dec_refl in X0.
    desh; desh.
    simpl in X0.
    now rewrite eq_dec_refl.
  simpl.
  desg; auto.
  specialize (X0 x0).
  rewrite Eq_eq_dec_refl in X0.
  inv X0.
Qed.

Program Instance termD_Proper {dom cod} :
  Proper (equiv ==> equiv) (@termD dom cod).
Next Obligation.
  repeat intro.
  apply list_equiv_termD.
  exact X.
Qed.

(*
Import EqNotations.

Equations termD (dom cod : obj_idx) (e : Term arr_idx) :
  option (objs dom ~> objs cod) :=
  termD dom cod Ident <= eq_dec dom cod => {
    | Specif.left H =>
      Some (rew [fun x => _ ~> objs x] H in @id cat (objs dom));
    | _ => None
  };
  termD dom cod (Morph a) <= arrs a => {
    | Some (existT d (existT c f)) <= eq_dec dom d => {
        | Specif.left H1 <= eq_dec cod c => {
            | Specif.left H2 =>
              Some (rew <- [fun x => objs x ~> _] H1 in
                    rew <- [fun x => _ ~> objs x] H2 in f);
            | _ => None
          };
        | _ => None
      };
    | _ => None
  };
  termD dom cod (Comp f g) <= Term_cod dom g => {
    | Some mid <= termD mid cod f => {
        | Some f' <= termD dom mid g => {
            | Some g' => Some (f' ∘ g');
            | _ => None
          };
        | _ => None
      };
    | _ => None
  }.
*)

Definition option_compose {C : Category} {dom mid cod}
           (f : option (@hom C mid cod))
           (g : option (@hom C dom mid)) : option (@hom C dom cod) :=
  match f, g with
  | Some f, Some g => Some (f ∘ g)
  | _, _ => None
  end.

Require Import Category.Monad.Kleisli.

Program Instance optionM : @Monad Coq optionF := {
  ret := @Some;
  join := fun _ x =>
    match x with
    | Some (Some x) => Some x
    | _ => None
    end
}.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
  destruct o; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
Qed.

Program Instance optional_compose_Proper {C : Category} {dom mid cod} :
  Proper (equiv ==> equiv ==> equiv) (@option_compose C dom mid cod).
Next Obligation.
  repeat intro.
  destruct x, x0, y, y0; simpl; auto.
  now rewrite X, X0.
Qed.

(** opt_arrs is a category that combines thin and thick morphisms. *)

Program Definition opt_arrs {C : Category} : Category := {|
  obj := C;
  hom := fun dom cod => option (@hom C dom cod);
  homset := fun _ _ => option_setoid;
  id := fun _ => Some id;
  compose := @option_compose C
|}.
Next Obligation. destruct f; cat. Qed.
Next Obligation. destruct f; simpl; cat. Qed.
Next Obligation. destruct f, g, h; simpl; cat. Qed.
Next Obligation. destruct f, g, h; simpl; cat. Qed.

Lemma option_compose_Comp {x z f g h} :
  (∃ y, option_compose (termD y z f) (termD x y g) = Some h)
    ↔ termD x z (Comp f g) = Some h.
Proof.
  unfold termD; induction f; simpl; split; intros.
  - repeat desh; repeat desg; auto.
  - repeat desh; repeat desg; auto.
    exists z.
    equalities.
  - repeat desh; simpl in *; repeat desg; auto; inv Heqo1.
      inv e.
      now equalities; subst.
    contradiction.
  - repeat desh; repeat desg; auto.
    exists x0.
    repeat equalities.
  - repeat desh; repeat desg; auto.
  - do 6 desh.
    exists x0.
    rewrite Heqo, Heqo2.
    do 2 equalities'; auto.
    now equalities.
Qed.

Lemma option_compose_Comp_None {x y z f g} :
  option_compose (termD y z f) (termD x y g) = None
    ↔ termD y z f = None ∨ termD x y g = None.
Proof.
  split; intros.
    destruct (termD y z f), (termD x y g); intuition idtac.
    discriminate.
  destruct H0; rewrite e; simpl; auto.
  destruct (termD y z f); auto.
Qed.

(* Program Instance Denote : Terms arr_idx ⟶ Coq := { *)
(*   fobj := fun _ => arr_idx; *)
(*   fmap := fun dom cod x => arrows x *)
(* }. *)

Program Instance Denote : Terms arr_idx ⟶ @opt_arrs cat := {
  fobj := objs;
  fmap := termD
}.
Next Obligation. now rewrite termD_Ident. Qed.
Next Obligation.
  rewrite termD_Comp.
  desg; repeat desh; repeat desg; auto.
  - pose proof (fst option_compose_Comp (y; Heqo3)).
    rewrite termD_Comp in H0.
    now repeat desh.
  - apply option_compose_Comp_None in Heqo3.
    (* jww (2018-03-09): This may not be needed. *)
Admitted.

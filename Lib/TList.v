(** A theory of type-aligned lists, using the Coq-Equations plugin *)

Require Export Coq.Classes.CRelationClasses.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Inductive tlist' {A :Type} {B : A → A → Type} (k : A) : A -> Type :=
| tnil : tlist' k
| tcons : ∀ i j : A, B i j -> tlist' j -> tlist' i.

Definition tlist {A : Type} (B : A → A → Type) (i j : A) := @tlist' A B j i.

Derive Signature NoConfusion Subterm for tlist'.
Next Obligation.
  apply Transitive_Closure.wf_clos_trans.
  intros a.
  destruct a as [? pr0].
  (* destruct a as [[] pr0]. *)
  simpl in pr0.
  induction pr0.
  - (* tnil *)
    constructor.
    intros y H.
    inversion H; subst; clear H.
  - (* tcons *)
    constructor. intros [ l m] pr1 . simpl in *.
    dependent induction pr1.
    assumption.
Defined.

Arguments tnil {A B k}.
Arguments tcons {A B k} i {j} x xs.

Notation "x ::: xs" := (tcons _ x xs) (at level 60, right associativity).

Section TList.

Context {A : Type}.
Context {B : A → A → Type}.

Fixpoint tlist_length {i j} (xs : tlist B i j) : nat :=
  match xs with
  | tnil => 0
  | tcons x _ xs => 1 + tlist_length xs
  end.

Definition tlist_singleton {i j} (x : B i j) : tlist B i j := x ::: tnil.

Equations tlist_rcons {i j k} (xs : tlist B i j) (y : B j k) : tlist B i k :=
  tlist_rcons tnil y := y ::: (@tnil _ B k);
  tlist_rcons (@tcons _ _ _ _ _ x xs) y := x ::: tlist_rcons xs y.
      
Equations tlist_app {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist B i k :=
  tlist_app tnil ys := ys;
  tlist_app xs tnil := xs;
  tlist_app (@tcons _ _ _ _ _ x xs) ys := x ::: tlist_app xs ys.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Equations tlist_uncons {i j} (xs : tlist B i j) :
  option { z : A & B i z * tlist B z j }%type :=
  tlist_uncons tnil := None;
  tlist_uncons (@tcons _ _ _ _ _ x xs) := Some (_; (x, xs)).

Equations tlist_map {i j A' C} {f : A → A'}
          (g : ∀ i j : A, B i j → C (f i) (f j))
          (xs : tlist B i j) : tlist C (f i) (f j) :=
  tlist_map _ tnil := tnil;
  tlist_map g (@tcons _ _ _ _ _ x xs) := g _ _ x ::: tlist_map g xs.

Equations tlist_mapv {i j C}
          (g : ∀ i j : A, B i j → C)
          (xs : tlist B i j) : list C :=
  tlist_mapv _ tnil := nil;
  tlist_mapv g (@tcons _ _ _ _ _ x xs) := g _ _ x :: tlist_mapv g xs.

Equations tlist_head {i j} (xs : tlist B i j) :
  option { z : A & B i z }%type :=
  tlist_head tnil := None;
  tlist_head (@tcons _ _ _ _ _ x xs) := Some (_; x).

Equations tlist_tail {i j} (xs : tlist B i j) :
  option { z : A & tlist B z j }%type :=
  tlist_tail tnil := None;
  tlist_tail (@tcons _ _ _ _ _ x xs) := Some (_; xs).

Equations tlist_init {i j} (xs : tlist B i j) :
  option { z : A & tlist B i z }%type :=
  tlist_init tnil := None;
  tlist_init (@tcons _ _ _ _ _ x xs) with tlist_init xs := {
    | None => Some (_; tnil);
    | Some (existT ys) => Some (_; (x ::: ys))
  }.

Equations tlist_last {i j} (xs : tlist B i j) :
  option { z : A & B z j }%type :=
  tlist_last tnil := None;
  tlist_last (@tcons _ _ _ _ _ x xs) with xs := {
    | tnil => Some (_; x);
    | @tcons _ _ _ _ _ y ys => tlist_last ys
  }.

Equations tlist_rev (flip : ∀ x y : A, B x y → B y x)
          {i j} (xs : tlist B i j) : tlist B j i :=
  tlist_rev flip tnil := tnil;
  tlist_rev flip (@tcons _ _ _ _ _ x xs) :=
    tlist_rev flip xs +++ flip _ _ x ::: tnil.

Fixpoint tlist_concat {i j} (xs : tlist (tlist B) i j) : tlist B i j :=
  match xs with
  | tnil => tnil
  | tcons _ x xs => x +++ tlist_concat xs
  end.

Context `{AE : EqDec A}.
Context `{BE : ∀ i j, EqDec (B i j)}.

Import EqNotations.

Equations tlist_eq_dec {i j : A} (x y : tlist B i j) : {x = y} + {x ≠ y} :=
  tlist_eq_dec tnil tnil := left eq_refl;
  tlist_eq_dec tnil _ := in_right;
  tlist_eq_dec _ tnil := in_right;
  tlist_eq_dec (@tcons _ _ _ _ m x xs) (@tcons _ _ _ _ o y ys)
  with @eq_dec _ AE m o := {
      | left H with @eq_dec _ (BE _ _) x (rew <- [fun x => B _ x] H in y) := {
          | left _ with tlist_eq_dec xs (rew <- [fun x => tlist B x _] H in ys) := {
             | left _ => left _;
             | _ => in_right
            };
          | _ => in_right
        };
      | _ => in_right
    }.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [ assumption |apply eq_dec].
Defined.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  assumption.
Defined.

#[export] Program Instance tlist_EqDec {i j} : @EqDec (tlist B i j) := {
  eq_dec := tlist_eq_dec
}.

Lemma tlist_app_tnil_l {i j} (xs : tlist B i j) :
  tnil +++ xs = xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_cons {i j k} (x : B i j) (xs : tlist B j k) :
  x ::: xs = (x ::: tnil) +++ xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_comm_cons {i j k l} (x : B i j)
      (xs : tlist B j k) (ys : tlist B k l) :
  x ::: (xs +++ ys) = (x ::: xs) +++ ys.
Proof. now destruct xs, ys. Qed.

Lemma tlist_app_assoc {i j k l}
      (xs : tlist B i j) (ys : tlist B j k) (zs : tlist B k l) :
  (xs +++ ys) +++ zs = xs +++ (ys +++ zs).
Proof.
  induction xs; auto.
  now rewrite <- !tlist_app_comm_cons, IHxs.
Qed.

Context `{∀ i j, Setoid (B i j)}.

Equations tlist_equiv {i j : A} (x y : tlist B i j) : Type :=
  tlist_equiv tnil tnil := True;
  tlist_equiv tnil _ := False;
  tlist_equiv _ tnil := False;
  tlist_equiv (@tcons _ _ _ _ m x xs) (@tcons _ _ _ _ o y ys)
    with eq_dec m o := {
      | left H =>
         equiv x (rew <- [fun x => B _ x] H in y) *
         tlist_equiv xs (rew <- [fun x => tlist B x _] H in ys);
      | right _ => False
    }.

#[export] Program Instance tlist_equiv_Equivalence {i j} :
  Equivalence (@tlist_equiv i j).
Next Obligation.
  repeat intro.
  induction x; simpl.
  - constructor.
  - rewrite tlist_equiv_equation_4.
    unfold tlist_equiv_clause_4.
    rewrite EqDec.peq_dec_refl.
    split.
    + apply Equivalence_Reflexive.
    + apply IHx.
Qed.
Next Obligation.
  intros x y X.
  induction x; simpl.
  - dependent elimination y as [tnil]; auto.
  - dependent elimination y as [tcons _ y ys]; auto.
    rewrite tlist_equiv_equation_4 in *.
    destruct (eq_dec j0 _); [|contradiction].
    subst.
    rewrite EqDec.peq_dec_refl.
    destruct X.
    split.
    + now apply Equivalence_Symmetric.
    + apply IHx, t.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
  - dependent elimination y as [tnil]; auto.
  - dependent elimination y as [tcons _ y ys]; auto.
    simpl; intros.
    dependent elimination z as [tcons _ z zs]; auto.
    rewrite tlist_equiv_equation_4 in *.
    destruct (eq_dec j0 _); [|contradiction].
    destruct (eq_dec _ _); [|contradiction].
    subst.
    rewrite EqDec.peq_dec_refl.
    destruct X, X0.
    split.
    + transitivity y; auto.
    + eapply IHx; eauto.
Qed.

#[export] Program Instance tlist_Setoid {i j} : Setoid (tlist B i j) := {
  equiv := tlist_equiv;
  setoid_equiv := tlist_equiv_Equivalence;
}.

#[export] Program Instance tlist_cons_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@tcons A B i j k).
Next Obligation.
  repeat intro.
  simpl in *.
  rewrite tlist_equiv_equation_4.
  now rewrite EqDec.peq_dec_refl.
Qed.

#[export] Program Instance tlist_app_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@tlist_app i j k).
Next Obligation.
  repeat intro.
  generalize dependent k.
  induction x; intros; dependent elimination y.
  - rewrite !tlist_app_tnil_l.
    exact X0.
  - contradiction.
  - contradiction.
  - rewrite <- !tlist_app_comm_cons.
    rewrite tlist_equiv_equation_4 in *.
    destruct (eq_dec j0 j1); [|contradiction].
    subst.
    destruct X.
    split; auto.
    apply IHx.
    + exact t0.
    + exact X0.
Qed.

End TList.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Section TListProofs.

Context {A : Type}.
Context {B : A → A → Type}.

Lemma tlist_app_tnil_r {i j} (xs : tlist B i j) :
  xs +++ tnil = xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_length {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_length (xs +++ ys) = (tlist_length xs + tlist_length ys)%nat.
Proof.
  induction xs; auto.
  rewrite <- tlist_app_comm_cons; simpl.
  now rewrite IHxs.
Qed.

Lemma tlist_concat_tnil {i} : tlist_concat tnil = @tnil A B i.
Proof. reflexivity. Qed.

Lemma tlist_concat_tcons {i j k} (x : tlist B i j) (xs : tlist (tlist B) j k) :
  tlist_concat (x ::: xs) = x +++ tlist_concat xs.
Proof. reflexivity. Qed.

End TListProofs.

Lemma tlist_concat_app {A : Type} {B : A → A → Type} {i j k}
      (xs : tlist (tlist B) i j) (ys : tlist (tlist B) j k) :
  tlist_concat (xs +++ ys) = tlist_concat xs +++ tlist_concat ys.
Proof.
  induction xs; auto.
  rewrite <- tlist_app_comm_cons; simpl.
  rewrite IHxs.
  now rewrite tlist_app_assoc.
Qed.

Section TListProofsRev.

Context {A : Type}.
Context {B : A → A → Type}.

Variables flip : ∀ x y : A, B x y → B y x.

Lemma tlist_rev_unit {i j k} (xs : tlist B i j) (x : B j k) :
  tlist_rev flip (xs +++ x ::: tnil) = flip _ _ x ::: tlist_rev flip xs.
Proof.
  induction xs; auto; simpl.
  rewrite <- tlist_app_comm_cons; simpl.
  rewrite tlist_rev_equation_2.
  now rewrite IHxs.
Qed.

Lemma tlist_rev_app_distr {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_rev flip (xs +++ ys) = tlist_rev flip ys +++ tlist_rev flip xs.
Proof.
  generalize dependent i.
  induction xs; simpl; intros; auto.
  - rewrite tlist_app_tnil_l.
    rewrite tlist_rev_equation_1.
    now rewrite tlist_app_tnil_r.
  - rewrite <- tlist_app_comm_cons; simpl.
    rewrite !tlist_rev_equation_2.
    rewrite IHxs.
    now rewrite <- tlist_app_assoc.
Qed.

Hypothesis flip_involutive : ∀ (i j : A) (x : B i j),
  flip _ _ (flip _ _ x) = x.

Lemma tlist_rev_involutive {i j} (xs : tlist B i j) :
  tlist_rev flip (tlist_rev flip xs) = xs.
Proof using A B flip flip_involutive.
  induction xs; simpl; auto.
  rewrite tlist_rev_equation_2.
  rewrite tlist_rev_app_distr.
  rewrite IHxs.
  rewrite tlist_rev_equation_2.
  rewrite tlist_rev_equation_1.
  rewrite flip_involutive.
  rewrite tlist_app_equation_1.
  now rewrite <- tlist_app_cons.
Qed.

Lemma tlist_rev_length {i j} (xs : tlist B i j) :
  tlist_length (tlist_rev flip xs) = tlist_length xs.
Proof.
  induction xs; auto; simpl.
  rewrite tlist_rev_equation_2.
  rewrite tlist_app_length, IHxs; simpl.
  apply PeanoNat.Nat.add_1_r.
Qed.

End TListProofsRev.

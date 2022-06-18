Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

(** A theory of type-aligned lists, using the Coq-Equations plugin *)

Require Import Coq.Bool.Bool.

Open Scope lazy_bool_scope.

Require Import Coq.Classes.CEquivalence.
Require Export Coq.Classes.CRelationClasses.
Require Import Coq.Classes.CMorphisms.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.

Inductive tlist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | tnil : forall i : A, tlist B i i
  | tcons : forall i j k : A, B i j -> tlist B j k -> tlist B i k.

Derive Signature for tlist.
Derive NoConfusion for tlist.
Derive Subterm for tlist.
Next Obligation.
apply Transitive_Closure.wf_clos_trans.
intros a.
destruct a as [[] pr0].
simpl in pr0.
induction pr0.
- (* tnil *)
  constructor.
  intros y H.
  inversion H; subst; clear H.
- (* tcons *)
  constructor.
  intros [[l m] pr1] H.
  simpl in *.
  dependent induction H.
  assumption.
Defined.

Arguments tnil {A B i}.
Arguments tcons {A B i} j {k} x xs.

Notation "x ::: xs" := (tcons _ x xs) (at level 60, right associativity).

Section TList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Fixpoint tlist_length {i j} (xs : tlist B i j) : nat :=
  match xs with
  | tnil => 0
  | tcons x _ xs => 1 + tlist_length xs
  end.

(*
The Fixpoint version does not work, as might be expected, but fails with
this rather confusing error:

  Error: Illegal application:
  The term "@eq" of type "forall A : Type, A -> A -> Prop"
  cannot be applied to the terms
   "A" : "Type"
   "k'" : "A"
   "ys0" : "tlist B j'0 k'"
  The 3rd term has type "tlist B j'0 k'" which should be coercible to "A".

Function also fails, but due to the missing rewrites that are needed to
align the values properly after matching has discovered the equalities.

Program Fixpoint tlist_app {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist B i k :=
  match xs, ys with
  | tnil, ys => ys
  | xs, tnil => xs
  | tcons _ x xs, ys => x ::: @tlist_app _ _ _ xs ys
  end.
*)

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

Equations tlist_map {i j A' C} {f : A -> A'}
          (g : forall i j : A, B i j -> C (f i) (f j))
          (xs : tlist B i j) : tlist C (f i) (f j) :=
  tlist_map _ tnil := tnil;
  tlist_map g (@tcons _ _ _ _ _ x xs) := g _ _ x ::: tlist_map g xs.

Equations tlist_mapv {i j C}
          (g : forall i j : A, B i j -> C)
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

Equations tlist_rev (flip : forall x y : A, B x y -> B y x)
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
Context `{BE : forall i j, EqDec (B i j)}.

Import EqNotations.

(* Returns true if [xs] is a sublist of [ys] *)
(*
Equations tlist_incl
          {j k} (xs : tlist B j k)
          {i l} (ys : tlist B i l) : bool :=
  tlist_incl (@tnil _ _ j) (@tnil _ _ i)
    with eq_dec j i := {
      | left _ => true;
      | right _ => false
    };
  tlist_incl (@tnil _ _ j) (@tcons _ _ i _ _ y ys)
    with eq_dec j i := {
      | left _ => true;
      | right _ => tlist_incl tnil ys
    };
  tlist_incl _ tnil := false;
  tlist_incl (@tcons _ _ j m _ x xs) (@tcons _ _ i o _ y ys)
    with (eq_dec j i, eq_dec m o) := {
      | pair (left H1) (left H2) =>
        (eq_dec x (rew <- [fun y => B _ y] H2 in
                   rew <- [fun x => B x _] H1 in y)
           &&& tlist_incl xs ys)
          ||| tlist_incl (x ::: xs) ys;
      | _ => tlist_incl (x ::: xs) ys
    }.
*)

Equations tlist_eq_dec {i j : A} (x y : tlist B i j) : {x = y} + {x ≠ y} :=
  tlist_eq_dec tnil tnil := left eq_refl;
  tlist_eq_dec tnil _ := in_right;
  tlist_eq_dec _ tnil := in_right;
  tlist_eq_dec (@tcons _ _ _ m _ x xs) (@tcons _ _ _ o _ y ys)
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
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  assumption.
Defined.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  assumption.
Defined.

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

Context `{forall i j, Setoid (B i j)}.

Equations tlist_equiv {i j : A} (x y : tlist B i j) : Type :=
  tlist_equiv tnil tnil := True;
  tlist_equiv tnil _ := False;
  tlist_equiv _ tnil := False;
  tlist_equiv (@tcons _ _ _ m _ x xs) (@tcons _ _ _ o _ y ys)
    with eq_dec m o := {
      | left H =>
         equiv x (rew <- [fun x => B _ x] H in y) *
         tlist_equiv xs (rew <- [fun x => tlist B x _] H in ys);
      | right _ => False
    }.

Global Program Instance tlist_equiv_Equivalence {i j} :
  Equivalence (@tlist_equiv i j).
Next Obligation.
  repeat intro.
  induction x; simpl.
    constructor.
  rewrite tlist_equiv_equation_4.
  unfold tlist_equiv_clause_4.
  rewrite EqDec.peq_dec_refl.
  split.
    apply Equivalence_Reflexive.
  apply IHx.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
    dependent elimination y as [tnil]; auto.
  dependent elimination y as [tcons _ y ys]; auto.
  rewrite tlist_equiv_equation_4 in *.
  destruct (eq_dec j _); [|contradiction].
  subst.
  rewrite EqDec.peq_dec_refl.
  destruct X.
  split.
    now apply Equivalence_Symmetric.
  apply IHx, t.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
    dependent elimination y as [tnil]; auto.
  dependent elimination y as [tcons _ y ys]; auto.
  simpl; intros.
  dependent elimination z as [tcons _ z zs]; auto.
  rewrite tlist_equiv_equation_4 in *.
  destruct (eq_dec j _); [|contradiction].
  destruct (eq_dec _ _); [|contradiction].
  subst.
  rewrite EqDec.peq_dec_refl.
  destruct X, X0.
  split.
    transitivity y; auto.
  eapply IHx; eauto.
Qed.

Global Program Instance tlist_Setoid {i j} : Setoid (tlist B i j) := {
  equiv := tlist_equiv;
  setoid_equiv := tlist_equiv_Equivalence;
}.

Global Program Instance tlist_cons_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@tcons A B i j k).
Next Obligation.
  repeat intro.
  simpl in *.
  rewrite tlist_equiv_equation_4.
  now rewrite EqDec.peq_dec_refl.
Qed.

Global Program Instance tlist_app_respects {i j k} :
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
    destruct (eq_dec j j0); [|contradiction].
    subst.
    destruct X.
    split; auto.
    apply IHx.
      exact t0.
    exact X0.
Qed.

Global Program Instance tlist_EqDec {i j} : @EqDec (tlist B i j) := {
  eq_dec := tlist_eq_dec
}.

End TList.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Section TListProofs.

Context {A : Type}.
Context {B : A -> A -> Type}.

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

Lemma tlist_concat_app {A : Type} {B : A -> A -> Type} {i j k}
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
Context {B : A -> A -> Type}.

Variables flip : forall x y : A, B x y -> B y x.

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
    rewrite tlist_app_tnil_l.
    rewrite tlist_rev_equation_1.
    now rewrite tlist_app_tnil_r.
  rewrite <- tlist_app_comm_cons; simpl.
  rewrite !tlist_rev_equation_2.
  rewrite IHxs.
  now rewrite <- tlist_app_assoc.
Qed.

Hypothesis flip_involutive : forall (i j : A) (x : B i j),
  flip _ _ (flip _ _ x) = x.

Lemma tlist_rev_involutive {i j} (xs : tlist B i j) :
  tlist_rev flip (tlist_rev flip xs) = xs.
Proof.
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

Section TListProofsInj.

(* Dependending on the choice of A, this can be either
      Eqdep.EqdepTheory.inj_pair2  (incurs axiom)
   or Eqdep_dec.inj_pair2_eq_dec   (when A is decidable)
*)
Hypothesis inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    (p; x) = (p; y) -> x = y.

Context {A : Type}.
Context {B : A -> A -> Type}.

Lemma tlist_cons_uncons
      {i m j} (xs : tlist B i j) (y : B i m) ys :
  tlist_uncons xs = Some (_; (y, ys)) -> xs = y ::: ys.
Proof.
  destruct xs; simpl; intros.
    inversion H.
  inversion H; subst; clear H.
  apply inj_pair2 in H2; auto.
  apply inj_pair2 in H3; auto.
  now rewrite H2, H3.
Qed.

End TListProofsInj.

Section Sublist.

Context {A : Type}.
Context {B : A -> A -> Type}.

Context `{EqDec A}.
Context `{forall i j, EqDec (B i j)}.

Import EqNotations.

Fixpoint tlist_find_sublist
         {j k} (xs : tlist B j k)
         {i l} (ys : tlist B i l) : option (tlist B i j * tlist B k l) :=
  match xs, ys with
  | @tnil _ _ j, @tnil _ _ i =>
    match eq_dec j i with
    | left H => Some (rew [fun x => tlist B x _] H in tnil,
                      rew [fun x => tlist B _ x] H in tnil)
    | _ => None
    end
  | @tnil _ _ j, @tcons _ _ k n l y ys =>
    match eq_dec j k with
    | left H =>
      Some (rew [fun x => tlist B x _] H in tnil,
            rew <- [fun x => tlist B x _] H in (y ::: ys))
    | _ =>
      match tlist_find_sublist tnil ys with
      | None => None
      | Some (ys, zs) => Some (y ::: ys, zs)
      end
    end
  | _, tnil => None
  | @tcons _ _ j m k x xs, @tcons _ _ i o l y ys =>
    match eq_dec j i, eq_dec m o with
    | left H1, left H2 =>
      match eq_dec x (rew <- [fun x => B x _] H1 in
                      rew <- [fun x => B _ x] H2 in y) with
      | left _ =>
        match tlist_find_sublist xs ys with
        | Some (bs, cs) =>
          match tlist_eq_dec bs (rew <- [fun a => tlist B _ a] H2 in tnil) with
          | left _ =>
            Some (rew [fun a => tlist B a _] H1 in tnil, cs)
          | _ =>
            match tlist_find_sublist (x ::: xs) ys with
            | None => None
            | Some (pair ys zs) =>
              Some (y ::: ys, zs)
            end
          end
        | _ =>
          match tlist_find_sublist (x ::: xs) ys with
          | None => None
          | Some (pair ys zs) =>
            Some (y ::: ys, zs)
          end
        end
      | _ =>
        match tlist_find_sublist (x ::: xs) ys with
        | None => None
        | Some (pair ys zs) =>
          Some (y ::: ys, zs)
        end
      end
    | _, _ =>
      match tlist_find_sublist (x ::: xs) ys with
      | None => None
      | Some (pair ys zs) =>
        Some (y ::: ys, zs)
      end
    end
  end.

End Sublist.

Section SublistProofsInj.

(* Dependending on the choice of A, this can be either
      Eqdep.EqdepTheory.inj_pair2  (incurs axiom)
   or Eqdep_dec.inj_pair2_eq_dec   (when A is decidable)
*)
Hypothesis inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    (p; x) = (p; y) -> x = y.

Context {A : Type}.
Context {B : A -> A -> Type}.

Context `{EqDec A}.
Context `{forall i j, EqDec (B i j)}.

Import EqNotations.

Open Scope signature_scope.

Ltac cleanup H IHf Heqo :=
  inversion H; subst; clear H;
  specialize (IHf _ _ _ _ _ Heqo); subst;
  now rewrite <- !tlist_app_comm_cons.

Lemma tlist_find_sublist_app
      {j k} (g : tlist B j k)
      {i l} (f : tlist B i l) {pre post} :
  tlist_find_sublist g f = Some (pre, post)
      -> f = pre +++ g +++ post.
Proof.
  intros.
  generalize dependent k.
  generalize dependent j.
  induction f; intros; simpl in H1.
  - destruct g.
      destruct (eq_dec i0 i); [|discriminate].
      inversion H1; now subst.
    discriminate.
  - destruct g.
      destruct (eq_dec i0 i); subst.
        inversion H1; now subst.
      destruct (tlist_find_sublist _ _) eqn:?; [|discriminate].
      destruct p.
      now cleanup H1 IHf Heqo.
    destruct (eq_dec i0 i); subst. {
      destruct (eq_dec j0 j); subst. {
        destruct (eq_dec _ _). {
          rewrite e.
          destruct (tlist_find_sublist g f) eqn:?. {
            destruct p.
            destruct (tlist_eq_dec _ _).
              now cleanup H1 IHf Heqo.
            clear Heqo.
            destruct (tlist_find_sublist (_ ::: g) f) eqn:?; [|discriminate].
            destruct p.
            now cleanup H1 IHf Heqo.
          }
          destruct (tlist_find_sublist (_ ::: g) f) eqn:?; [|discriminate].
          destruct p.
          now cleanup H1 IHf Heqo0.
        }
        destruct (tlist_find_sublist (_ ::: g) f) eqn:?; [|discriminate].
        destruct p.
        now cleanup H1 IHf Heqo.
      }
      destruct (tlist_find_sublist (_ ::: g) f) eqn:?; [|discriminate].
      destruct p.
      now cleanup H1 IHf Heqo.
    }
    destruct (tlist_find_sublist (_ ::: g) f) eqn:?; [|discriminate].
    destruct p.
    now cleanup H1 IHf Heqo.
Qed.

End SublistProofsInj.

Definition nat_triple (i j : nat) : Type := ((nat * nat) * nat)%type.

Open Scope nat_scope.

Definition my_list : tlist nat_triple 0 4 :=
  tcons 1 ((0, 1), 100)
        (tcons 2 ((1, 2), 200)
               (tcons 3 ((2, 3), 300)
                      (tcons 4 ((3, 4), 400)
                             tnil))).

Require Import Coq.Arith.EqNat.

Definition nat_equiv (i j : nat) (x y : nat_triple i j) : Type :=
  match x, y with
    (_, a), (_, b) => a = b
  end.

#[global]
Program Instance nat_equivalence {i j} : Equivalence (nat_equiv i j).
Next Obligation.
  repeat intro.
  destruct x; simpl; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct x, y; simpl; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct x, y, z; simpl in *; subst; auto.
Qed.

#[global]
Program Instance nat_Setoid {i j} : Setoid (nat_triple i j) := {
  equiv := nat_equiv i j;
  setoid_equiv := nat_equivalence
}.

Example tlist_find_sublist_nat_ex1 :
  ∀ H : ∀ i j : nat, EqDec (nat_triple i j),
  @tlist_find_sublist
    nat nat_triple PeanoNat.Nat.eq_dec _
    1 3 (tcons 2 ((1, 2), 200) (tcons 3 ((2, 3), 300) tnil))
    0 4 my_list
    = Some (((0, 1, 100) ::: tnil), ((3, 4, 400) ::: tnil)).
Proof.
  intros; simpl; simpl_eq.
  now rewrite !EqDec.peq_dec_refl.
Qed.

Reserved Infix "<+>" (at level 42, right associativity).

Class IMonoid {A : Type} (B : A -> A -> Type) := {
  imempty {i : A} : B i i;
  imappend {i j k : A} : B i j -> B j k -> B i k
    where "x <+> y" := (imappend x y);

  imempty_left {i j} {x : B i j} : imempty <+> x = x;
  imempty_right {i j} {x : B i j} : x <+> imempty = x;
  imappend_assoc {i j k l} {x : B i j} {y : B j k} {z : B k l} :
    (x <+> y) <+> z = x <+> (y <+> z)
}.

Infix "<+>" := imappend (at level 42, right associativity).

#[global]
Instance tlist_IMonoid {A} {B : A -> A -> Type} : IMonoid (tlist B) := {
  imempty := @tnil A B;
  imappend := @tlist_app A B;
  imempty_left := @tlist_app_tnil_l A B;
  imempty_right := @tlist_app_tnil_r A B;
  imappend_assoc := @tlist_app_assoc A B
}.

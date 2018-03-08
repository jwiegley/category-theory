(** A theory of type-aligned lists, using the Coq-Equations plugin *)

Require Import Coq.Bool.Bool.

Open Scope lazy_bool_scope.

Require Import Coq.Classes.CEquivalence.
Require Export Coq.Classes.CRelationClasses.
Require Import Coq.Classes.CMorphisms.

Open Scope equiv_scope.

Class EquivDec {A} {B : A -> A -> Type} {i j}
      (R : crelation (B i j)) `{Equivalence _ R} := {
  equiv_dec : forall (x y : B i j), (x === y) + (x =/= y)
}.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Notation "( x ; y )" := (existT _ x y) (at level 0).

Inductive tlist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | tnil : forall i : A, tlist B i i
  | tcons : forall (i j k : A) (x : B i j) (xs : tlist B j k), tlist B i k.

Derive Signature Subterm for tlist.

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
  tlist_app (tcons x xs) ys := x ::: tlist_app xs ys.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Equations tlist_uncons {i j} (xs : tlist B i j) :
  option { z : A & B i z * tlist B z j }%type :=
  tlist_uncons tnil := None;
  tlist_uncons (tcons x xs) := Some (_; (x, xs)).

Equations tlist_map {i j A' C} {f : A -> A'}
          (g : forall i j : A, B i j -> C (f i) (f j))
          (xs : tlist B i j) : tlist C (f i) (f j) :=
  tlist_map _ tnil := tnil;
  tlist_map g (tcons x xs) := g _ _ x ::: tlist_map g xs.

Equations tlist_mapv {i j C}
          (g : forall i j : A, B i j -> C)
          (xs : tlist B i j) : list C :=
  tlist_mapv _ tnil := nil;
  tlist_mapv g (tcons x xs) := g _ _ x :: tlist_mapv g xs.

Equations tlist_head {i j} (xs : tlist B i j) :
  option { z : A & B i z }%type :=
  tlist_head tnil := None;
  tlist_head (tcons x xs) := Some (_; x).

Equations tlist_tail {i j} (xs : tlist B i j) :
  option { z : A & tlist B z j }%type :=
  tlist_tail tnil := None;
  tlist_tail (tcons x xs) := Some (_; xs).

Equations tlist_init {i j} (xs : tlist B i j) :
  option { z : A & tlist B i z }%type :=
  tlist_init tnil := None;
  tlist_init (tcons x xs) <= tlist_init xs => {
    | None => Some (_; tnil);
    | Some (existT _ ys) => Some (_; (x ::: ys))
  }.

Equations tlist_last {i j} (xs : tlist B i j) :
  option { z : A & B z j }%type :=
  tlist_last tnil := None;
  tlist_last (tcons x xs) <= xs => {
    | tnil => Some (_; x);
    | tcons y ys => tlist_last ys
  }.

Equations tlist_rev (flip : forall x y : A, B x y -> B y x)
          {i j} (xs : tlist B i j) : tlist B j i :=
  tlist_rev flip tnil := tnil;
  tlist_rev flip (tcons x xs) :=
    tlist_rev flip xs +++ flip _ _ x ::: tnil.

Equations tlist_concat {i j} (xs : tlist (tlist B) i j) : tlist B i j :=
  tlist_concat tnil := tnil;
  tlist_concat (tcons x xs) := x +++ tlist_concat xs.

Context `{EqDec A}.

Hypothesis B_equiv : forall i j, crelation (B i j).
Hypothesis B_equivalence : forall i j, `{Equivalence (B_equiv i j)}.
Hypothesis B_equiv_dec : forall i j, EquivDec (B_equiv i j).

Import EqNotations.

(* Returns true if [xs] is a sublist of [ys] *)
Equations tlist_incl
          {j k} (xs : tlist B j k)
          {i l} (ys : tlist B i l) : bool :=
  tlist_incl (tnil j) (tnil i)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => false
    };
  tlist_incl (tnil j) (tcons i _ _ y ys)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => tlist_incl tnil ys
    };
  tlist_incl _ tnil := false;
  tlist_incl (tcons j m _ x xs) (tcons i o _ y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2) =>
        (equiv_dec x (rew <- [fun y => B _ y] H2 in
                      rew <- [fun x => B x _] H1 in y)
           &&& tlist_incl xs ys)
          ||| tlist_incl (x ::: xs) ys;
      | _ => tlist_incl (x ::: xs) ys
    }.

Equations tlist_equiv {i j : A} (x y : tlist B i j) : Type :=
  tlist_equiv tnil tnil := True;
  tlist_equiv tnil _ := False;
  tlist_equiv _ tnil := False;
  tlist_equiv (tcons _ m _ x xs) (tcons _ o _ y ys)
    <= eq_dec m o => {
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
  unfold tlist_equiv_obligation_1.
  rewrite eq_dec_refl.
  split.
    apply Equivalence_Reflexive.
  apply IHx.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
    dependent elimination y as [tnil]; auto.
  dependent elimination y as [tcons y ys]; auto.
  rewrite tlist_equiv_equation_4 in *.
  unfold tlist_equiv_obligation_1 in *.
  destruct (eq_dec j wildcard0); [|contradiction].
  subst.
  rewrite eq_dec_refl.
  destruct X.
  split.
    now apply Equivalence_Symmetric.
  apply IHx, t.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
    dependent elimination y as [tnil]; auto.
    contradiction.
  dependent elimination y as [tcons y ys]; auto.
    simpl; intros.
    dependent elimination z as [tcons z zs]; auto.
    rewrite tlist_equiv_equation_4 in *.
    unfold tlist_equiv_obligation_1 in *.
    destruct (eq_dec j wildcard2); [|contradiction].
    destruct (eq_dec wildcard2 wildcard0); [|contradiction].
    subst.
    rewrite eq_dec_refl.
    destruct X, X0.
    split.
      transitivity y; auto.
    eapply IHx; eauto.
  simpl; intros.
  contradiction.
Qed.

Global Program Instance tlist_cons_respects {i j k} :
  Proper (B_equiv i j ==> @tlist_equiv j k ==> @tlist_equiv i k)
         (@tcons A B i j k).
Next Obligation.
  repeat intro.
  simpl in *.
  rewrite tlist_equiv_equation_4.
  unfold tlist_equiv_obligation_1.
  now rewrite eq_dec_refl.
Qed.

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

Global Program Instance tlist_app_respects {i j k} :
  Proper (@tlist_equiv i j ==> @tlist_equiv j k ==> @tlist_equiv i k)
         tlist_app.
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
    unfold tlist_equiv_obligation_1 in *.
    destruct (eq_dec j0 j); [|contradiction].
    subst.
    destruct X.
    split; auto.
    apply IHx.
      exact t.
    exact X0.
Qed.

Global Program Instance tlist_equiv_EquivDec {i j} :
  EquivDec (@tlist_equiv i j).
Next Obligation.
  induction x; dependent elimination y.
  - left; reflexivity.
  - right; intro; inversion X.
  - right; intro; inversion X.
  - destruct (eq_dec j j0); subst.
    + destruct (@equiv_dec A B _ _ (B_equiv _ _) (B_equivalence _ _)
                           (B_equiv_dec _ _) x1 x).
      * destruct (IHx xs).
          now left; rewrite e, e0.
        right; intro.
        apply c; clear c.
        rewrite e in X; clear e.
        unfold equiv in X.
        rewrite tlist_equiv_equation_4 in X.
        unfold tlist_equiv_obligation_1 in X.
        rewrite eq_dec_refl in X.
        destruct X.
        apply t.
      * right; intro.
        apply c; clear c.
        unfold equiv in X.
        rewrite tlist_equiv_equation_4 in X.
        unfold tlist_equiv_obligation_1 in X.
        rewrite eq_dec_refl in X.
        destruct X.
        apply e.
    + right; intro.
      apply n; clear n.
      unfold equiv in X.
      rewrite tlist_equiv_equation_4 in X.
      unfold tlist_equiv_obligation_1 in X.
      destruct (eq_dec j0 j); auto.
      contradiction.
Defined.

End TList.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Section TListProofs.

Context {A : Type}.
Context {B : A -> A -> Type}.

Lemma tlist_app_tnil_r {i j} (xs : tlist B i j) :
  xs +++ tnil = xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_length {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_length (xs +++ ys) = tlist_length xs + tlist_length ys.
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
  now rewrite IHxs.
Qed.

Lemma tlist_rev_app_distr {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_rev flip (xs +++ ys) = tlist_rev flip ys +++ tlist_rev flip xs.
Proof.
  generalize dependent i.
  induction ys; intros.
    now rewrite tlist_app_tnil_r.
  rewrite tlist_app_cons.
  rewrite <- tlist_app_assoc.
  rewrite IHys, (IHys _ (x ::: tnil)).
  rewrite tlist_app_assoc.
  f_equal.
  rewrite tlist_rev_unit.
  now rewrite <- tlist_app_cons.
Qed.

Hypothesis flip_involutive : forall (i j : A) (x : B i j),
  flip _ _ (flip _ _ x) = x.

Lemma tlist_rev_involutive {i j} (xs : tlist B i j) :
  tlist_rev flip (tlist_rev flip xs) = xs.
Proof.
  induction xs; simpl; auto.
  rewrite tlist_rev_app_distr.
  rewrite IHxs.
  simpl tlist_rev.
  rewrite <- tlist_app_comm_cons.
  now rewrite flip_involutive.
Qed.

Lemma tlist_rev_length {i j} (xs : tlist B i j) :
  tlist_length (tlist_rev flip xs) = tlist_length xs.
Proof.
  induction xs; auto; simpl.
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
  now subst.
Qed.

End TListProofsInj.

Section WList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Context `{EqDec A}.

Hypothesis B_equiv : forall i j, crelation (B i j).
Hypothesis B_equivalence : forall i j, `{Equivalence (B_equiv i j)}.
Hypothesis B_equiv_dec : forall i j, EquivDec (B_equiv i j).

Import EqNotations.

Equations tlist_find_wlist
          {j k} (xs : tlist B j k)
          {i l} (ys : tlist B i l) : option (tlist B i j * tlist B k l) :=
  tlist_find_wlist (tnil j) (tnil i)
    <= eq_dec j i => {
      | left H => Some (rew [fun x => tlist B x _] H in tnil,
                        rew [fun x => tlist B _ x] H in tnil);
      | _ => None
    };
  tlist_find_wlist (tnil j) (tcons k n l y ys)
    <= eq_dec j k => {
      | left H =>
        Some (rew [fun x => tlist B x _] H in tnil,
              rew <- [fun x => tlist B x _] H in (y ::: ys));
      | _ <= tlist_find_wlist tnil ys => {
        | None => None;
        | Some (pair ys zs) => Some (y ::: ys, zs)
      }
    };
  tlist_find_wlist _ tnil := None;
  tlist_find_wlist (tcons j m k x xs) (tcons i o l y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2)
        <= equiv_dec x (rew <- [fun x => B x _] H1 in
                        rew <- [fun x => B _ x] H2 in y) => {
          | inl _ <= tlist_find_wlist xs ys => {
              | Some (pair bs cs)
                <= equiv_dec bs (rew <- [fun a => tlist B _ a] H2 in tnil) => {
                  | inl _ =>
                    Some (rew [fun a => tlist B a _] H1 in tnil, cs);
                  | _ <= tlist_find_wlist (x ::: xs) ys => {
                    | None => None;
                    | Some (pair ys zs) =>
                      Some (y ::: ys, zs)
                  }
                };
              | None <= tlist_find_wlist (x ::: xs) ys => {
                  | None => None;
                  | Some (pair ys zs) =>
                    Some (y ::: ys, zs)
                }
            };
          | _ <= tlist_find_wlist (x ::: xs) ys => {
              | None => None;
              | Some (pair ys zs) =>
                Some (y ::: ys, zs)
            }
        };
      | _  <= tlist_find_wlist (x ::: xs) ys => {
          | None => None;
          | Some (pair ys zs) =>
            Some (y ::: ys, zs)
        }
      }.

End WList.

Section WListProofsInj.

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

Hypothesis B_equiv : forall i j, crelation (B i j).
Hypothesis B_equivalence : forall i j, `{Equivalence (B_equiv i j)}.
Hypothesis B_equiv_dec : forall i j, EquivDec (B_equiv i j).

Import EqNotations.

Open Scope signature_scope.

Definition tequiv {i j : A} := tlist_equiv B_equiv B_equivalence (i:=i) (j:=j).
Arguments tequiv /.

Ltac cleanup H0 H2 H3 IHf Heqo :=
  inversion H0; subst; clear H0;
  specialize (IHf _ _ _ _ _ Heqo);
  rewrite <- !tlist_app_comm_cons;
  try (rewrite <- !tlist_app_comm_cons in IHf);
  simpl in IHf |- *;
  unfold tlist_equiv_obligation_1;
  rewrite eq_dec_refl;
  split; auto;
  try reflexivity.

Lemma tlist_find_wlist_app {i l} (f : tlist B i l)
      {j k} (g : tlist B j k) {pre post} :
  tlist_find_wlist B_equiv B_equivalence B_equiv_dec g f = Some (pre, post)
      -> tequiv f (pre +++ g +++ post).
Proof.
  unfold tequiv; intros.
  generalize dependent k.
  generalize dependent j.
  induction f; intros; simpl in H0.
  - destruct g.
      unfold tlist_find_wlist_obligation_1 in H0.
      destruct (eq_dec i0 i); [|discriminate].
      inversion H0; now subst.
    discriminate.
  - destruct g.
      unfold tlist_find_wlist_obligation_3 in H0.
      destruct (eq_dec i0 i); subst.
        inversion H0; now subst.
      unfold tlist_find_wlist_obligation_2 in H0.
      destruct (tlist_find_wlist _ _ _) eqn:?; [|discriminate].
      destruct p.
      inversion H0; subst.
      now cleanup H0 H2 H3 IHf Heqo.
    destruct (eq_dec i0 i); subst. {
      destruct (eq_dec j0 j); subst. {
        unfold tlist_find_wlist_obligation_7 in H0.
        destruct (equiv_dec _ _). {
          rewrite e.
          unfold tlist_find_wlist_obligation_9 in H0.
          unfold tlist_find_wlist_obligation_7 in H0.
          destruct (tlist_find_wlist _ _ _ g f) eqn:?. {
            destruct p.
            unfold tlist_find_wlist_obligation_5 in H0.
            destruct (equiv_dec _ _). {
              cleanup H0 H2 H3 IHf Heqo.
              rewrite e0 in IHf.
              apply IHf.
            }
            clear Heqo.
            unfold tlist_find_wlist_obligation_4 in H0.
            destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
            destruct p.
            rewrite <- e.
            now cleanup H0 H2 H3 IHf Heqo.
          }
          unfold tlist_find_wlist_obligation_4 in H0.
          destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
          destruct p.
          rewrite <- e.
          now cleanup H0 H2 H3 IHf Heqo0.
        }
        unfold tlist_find_wlist_obligation_9 in H0.
        unfold tlist_find_wlist_obligation_8 in H0.
        destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
        destruct p.
        now cleanup H0 H2 H3 IHf Heqo.
      }
      unfold tlist_find_wlist_obligation_10 in H0.
      destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
      destruct p.
      now cleanup H0 H2 H3 IHf Heqo.
    }
    unfold tlist_find_wlist_obligation_11 in H0.
    destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
    destruct p.
    now cleanup H0 H2 H3 IHf Heqo.
Qed.

End WListProofsInj.

Definition nat_triple (i j : nat) : Type := ((nat * nat) * nat)%type.

Definition my_list : tlist nat_triple 0 4 :=
  tcons 1 ((0, 1), 100)
        (tcons 2 ((1, 2), 200)
               (tcons 3 ((2, 3), 300)
                      (tcons 4 ((3, 4), 400)
                             tnil))).

Require Import Coq.Arith.EqNat.

Definition nat_equivb (i j : nat) (x y : nat_triple i j) : Type :=
  match x, y with
    (_, a), (_, b) => a = b
  end.

Program Instance nat_equivalence {i j} : Equivalence (nat_equivb i j).
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

Program Instance nat_equiv_dec {i j : nat} :
  EquivDec (A:=nat) (B:=nat_triple) (i:=i) (j:=j) (nat_equivb i j)
           (H:=@nat_equivalence i j).
Next Obligation.
  destruct x, y.
  destruct (eq_dec n n0).
    subst.
    left; reflexivity.
  right; intro.
  apply n1.
  inversion X.
  reflexivity.
Defined.

Example tlist_find_wlist_nat_ex1 :
  @tlist_find_wlist
    nat nat_triple PeanoNat.Nat.eq_dec nat_equivb
    (fun _ _ => nat_equivalence) (fun _ _ => nat_equiv_dec)
    1 3 (tcons 2 ((1, 2), 200) (tcons 3 ((2, 3), 300) tnil))
    0 4 my_list
    === Some (((0, 1, 100) ::: tnil), ((3, 4, 400) ::: tnil)).
Proof. reflexivity. Qed.

Print Assumptions tlist_find_wlist_nat_ex1.

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

Instance tlist_IMonoid {A} {B : A -> A -> Type} : IMonoid (tlist B) := {
  imempty := @tnil A B;
  imappend := @tlist_app A B;
  imempty_left := @tlist_app_tnil_l A B;
  imempty_right := @tlist_app_tnil_r A B;
  imappend_assoc := @tlist_app_assoc A B
}.

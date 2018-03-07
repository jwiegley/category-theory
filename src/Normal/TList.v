(** A theory of type-aligned lists, using the Coq-Equations plugin *)

Require Import Coq.Lists.List.
Require Import Coq.Classes.CEquivalence.
Require Import Coq.Bool.Bool.

Open Scope lazy_bool_scope.

Require Import Equations.Equations.
Unset Equations WithK.

Notation "( x ; y )" := (existT _ x y) (at level 0).

Inductive tlist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | anil : forall i : A, tlist B i i
  | acons : forall (i j k : A) (x : B i j) (xs : tlist B j k), tlist B i k.

Derive Signature Subterm for tlist.

Arguments anil {A B i}.
Arguments acons {A B i} j {k} x xs.

Notation "x ::: xs" := (acons _ x xs) (at level 60, right associativity).

Section Tlist.

Context {A : Type}.
Context {B : A -> A -> Type}.

Fixpoint tlist_length {i j} (xs : tlist B i j) : nat :=
  match xs with
  | anil => 0
  | acons x _ xs => 1 + tlist_length xs
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
  | anil, ys => ys
  | xs, anil => xs
  | acons _ x xs, ys => x ::: @tlist_app _ _ _ xs ys
  end.
*)

Equations tlist_app {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist B i k :=
  tlist_app anil ys := ys;
  tlist_app xs anil := xs;
  tlist_app (acons x xs) ys := x ::: tlist_app xs ys.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Equations tlist_uncons {i j} (xs : tlist B i j) :
  option { z : A & B i z * tlist B z j }%type :=
  tlist_uncons anil := None;
  tlist_uncons (acons x xs) := Some (_; (x, xs)).

Equations tlist_map {i j A' C} {f : A -> A'}
          (g : forall i j : A, B i j -> C (f i) (f j))
          (xs : tlist B i j) : tlist C (f i) (f j) :=
  tlist_map _ anil := anil;
  tlist_map g (acons x xs) := g _ _ x ::: tlist_map g xs.

Equations tlist_head {i j} (xs : tlist B i j) :
  option { z : A & B i z }%type :=
  tlist_head anil := None;
  tlist_head (acons x xs) := Some (_; x).

Equations tlist_tail {i j} (xs : tlist B i j) :
  option { z : A & tlist B z j }%type :=
  tlist_tail anil := None;
  tlist_tail (acons x xs) := Some (_; xs).

Equations tlist_init {i j} (xs : tlist B i j) :
  option { z : A & tlist B i z }%type :=
  tlist_init anil := None;
  tlist_init (acons x xs) <= tlist_init xs => {
    | None => Some (_; anil);
    | Some (existT _ ys) => Some (_; (x ::: ys))
  }.

Equations tlist_last {i j} (xs : tlist B i j) :
  option { z : A & B z j }%type :=
  tlist_last anil := None;
  tlist_last (acons x xs) <= xs => {
    | anil => Some (_; x);
    | acons y ys => tlist_last ys
  }.

Equations tlist_rev (sym : forall x y : A, B x y -> B y x)
          {i j} (xs : tlist B i j) : tlist B j i :=
  tlist_rev sym anil := anil;
  tlist_rev sym (acons x xs) :=
    tlist_rev sym xs +++ sym _ _ x ::: anil.

Equations tlist_concat {i j} (xs : tlist (tlist B) i j) : tlist B i j :=
  tlist_concat anil := anil;
  tlist_concat (acons x xs) := x +++ tlist_concat xs.

Import EqNotations.

(* Returns true if [xs] is a sublist of [ys] *)
Equations tlist_incl
          (A_eq_dec : forall x y : A, { x = y } + { x <> y })
          (B_equivb : forall (i j : A) (x y : B i j), bool)
          {j k} (xs : tlist B j k)
          {i l} (ys : tlist B i l) : bool :=
  tlist_incl eq_dec equivb (anil j) (anil i)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => false
    };
  tlist_incl eq_dec equivb (anil j) (acons i _ _ y ys)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => tlist_incl eq_dec equivb anil ys
    };
  tlist_incl _ _ _ anil := false;
  tlist_incl eq_dec equivb (acons j m _ x xs) (acons i o _ y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2) =>
        (equivb _ _ x (rew <- [fun y => B _ y] H2 in
                       rew <- [fun x => B x _] H1 in y)
           &&& tlist_incl eq_dec equivb xs ys)
          ||| tlist_incl eq_dec equivb (x ::: xs) ys;
      | _ => tlist_incl eq_dec equivb (x ::: xs) ys
    }.

End Tlist.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Section TlistProofs.

Context {A : Type}.
Context {B : A -> A -> Type}.

Lemma tlist_app_anil_l {i j} (xs : tlist B i j) :
  anil +++ xs = xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_anil_r {i j} (xs : tlist B i j) :
  xs +++ anil = xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_cons {i j k} (x : B i j) (xs : tlist B j k) :
  x ::: xs = (x ::: anil) +++ xs.
Proof. now destruct xs. Qed.

Lemma tlist_app_assoc {i j k l}
      (xs : tlist B i j) (ys : tlist B j k) (zs : tlist B k l) :
  (xs +++ ys) +++ zs = xs +++ (ys +++ zs).
Proof.
  induction xs, ys, zs; auto; simpl.
  now rewrite IHxs.
Qed.

Lemma tlist_app_comm_cons {i j k l} (x : B i j)
      (xs : tlist B j k) (ys : tlist B k l) :
  x ::: (xs +++ ys) = (x ::: xs) +++ ys.
Proof.
  rewrite tlist_app_cons.
  rewrite <- tlist_app_assoc.
  now rewrite <- tlist_app_cons.
Qed.

Lemma tlist_app_length {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_length (xs +++ ys) = tlist_length xs + tlist_length ys.
Proof.
  induction xs; auto.
  rewrite <- tlist_app_comm_cons; simpl.
  now rewrite IHxs.
Qed.

Lemma tlist_concat_anil {i} : tlist_concat anil = @anil A B i.
Proof. reflexivity. Qed.

Lemma tlist_concat_acons {i j k} (x : tlist B i j) (xs : tlist (tlist B) j k) :
  tlist_concat (x ::: xs) = x +++ tlist_concat xs.
Proof. reflexivity. Qed.

End TlistProofs.

Lemma tlist_concat_app {A : Type} {B : A -> A -> Type} {i j k}
      (xs : tlist (tlist B) i j) (ys : tlist (tlist B) j k) :
  tlist_concat (xs +++ ys) = tlist_concat xs +++ tlist_concat ys.
Proof.
  induction xs; auto.
  rewrite <- tlist_app_comm_cons; simpl.
  rewrite IHxs.
  now rewrite tlist_app_assoc.
Qed.

Section TlistProofsRev.

Context {A : Type}.
Context {B : A -> A -> Type}.

Variables sym : forall x y : A, B x y -> B y x.

Lemma tlist_rev_unit {i j k} (xs : tlist B i j) (x : B j k) :
  tlist_rev sym (xs +++ x ::: anil) = sym _ _ x ::: tlist_rev sym xs.
Proof.
  induction xs; auto; simpl.
  now rewrite IHxs.
Qed.

Lemma tlist_rev_app_distr {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist_rev sym (xs +++ ys) = tlist_rev sym ys +++ tlist_rev sym xs.
Proof.
  generalize dependent i.
  induction ys; intros.
    now rewrite tlist_app_anil_r.
  rewrite tlist_app_cons.
  rewrite <- tlist_app_assoc.
  rewrite IHys, (IHys _ (x ::: anil)).
  rewrite tlist_app_assoc.
  f_equal.
  rewrite tlist_rev_unit.
  now rewrite <- tlist_app_cons.
Qed.

Hypothesis sym_involutive : forall (i j : A) (x : B i j),
  sym _ _ (sym _ _ x) = x.

Lemma tlist_rev_involutive {i j} (xs : tlist B i j) :
  tlist_rev sym (tlist_rev sym xs) = xs.
Proof.
  induction xs; simpl; auto.
  rewrite tlist_rev_app_distr.
  rewrite IHxs.
  simpl tlist_rev.
  rewrite <- tlist_app_comm_cons.
  now rewrite sym_involutive.
Qed.

Lemma tlist_rev_length {i j} (xs : tlist B i j) :
  tlist_length (tlist_rev sym xs) = tlist_length xs.
Proof.
  induction xs; auto; simpl.
  rewrite tlist_app_length, IHxs; simpl.
  apply PeanoNat.Nat.add_1_r.
Qed.

End TlistProofsRev.

Section TlistProofsInj.

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

End TlistProofsInj.

Section WList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Inductive wlist : A -> A -> A -> A -> Type :=
  | segments : forall (i j k l : A),
      tlist B i j -> tlist B k l -> wlist i j k l.

Arguments segments {i j k l} xs ys.

Import EqNotations.

Equations tlist_find_wlist
          (A_eq_dec : forall x y : A, { x = y } + { x <> y })
          (B_equivb : forall (i j : A) (x y : B i j), bool)
          {j k} (xs : tlist B j k)
          {i l} (ys : tlist B i l) : option (wlist i j k l) :=
  tlist_find_wlist eq_dec equivb (anil j) (anil i)
    <= eq_dec j i => {
      | left H => Some (rew <- [fun x => wlist _ x x _] H
                          in segments anil anil);
      | _ => None
    };
  tlist_find_wlist eq_dec equivb (anil j) (acons k n l y ys)
    <= eq_dec j k => {
      | left H =>
        Some (rew <- [fun x => wlist _ x x _] H
                in segments anil (y ::: ys));
      | _ <= tlist_find_wlist eq_dec equivb anil ys => {
        | None => None;
        | Some (segments ys zs) =>
          Some (segments (y ::: ys) zs)
      }
    };
  tlist_find_wlist _ _ _ anil := None;
  tlist_find_wlist eq_dec equivb (acons j m k x xs) (acons i o l y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2)
        <= equivb _ _ x (rew <- [fun y => B _ y] H2 in
                         rew <- [fun x => B x _] H1 in y) => {
          | true <= tlist_find_wlist eq_dec equivb xs ys => {
              | Some (segments ys ws zs) =>
                Some (rew [fun a => wlist a j _ _] H1
                        in segments anil zs);
              | None <= tlist_find_wlist eq_dec equivb (x ::: xs) ys => {
                  | None => None;
                  | Some (segments ys zs) =>
                    Some (segments (y ::: ys) zs)
                }
            };
          | false <= tlist_find_wlist eq_dec equivb (x ::: xs) ys => {
              | None => None;
              | Some (segments ys zs) =>
                Some (segments (y ::: ys) zs)
            }
        };
      | _  <= tlist_find_wlist eq_dec equivb (x ::: xs) ys => {
          | None => None;
          | Some (segments ys zs) =>
            Some (segments (y ::: ys) zs)
        }
      }.

End WList.

Arguments segments {A B i j k l} xs ys.

Definition nat_triple := fun (_ _ : nat) => ((nat * nat) * nat)%type.

Definition my_list : tlist nat_triple 0 4 :=
  acons 1 ((0, 1), 100)
        (acons 2 ((1, 2), 200)
               (acons 3 ((2, 3), 300)
                      (acons 4 ((3, 4), 400)
                             anil))).

Lemma nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Require Import Coq.Arith.EqNat.

Definition nat_equivb (x y : ((nat * nat) * nat)) : bool :=
  match x, y with
    (_, a), (_, b) => beq_nat a b
  end.

Example tlist_find_wlist_nat_ex1 :
  @tlist_find_wlist nat nat_triple nat_eq_dec (fun _ _ => nat_equivb)
                    1 3 (acons 2 ((1, 2), 200) (acons 3 ((2, 3), 300) anil))
                    0 4 my_list
    = Some (segments ((0, 1, 100) ::: anil) ((3, 4, 400) ::: anil)).
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
  imempty := @anil A B;
  imappend := @tlist_app A B;
  imempty_left := @tlist_app_anil_l A B;
  imempty_right := @tlist_app_anil_r A B;
  imappend_assoc := @tlist_app_assoc A B
}.

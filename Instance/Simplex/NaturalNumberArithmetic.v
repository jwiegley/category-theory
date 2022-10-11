Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.

Global Create HintDb arith discriminated.
(* Check leq_trans. *)
(* leq_trans *)
(*      : forall n m p : nat, m <= n -> n <= p -> m <= p *)
Ltac leq_transleft :=
  match goal with
  | [ H : is_true( ?m <= ?n ) |- is_true ( ?m <= ?p ) ] => apply (@leq_trans n _ _ H)
  end.
Ltac leq_transright :=
  match goal with
  | [ H : is_true( ?n <= ?p ) |- is_true( ?m <= ?p ) ] => refine (@leq_trans n _ _ _ H)
  end.

Ltac ltn_predKhint :=
  match goal with
  | [ H : is_true (S ?Y <= ?X) |- ?X = ?X.-1.+1 ] => symmetry; exact: (@ltn_predK Y X H)
  | [ H : is_true (S ?Y <= ?X) |- ?X.-1.+1 = ?X ] => exact: (@ltn_predK Y X H)
  end.


Global Hint Extern 2 => leq_transleft : arith.
Global Hint Extern 2 => leq_transright : arith.
Global Hint Extern 2 => ltn_predKhint : arith.
Global Hint Resolve leq_trans : arith.
Global Hint Resolve ltn_predK : arith. 
Global Hint Resolve ltn_ord : arith.
Global Hint Resolve leq_addr : arith.

(* This hint tends to lead immediately to infinite loops, as repeatedly applying
   ltnW makes the goal evolve like
   n <= m  
   S n <= m
   S S n <= m 
   (...)
   so we remove it.
 *)
Global Remove Hints ltnW : core.

(* Global Hint Resolve ltnW : arith. *)
Global Hint Resolve leq_addr : arith.
Global Hint Resolve leq_addl : arith.

(* Tactics like 'rewrite', 'unfold' and 'set' can all succeed 
   even if nothing happens in the goal. 
   Therefore one cannot use them as usefully with "auto" or any other 
   automation with backtracking on failure, as they will always succeed.
   This tactic script lets us add rewrite and unfold hints to auto with Extern.
*)
Ltac fail_if_unchanged t :=
  match goal with
  | [ |- ?G1 ] => t;
                  match goal with
                  | [ |- ?G2 ] =>
                      match G1 with
                      | G2 => fail 1
                      | _ => idtac
                      end
                  end
  end.

Proposition nlek_nm1lek : forall (n m : nat), (n <= m) -> (n.-1 <= m).
Proof.
  intros n m ineq; apply (@leq_trans n); [exact: leq_pred | assumption].
Qed.
Proposition nltk_nm1ltk : forall (n m : nat), (n < m) -> (n.-1 < m).
Proof.
  intro n; destruct n; [ done |].
  exact: nlek_nm1lek.
Qed.

Proposition nlek_nm1lekm1 : forall (n m : nat), (n <= m) -> (n.-1 <= m.-1).
Proof.
  intros n m ineq; do 2 ! rewrite -subn1. exact: leq_sub. 
Qed.

Global Hint Resolve nlek_nm1lek : arith.
Global Hint Resolve nltk_nm1ltk : arith.
Global Hint Resolve nlek_nm1lekm1 : arith.
Global Hint Resolve negbTE : arith.

Proposition nltm_nltmk : forall n m k: nat, n <= m -> n <= m + k.
Proof.
  intros n m k ineq.
  apply: (@leq_trans m n (m + k)); [ exact: ineq | exact: leq_addr ].
Qed.

Proposition nltk_nltmk : forall n m k: nat, n <= k -> n <= m + k.
Proof.
  intros n m k ineq.
  apply (@leq_trans k n (m + k)); auto with arith.
Qed.

Proposition nltm_nneqm : forall n m : nat, n < m -> n !=m.
Proof.
  intros n m.
  rewrite ltn_neqAle.
  move/andP; by case.
Qed.

Proposition nltm_mneqn : forall n m : nat, m < n -> n !=m.
Proof.
  intros n m.
  rewrite ltn_neqAle; intro H.
  apply (rwP andP) in H; destruct H as [ neq _].
  apply/eqP. intro H; rewrite H in neq; apply negbTE in neq; rewrite eq_refl in neq.
  discriminate.
Qed.

Global Hint Resolve nltm_nltmk : arith.
Global Hint Resolve nltk_nltmk : arith.
Global Hint Resolve addn0 : arith.
Global Hint Resolve addnA : arith.
Global Hint Unfold addn : arith.
Global Hint Rewrite leq_add2l : arith.
Global Hint Rewrite -> addn0 : arith.
Global Hint Rewrite -> add0n : arith.
Global Hint Resolve nltm_nneqm : arith.
Global Hint Resolve nltm_mneqn : arith.

(* My automation strategy in this file is that if I think a tactic 
   should *always* be applied 
   if it can (i.e. it should be applied eagerly and without backtracking)
   then I will put the tactic in a block repeat-match-goal script like this;

   and if I think that it should only *sometimes* be applied, then I will
   add it to a hint database for auto, so that it can be applied with backtracking.

   The main downside I can think of to this approach is that it is not
   easy to add new "hints" to the repeat-match-goal block this way.
 *)


Ltac arith_simpl :=
  do ! (match goal with
        |[ |- context[addn _ _] ] => fail_if_unchanged ltac:(rewrite add0n)
        |[ |- context[addn _ _] ] => fail_if_unchanged ltac:(rewrite addn0)
        |[ |- context[addn _ _] ] => fail_if_unchanged ltac:(rewrite addn1)
        |[ |- context[addn _ _] ] => fail_if_unchanged ltac:(rewrite add1n)
        |[ |- context[subn _ _] ] => fail_if_unchanged ltac:(rewrite subn1)
        |[ |- context[subn _ _] ] => fail_if_unchanged ltac:(rewrite subn0)
        |[ |- context[subn _ _] ] => fail_if_unchanged ltac:(rewrite leq_add2l)
        |[ |- context[(?x < ?n.+1)] ] => fail_if_unchanged ltac:(rewrite leq_add2l)
        |[ H : lt ?x ?y |- _ ] =>
            apply (rwP ltP) in H
        |[ H : not (lt ?x ?y) |- _ ] =>
            apply (@introN _ _ (@ltP x y)) in H
        (* | [ H : not (leq ?x ?y) |- _ ] => *)
        (*     apply (@introN _ _ (@leP x y)) in H *)
        | [ H : le ?x ?y |- _ ] =>
            apply (rwP (@leP x y)) in H
        | [ H : not( le ?x ?y ) |- _ ] =>
            apply (introN (@leP x y)) in H
        |[ H : is_true ( leq (S _) (S _) ) |- _ ] =>
           rewrite ltnS in H
        |[ |- context[ leq (S _) (S _) ] ] => rewrite ltnS
        |[ H : context[ (nat_of_bool _) + _ ] |- _ ] =>
           rewrite add1n in H + rewrite add0n in H
        | [ H : context[ bump ?x ?x ] |- _ ] =>
            unfold bump in H; rewrite leqnn add1n in H
        | [|- context[?X.+1.-1] ] => change X.+1.-1 with X
        | [ H : is_true ( ?x < 0 ) |- _ ] => rewrite ltn0 in H; discriminate
         end).

Global Hint Extern 0 => arith_simpl : arith.
Global Hint Extern 10 (_ <= _) => (eapply leq_trans) : arith.
Global Hint Resolve leqW : arith.

Ltac ltnNge_in_H :=
  match goal with
  | [ H : is_true (~~ ( leq ?n ?m )) |-  _] => rewrite -ltnNge in H
  end.
Ltac ltnNge_in_goal :=
  match goal with
  | [ |- is_true (~~ ( leq ?n ?m ))] => rewrite -ltnNge
  end.
Global Hint Extern 4 => ltnNge_in_H : arith.
Global Hint Extern 4 => ltnNge_in_goal : arith.
Proposition n_leq_m_n_lt_msub1 (n m : nat) : n < m -> n <= m.-1.
Proof.
  intro ineq. change n with n.+1.-1. by auto with arith.
Qed.

Global Hint Resolve n_leq_m_n_lt_msub1 : arith.
Definition leB := fun n m : nat => rwP (@leP n m).
Global Hint Resolve <- leB : arith.

Proposition δi_δj_nat :
  forall (i j : nat), i < j -> 
           comp (bump j) (bump i) =1 comp (bump i) (bump j.-1).
Proof.
  intros i j ineq x; simpl.
  rewrite [bump i (bump _ _)]bumpC; unfold unbump.
  destruct j; [done |]; arith_simpl; simpl.
  destruct (@leqP i j) as [ineq' | _]; [ | discriminate ]; arith_simpl.
  rewrite {4}/bump.
  rewrite ineq'; by arith_simpl.
Qed.

Proposition σi_σj_nat :
  forall (i j : nat), i <= j -> 
           comp (unbump j) (unbump i) =1 comp (unbump i) (unbump j.+1).
  intros i j ineq x; simpl.
  unfold unbump.
  (* destruct (@leq_thirdP i j ineq x) as *)
  (*   [ _ _ xnlti xntlj ja1nltx | *)
  (*    iltx jgex js1nltx *)
  (*   |]. *)
  destruct (@leP (S i) x) as [i_lt_x | i_ge_x]; arith_simpl.
  {
    destruct (@leP (j.+2) x) as [j_llt_x | jrx]; arith_simpl. {
      assert (z : i < x.-1) by
        (apply nlek_nm1lekm1 in j_llt_x; simpl in j_llt_x;
         eapply leq_ltn_trans; eauto); rewrite z.
      
      assert (z2 : (j < x.-1)) by auto with arith; rewrite z2; arith_simpl.
      done. }
    {
      rewrite -ltnNge in jrx. rewrite ltnS in jrx.
      assert (z : j < x.-1 = false). { apply negbTE; rewrite -ltnNge.
                                       by rewrite (ltn_predK i_lt_x). }
      rewrite z i_lt_x; arith_simpl; done.
    }
  } 
  {
    ltnNge_in_H; rewrite ltnS in i_ge_x.
    assert (z : j < x = false) by auto with arith; rewrite z; clear z.
    assert (z : j.+1 < x = false) by auto 8 with arith ; rewrite z; clear z.
    arith_simpl.
    assert (z : i < x = false) by auto with arith; rewrite z; arith_simpl.
    reflexivity.
  } 
Qed.                                                                         

Ltac resolve_boolean :=  let VAR := fresh "boolvar" in 
                         set (VAR := _ : bool); cbn beta in VAR;
                         (let IS_FALSE := fresh "isfalse" in
                          assert (IS_FALSE : VAR = false) by (unfold VAR; auto 8 with arith);
                            rewrite IS_FALSE; clear IS_FALSE) + 
                         (let IS_TRUE := fresh "istrue" in
                          assert (IS_TRUE : VAR) by (unfold VAR; auto 8 with arith);
                          rewrite IS_TRUE; clear IS_TRUE) ; clear VAR.



Proposition δi_σj_iltj_nat :
  forall (i j : nat), i < j -> comp (unbump j) (bump i) =1 comp (bump i) (unbump j.-1).
Proof.
  intros i j ineq x; 
  unfold bump, unbump; simpl.
  destruct j ; [done | ]; simpl. 
  destruct (leqP i x) as [i_leq_x | i_gt_x ]; arith_simpl.
  { destruct (leqP j.+1 x) as [j_lt | j_gt];
      arith_simpl; resolve_boolean; auto with arith. }
  resolve_boolean; arith_simpl.
  assert (z : (j < x) = false ) by auto with arith; rewrite z; clear z; arith_simpl.
  resolve_boolean; done.
Qed.

Notation δi_σi_eq_id_nat := bumpK.

Proposition δSi_σi_eq_id_nat : forall i : nat,
    comp (unbump i) (bump (S i)) =1 id.
  intros i x; simpl.
  unfold bump, unbump; simpl.
  destruct (leqP (S i) x) as [lt | eq]; arith_simpl;
    resolve_boolean; arith_simpl; done. 
Qed.

Proposition δi_σj_i_gt_addnj1_nat {n : nat} :
  forall i j : nat, i > j.+1 ->
                    comp (unbump j) (bump i) =1 comp (bump i.-1) (unbump j).
Proof.
  intros i j ineq x; simpl.
  unfold unbump, bump.
  destruct (leqP i x) as [i_leq_x | i_gt_x ]; arith_simpl.  {
    resolve_boolean; arith_simpl.
    assert (z2 : j < x) by auto with arith; rewrite z2;  arith_simpl.
    resolve_boolean; eauto with arith. }
  destruct (leqP x j) as [j_leq_x | j_gt_x]; arith_simpl.  {
    assert (z1 : i.-1 <= x = false) by auto using (@leq_trans j.+1) with arith.
    rewrite z1; done.
  }
  destruct x; resolve_boolean; auto with arith.
Qed.      

Open Scope nat_scope.
Definition nat_eqP_hint := fun n m : nat => (rwP (@eqP nat_eqType n m)).
Global Hint Resolve -> nat_eqP_hint : arith.

Lemma σ_i_eq_i_nat ( i x : nat ) :
  ( (unbump i x) == i )  = ( ( x == i ) || ( x == i.+1 ) ).
Proof.
  apply/eqP/orP.
  { intro H. apply (f_equal (bump i)) in H.
    rewrite unbumpKcond in H.  
    destruct (@eqP _ x i); auto with arith. }
  { intro H; destruct H as [eq | succ].
    { unfold unbump. apply (rwP eqP) in eq; destruct eq; rewrite ltnn subn0; done. }
    { unfold unbump. apply (rwP eqP) in succ.
      by rewrite succ ltnSn subn1. }
  } 
Qed.

Inductive rgeq (m: nat) : nat -> Set :=
| rgeq_refl : rgeq m m
| rgeq_succ n : rgeq m (S n) -> rgeq m n.

Lemma rgeq_sub : forall m n k, rgeq m n -> rgeq m (n - k).
Proof.
  intros m n k; induction k; [ by rewrite subn0 |].
  intro H; apply IHk in H.
  destruct (leqP n k) as [leq | gt ].
  { assert (leq' : n <= k.+1) by auto with arith. 
    rewrite -subn_eq0 in leq, leq'; apply (rwP eqP) in leq, leq'; destruct leq, leq';
      done. }
  { constructor. rewrite subnSK; done. }
Qed.

Theorem leq_implies_rgeq : forall n m : nat, n <= m -> rgeq m n.
Proof.
  intros n m H.
  rewrite -(subKn H); apply rgeq_sub; constructor. 
Qed.

Theorem rgeq_implies_leq : forall n m : nat, rgeq m n -> n <= m.
Proof.
  intros n m H.
  induction H; [ done | exact: ltnW ].
Qed.


Close Scope nat_scope.

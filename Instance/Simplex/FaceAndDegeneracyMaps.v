Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Simplex.AugmentedSimplexCategory.
Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.MonoidalStructure.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

Open Scope nat_scope.

(*
  Section: 
   Setting up arithmetic hints and automation
 *)

(* This hint tends to lead immediately to infinite loops, as repeatedly applying
   ltnW makes the goal evolve like
   n <= m  
   S n <= m
   S S n <= m 
   (...)
   so we remove it.
 *)
Local Remove Hints ltnW : core.

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
         end).

Local Hint Extern 0 => arith_simpl : arith.
Local Hint Extern 10 (_ <= _) => (eapply leq_trans) : arith.
Local Hint Resolve leqW : arith.

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

Local Hint Resolve nlek_nm1lek : arith.
Local Hint Resolve nltk_nm1ltk : arith.
Local Hint Resolve nlek_nm1lekm1 : arith.

Local Hint Resolve negbTE : arith.
Ltac ltnNge_in_H :=
  match goal with
  | [ H : is_true (~~ ( leq ?n ?m )) |-  _] => rewrite -ltnNge in H
  end.
Ltac ltnNge_in_goal :=
  match goal with
  | [ |- is_true (~~ ( leq ?n ?m ))] => rewrite -ltnNge
  end.
Local Hint Extern 4 => ltnNge_in_H : arith.
Local Hint Extern 4 => ltnNge_in_goal : arith.
Proposition n_leq_m_n_lt_msub1 (n m : nat) : n < m -> n <= m.-1.
Proof.
  intro ineq. change n with n.+1.-1. by auto with arith.
Qed.

Local Hint Resolve n_leq_m_n_lt_msub1 : arith.
Definition leB := fun n m : nat => rwP (@leP n m).
Local Hint Resolve <- leB : arith.

Ltac simplex_simpl :=
  do ! (match goal with
        | [ |- @eq (@hom finord _ _) _ _ ]  => apply: val_inj; simpl
        | [ |- @eq (ordinal _) _ _] => apply: val_inj; simpl
        | [ |- @eq (monotonic_fn_sig _ _) _ _] => apply:val_inj; simpl
        | [ |- context[AugmentedSimplexCategory.comp _ _]] =>
            fail_if_unchanged ltac:(unfold AugmentedSimplexCategory.comp)
        | [ |- eqfun _ _ ] => unfold eqfun
        | [ |- @eq (@finfun_of _ _ _) _ _ ] => apply: eq_ffun
        | [ |- _ ] => fail_if_unchanged ltac:(rewrite ! ffunE)
        | [ |- _ ] => fail_if_unchanged simpl
         end).
Local Create HintDb simplex discriminated.

Local Hint Extern 0 => simplex_simpl : simplex.
Local Hint Extern 5 => (fail_if_unchanged ltac:(simpl)) : simplex.

(* Definitions of the face and degeneracy maps *)

Proposition δ_monotonic : forall (n : nat) (i : 'I_(n.+1)),
    monotonic [ffun j : 'I_n => lift i j].
Proof.
  intros n i; apply/monotonicP.
  intros x y ineq. rewrite 2! ffunE; unfold lift; simpl; unfold bump.
  destruct (@leP i x); arith_simpl.
  {  assert (z : i <= y) by eauto using leq_trans; rewrite z; by auto with arith. }
  { destruct (@leP i y); by auto with arith. }
Qed.

Definition δ (n : nat) (i : 'I_(n.+1)) : monotonic_fn n n.+1 :=
  @Sub {ffun 'I_n -> 'I_(n.+1)} monotonic _ _ (δ_monotonic n i).

Lemma σ_subproof (n : nat) (i : 'I_(n.+1)) : forall j : 'I_(n.+2), unbump i j < n.+1.
Proof.
  intro j; rewrite ltnS -leq_bump. unfold bump.
  destruct i as [ival ibd]; simpl.
  rewrite -[ival <= n]ltnS ibd -ltnS; unfold addn; simpl.
  by (destruct j).
Qed.

Ltac by_cases_on_leq_goal :=
  match goal with
  | [ |- context[ nat_of_bool (leq ?n ?m) ] ] =>
      let var1 := fresh "LEQ" in
      let var2 := fresh "GT" in 
      destruct (@leqP n m) as [var1 | var2]
  end.

Local Hint Extern 11 => by_cases_on_leq_goal : arith.

Proposition σ_monotonic: forall n i, monotonic [ffun j : 'I_(n.+2) => Ordinal (σ_subproof n i j)].
Proof.
  intros n [ival ibd]. apply (rwP (monotonicP _)).
  intros [xval xbd] [yval ybd]; simpl. intro ineq.
  rewrite ! ffunE; simpl; unfold unbump; clear xbd ybd.
  destruct (@ltP ival xval) as [l | eq]; arith_simpl. 
  {  rewrite (leq_trans l ineq); auto with arith. }
  {  rewrite -ltnNge ltnS in eq. 
     destruct (@ltP ival yval) as [i_lt_y | i_ge_y]; arith_simpl; [ | assumption ].
     by eapply leq_trans; eauto with arith. 
  }
Qed.   

Definition σ (n : nat) (i : 'I_(n.+1)) : monotonic_fn (n.+2) (n.+1) :=
  @Sub {ffun 'I_(n.+2) -> 'I_(n.+1)} monotonic _ _ (σ_monotonic n i).

Program Definition lshift_m (m n : nat) : monotonic_fn n (n + m):=
  Sub (finfun (fun i => lshift m i)) _.
Next Obligation.
  by apply (rwP (monotonicP _)); intros; rewrite ! ffunE. Qed.

Program Definition rshift_m (m n : nat) : monotonic_fn m (n + m) :=
  Sub (finfun (fun i => rshift n i)) _.
Next Obligation.
  by apply (rwP (monotonicP _ )); intros; rewrite ! ffunE;
    unfold rshift; simpl; autorewrite with arith.
Qed.  

Proposition predn_subproof (n : nat) (i : 'I_(n.+2)) : predn i < n.+1.
Proof.
  destruct i as [ival ibd]; destruct ival; done.
Qed.

Definition ord_predn {n : nat} (i : 'I_(n.+2)) : 'I_(n.+1) := Sub (predn i) (predn_subproof n i).

Definition ord_upcast {n : nat} (i : 'I_n) : 'I_n.+1.
Proof.
  destruct i as [ival ibd]; exists ival; auto with arith.
Defined.

(* The definition of "bump i x" is  x + nat_of_bool ( i <= x)
   In general we 
   This script scans the current goal to find the pattern nat_of_bool i <= x 
   and then tries to automatically decide whether this is true or false 
   so that the value of bump i x can be determined as x.+1 or x respectively.
 *)
(* Ltac resolve_boolean := *)
(*   let z := fresh "bexp" in *)
(*   let RW := fresh "RW" in *)
(*   set z := (selector in nat_of_bool selector); *)
(*            first [ assert (RW : z) by (unfold z; auto with arith) | *)
(*                    assert (RW : z = false) by (unfold z; auto with arith) ]; *)
(*            rewrite RW; clear RW; arith_simpl; simpl; clear z. *)

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

Arguments δ {n} i.
Arguments σ {n} i.

(*   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j *)
Proposition δi_δj {n : nat} : forall i : 'I_(n.+1), forall j : 'I_(n.+2),
  forall (t : i < j),
    @compose finord n n.+1 n.+2 (δ j) (δ i) =
      @compose finord n n.+1 n.+2 (δ (ord_upcast i))
                                     (δ (ord_predn j)).
Proof.
  intros [ival ibd] [jval jbd] ineq; simpl in ineq.
  simplex_simpl. intros [xval xbd]; simplex_simpl.
  exact: δi_δj_nat.
Qed.

(*   σ_j ∘ σ_i = σ_i ∘ σ_(j+1)   ;  i <= j *)
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
    assert (z : j < x = false) by eauto with arith; rewrite z; clear z.
    assert (z : j.+1 < x = false) by eauto 6 using leq_trans with arith; rewrite z; clear z.
    arith_simpl.
    assert (z : i < x = false) by auto with arith; rewrite z; arith_simpl.
    reflexivity.
  } 
Qed.                                                                         

Proposition δi_σj_iltj_nat :
  forall (i j : nat), i < j -> comp (unbump j) (bump i) =1 comp (bump i) (unbump j.-1).
Proof.
  intros i j ineq x; 
  unfold bump, unbump; simpl.
  destruct j ; [done | ].
  destruct (leqP i x) as [i_leq_x | i_gt_x ]; arith_simpl.
  { destruct (leqP j.+1 x) as [j_lt | j_gt].
    { arith_simpl; rewrite j_lt; arith_simpl;  simpl.
      assert (z: (i <= x.-1)) by
      (eapply leq_trans; [exact: ineq | auto with arith]);
        rewrite z; clear z; simpl; by eauto using Lt.S_pred_stt with arith. }
    {arith_simpl; simpl. simpl.
      assert (z : j < x = false) by auto with arith; rewrite z; clear z;
        arith_simpl.
      rewrite i_leq_x; arith_simpl; done.
    }
  }
  {  
    assert (z : (j < x) = false) by eauto with arith; rewrite z.
    assert (z': (j.+1 < x) = false) by (eauto 7 with arith); rewrite z'; clear z'.
    arith_simpl;
    assert (z'' : i <= x = false) by eauto with arith; rewrite z''.
    done.
  }
Qed.

Proposition δi_σj_iltj {n : nat} :
  forall (i : 'I_n.+2) (j : 'I_n.+2), (i < j) ->
    @compose finord n.+2 n.+3 n.+2 (σ j) (δ (ord_upcast i)) =
      @compose finord n.+2 n.+1 n.+2 (δ i) (σ (ord_predn j)).
Proof.
  intros i j ineq; destruct i as [ival ibd], j as [jval jbd]; simpl in ineq.
  simplex_simpl. intros [xval xbd].
  simplex_simpl.
  exact: δi_σj_iltj_nat.
Qed.

Notation δi_σi_eq_id_nat := bumpK.
  
Proposition δi_σi_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (σ i) (δ (ord_upcast i)) = @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl; unfold AugmentedSimplexCategory.comp.
  apply eq_ffun; intro x. rewrite ! ffunE; apply val_inj; simpl;
    exact: δi_σi_eq_id_nat.
Qed.

Proposition δSi_σi_eq_id_nat : forall i : nat,
    comp (unbump i) (bump (S i)) =1 id.
  intros i x; simpl.
  unfold bump, unbump; simpl.
  destruct (leqP (S i) x) as [lt | eq]; arith_simpl.
  { assert (z : i <= x) by exact: ltnW; rewrite z; by arith_simpl. }
  { assert (z : (i < x) = false) by auto with arith; rewrite z; by arith_simpl. }
Qed.

Proposition δSi_σi_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (σ i) (δ (lift ord0 i)) = @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl; unfold AugmentedSimplexCategory.comp;
    apply eq_ffun; intro x; rewrite ! ffunE; apply val_inj; simpl.
  rewrite {2}/bump; arith_simpl. exact: δSi_σi_eq_id_nat.
Qed.

Proposition δi_σj_i_gt_addnj1_nat {n : nat} :
  forall i j : nat, i > j.+1 ->
                    comp (unbump j) (bump i) =1 comp (bump i.-1) (unbump j).
Proof.
  intros i j ineq x; simpl.
  unfold unbump, bump.
  destruct (leqP i x) as [i_leq_x | i_gt_x ]; arith_simpl.  {
    assert (z1 : j <= x) by eauto with arith; rewrite z1; clear z1; arith_simpl.
    assert (z2 : j < x) by eauto with arith; rewrite z2; clear z2; arith_simpl.
    assert (z3 : i.-1 <= x.-1) by auto with arith; rewrite z3; clear z3; arith_simpl.
    eapply Lt.S_pred_stt; apply/leP; eapply leq_trans; eauto.
  }  {
    destruct (leqP x j) as [j_leq_x | j_gt_x]; arith_simpl.  {
      assert (z1 : i.-1 <= x = false) by auto using (@leq_trans j.+1) with arith.
      rewrite z1; done.
    } {
      assert (z2: i.-1 <= x.-1 = false) by (destruct x; auto with arith);
        rewrite z2; done.
    } 
  }      
Qed.      

Proposition δi_σj_i_gt_addnj1 {n : nat} : forall i : 'I_(n.+3), forall j : 'I_(n.+1),
  forall (t : i > j.+1),
    @compose finord n.+2 n.+3 n.+2 (σ (ord_upcast j)) (δ i) =
      @compose finord n.+2 n.+1 n.+2 (δ (ord_predn i)) (σ j).
Proof. 
  intros [ival ibd] [jval jbd]; simpl; intro ineq.
  simplex_simpl; intros [xval xbd].
  simplex_simpl.
  exact: δi_σj_i_gt_addnj1_nat.
Qed.

(* Factoring *)

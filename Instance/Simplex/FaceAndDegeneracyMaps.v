Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Simplex.AugmentedSimplexCategory.
Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.MonoidalStructure.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.

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
Local Hint Resolve leq_trans : arith.

(* Ltac always_simplify := do ! *)
(* ( intros; *)
(*   match goal with *)
(*   | [|- _ = _ ] => apply: val_inj *)
(*   | [|- (@Setoid.equiv _ _ _ _)] => apply: val_inj *)
(*   | [|- val _ = val _ ] => rewrite ! /val *)
(*   | [|- context[fun_of_fin _] ] => rewrite ! ffunE *)
(*   | [|- context[@eq (finfun_of _) _ _] ] => apply: eq_ffun *)
(*   | [ _ : ordinal O |- _ ] => discriminate *)
(*   | [ x : 'I_0 |- _ ] => *)
(*       (have ? : x < 0 by (apply: valP x)); discriminate *)
(*   end; move => /=;  try(done)). *)

Proposition d_monotonic : forall (n : nat) (i : 'I_(n.+1)), monotonic [ffun j : 'I_n => lift i j].
Proof.
  intros n i; apply/monotonicP.
  intros x y ineq. rewrite 2! ffunE; unfold lift; simpl; unfold bump.
   destruct (@leP i x) as [tt | ff].
  { move/leP : tt => tt.
    assert (z : (i <= y)) by (eapply leq_trans; eauto); rewrite z; clear z.
    by apply: leq_add. }
  by auto with arith.
Defined.

Definition d (n : nat) (i : 'I_(n.+1)) : monotonic_fn n n.+1 :=
  @Sub {ffun 'I_n -> 'I_(n.+1)} monotonic _ _ (d_monotonic n i).

Lemma s_subproof (n : nat) (i : 'I_(n.+1)) : forall j : 'I_(n.+2), unbump i j < n.+1.
Proof.
  intro j; rewrite ltnS -leq_bump. unfold bump.
  destruct i as [ival ibd]; simpl.
  rewrite -[ival <= n]ltnS ibd -ltnS; unfold addn; simpl.
  by (destruct j).
Qed.

Proposition s_monotonic: forall n i, monotonic [ffun j : 'I_(n.+2) => Ordinal (s_subproof n i j)].
Proof.
  intros n [ival ibd]. apply (rwP (monotonicP _)).
  intros [xval xbd] [yval ybd]. simpl. intro ineq.
  rewrite ! ffunE; simpl; unfold unbump.
  destruct (@ltP ival xval) as [l | eq].
  { apply (rwP ltP) in l; 
    assert (z : (ival < yval)) by (eapply leq_trans; eauto); rewrite z; clear z; simpl.
    by apply: leq_sub. }
  { rewrite (rwP ltP) in eq; apply (rwP negP) in eq; rewrite -leqNgt leq_eqVlt in eq;
      apply (rwP orP) in eq.
     rewrite subn0; destruct eq as [eq | lt].
     { apply (rwP eqP) in eq; rewrite eq.
      destruct (@ltP ival yval) as [lt | nlt].
      { assert (z : ival = (ival.+1) - 1). { by (rewrite subn1). } rewrite z; clear z.
        apply leq_sub; apply (rwP ltP); done. }
      by rewrite subn0 -eq. } 
     { destruct (@ltP ival yval).
       { apply (rwP ltP) in l.
         assert (z : (xval = xval.+1 - 1)). { by (rewrite subn1). } rewrite z; clear z.
         apply leq_sub; [ | done]. apply (@leq_ltn_trans ival); [ by apply ltnW | done].
       } {
         rewrite subn0. done.
       } 
     } 
  }          
Qed.

Definition s (n : nat) (i : 'I_(n.+1)) : monotonic_fn (n.+2) (n.+1) :=
  @Sub {ffun 'I_(n.+2) -> 'I_(n.+1)} monotonic _ _ (s_monotonic n i).

Program Definition lshift_m (m n : nat) : monotonic_fn n (n + m):=
  Sub (finfun (fun i => lshift m i)) _.
Next Obligation.
  by apply (rwP (monotonicP _)); intros; rewrite ! ffunE. Qed.

Local Hint Rewrite leq_add2l : arith.

Program Definition rshift_m (m n : nat) : monotonic_fn m (n + m) :=
  Sub (finfun (fun i => rshift n i)) _.
Next Obligation.
  by apply (rwP (monotonicP _ )); intros; rewrite ! ffunE;
    unfold rshift; simpl; autorewrite with arith.
Qed.  

Arguments d _ i : clear implicits.

Proposition predn_subproof (n : nat) (i : 'I_(n.+2)) : predn i < n.+1.
Proof.
  destruct i as [ival ibd]; destruct ival; done.
Qed.

Definition ord_predn {n : nat} (i : 'I_(n.+2)) : 'I_(n.+1) := Sub (predn i) (predn_subproof n i).
Definition ord_upcast {n : nat} (i : 'I_n) : 'I_n.+1.
Proof.
  destruct i as [ival ibd]; exists ival; auto with arith.
Defined. 

Proposition face_swap {n : nat} : forall i : 'I_(n.+1), forall j : 'I_(n.+2),
  forall (t : i < j),
    @compose finord n n.+1 n.+2 (d _ j) (d _ i) =
      @compose finord n n.+1 n.+2 (d _ (ord_upcast i))
                                     (d _ (ord_predn j)).
Proof. 
  intros [ival ibd] [jval jbd] ineq; simpl; apply: val_inj; simpl;
    unfold AugmentedSimplexCategory.comp; 
  apply: eq_ffun; intro x; rewrite ! ffunE; simpl in ineq.
  unfold lift; simpl. apply val_inj; simpl; unfold bump.
  destruct (leqP ival x) as [i_leq_x | i_nleq_x].
  {
    rewrite ! add1n.
    destruct jval; [ done | ]. rewrite -pred_Sn ltnS.
    destruct (leqP jval x) as [j_leq_x | j_nleq_x].
    { assert (z : (ival <= 1 + x)) by (auto with arith); rewrite z; clear z.
      done. }
    { by rewrite ! add0n i_leq_x add1n. }
  } 
  {
    assert (z : (jval <= false + x) = false). {
      rewrite add0n. apply negbTE. rewrite -ltnNge. by eapply ltn_trans; eauto. }
    rewrite z; clear z. rewrite ! add0n.
    assert (z : (jval.-1 <= x) = false). {
      apply negbTE. rewrite -ltnNge. destruct jval; [ done |]; simpl.
      rewrite ltnS in ineq. by eapply leq_trans ; eauto. }  rewrite z; clear z;
      rewrite ! add0n.
    assert (z : (ival <= x) = false). { by (apply negbTE; rewrite -ltnNge). }
    rewrite z; clear z. rewrite add0n; done.
  } 
Qed.

Proposition di_si_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (s _ i) (d _ (ord_upcast i)) = @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl; unfold AugmentedSimplexCategory.comp.
  apply eq_ffun; intro x. rewrite ! ffunE; apply val_inj; simpl; exact: bumpK.
Qed.  

Proposition dSi_si_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (s _ i) (d _ (lift ord0 i)) = @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl; unfold AugmentedSimplexCategory.comp;
    apply eq_ffun; intro x; rewrite ! ffunE; apply val_inj; simpl.
  unfold bump, unbump; simpl.
  destruct (leqP (S ival) x) as [lt | eq].
  { rewrite lt add1n.
    assert (z : (ival < x.+1)) by auto with arith; rewrite z; clear z; by rewrite subn1. }
  { rewrite add1n; rewrite ltnS in eq.
    assert (z : (ival < x = false)) by (apply negbTE; rewrite -ltnNge ltnS; done);
      rewrite ! z; clear z.
    by rewrite add0n subn0.
  }   
Qed.

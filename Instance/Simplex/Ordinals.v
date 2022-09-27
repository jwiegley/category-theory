Require Import Category.Lib.
Require Import Category.Instance.Simplex.NaturalNumberArithmetic.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

(* Require Import Coq.Logic.FinFun. *)

Local Notation "''I_' n" := (ordinal n).
Open Scope nat_scope.

Section findlast.
  Variable A : Type.
  Variable P : pred A.

  Definition findlast (l : seq A) := size l - (find P (rev l)).+1.
  Proposition has_findlast l : has P l -> findlast l < size l.
  Proof.
    intro H. unfold findlast. 
    assert (z : has predT l) by (unshelve eapply (@sub_has _ P); done).
    rewrite has_predT in z; by rewrite ltn_subrL z.
  Qed.
  Proposition findlast_size s : findlast s <= size s. 
  Proof.
    unfold findlast; exact: leq_subr.
  Qed.
  Lemma findlast_cat s1 s2 :
    findlast (s1 ++ s2) = if has P s2 then size s1 + findlast s2
                          else findlast s1.
  Proof.
    remember (has P s2) as b eqn:Heqn; apply symmetry in Heqn; destruct b.
    { assert (z := has_findlast s2 Heqn).
      unfold findlast.
      erewrite (@addnBA (size s1) (size s2) (find P (rev s2)).+1); 
        [ | by rewrite -size_rev -has_find has_rev].
      rewrite size_cat.
      cut (find P (rev (s1 ++ s2)) = (find P (rev s2)));
        [ intro RW; by rewrite RW | by rewrite rev_cat find_cat has_rev Heqn ].
    } {
      unfold findlast.
      cut (find P (rev (s1 ++ s2)) = (size s2 + find P (rev s1))); 
        [ intro H; rewrite size_cat H; by rewrite addnC -addnS (subnDl (size s2)) |].
      by rewrite rev_cat find_cat has_rev Heqn size_rev.
    } 
  Qed.

  Definition has_default (l : seq A) (p : has P l) : A.
  Proof.
    unfold has in p; destruct l; done.
  Defined.

  Lemma findlast_rcons (s : seq A) (x : A) :
    findlast (rcons s x) = if P x then size s else findlast s.
  Proof.
    remember (P x) as b eqn:Heqn; destruct b; unfold findlast; rewrite rev_rcons;
      simpl; rewrite -Heqn size_rcons; 
      [  by  rewrite subn1 | by rewrite subSS ].
  Qed.

  Lemma after_findlast (x : A) (s : seq A) (i : nat) :
    findlast s < i < size s -> P (nth x s i) = false.
  Proof.
    intro H; apply (rwP andP) in H; destruct H as [fls_lt_i i_lt_size].
    unfold findlast in fls_lt_i. 
    rewrite -(revK s) nth_rev size_rev; [ | done].
    apply: before_find.
    destruct s; [ discriminate |].
    assert (z : find P (rev (a :: s )) <= size (a :: s)) by ( rewrite -size_rev; exact: find_size).
    rewrite (ltn_subCl i_lt_size z).
    simpl size in *.
    rewrite subnS in fls_lt_i; rewrite ltnS.
    set m := ( a in a <= _). apply (@leq_trans m.-1.+1); [ exact: leqSpred| assumption].
  Qed.
    
  Lemma nth_findlast (a : A) (s : seq A) : has P s -> P (nth a s (findlast s)).
  Proof.
    revert s. apply: last_ind; [ done | ].
    intros s x IH H.
    rewrite findlast_rcons.
    rewrite nth_rcons.
    remember (P x) as b eqn:Heqn; apply symmetry in Heqn; destruct b;
      [ by rewrite ltnn eq_refl |
        rewrite has_rcons Heqn in H; simpl in H;
        rewrite has_findlast; [ exact: (IH H) | assumption]
      ].
  Qed.
End findlast.

Definition find_ord { n : nat } (P : pred 'I_n ) :
  has P (enum 'I_n) -> 'I_n.
Proof.
  intro H; exists (find P (enum 'I_n)); rewrite has_find in H; by rewrite size_enum_ord in H.
Defined.

Definition least_st {n : nat} (P : pred 'I_n) : pred 'I_n :=
  fun x => (P x && [forall y, P y ==> (x <= y)]).

Proposition find_ord_spec {n : nat} (P : pred 'I_n) (p : has P (enum 'I_n)) :
  least_st P (find_ord P p).
Proof.
  set k := (has_default _ P _ p).
  unfold least_st; apply/andP; split.
  { cut (nth k (enum 'I_n) (find P (enum 'I_n)) = find_ord P p);
      [ intro A; rewrite -A; by apply nth_find |].
    rewrite [find P (enum 'I_n)]/(val (find_ord P p)); exact: nth_ord_enum.
  }
  {
    apply (rwP forallP); intro x; apply/implyP; intro Px.
    rewrite -[_ <= _]negbK -ltnNge; apply (rwP negP); intro H; simpl in H.
    assert (z := (before_find k H)).
    cut ( nth k (enum 'I_n) x = x). { intro R; rewrite R in z; rewrite Px in z; discriminate. }
    exact: nth_ord_enum.
  }
Qed.

Definition findlast_ord {n : nat} (P : pred 'I_n) :
  has P (enum 'I_n) -> 'I_n.
Proof.
  intro;  exists (findlast _ P (enum 'I_n)); rewrite -{7}(size_enum_ord n).
  exact: has_findlast.
Defined.

Definition gtest_st {n : nat} (P : pred 'I_n) :=
  fun x : 'I_n => P x && [forall y : 'I_n, P y ==> (y <= x)].

Proposition gtest_st_spec {n : nat} (P : pred 'I_n) (p : has P (enum 'I_n)):
  gtest_st P (findlast_ord P p).
Proof.
  unfold gtest_st. set k := (has_default _ P _ p).
  apply/andP; split.
  {
    cut (nth k (enum 'I_n) (findlast _ P (enum 'I_n)) = findlast_ord P p);
      [ intro H; rewrite <- H; by apply nth_findlast |].
    rewrite [findlast 'I_n P (enum 'I_n)]/(val (findlast_ord P p)).
    exact: nth_ord_enum.
  }
  { 
    apply (rwP forallP); intro x. apply/implyP; intro Px.
    simpl. rewrite leqNgt. apply (rwP negP); intro fltx.
    cut (P x = false). { intro H; rewrite Px in H; discriminate. }
    rewrite -(nth_ord_enum k x).
    apply: after_findlast; rewrite fltx; simpl. rewrite size_enum_ord; by destruct x.
  }
Qed.

Definition least_st {n : nat} (P : pred 'I_n) : pred 'I_n :=
    fun x => (P x && [forall y, P y ==> (y <= x)]).


Close Scope nat.

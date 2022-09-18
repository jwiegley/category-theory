Require Import Category.Theory.Category
               Category.Instance.Simplex.AugmentedSimplexCategory
               Category.Instance.Simplex.NaturalNumberArithmetic.

Require Import 
        ssreflect ssrfun ssrbool
        mathcomp.ssreflect.seq
        mathcomp.ssreflect.ssrnat
        mathcomp.ssreflect.eqtype
        mathcomp.ssreflect.fintype
        mathcomp.ssreflect.finfun
        mathcomp.ssreflect.tuple
        mathcomp.ssreflect.ssrnat.


Definition d (n : nat) (i : 'I_(n.+1)) := [ffun j : 'I_n => lift i j].
Lemma s_subproof (n : nat) (i : 'I_(n.+1)) : forall j : 'I_(n.+2), unbump i j < n.+1.
Proof.
  move => j; rewrite ltnS -leq_bump /bump.
  case: i => [ival ibd] /=. rewrite -[ival <= n]ltnS ibd -ltnS /addn /=.
  by case: j.
Defined.

Definition s (n : nat) (i : 'I_(n.+1)) := [ffun j : 'I_(n.+2) => Ordinal (s_subproof n i j)].

Open Scope nat_scope.
Local Hint Resolve leq_trans : arith.
Proposition d_monotonic : forall n i, monotonic (d n i).
Proof.
  move => n i. 
  apply/monotonicP.
  move => x y ineq; rewrite 2! ffunE /lift /= /bump.
  case: (@leP i x).
  { rewrite /addn /=; move/leP => ineq1.
    have -> : (i <= y) by eapply leq_trans; by eauto.  done. }
  by auto with arith.
Defined.

Proposition s_monotonic: forall n i, monotonic (s n i).
Proof.
  move=> n. case => ival ibd; apply/monotonicP.
  case => [xval xbd] [yval ybd] /= ineq.
  rewrite /s ! ffunE /=.
  rewrite /unbump.
  case: (@ltP ival xval). { move/ltP => p;
                            have -> : (ival < yval) by (eapply leq_trans; eauto).
                            by apply: leq_sub. }
  { move/ltP => ineq2. rewrite -leqNgt in ineq2; rewrite subn0.
    rewrite leq_eqVlt in ineq; move: ineq; case/orP. {
      move/eqP <-. rewrite leqNgt in ineq2; move/negPf : ineq2 -> ; by rewrite subn0.
    }
    case: (ival < yval);
      move => a;
              (have -> : xval = xval.+1 - 1 by rewrite subn1); by apply: leq_sub.  }
Defined.


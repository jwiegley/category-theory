Require Import Category.Theory.Category
               Category.Theory.Isomorphism
               Category.Construction.Product
               Category.Theory.Functor
               Category.Structure.Monoidal
               Category.Lib.

Require Import
  Category.Instance.Simplex.AugmentedSimplexCategory
  Category.Instance.Simplex.NaturalNumberArithmetic.

Require Import
        ssreflect ssrfun ssrbool
        mathcomp.ssreflect.seq
        mathcomp.ssreflect.eqtype
        mathcomp.ssreflect.fintype
        mathcomp.ssreflect.finfun
        mathcomp.ssreflect.tuple
        mathcomp.ssreflect.ssrnat.

Definition monotonicP' (n m : nat) (f : 'I_m^n) := rwP (monotonicP f).

Local Hint Rewrite <- monotonicP' : brefl.
Notation "''I_' n" := (ordinal n).
Notation "n < m" := (leq (S n) m).
Notation "n <= m" := (leq n m).

Definition ordinal_sum_morphisms {n n' m m' : nat}
  (f : 'I_m ^n) (g: 'I_m'^n') : 'I_(m+m')^(n+n') :=
  finfun (fun x : 'I_(n+n') =>
            match split x with
            | inl a => @lshift m m' (f a)
            | inr b => @rshift m m' (g b)
            end).

Open Scope nat_scope.
Proposition sum_of_monotonics {n n' m m' : nat}
  (f : @monotonic_fn n m) (g: @monotonic_fn n' m') :
  monotonic (ordinal_sum_morphisms f g).
Proof.  
  move: f g => [f fm] [g gm] /=.
  apply/monotonicP => i j ineq; rewrite /ordinal_sum_morphisms 2! ffunE.
  case: (split_ordP i); move => i0 eqi; case: (split_ordP j); move => j0 eqj /=.
  { apply/monotonicP => //. 
  by rewrite -[nat_of_ord i0]/(nat_of_ord (lshift n' i0))
     -[nat_of_ord j0]/(nat_of_ord (lshift n' j0)) -eqi -eqj. } 
  { by auto with arith. } 
  { have z : j < i.  {
      rewrite eqj eqi /= [j0 < n + i0]/(S j0 <= n + i0).
      apply: (@leq_trans n). { exact: ltn_ord j0. } { exact: leq_addr. } }
    case/idPn : z. by rewrite -leqNgt. }
  rewrite leq_add2l. apply/(monotonicP _ gm).
  by rewrite -(leq_add2l n) -[n+i0]/(nat_of_ord (rshift n i0)) -[n+j0]/(nat_of_ord (rshift n j0))
     -eqi -eqj.
Qed.

Global Create HintDb monoidal discriminated.
Global Hint Resolve eq_ffun : monoidal.
Global Hint Rewrite ffunE : monoidal.
Global Hint Extern 100 => shelve : monoidal.

Ltac always_simplify := do !
( intros;
  match goal with
  | [|- _ = _ ] => apply: val_inj
  | [|- (@Setoid.equiv _ _ _ _)] => apply: val_inj
  | [|- val _ = val _ ] => rewrite ! /val
  | [|- context[fun_of_fin _] ] => rewrite ! ffunE
  | [|- context[@eq (finfun_of _) _ _] ] => apply: eq_ffun
  | [ _ : ordinal O |- _ ] => discriminate
  | [ x : 'I_0 |- _ ] =>
      (have ? : x < 0 by (apply: valP x)); discriminate
  end; move => /=;  try(done)).
                           
Global Hint Extern 90 => always_simplify : monoidal.
Global Hint Extern 8 (_ = _) => (do ! apply: f_equal => /=) : monoidal.
Global Hint Extern 9 =>
         match goal with
         |[ |- context[split _] ] => case: splitP
         end : monoidal.

(* Arguments addn / n m . *)
Ltac saturation_assert_term t varname :=
  match type of t with
    ?X =>
      match goal with
      | [ H : X |- _ ] => fail 1
      | _ => (assert (varname := t))
      end
  end.

(* This should be a less redundant version of saturation assert.
   It fails if (typeof t) already has a proof in the context, 
   up to convertibility. *)
Ltac sat_assert_term t :=
  let ttype := type of t in
  let pfname := fresh "P" in
  tryif (have pfname: ttype by assumption) then fail else
    have pfname: ttype by exact: t.

Ltac saturation_assert X pftactic :=
  match goal with
  | [ H : X |- _ ] => fail 1
  | _ => assert X by pftactic
  end.
Ltac example_usage :=
  match goal with
  |[ H : 'I_ ?x |- _ ] => 
     saturation_assert (H < x) ltac:(apply: (valP H))
  end.

(* Not happy about the current definition of saturation_define 
           because it doesn't "set" in the way I want it to. *)      
Ltac saturation_define A t :=
  match goal with
  | [ H := t |- _ ] => fail 1
  | _ => let termname := fresh "sat_term" in
         set termname : A := t
  end.

Ltac saturation_define' t :=
  match goal with
  | [ H := t |- _ ] => fail 1
  | _ => let termname := fresh "sat_term" in set (termname := t) in *
  end.

Ltac saturation_inequality_solver :=
  simpl in *; repeat(intro); try(apply: val_inj); rewrite /=;
  repeat(
      match goal with
      | [ H : ?x = ?x |- _ ] => clear H 
      | [ f : monotonic_fn_sig ?n ?m, x : ordinal ?n |- _ ] =>
          saturation_define 'I_ m (f x)
      |[ H : 'I_ ?x |- _ ] => 
         saturation_assert (is_true (S H <= x)) ltac:(apply: (valP H))
      |[ H : ?x = ?y |- _ ] => 
         saturation_assert (y = x) ltac:( exact : (@Logic.eq_sym _ x y H) )
      |[ H0 : ?x = ?y + ?z, H1 : ?z = ?t |- _ ] =>
             saturation_assert (@eq nat x (y + t)) ltac:(rewrite -H1; apply: H0)
      |[ H : context[addn ?x ?y] |- _] =>
         saturation_assert (is_true (x <= addn x y)) ltac:( apply: (leq_addr))
      |[ H0 : is_true (leq (S ?x) ?y), H1 : is_true (leq ?y ?z) |- _ ] => 
         saturation_assert (is_true (S x <= z))
           ltac:(apply:(@leq_trans _ _ _ H0 H1))
      |[ H0 : ?x = ?y + ?z |- _ ] => 
         saturation_assert (is_true (y <= x))
           ltac:(rewrite H0; apply: leq_addr)
      |[ H0 : is_true (S ?x <= ?y), H1 : ?y = ?z |- _ ] =>
         let QQ := fresh "var" in
         saturation_assert (is_true (S x <= z))
           ltac:(rewrite -[QQ in _ <= QQ]H1; apply: H0)
      |[ H : context[?n + ?m + ?k] |- _ ] => destruct (addnA n m k)
      |[ H0 : is_true (S ?n <= ?m), H1 : context[?p + ?n] |- _] =>
         saturation_assert (is_true (p + n < p + m))
           ltac:(rewrite -addnS leq_add2l; by apply: H0)
      |[ H : is_true ( ?p + ?n <= ?p + ?m ) |- _] =>
         saturation_assert (is_true (n <= m)) ltac:(rewrite -leq_add2l; by apply: H)
      end);
  try(solve [do ! match goal with 
        |[ H : ?x = ?x |- _ ] => clear H
        |[ H : ?p + ?n = ?p + ?m |- _ ] => saturation_assert (@eq nat n m)
                    ltac:(apply/eqP; rewrite -(eqn_add2l p); apply/eqP; exact: H)
        |[ H : context[?x + ?y + ?z] |- _ ] => destruct (addnA x y z)
        |[ H : ?x + ?y = ?z |- _ ] => destruct H
        |[ H : _ = _ |- _ ] => destruct H
       end; done | 
             (apply False_ind;
             unshelve eapply (@Bool.eq_true_false_abs _ _ (ltnn _)); (timeout 10 eauto))]).

Ltac msimp := unshelve auto with monoidal.


Open Scope category_scope.


Module MonoidalStructure.
  Local Notation I := 0.
  Definition tensor : Δ ∏ Δ ⟶ Δ.
    unshelve eapply (Build_Functor).
    { exact [fun nm : Δ ∏ Δ => let (n, m) := nm in n + m]. }
    { move => [n n']  [m m'] [f g] /=.
      unshelve eapply (Sub (ordinal_sum_morphisms f g) _ ).
      apply: sum_of_monotonics. }
    { move => [n n'] [m m'] [f g] [h k] [eq1 eq2].
      move: n n' m m' f g h k eq1 eq2.
      rewrite /fst /snd => n n' m m' f g h k.
      by move => -> ->. }
    { move => [n n']; msimp. }
    { 
      move => [n1 n2] [m1 m2] [k1 k2] [f1 f2] [g1 g2].
      move: n1 n2 m1 m2 k1 k2 f1 f2 g1 g2.
      rewrite /fst /snd.
      move => n1 n2 m1 m2 k1 k2 f1 f2 g1 g2 /=.
      msimp.
      { msimp. }
      all: msimp ; simpl in *.
      { saturation_inequality_solver. }
      { saturation_inequality_solver. } 
      { apply/eqP; erewrite <- eqn_add2l; apply/eqP; eauto. }
    } 
  Defined.

  Proposition monotonic_widen_ord (n m : nat) (p : n <= m) : monotonic (finfun (widen_ord p)).
  Proof.
    by apply/monotonicP => i j ineq; rewrite ! ffunE /nat_of_ord.
  Qed.

  Proposition monotonic_cast_ord (n m : nat) (p : n = m) : monotonic (finfun (cast_ord p)).
  Proof.
    by apply/monotonicP => i j ineq; rewrite ! ffunE /nat_of_ord.
  Qed.

  Global Instance eq_iso (n m : finord) (p : n = m) : Isomorphism n m.
  Proof.
    unshelve eapply Build_Isomorphism.
    { refine (Sub (finfun (cast_ord p)) (monotonic_cast_ord _ _ _)). }
    { by refine (Sub (finfun (cast_ord (Logic.eq_sym p))) (monotonic_cast_ord _ _ _)). }
    { apply: val_inj => /= ; apply eq_ffun => x; rewrite ! ffunE /=; 
      by rewrite cast_ord_comp cast_ord_id. }
    { apply: val_inj => /= ; apply eq_ffun => x; rewrite ! ffunE /=; 
                                                by rewrite cast_ord_comp cast_ord_id. }

  Defined.

  Ltac simpl_addn := repeat( match goal with | [ H : context[ addn _ _] |- _ ] => move: H end);
                     rewrite /addn /=.
  
  Ltac push := match goal with [ H : _ |- _ ] => revert H end.
 
   Definition MonoidalStructure : @Monoidal finord.
     unshelve eapply Build_Monoidal.
    { exact I. (* Unit *)}
    { exact tensor. (* Tensor functor *) }
    { move => n /=. rewrite /addn /=. (* Unit_left 0 + x ≅ x *)
      apply:iso_id. }
    { move => n /=. apply: eq_iso; auto with arith. (* Unit right *)}
    { move => n m k /=.  (* Associator *) 
      apply: eq_iso. auto with arith. }
    { simpl. msimp.
      simpl_addn. move => x0 eq; (do 2! apply: f_equal); by apply: val_inj. }
    { msimp. simpl_addn => a. msimp. } 
    { msimp. }
    { msimp. rewrite /=. msimp. }
    { move => n n' m m' k k'.
      msimp. { msimp. { saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      { saturation_inequality_solver. }
      { msimp. { saturation_inequality_solver. }
        { apply/eqP. rewrite -(eqn_add2l n). apply/eqP.
          saturation_inequality_solver. }
        { saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      apply/eqP; rewrite -addnA (eqn_add2l n'); apply/eqP.
      msimp => /=. { saturation_inequality_solver. } 
      {  apply/eqP; rewrite (eqn_add2l m'); apply/eqP; do 2! apply: f_equal.
         saturation_inequality_solver. }
    }
    { move => n n' m m' k k'.
      msimp. { msimp. { rewrite /=; do 2! apply: f_equal; saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      { msimp. { saturation_inequality_solver. }
        { saturation_inequality_solver. }
        { apply/eqP. rewrite (eqn_add2l n'). apply/eqP => /=. do 2! apply: f_equal. 
          saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      { saturation_inequality_solver. }
      { apply/eqP. rewrite -addnA (eqn_add2l n'). apply/eqP => /=.
        msimp; saturation_inequality_solver. } 
    }
    {
      msimp.
     { msimp. saturation_inequality_solver. }
     { msimp. saturation_inequality_solver. }
     { msimp. do 5! push. move=> [x0val xbd] [kval kbd] /=. rewrite addn0 in xbd *.
       by move => -> . }
     { msimp. do 5! push.
       move=> [x0val xbd] [kval kbd] /=. rewrite addn0 in xbd *.
       unlock addn => /= -> k0. move/eqP => a; apply/eqP. by rewrite eqn_add2l in a. }
    }
    { move => n m k l. msimp.  { 
        push.
      { case:splitP.
        { simpl in *. move => x_nmk eq_nmk. rewrite ffunE /=. by move <-. }
        { simpl in *. saturation_inequality_solver. } } } 
      { push; case: splitP.
        { move => j eq /=; by rewrite ffunE /= => <-. }
        { move => j eq /=. rewrite ffunE /= {}eq. by rewrite ! addnA. }
      }
    } 
Defined.
End MonoidalStructure.

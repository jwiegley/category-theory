Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Simplex.AugmentedSimplexCategory.
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

Open Scope nat_scope.
(* Notation "''I_' n" := (ordinal n). *)
(* Notation "n < m" := (leq (S n) m). *)
(* Notation "n <= m" := (leq n m). *)

Definition ordinal_sum_morphisms {n n' m m' : nat}
  (f : 'I_m ^n) (g: 'I_m'^n') : 'I_(m+m')^(n+n') :=
  finfun (fun x : 'I_(n+n') =>
            match split x with
            | inl a => @lshift m m' (f a)
            | inr b => @rshift m m' (g b)
            end).

Proposition sum_of_monotonics {n n' m m' : nat}
  (f : @monotonic_fn n m) (g: @monotonic_fn n' m') :
  monotonic (ordinal_sum_morphisms f g).
Proof.
  destruct f as [f fm], g as [g gm]; simpl.
  apply/monotonicP; intros i j ineq.
  unfold ordinal_sum_morphisms; rewrite 2! ffunE.
  destruct (split_ordP i) as [i0 eqi | i0 eqi];
  destruct (split_ordP j) as [j0 eqj | j0 eqj]; simpl.
  { apply/monotonicP; [ exact fm | ].
    (* We have ineq: i <= j, and i = i0 & j = j0 as natural numbers, so i0 <= j0. *)
    by rewrite -[nat_of_ord i0]/(nat_of_ord (lshift n' i0))
     -[nat_of_ord j0]/(nat_of_ord (lshift n' j0)) -eqi -eqj. } 
  { by auto with arith. } 
  { (* Inconsistent hypotheses, we have ineq : i <= j but also j < i, contradiction. *)
    assert (j < i) as z.  {
      rewrite eqj eqi /= [j0 < n + i0]/(S j0 <= n + i0).
      apply: (@leq_trans n); [ exact: ltn_ord j0 | exact: leq_addr ].
    } 
    case/idPn : z. by rewrite -leqNgt. }
  { 
    rewrite leq_add2l. apply/(monotonicP _ gm).
    (* Similar to part 2 above, i = i0 and j = j0. *)
    by rewrite -(leq_add2l n) -[n+i0]/(nat_of_ord (rshift n i0))
       -[n+j0]/(nat_of_ord (rshift n j0)) -eqi -eqj.
  } 
Qed.

Global Create HintDb monoidal discriminated.
Global Hint Resolve eq_ffun : monoidal.
Global Hint Rewrite ffunE : monoidal.

(* The following line of code was suggested by Theo Winterhalter.  The default behavior of
   auto is to try and solve the goal completely or make no changes.  With the following
   line of code, once auto has exhausted all other options (all hints with cost < 100) it
   shelves the goal, thus *succeeding*; ergo all previous changes it made to the goal
   remain in place.

   This is convenient in situations where you expect auto to make unambiguous progress
   toward the goal even if it does not completely solve it.  *)
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

(* If some other term of the same type of t is already in the context, fail;
   else add t to the context. *)
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

(* If the proposition X already has a proof in the context, fail;
   otherwise prove X by executing pftactic and add the resulting term to the context. *)
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
(* Add a new definition to the context unless this definition is already in the context *)
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

(* This solver either proves an equality of natural number arithmetic or
   identifies a contradiction of the form j < j, arising from 
   some circular chain of inequalities j < j1, j1 <= j2,... jn <= j. 
   It is used heavily in checking the naturality conditions for the monoidal structure on
   the simplex cat below.
*)
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
  (* Check ordinal_sum_morphisms. *)
  (* Check @Sub _ _ (monotonic_fn _ _). *)
  
  (* Program Definition tensor : Δ ∏ Δ ⟶ Δ := *)
  (*   {| *)
  (*     fobj := fun nm => let (n, m) := nm in n + m; *)
  (*     fmap := fun nn' =>  *)
  (*             fun mm' =>  *)
  (*             fun fg => let (f, g) := fg in *)
  (*                       (@Sub ('I_(mm'.1 + mm'.2)^(nn'.1 + nn'.2)) *)
  (*                          monotonic (monotonic_fn _ _) (ordinal_sum_morphisms f g) _); *)
  (*     fmap_respects := fun nn' mm' _ _ => _ ; *)
  (*     fmap_id := fun _ => val_inj _ ; *)
  (*     fmap_comp := fun _ _ _ _ _ => val_inj _; *)
  (*   |}. *)
  (* Next Obligation. exact: sum_of_monotonics. Qed. *)
  (* Next Obligation. *)
  (*   do 2! match goal with [ H : eq _ _ |- _ ] => destruct H end; reflexivity. *)
  (* Qed. *)
  (* Next Obligation. *)
  Definition tensor : Δ ∏ Δ ⟶ Δ.
    unshelve eapply (Build_Functor).
    { exact [fun nm : Δ ∏ Δ => let (n, m) := nm in n + m]. }
    { intros [n n']  [m m'] [f g]; simpl.
      unshelve eapply (Sub (ordinal_sum_morphisms f g) _ ).
      apply: sum_of_monotonics. }
    { intros [n n'] [m m'] [f g] [h k] [eq1 eq2];
               revert n n' m m' f g h k eq1 eq2;
               rewrite /fst /snd; intros n n' m m' f g h k;
               intro rew1; rewrite rew1;
               intro rew2; rewrite rew2; reflexivity. }
    { intros [n n']; msimp. }
    { intros [n1 n2] [m1 m2] [k1 k2] [f1 f2] [g1 g2].
      revert n1 n2 m1 m2 k1 k2 f1 f2 g1 g2.
      rewrite /fst /snd.
      intros n1 n2 m1 m2 k1 k2 f1 f2 g1 g2; simpl.
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
    by apply/monotonicP; intros i j ineq; rewrite ! ffunE.
  Qed.

  Proposition monotonic_cast_ord (n m : nat) (p : n = m) : monotonic (finfun (cast_ord p)).
  Proof.
    by apply/monotonicP; intros i j ineq; rewrite ! ffunE.
  Qed.

  Global Instance eq_iso (n m : finord) (p : n = m) : Isomorphism n m.
  Proof.
    unshelve eapply Build_Isomorphism.
    { by refine (Sub (finfun (cast_ord p)) (monotonic_cast_ord _ _ _)). }
    { by refine (Sub (finfun (cast_ord (Logic.eq_sym p))) (monotonic_cast_ord _ _ _)). }
    { apply: val_inj; simpl; apply eq_ffun; intro x; rewrite ! ffunE; 
      by rewrite cast_ord_comp cast_ord_id. }
    { apply: val_inj; simpl; apply eq_ffun; intro x; rewrite ! ffunE; 
        by rewrite cast_ord_comp cast_ord_id. }
  Defined.

  Ltac simpl_addn := repeat( match goal with | [ H : context[ addn _ _] |- _ ] => move: H end);
                     rewrite /addn /=.
  
  Ltac push := match goal with [ H : _ |- _ ] => revert H end.
  Definition MonoidalStructure : @Monoidal finord.
     unshelve eapply Build_Monoidal.
    { exact I. (* Unit *)}
    { exact tensor. (* Tensor functor *) }
    { intro n; rewrite /addn; simpl. (* Unit_left 0 + x ≅ x *)
      exact: iso_id. }
    { intro n; simpl; apply: eq_iso; by auto with arith. (* Unit right *)}
    { intros n m k ; simpl.  (* Associator *) 
      by apply: eq_iso; auto with arith. }
    { simpl. msimp.
      simpl_addn. intros x0 eq; (do 2! apply: f_equal); by apply: val_inj. }
    { msimp. simpl_addn ; intro a; by msimp. } 
    { by msimp. }
    { by msimp; simpl;  msimp. }
    { intros n n' m m' k k'.
      msimp.  { msimp; saturation_inequality_solver. }
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
    { intros n n' m m' k k'.
      msimp. { msimp. { rewrite /=; do 2! apply: f_equal; saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      { msimp. { saturation_inequality_solver. }
        { saturation_inequality_solver. }
        { apply/eqP. rewrite (eqn_add2l n'). apply/eqP; simpl. do 2! apply: f_equal. 
          saturation_inequality_solver. }
        { saturation_inequality_solver. }
      }
      { saturation_inequality_solver. }
      { apply/eqP. rewrite -addnA (eqn_add2l n'). apply/eqP ; simpl.
        msimp; saturation_inequality_solver. } 
    }
    {
      msimp.
     { msimp. saturation_inequality_solver. }
     { msimp. saturation_inequality_solver. }
     { msimp. do 5! push. intros [x0val xbd] [kval kbd]; simpl. rewrite addn0 in xbd *.
       intro H; rewrite H. done. }
     { msimp. do 5! push.
       intros [x0val xbd] [kval kbd] ; simpl;  rewrite addn0 in xbd *.
       unlock addn; simpl.
       intro H; rewrite H; clear H; intro k0.
       move/eqP => a. apply/eqP. rewrite eqn_add2l in a; done.
     } }
    { intros n m k l. msimp;
        do 3! push; intros x e.
      { destruct (splitP x).
        { simpl in *. rewrite ffunE. saturation_inequality_solver. }
        { simpl in *. saturation_inequality_solver. } }
      { destruct (splitP x).
        {  rewrite ffunE. intro H; rewrite <- H. done. }
        { rewrite ffunE. intro H; rewrite <- H.
          simpl. by rewrite ! addnA. }
      }
    } 
Defined.
End MonoidalStructure.

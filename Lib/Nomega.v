Set Warnings "-compatibility-notation".
Set Warnings "-deprecated".

Require Export
  Coq.Arith.Arith
  Coq.NArith.NArith
  Coq.micromega.Lia.

Local Open Scope N_scope.

Corollary sumbool_split : forall P Q : Prop,
  {P} + {~P} -> {Q} + {~Q} -> {P /\ Q} + {~ (P /\ Q)}.
Proof. intros; intuition. Qed.

Section N_theory.

Variables n m : N.

Lemma Neq_in : nat_of_N n = nat_of_N m -> n = m.
Proof.
  lia.
Qed.

Lemma Neq_out : n = m -> nat_of_N n = nat_of_N m.
Proof.
  lia.
Qed.

Lemma Nneq_out : n <> m -> nat_of_N n <> nat_of_N m.
Proof. intuition; apply Neq_in in H0; tauto. Qed.

Lemma Nlt_in : (nat_of_N n < nat_of_N m)%nat -> n < m.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_lt _ _)); assumption.
Qed.

Lemma Nlt_out : n < m -> (nat_of_N n < nat_of_N m)%nat.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.

Lemma Nle_in : (nat_of_N n <= nat_of_N m)%nat -> n <= m.
Proof.
  unfold N.le; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_le _ _)); assumption.
Qed.

Lemma Nle_out : n <= m -> (nat_of_N n <= nat_of_N m)%nat.
Proof.
  unfold N.le; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_le; assumption.
Qed.

Lemma Ngt_out : n > m -> (nat_of_N n > nat_of_N m)%nat.
Proof.
  unfold N.gt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_gt; assumption.
Qed.

Lemma Ngt_in : (nat_of_N n > nat_of_N m)%nat -> n > m.
Proof.
  unfold N.gt; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_gt; assumption.
Qed.

Lemma Nge_out : n >= m -> (nat_of_N n >= nat_of_N m)%nat.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_ge; assumption.
Qed.

Lemma Nge_in : (nat_of_N n >= nat_of_N m)%nat -> n >= m.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_ge; assumption.
Qed.

Lemma Nlt_dec : {n < m} + {~ n < m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - right; congruence.
  - left; congruence.
  - right; congruence.
Qed.

Lemma Nle_dec : {n <= m} + {~ n <= m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - left; congruence.
  - left; congruence.
  - right; congruence.
Qed.

Lemma Ngt_dec : {n > m} + {~ n > m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - right; congruence.
  - right; congruence.
  - left; congruence.
Qed.

Lemma Nge_dec : {n >= m} + {~ n >= m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - left; congruence.
  - right; congruence.
  - left; congruence.
Qed.

End N_theory.

(*** tactics ***)

Ltac nsimp := simpl; repeat progress (autorewrite with N; simpl).
Ltac nsimp_H H :=
  simpl in H; repeat progress (autorewrite with N in H; simpl in H).

Hint Extern 3 (Decidable.decidable (_ = _))  => apply N.eq_decidable.
Hint Extern 3 (Decidable.decidable (_ < _))  => apply N.lt_decidable.
Hint Extern 3 (Decidable.decidable (_ <= _)) => apply N.le_decidable.

Lemma not_and_implication : forall (P Q: Prop), ( ~ (P /\ Q) ) <-> (P -> ~ Q).
Proof. firstorder. Qed.

Ltac norm_N_step :=
  match goal with
  | [ |- ~ _ ] => unfold not; intros

  | [ H : is_true _ |- _ ] => unfold is_true in H
  | [ |- is_true _ ] => unfold is_true

  | [ H : negb _ = true |- _ ] => apply Bool.negb_true_iff in H
  | [ |- negb _ = true ] => apply Bool.negb_true_iff

  | [ H : (_ <? _)  = true  |- _ ] => apply N.ltb_lt in H
  | [ H : (_ <? _)  = false |- _ ] => apply N.ltb_ge in H
  | [ H : (_ <=? _) = true  |- _ ] => apply N.leb_le in H
  | [ H : (_ <=? _) = false |- _ ] => apply N.leb_gt in H
  | [ H : (_ =? _)  = true  |- _ ] => apply N.eqb_eq in H; subst
  | [ H : (_ =? _)  = false |- _ ] => apply N.eqb_neq in H

  | [ |- (_ <? _)  = true  ] => apply N.ltb_lt
  | [ |- (_ <? _)  = false ] => apply N.ltb_ge
  | [ |- (_ <=? _) = true  ] => apply N.leb_le
  | [ |- (_ <=? _) = false ] => apply N.leb_gt
  | [ |- (_ =? _)  = true  ] => apply N.eqb_eq
  | [ |- (_ =? _)  = false ] => apply N.eqb_neq

  | [ H : _ /\ _ |- _ ] => destruct H

  | [ H : (_ && _)%bool = true |- _ ] =>
    apply Bool.andb_true_iff in H; destruct H
  | [ H : (_ && _)%bool = false |- _ ] =>
    apply Bool.andb_false_iff in H; destruct H

  | [ |- (_ && _)%bool = true  ] => apply Bool.andb_true_iff; split
  | [ |- (_ && _)%bool = false ] => apply Bool.andb_false_iff

  | [ H : { _ : N | _ } |- _ ] => destruct H; simpl in *

  | [ |- {?P /\ ?Q} + {(?P /\ ?Q) -> False} ] => apply sumbool_split

  | [ |- {?n =  ?m} + {?n <> ?m} ] => apply N.eq_dec

  | [ |- {?n <  ?m} + {(?n <  ?m) -> False} ] => apply Nlt_dec
  | [ |- {?n <= ?m} + {(?n <= ?m) -> False} ] => apply Nle_dec
  | [ |- {?n >  ?m} + {(?n >  ?m) -> False} ] => apply Ngt_dec
  | [ |- {?n >= ?m} + {(?n >= ?m) -> False} ] => apply Nge_dec

  | [ H : (_ < _)  -> False |- _ ] => apply N.nlt_ge in H
  | [ H : (_ <= _) -> False |- _ ] => apply N.nle_gt in H

  | [ H : _ <  _ <  _ |- _ ] => destruct H
  | [ H : _ <= _ <  _ |- _ ] => destruct H
  | [ H : _ <  _ <= _ |- _ ] => destruct H
  | [ H : _ <= _ <= _ |- _ ] => destruct H

  | [ H : (?x <  ?y <  ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <= ?y <  ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <  ?y <= ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <= ?y <= ?z) -> False |- _ ] => apply Decidable.not_and in H

  | [ |- (?x <  ?y <  ?z) -> False ] => apply Decidable.not_and
  | [ |- (?x <= ?y <  ?z) -> False ] => apply Decidable.not_and
  | [ |- (?x <  ?y <= ?z) -> False ] => apply Decidable.not_and
  | [ |- (?x <= ?y <= ?z) -> False ] => apply Decidable.not_and

  | [ H : (?x <  ?y /\ ?w <  ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <= ?y /\ ?w <  ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <  ?y /\ ?w <= ?z) -> False |- _ ] => apply Decidable.not_and in H
  | [ H : (?x <= ?y /\ ?w <= ?z) -> False |- _ ] => apply Decidable.not_and in H

  | [ |- (?x <  ?y /\ ?w <  ?z) -> False ] => apply not_and_implication; intros
  | [ |- (?x <= ?y /\ ?w <  ?z) -> False ] => apply not_and_implication; intros
  | [ |- (?x <  ?y /\ ?w <= ?z) -> False ] => apply not_and_implication; intros
  | [ |- (?x <= ?y /\ ?w <= ?z) -> False ] => apply not_and_implication; intros

  | [ |- _ <  _ <  _ ] => split
  | [ |- _ <= _ <  _ ] => split
  | [ |- _ <  _ <= _ ] => split
  | [ |- _ <= _ <= _ ] => split

  | [ H : ?n < ?m |- ?n < ?m + ?o ] => apply (N.lt_lt_add_r _ _ _ H)
  | [ H : 0 < ?m  |- ?n < ?n + ?m ] => apply (N.lt_add_pos_r _ _ H)

  | [ H1 : ?n <= ?m, H2 : ?m <= ?n |- _ ] =>
    pose proof (N.le_antisymm _ _ H1 H2); subst; clear H1 H2

  | [ H : _ = _ |- _ ] => subst
  end.

Ltac norm_N := repeat progress (norm_N_step; auto).

Ltac pre_nomega :=
  first
  [ discriminate
  | tauto
  | congruence
  | unfold not in *; autounfold in *; nsimp; intros; norm_N; nsimp;
    repeat match goal with
    | [ H : _ = _          |- _ ] => apply Neq_out in H; nsimp_H H
    | [ H : _ <> _         |- _ ] => apply Nneq_out in H; nsimp_H H
    | [ H : _ = _ -> False |- _ ] => apply Nneq_out in H; nsimp_H H
    | [ H : _ < _          |- _ ] => apply Nlt_out in H; nsimp_H H
    | [ H : _ <= _         |- _ ] => apply Nle_out in H; nsimp_H H
    | [ H : _ > _          |- _ ] => apply Ngt_out in H; nsimp_H H
    | [ H : _ >= _         |- _ ] => apply Nge_out in H; nsimp_H H

    | [ |- _ = _  ] => apply Neq_in; nsimp
    | [ |- _ < _  ] => apply Nlt_in; nsimp
    | [ |- _ <= _ ] => apply Nle_in; nsimp
    | [ |- _ > _  ] => apply Ngt_in; nsimp
    | [ |- _ >= _ ] => apply Nge_in; nsimp
    end ].

Ltac nomega' :=
  pre_nomega;
  repeat progress match goal with
  | _ => lia || (unfold nat_of_P in *; simpl in *; lia)

  | [ H : _ \/ _ |- _ ] => destruct H; nomega'
  | [ |- _ /\ _ ]       => split; intros; nomega'
  | [ |- _ <-> _ ]      => split; intros; nomega'
  | [ |- _ \/ _ ]       => first [ solve [ left; nomega' ]
                                 | solve [ right; nomega' ] ]
  end.

Ltac nomega  := solve [ abstract nomega' | autounfold in *; abstract nomega' ].
Ltac nomega_ := solve [ nomega' | autounfold in *; nomega' ].


Lemma Npeano_rect_eq :
  forall (P : N -> Type) (a : P 0)
         (f g : forall n : N, P n -> P (N.succ n)) (n : N),
    (forall (n : N) (p : P n), f n p = g n p)
      -> N.peano_rect P a f n = N.peano_rect P a g n.
Proof.
  intros.
  induction n using N.peano_ind; simpl.
    reflexivity.
  rewrite !N.peano_rect_succ.
  rewrite H.
  f_equal.
  assumption.
Qed.

Lemma Npeano_rec_eq : forall (P : N -> Set) (z : P 0) f g n,
  (forall k x y, k < n -> x = y -> f k x = g k y)
    -> N.peano_rec P z f n = N.peano_rec P z g n.
Proof.
  intros.
  destruct n using N.peano_ind.
    reflexivity.
  rewrite !N.peano_rec_succ.
  apply H.
    nomega.
  apply IHn.
  intros; subst.
  apply H.
    nomega.
  reflexivity.
Qed.

Lemma Npeano_rec_list_app : forall (A : Set) (z : list A) f g n m,
  (N.peano_rec (fun _ => list A) z (fun x rest => f x :: rest) n
     ++ N.peano_rec (fun _ => list A) z
                    (fun x rest => g x :: rest) m)%list =
  N.peano_rec (fun _ => list A)
              (z ++ N.peano_rec (fun _ => list A) z
                                (fun x rest => g x :: rest) m)%list
              (fun x rest => f x :: rest)%list n.
Proof.
  intros.
  generalize dependent z.
  destruct n using N.peano_ind; simpl; intros.
    reflexivity.
  rewrite !N.peano_rec_succ.
  rewrite <- List.app_comm_cons.
  f_equal.
  apply IHn.
Qed.

Lemma Npeano_rec_list_add : forall (A : Set) (z : list A) f g h n m,
  (forall k x y, k < n + m -> x = y ->
     ((if k <? m
       then g k
       else f (k - m)) :: x)%list = h k y) ->
  N.peano_rec (fun _ => list A)
              (N.peano_rec (fun _ => list A) z
                           (fun k rest => g k :: rest) m)%list
              (fun k rest => f k :: rest)%list n =
  N.peano_rec (fun _ => list A) z h (n + m).
Proof.
  intros.
  destruct n using N.peano_ind; simpl; intros.
    apply Npeano_rec_eq with (P := fun _ => list A).
    intros; subst.
    rewrite <- H with (x:=y); trivial.
    assert (k <? m = true) by nomega.
    rewrite H1; reflexivity.
  rewrite N.add_succ_l, !N.peano_rec_succ.
  remember (N.peano_rec _ _ _ (n + m)) as xs.
  pose proof (H (n + m)) as H0.
  assert (n + m <? m = false) by nomega.
  rewrite H1, N.add_sub in H0; clear H1.
  apply H0; trivial.
    nomega.
  apply IHn.
  intros; subst.
  apply H.
    nomega.
  reflexivity.
Qed.

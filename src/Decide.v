Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.

Generalizable All Variables.

Section Decide.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Import EqNotations.

Lemma arrows_identity {f x} :
  arrows f = [] -> @termD C objs arrs x x f ≈ Some id.
Proof.
  unfold termD.
  generalize dependent x.
  induction f; simpl; intros; subst; auto.
  - equalities.
    reflexivity.
  - discriminate.
  - assert (arrows f1 = []). {
      destruct (arrows f2); simpl in H.
        now rewrite app_nil_r in H.
      destruct (arrows f1); simpl in H; inversion H.
    }
    assert (arrows f2 = []). {
      destruct (arrows f1); simpl in H.
        assumption.
      destruct (arrows f2); simpl in H; inversion H.
    }
    specialize (IHf2 x).
    destruct (termD_work objs _ _ f2) eqn:?.
    + destruct s.
      specialize (IHf1 x0).
      destruct (termD_work objs _ _ f1) eqn:?.
      * destruct s.
        equalities'; auto.
        equalities; try contradiction.
        red in X.
        red in X0.
        simpl_eq.
        rewrite X, X0; cat.
      * intuition.
    + intuition.
Qed.

Lemma arrows_morph {f a x y} {f' : objs x ~> objs y} :
  arrows f = [a] ->
  arrs a = Some (x; (y; f')) ->
  @termD C objs arrs x y f ≈ Some f'.
Proof.
  unfold termD.
  generalize dependent x.
  induction f; simpl; intros; subst; auto.
  - equalities.
  - inversion_clear H.
    rewrite H0.
    repeat equalities.
    reflexivity.
  - assert ((arrows f1 = [a] ∧ arrows f2 = []) ∨
            (arrows f2 = [a] ∧ arrows f1 = [])). {
      destruct (arrows f1); simpl in H.
        now right.
      destruct (arrows f2); simpl in H.
        rewrite app_nil_r in H.
        now left.
      destruct l; simpl in H.
        inversion H.
      destruct l0; simpl in H; inversion H.
    }
    destruct H1, p.
    + specialize (IHf1 _ f' e H0).
      pose proof (arrows_identity (x:=x) e0).
      unfold termD in X.
      destruct (termD_work objs _ _ f2) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction].
      destruct (termD_work objs _ _ f1) eqn:?; [|contradiction].
      destruct s; equalities; simpl_eq.
      red in IHf1.
      red in X.
      rewrite IHf1, X.
      cat.
    + specialize (IHf2 _ f' e H0).
      pose proof (arrows_identity (x:=y) e0).
      unfold termD in X.
      destruct (termD_work objs _ _ f1) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction].
      destruct (termD_work objs _ _ f2) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction]; simpl_eq.
      red in IHf2.
      red in X.
      rewrite Heqo.
      equalities.
      rewrite IHf2, X.
      cat.
Qed.

Lemma attempt {f x mid y} {f' : objs x ~> objs y} i i' j j' :
  @termD C objs arrs x y f ≈ Some f' ->
  @termD C objs arrs mid y i ≈ Some i' ->
  @termD C objs arrs x mid j ≈ Some j' ->
  arrows f = arrows i ++ arrows j -> f' ≈ i' ∘ j'.
Proof.
  unfold termD.
  generalize dependent y.
  generalize dependent mid.
  generalize dependent x.
  induction i; simpl; intros; repeat equalities; simpl_eq;
  (destruct (termD_work objs _ _ j) eqn:?; [|contradiction]; destruct s);
  (destruct (termD_work objs _ _ f) eqn:?; [|contradiction]; destruct s);
  equalities.
  - admit.
  - destruct (arrs a); [|contradiction].
    destruct s, s; equalities.
    admit.
  - unfold termD in *.
    destruct (termD_work objs _ _ i2) eqn:?; [|contradiction]; destruct s.
    destruct (termD_work objs _ _ i1) eqn:?; [|contradiction]; destruct s.
    equalities.
    rewrite <- X; clear X.
    rewrite <- X0; clear X0.
    rewrite <- X1; clear X1.
    rewrite <- app_assoc in H.
Admitted.

(*
Lemma arrows_compose {f x y} {f' : objs x ~> objs y} i j :
  arrows f = arrows i ++ arrows j ->
  @termD C objs arrs x y f ≈ Some f' ->
  ∃ mid i' j',
    @termD C objs arrs mid y i ≈ Some i' ∧
    @termD C objs arrs x mid j ≈ Some j' ∧
    f' ≈ i' ∘ j'.
Proof.
  unfold termD.
  generalize dependent j.
  generalize dependent i.
  generalize dependent y.
  generalize dependent x.
  generalize dependent f.
  induction i; simpl; intros; subst; auto.
  - destruct j; simpl in *; admit.
  - destruct j; simpl in *; admit.
  - 
  induction f; simpl; intros; subst; auto.
  - admit.
  - admit.
  - destruct (termD_work objs _ _ f2) eqn:?; [|contradiction]; destruct s.
    destruct (termD_work objs _ _ f1) eqn:?; [|contradiction]; destruct s.
    equalities; simpl_eq.

    specialize (IHf1 _ _ h0 f1 Identity).
    rewrite Heqo0, Eq_eq_dec_refl in IHf1.
    rewrite app_nil_r in IHf1.
    specialize (IHf1 eq_refl (reflexivity _)).

    specialize (IHf2 _ _ h Identity f2).
    rewrite Heqo, Eq_eq_dec_refl in IHf2.
    specialize (IHf2 eq_refl (reflexivity _)).

    destruct IHf1, s, s, p, p.
    destruct IHf2, s, s, p, p.
    simpl in *.
    equalities.

    rewrite Heqo0 in e.
    rewrite Pos_eq_dec_refl in e.

    exists x1, h0, h.

    split.
    + 
    + split.
      * admit.
      * now symmetry.

    destruct (termD_work objs _ _ i) eqn:?;
    destruct (termD_work objs _ _ j) eqn:?;
    try destruct s.
    + repeat equalities.
      * admit.
      * admit.
      * 
        destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    
Admitted.
*)
(*
    destruct (termD_work objs _ _ i) eqn:?; [|contradiction]; destruct s.
    destruct (termD_work objs _ _ j) eqn:?; [|contradiction]; destruct s.
    repeat equalities; simpl_eq.
      admit.
    admit.
  - assert ((arrows i = [a] ∧ arrows j = []) ∨
            (arrows j = [a] ∧ arrows i = [])). {
      destruct (arrows i); simpl in H.
        now right.
      destruct (arrows j); simpl in H.
        rewrite app_nil_r in H.
        now left.
      destruct l; simpl in H.
        inversion H.
      destruct l0; simpl in H; inversion H.
    }
    destruct H0, p.
    + pose proof (arrows_morph (x:=x) (y:=mid) (f':=j') e).
      unfold termD in X1.
      destruct (arrs a).
        destruct s, s.
        admit.
      admit.
    + admit.
 - specialize (IHf1 _ _ i' _ f' j').
Admitted.
*)

Lemma arrows_decide {x y f f' g g'} :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y g = Some g' ->
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  f' ≈ g'.
Proof.
  unfold termD; intros.
  destruct (termD_work objs _ _ f) eqn:?; [|discriminate]; destruct s.
  destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
  equalities; simpl_eq.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  generalize dependent g.
  generalize dependent x.
  induction f; simpl; intros; equalities.
  - destruct (arrows g) eqn:?; [|discriminate].
    pose proof (arrows_identity (x:=y) Heql).
    unfold termD in X.
    inversion Heqo; subst.
    rewrite Heqo0 in X.
    rewrite Eq_eq_dec_refl in X; simpl_eq.
    rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H2).
    red in X.
    rewrite <- X.
    reflexivity.
  - destruct (arrows g) eqn:?; [discriminate|].
    destruct l; [|now equalities].
    pose proof (arrows_morph (x:=x) (y:=y) (f':=f') Heql).
    unfold termD in X.
    inversion H1; subst; clear H1.
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    inversion Heqo0; subst; clear Heqo0.
    destruct (arrs a0); [|discriminate].
    destruct s, s; equalities; simpl_eq.
    red in X.
    rewrite <- X.
      rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H1).
      reflexivity.
    inversion Heqo.
    now rewrite H2.
  - destruct (termD_work objs _ _ f2) eqn:?; [|discriminate]; destruct s.
    destruct (termD_work objs _ _ f1) eqn:?; [|discriminate]; destruct s.
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    inversion Heqo; subst; clear Heqo.
    rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H2).
    clear H2.
    inversion Heqo0; subst; clear Heqo0.
    pose proof (attempt (x:=x) (mid:=x0) (y:=y) (f:=g) (f':=g') f1 h0 f2 h).
    unfold termD in X.
    rewrite Heqo1, Heqo2, Heqo3 in X.
    rewrite !Eq_eq_dec_refl in X.
    rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H2) in X |- *.
    clear H2.
    specialize (X (reflexivity _) (reflexivity _) (reflexivity _)).
    equalities; simpl_eq.
    intuition.
Qed.

End Decide.

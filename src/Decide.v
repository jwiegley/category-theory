Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.
Require Import Solver.Sound.

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

Lemma arrows_compose {f x mid y} {f' : objs x ~> objs y} i i' j j' :
  arrows f = arrows i ++ arrows j ->
  @termD C objs arrs x y f   = Some f' ->
  @termD C objs arrs mid y i = Some i' ->
  @termD C objs arrs x mid j = Some j' -> f' ≈ i' ∘ j'.
Proof.
  intros.
  destruct (arrowsD_sound_r objs arrs H0), p; clear H0.
  destruct (arrowsD_sound_r objs arrs H1), p; clear H1.
  destruct (arrowsD_sound_r objs arrs H2), p; clear H2.
  rewrite H in e0.
  rewrite e, e1, e3; clear H e e1 e3 f f' i' j'.
  unfold arrowsD in *.
  destruct (arrowsD_work _ _ _ _) as [[]|] eqn:?; [|discriminate].
  destruct (arrowsD_work _ _ _ (arrows i)) as [[]|] eqn:?; [|discriminate].
  destruct (arrowsD_work _ _ _ (arrows j)) as [[]|] eqn:?; [|discriminate].
  equalities; simpl_eq.
  inversion e0; subst; clear e0.
  inversion e2; subst; clear e2.
  inversion e4; subst; clear e4.
  pose proof (arrowsD_compose objs arrs Heqo).
  equalities.
  rewrite a; clear a.
  clear Heqo x0.
  rewrite Heqo1 in b0.
  inversion b0; subst.
  rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H1).
  rewrite Heqo0 in a0.
  inversion a0; subst.
  rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H0).
  reflexivity.
Qed.

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
    pose proof (arrows_compose (x:=x) (mid:=x0) (y:=y) (f:=g) (f':=g') f1 h0 f2 h).
    unfold termD in X.
    rewrite Heqo1, Heqo2, Heqo3 in X.
    rewrite !Eq_eq_dec_refl in X.
    rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H2) in X |- *.
    now specialize (X (symmetry H1)
                      (reflexivity _) (reflexivity _) (reflexivity _)); subst.
Qed.

End Decide.

Set Warnings "-notation-overridden".

Require Export Solver.Normal.

Unset Equations WithK.

Generalizable All Variables.

Section Sound.

Context `{Env}.

Remove Hints Coq.Coq : typeclass_instances.

Ltac destruct_arrows :=
  lazymatch goal with
  | [ H : context[match arrs ?t with _ => _ end] |- _ ] =>
    destruct (arrs t) as [[? []]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : context[match arrowsD_work ?o ?t with _ => _ end] |- _ ] =>
    destruct (arrowsD_work o t) as [[]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : context[match termD_work ?o ?t with _ => _ end] |- _ ] =>
    destruct (termD_work o t) as [[]|] eqn:?;
    [|discriminate + contradiction]
  | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
  | [ H : (?x; ?f) = (?y; ?g) |- _ ] => inversion H; subst
  end;
  try (equalities; let n := numgoals in guard n < 2);
  simpl_eq.

Theorem arrowsD_compose {xs ys dom cod f} :
  arrowsD_work dom (xs ++ ys) = Some (cod; f) ->
  ∃ mid g h, f ≈ g ∘ h ∧
    arrowsD_work mid xs = Some (cod; g) ∧
    arrowsD_work dom ys = Some (mid; h).
Proof.
  generalize dependent ys.
  generalize dependent cod.
  generalize dependent dom.
  induction xs; simpl; intros.
    simpl in H.
    exists cod, (@id _ _), f.
    split; cat.
  destruct_arrows.
  destruct ys eqn:?.
    exists dom, f, (@id _ _).
    rewrite app_nil_r in H0.
    split; cat.
    assert (
      match arrowsD_work dom (xs ++ a0 :: l) with
      | Some s =>
        match s with
        | (mid; g) =>
          match BinPos.Pos.eq_dec mid x with
          | left emid =>
            Some (x0; (h ∘ match emid with eq_refl => g end))
          | right _ =>
            @None (@sigT obj_idx
                         (fun cod : obj_idx =>
                            @hom _ (objs dom) (objs cod)))
          end
        end
      | None => None
      end = Some (existT _ cod f)) by (destruct xs; auto).
  clear H0.
  destruct_arrows.
  destruct (IHxs _ _ _ _ Heqo0), s, s, p, p.
  simpl in e1.
  destruct_arrows.
  destruct xs.
  - simpl in e0.
    inv e0.
    desh.
    exists _, h, x4.
    split.
    + rewrite e; cat.
    + split.
      * now rewrite Pos_eq_dec_refl.
      * now rewrite Heqo1, e1.
  - desh.
    eexists _, (h ∘ x3), x4.
    split.
    + rewrite e; cat.
    + split.
      * simpl in e0.
        destruct (arrs a1); cat; [|discriminate].
        rewrite e0.
        now rewrite Pos_eq_dec_refl.
      * now rewrite Heqo1, e1.
Qed.

Theorem arrowsD_sound {p dom cod f} :
  arrowsD dom cod (arrows p) = Some f ->
  ∃ f', f ≈ f' ∧ termD dom cod p = Some f'.
Proof.
  unfold termD, arrowsD.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; firstorder desh.
  - exists id; intuition.
  - exists f; intuition.
  - desh.
    destruct (arrowsD_compose Heqo), s, s, p, p.
    specialize (IHp1 cod x x0).
    rewrite e0 in IHp1.
    rewrite Eq_eq_dec_refl in IHp1.
    specialize (IHp1 (reflexivity _)).
    destruct IHp1, p.
    specialize (IHp2 x dom x1).
    rewrite e1 in IHp2.
    rewrite Eq_eq_dec_refl in IHp2.
    specialize (IHp2 (reflexivity _)).
    destruct IHp2, p.
    exists (x2 ∘ x3).
    split.
      now rewrite e, e2, e4.
    repeat destruct_arrows.
    rewrite Heqo1.
    equalities.
Qed.

Theorem arrowsD_compose_r {xs ys dom mid cod g h} :
  arrowsD_work mid xs = Some (cod; g) ->
  arrowsD_work dom ys = Some (mid; h) ->
  ∃ f, f ≈ g ∘ h ∧
    arrowsD_work dom (xs ++ ys) = Some (cod; f).
Proof.
  intros.
  generalize dependent ys.
  generalize dependent cod.
  generalize dependent dom.
  induction xs; simpl; intros.
    destruct_arrows; cat.
  desh.
  destruct xs; simpl.
    desh.
    rewrite H1.
    rewrite Pos_eq_dec_refl.
    destruct ys.
      inv H1.
      rewrite Pos_eq_dec_refl.
      rewrite <- (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H3).
      exists g; cat.
    exists (g ∘ h); cat.
  simpl in *.
  desh; desh; desh.
  destruct (IHxs dom h x _ eq_refl _ H1); clear IHxs.
  destruct p.
  rewrite e3.
  rewrite Pos_eq_dec_refl.
  exists (e0 ∘ x2).
  split; auto.
  now rewrite <- comp_assoc, <- e1.
Qed.

Theorem arrowsD_sound_r {p dom cod f} :
  termD dom cod p = Some f ->
  ∃ f', f ≈ f' ∧ arrowsD dom cod (arrows p) = Some f'.
Proof.
  unfold termD, arrowsD.
  generalize dependent cod.
  generalize dependent dom.
  induction p; simpl; intros; firstorder desh.
  - eexists; cat.
  - eexists; cat.
    now desh.
  - desh; desh; desh.
    specialize (IHp1 x cod e0).
    rewrite Heqo1 in IHp1.
    rewrite Eq_eq_dec_refl in IHp1.
    specialize (IHp1 (reflexivity _)).
    destruct IHp1, p.
    specialize (IHp2 dom x e).
    rewrite Heqo0 in IHp2.
    rewrite Eq_eq_dec_refl in IHp2.
    specialize (IHp2 (reflexivity _)).
    destruct IHp2, p.
    repeat desh.
    destruct (arrowsD_compose_r Heqo2 Heqo), p.
    exists x2.
    split.
      now rewrite e1, e3, e2.
    rewrite e4.
    now rewrite Pos_eq_dec_refl.
Qed.

Lemma termD_arrows dom cod x :
  termD dom cod x ≈ arrowsD dom cod (arrows x).
Proof.
  destruct (termD _ _ _) eqn:?, (arrowsD _ _ _) eqn:?.
  - apply arrowsD_sound in Heqo0.
    destruct Heqo0; cat.
    f_equiv.
    rewrite Heqo in H0.
    inv H0.
    now symmetry.
  - apply arrowsD_sound_r in Heqo.
    destruct Heqo; cat.
    rewrite H0 in Heqo0.
    discriminate.
  - apply arrowsD_sound in Heqo0.
    destruct Heqo0; cat.
    rewrite H0 in Heqo.
    discriminate.
  - reflexivity.
Qed.

Lemma arrows_decide {x y f f' g g'} :
  termD x y f = Some f' ->
  termD x y g = Some g' ->
  list_beq Eq_eqb (arrows f) (arrows g) = true -> f' ≈ g'.
Proof.
  intros.
  destruct (arrowsD_sound_r H0), p.
  destruct (arrowsD_sound_r H1), p.
  apply list_beq_eq in H2.
    rewrite H2 in e0.
    rewrite e, e1.
    rewrite e0 in e2.
    now inversion_clear e2.
  apply Eq_eqb_eq.
Qed.

Lemma termD_app {dom cod f g} :
  ∃ mid, termD dom cod (Comp f g)
           = termD mid cod f ∘[opt_arrs] termD dom mid g.
Proof.
  unfold termD; simpl.
  destruct (termD_work dom g) eqn:?.
  - destruct s.
    exists x.
    destruct f; simpl; intros.
    + rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x cod); subst; auto.
    + destruct (arrs a) eqn:?.
        destruct s, s.
        repeat desg; repeat desh; cat.
      repeat desg; repeat desh; cat.
    + destruct (termD_work x f2) eqn:?; auto.
      destruct s.
      destruct (termD_work x0 f1) eqn:?; auto.
      destruct s.
      rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x1 cod); subst; auto.
  - exists cod.
    destruct (termD_work cod f) eqn:?; auto.
    destruct s.
    destruct (Pos.eq_dec x cod); subst; auto.
Qed.

Lemma arrowsD_app {dom cod f g} :
  ∃ mid, arrowsD dom cod (f ++ g)
           ≈ arrowsD mid cod f ∘[opt_arrs] arrowsD dom mid g.
Proof.
  unfold arrowsD; simpl.
  destruct (arrowsD_work dom (f ++ g)) eqn:?.
    destruct s.
    destruct (arrowsD_compose Heqo), s, s, p, p.
    exists x0.
    destruct (Pos.eq_dec x cod); subst; simpl; cat;
    rewrite e0, e1;
    rewrite !Pos_eq_dec_refl; auto.
    destruct (Pos.eq_dec x cod); subst; [contradiction|];
    simpl; auto.
  exists cod.
  destruct (arrowsD_work cod f) eqn:?; cat.
  destruct (Pos.eq_dec x cod); subst; simpl; cat.
  destruct (arrowsD_work dom g) eqn:?; cat.
  destruct (Pos.eq_dec x cod); subst; simpl; cat.
  destruct (arrowsD_compose_r Heqo0 Heqo1), p.
  rewrite Heqo in e2.
  discriminate.
Qed.

Lemma arrowsD_apply dom cod (f g : Term arr_idx) :
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  arrowsD dom cod (arrows f) ||| false = true ->
  arrowsD dom cod (arrows f) = arrowsD dom cod (arrows g) ->
  termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  destruct (arrowsD dom cod (arrows f)) eqn:?; [|discriminate].
  destruct (arrowsD_sound Heqo), p.
  rewrite e0; clear e0.
  red.
  symmetry in H2.
  apply arrowsD_sound in H2.
  equalities.
  rewrite H2.
  rewrite <- e0, <- e.
  reflexivity.
Qed.

Definition list_equiv_termD (x y : Term arr_idx) :
  list_equiv (arrows x) (arrows y)
    -> ∀ dom cod, termD dom cod x ≈ termD dom cod y.
Proof.
  intros.
  apply list_equiv_eq in X; auto.
  rewrite !termD_arrows.
  now rewrite X.
Qed.

Global Program Instance termD_work_Proper {dom} :
  Proper (equiv ==> equiv) (@termD_work _ dom).
Next Obligation.
  repeat intro.
  pose proof (list_equiv_termD _ _ X).
  unfold termD in *.
  specialize (X0 dom).
  destruct (termD_work dom x) eqn:?; cat.
    specialize (X0 x0).
    rewrite Eq_eq_dec_refl in X0.
    desh; desh.
    simpl in X0.
    now rewrite eq_dec_refl.
  simpl.
  desg; auto.
  specialize (X0 x0).
  rewrite Eq_eq_dec_refl in X0.
  inv X0.
Qed.

Global Program Instance termD_Proper {dom cod} :
  Proper (equiv ==> equiv) (@termD _ dom cod).
Next Obligation.
  repeat intro.
  apply list_equiv_termD.
  exact X.
Qed.

Lemma exprAD_sound (e : Expr arr_idx) : exprAD e ↔ exprD e.
Proof.
  induction e; simpl; split; intros; firstorder auto.
  - destruct (arrowsD x y (arrows f)) eqn:?.
      destruct (arrowsD x y (arrows g)) eqn:?; [|contradiction].
      destruct (arrowsD_sound Heqo), p.
      destruct (arrowsD_sound Heqo0) ,p.
      now rewrite e0, e2, <- e, <- e1.
    destruct (arrowsD x y (arrows g)) eqn:?; [contradiction|].
    destruct (termD x y f) eqn:?.
      destruct (arrowsD_sound_r Heqo1), p.
      rewrite Heqo in e0.
      discriminate.
    destruct (termD x y g) eqn:?; auto.
    destruct (arrowsD_sound_r Heqo2), p.
    rewrite Heqo0 in e0.
    discriminate.
  - destruct (termD x y f) eqn:?.
      destruct (termD x y g) eqn:?; [|contradiction].
      destruct (arrowsD_sound_r Heqo), p.
      destruct (arrowsD_sound_r Heqo0), p.
      now rewrite e0, e2, <- e, <- e1.
    destruct (termD x y g) eqn:?; [contradiction|].
    destruct (arrowsD x y (arrows f)) eqn:?.
      destruct (arrowsD_sound Heqo1), p.
      rewrite Heqo in e0.
      discriminate.
    destruct (arrowsD x y (arrows g)) eqn:?; auto.
    destruct (arrowsD_sound Heqo2), p.
    rewrite Heqo0 in e0.
    discriminate.
Qed.

(* Program Instance Denote : Terms arr_idx ⟶ Coq := { *)
(*   fobj := fun _ => arr_idx; *)
(*   fmap := fun dom cod x => arrows x *)
(* }. *)

(*
Local Obligation Tactic := intros.

Global Program Instance Denote : Terms arr_idx ⟶ @opt_arrs cat := {
  fobj := objs;
  fmap := termD
}.
Next Obligation. now rewrite termD_Ident. Qed.
Next Obligation.
  destruct (@termD_app x z f g).
  rewrite e.
  destruct (eq_dec x0 y); subst.
    reflexivity.
  (* This cannot be a functor because Comp doesn't remember the type
     of the intermediate object, and there is only one correct choice. *)
Admitted.
*)

Lemma termD_Ident {x} : termD x x Ident = Some id.
Proof.
  unfold termD; simpl; intros.
  now rewrite Pos_eq_dec_refl.
Defined.

Lemma termD_Comp {f g dom cod h} :
  termD dom cod (Comp f g) = Some h ->
  ∃ mid f' g',
    h = f' ∘ g' ∧ termD mid cod f = Some f' ∧ termD dom mid g = Some g'.
Proof.
  unfold termD; simpl; intros;
  repeat desg; repeat desh.
  exists x, e0, e.
  split; auto.
  rewrite Heqo1.
  rewrite !Pos_eq_dec_refl.
  split; auto.
Defined.

Lemma termD_Comp_impl {f g dom mid cod f' g'} :
  termD mid cod f = Some f'
    -> termD dom mid g = Some g'
    -> termD dom cod (Comp f g) = Some (f' ∘ g').
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Program Definition DefinedTerms : Category := {|
  obj := obj_idx;
  hom := fun dom cod => ∃ f f', termD dom cod f = Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun _ => (Ident; (id; _));
  compose := fun _ _ _ '(f; (f'; _)) '(g; (g'; _)) => (Comp f g; (f' ∘ g'; _))
|}.
Next Obligation. now rewrite termD_Ident. Defined.
Next Obligation. now apply termD_Comp_impl. Defined.

Program Definition DefinedArrows : Category := {|
  obj := obj_idx;
  hom := fun dom cod => ∃ f f', arrowsD dom cod f ≈ Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun _ => ([]; (id; _));
  compose := fun _ _ _ '(f; (f'; _)) '(g; (g'; _)) => (f ++ g; (f' ∘ g'; _))
|}.
Next Obligation.
  unfold arrowsD; simpl; rewrite Pos_eq_dec_refl.
  reflexivity.
Qed.
Next Obligation.
  unfold arrowsD in *; simpl in *.
  repeat desh.
  destruct (arrowsD_compose_r Heqo1 Heqo0), p.
  rewrite e0, Pos_eq_dec_refl; simpl.
  now rewrite e, X2, X0.
Qed.

Global Program Instance Denote : DefinedTerms ⟶ cat := {
  fobj := objs;
  fmap := fun _ _ '(_; (f'; _)) => f'
}.

Global Program Instance Denote_Faithful : Faithful Denote.

End Sound.

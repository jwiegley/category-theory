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

Theorem arrowsD_work_compose {xs ys dom cod f} :
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
    exists cod, (@id cat _), f.
    split; cat.
  destruct_arrows.
  destruct ys eqn:?.
    exists dom, f, (@id cat _).
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

Corollary arrowsD_compose {xs ys dom cod f} :
  arrowsD dom cod (xs ++ ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    arrowsD mid cod xs = Some g ∧
    arrowsD dom mid ys = Some h.
Proof.
  unfold arrowsD; intros.
  repeat desh.
  destruct (arrowsD_work_compose Heqo), s, s, p, p.
  exists _, x0, x1.
  split; auto.
  rewrite e0, e1.
  equalities.
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
    destruct (arrowsD_work_compose Heqo), s, s, p, p.
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

Theorem arrowsD_work_compose_r {xs ys dom mid cod g h} :
  arrowsD_work mid xs = Some (cod; g) ->
  arrowsD_work dom ys = Some (mid; h) ->
  ∃ f, f ≈ g ∘ h ∧ arrowsD_work dom (xs ++ ys) = Some (cod; f).
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

Corollary arrowsD_compose_r {xs ys dom mid cod g h} :
  arrowsD mid cod xs = Some g ->
  arrowsD dom mid ys = Some h ->
  ∃ f, f ≈ g ∘ h ∧ arrowsD dom cod (xs ++ ys) = Some f.
Proof.
  unfold arrowsD; intros.
  repeat desh.
  destruct (arrowsD_work_compose_r Heqo0 Heqo), p.
  exists x.
  split; auto.
  rewrite e0.
  equalities.
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
    destruct (arrowsD_work_compose_r Heqo2 Heqo), p.
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

Lemma arrowsD_app dom cod f g :
  ∃ mid, arrowsD dom cod (f ++ g)
           ≈ arrowsD mid cod f ∘[opt_arrs] arrowsD dom mid g.
Proof.
  unfold arrowsD; simpl.
  destruct (arrowsD_work dom (f ++ g)) eqn:?.
    destruct s.
    destruct (arrowsD_work_compose Heqo), s, s, p, p.
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
  destruct (arrowsD_work_compose_r Heqo0 Heqo1), p.
  rewrite Heqo in e2.
  discriminate.
Qed.

Lemma arrowsD_cons {dom cod f fs f'} :
  arrowsD dom cod (f :: fs) = Some f' ->
    ∃ mid g' h',
      f' ≈ g' ∘ h'
        ∧ arrs f = Some (mid; (cod; g'))
        ∧ arrowsD dom mid fs = Some h'.
Proof.
  intros.
  unfold arrowsD in *; simpl in *.
  destruct (arrs f) eqn:?; [|discriminate].
  destruct s, s.
  destruct fs.
    repeat desh.
    repeat eexists.
      instantiate (1 := id); cat.
    equalities.
  destruct (arrowsD_work dom (a :: fs)) eqn:?.
    destruct s.
    repeat desh.
    repeat eexists.
      instantiate (1 := h0); cat.
    equalities.
  discriminate.
Qed.

Lemma arrowsD_dom_eq {dom cod f f' dom' cod' f''} :
     arrowsD dom cod f = Some f'
  -> arrowsD dom' cod' f = Some f''
  -> f <> nil
  -> dom = dom'.
Proof.
  destruct f using rev_ind; intros.
    contradiction.
  destruct (arrowsD_compose H0), s, s, p, p.
  destruct (arrowsD_compose H1), s, s, p, p.
  clear -e1 e4.
  unfold arrowsD in *; simpl in *.
  repeat desh; auto.
Qed.

Lemma arrowsD_cod_eq {dom cod f f' dom' cod' f''} :
     arrowsD dom cod f = Some f'
  -> arrowsD dom' cod' f = Some f''
  -> f <> nil
  -> cod = cod'.
Proof.
  destruct f; intros.
    contradiction.
  destruct (arrowsD_cons H0), s, s, p, p.
  destruct (arrowsD_cons H1), s, s, p, p.
  rewrite e0 in e3; clear e0.
  inv e3; split; auto.
Qed.

Lemma arrowsD_app_alt {dom mid cod f g f' fg'} :
  arrowsD dom mid g = Some f' ->
  arrowsD dom cod (f ++ g) = Some fg' ->
  arrowsD dom cod (f ++ g) ≈ arrowsD mid cod f ∘[opt_arrs] arrowsD dom mid g.
Proof.
  intros.
  destruct (arrowsD_app dom cod f g).
  rewrite H1 in e.
  destruct (arrowsD dom x g) eqn:?.
    destruct g.
      rewrite app_nil_r in *.
      unfold arrowsD in *; simpl in *.
      repeat desh; cat.
    rewrite (arrowsD_cod_eq H0 Heqo).
      now rewrite Heqo, H1.
    intro; discriminate.
  simpl in e.
  destruct (arrowsD x cod f); desh.
Qed.

Import EqNotations.

Lemma arrowsD_nil {dom cod f'} :
  arrowsD dom cod [] = Some f'
    -> ∃ H : dom = cod, f' = rew [fun x => _ ~> objs x] H in id.
Proof.
  unfold arrowsD; simpl.
  equalities.
  exists eq_refl.
  now inv H0.
Qed.

Lemma arrowsD_within {dom cod i j pre post f f' g g' h} :
     f <> nil                   (* this shouldn't be necessary *)
  -> arrowsD i j f = Some f'
  -> arrowsD i j g = Some g'
  -> arrowsD i j f ≈ arrowsD i j g
  -> arrowsD dom cod (pre ++ f ++ post) = Some h
  -> arrowsD dom cod (pre ++ f ++ post) ≈ arrowsD dom cod (pre ++ g ++ post).
Proof.
  intros fnil Hf Hg Hfg Hpfp.
  destruct (arrowsD_compose Hpfp); cat.
  pose proof (arrowsD_app_alt H1 Hpfp).
  rewrite X; clear X.
  destruct (arrowsD_compose H1); cat.
  pose proof (arrowsD_app_alt H3 H1).
  rewrite X; clear X.
  pose proof (arrowsD_cod_eq Hf H2 fnil).
  pose proof (arrowsD_dom_eq Hf H2 fnil).
  rewrite <- H4 in *; clear H4.
  rewrite <- H5 in *; clear H5.
  destruct (arrowsD_app dom cod pre (g ++ post)).
  destruct (arrowsD_app dom x5 g post).
  rewrite e, e2.
  assert (∃ h', arrowsD dom cod (pre ++ g ++ post) ≈ Some h').
    destruct (arrowsD_compose Hpfp), s, s, p, p.
    destruct (arrowsD_compose e5), s, s, p, p.
    pose proof (arrowsD_cod_eq Hf e7 fnil).
    pose proof (arrowsD_dom_eq Hf e7 fnil).
    subst.
    rewrite app_assoc in Hpfp.
    destruct (arrowsD_compose Hpfp), s, s, p, p.
    destruct (arrowsD_compose e10), s, s, p, p.
    pose proof (arrowsD_cod_eq Hf e14 fnil).
    pose proof (arrowsD_dom_eq Hf e14 fnil).
    subst.
    destruct (arrowsD_compose_r e13 Hg), p.
    destruct (arrowsD_compose_r e16 e11), p.
    rewrite <- app_assoc in e18.
    rewrite e18.
    now exists x10.
  destruct X as [h' Hpgp].
  destruct (arrowsD x6 x5 g) eqn:?.
    rewrite <- Heqo.
    destruct g.
      destruct (arrowsD_nil Heqo); subst; simpl_eq.
      rewrite Heqo.
      destruct (arrowsD_nil Hg); subst; simpl_eq.
      rewrite Hg in Hfg.
      rewrite Hfg.
      rewrite <- e2.
      simpl app in *.
      rewrite Hpgp in e.
      rewrite id_left.
      rewrite <- e.
      rewrite <- Hpgp.
      clear -Hf Hpfp fnil.
      destruct (arrowsD_compose Hpfp), s, s, p, p.
      destruct (arrowsD_compose e1), s, s, p, p.
      pose proof (arrowsD_cod_eq Hf e3 fnil).
      pose proof (arrowsD_dom_eq Hf e3 fnil).
      subst.
      destruct (arrowsD_compose_r e0 e4), p.
      rewrite e6, e4, e0.
      simpl.
      now symmetry.
    assert (a :: g ≠ nil) as gnil by (intro; discriminate).
    pose proof (arrowsD_cod_eq Hg Heqo gnil).
    pose proof (arrowsD_dom_eq Hg Heqo gnil).
    rewrite <- H4, <- H5.
    now rewrite Hfg.
  rewrite Hpgp in e.
  rewrite e2 in e.
  clear -e.
  simpl in *.
  destruct (arrowsD x5 cod pre); repeat desh.
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
  simpl.
  rewrite <- e0, <- e.
  reflexivity.
Qed.

Definition list_equiv_termD (x y : Term arr_idx) :
  arrows x = arrows y
    -> ∀ dom cod, termD dom cod x ≈ termD dom cod y.
Proof.
  intros.
  rewrite !termD_arrows.
  now rewrite H0.
Qed.

Definition option_ex_equiv {dom}
           (x y : option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) :=
  match x, y with
  | Some (cf; f), Some (cg; g) =>
    match eq_dec cf cg with
    | Specif.left H => f ≈ rew <- [fun x => _ ~> objs x] H in g
    | _ => False
    end
  | None, None => True
  | _, _ => False
  end.

Global Instance option_ex_equivalence {dom} :
  Equivalence (@option_ex_equiv dom).
Proof.
  unfold option_ex_equiv.
  equivalence.
  - destruct x; cat.
    now rewrite eq_dec_refl.
  - destruct x, y; cat; desh.
    now rewrite eq_dec_refl.
  - destruct x, y, z; cat; repeat desh.
    now transitivity e0.
Qed.

Global Program Instance option_ex_Setoid {dom} :
  Setoid (option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) := {
  equiv := option_ex_equiv
}.

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
  induction e; simpl; split; intros; firstorder auto;
  simpl in *; unfold opt_arrs_equiv.
  - destruct (arrowsD x y (arrows f)) eqn:?.
      destruct (arrowsD x y (arrows g)) eqn:?; [|contradiction].
      destruct (arrowsD_sound Heqo), p.
      destruct (arrowsD_sound Heqo0), p.
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
      rewrite e0, e2.
      simpl.
      now rewrite <- e, <- e1.
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
  unfold opt_arrs_equiv, arrowsD in *; simpl in *.
  repeat desh.
  destruct (arrowsD_work_compose_r Heqo1 Heqo0), p.
  rewrite e0, Pos_eq_dec_refl; simpl.
  now rewrite e, X2, X0.
Qed.

Global Program Instance Denote : DefinedTerms ⟶ cat := {
  fobj := objs;
  fmap := fun _ _ '(_; (f'; _)) => f'
}.

Global Program Instance Denote_Faithful : Faithful Denote.

End Sound.

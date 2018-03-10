(*
Program Definition arr_uncons {dom cod} `(f : ValidArrow dom cod) :
  ∃ mid (g : ValidArrow mid cod) (h : ValidArrow dom mid),
    f ≈ g ∘[Arrows] h ∧
    match getArrList f with
    | x :: xs => getArrList g = [x] ∧ getArrList h = xs
    | nil => getArrList g = nil ∧ getArrList h = nil
    end :=
  match f with
  | mkArr nil g H =>
    match Pos.eq_dec dom cod with
    | left _ => (dom; (f; (f; _)))
    | right _ => !
    end
  | mkArr (x :: xs) f' H =>
    match Normal.arrs x with
    | None => !
    | Some (mid; (cod'; g)) =>
      match Pos.eq_dec cod cod' with
      | left _ =>
        match arrowsD dom mid xs with
        | None => !
        | Some h => (mid; (mkArr [x] g _; (mkArr xs h _; _)))
        end
      | right _ => !
      end
    end
  end.
Next Obligation.
  split; auto.
  unfold arrowsD in H; simpl in H.
  rewrite Pos_eq_dec_refl in H.
  simpl_eq.
  rewrite <- H; cat.
Qed.
Next Obligation.
  unfold arrowsD in H; simpl in H.
  destruct (Pos.eq_dec dom cod); subst; contradiction.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous in e0.
  discriminate.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose Heqo), s, s, p, p.
  unfold arrowsD in Heq_anonymous.
  rewrite e1 in Heq_anonymous.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  simpl in *.
  destruct (Pos.eq_dec x0 mid); subst.
    discriminate.
  destruct (Pos.eq_dec mid x0); subst.
    contradiction.
  discriminate.
Qed.
Next Obligation.
  unfold arrowsD in *.
  simpl in *.
  rewrite <- Heq_anonymous0 in *.
  do 2 rewrite Pos_eq_dec_refl.
  reflexivity.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  destruct (Pos.eq_dec mid x0); subst; [|discriminate].
  simpl_eq.
  inversion e0; clear e0.
  rewrite H in e.
  apply Eqdep_dec.inj_pair2_eq_dec in H1.
    subst.
    unfold arrowsD in Heq_anonymous.
    rewrite e1 in Heq_anonymous.
    rewrite Pos_eq_dec_refl in Heq_anonymous.
    simpl_eq.
    inversion Heq_anonymous.
    subst.
    assumption.
  apply Pos.eq_dec.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  destruct (Pos.eq_dec mid x0); subst; [|discriminate].
  simpl_eq.
  inversion e0.
  subst.
  contradiction.
Qed.
*)

(*
Lemma arr_rect {dom} (P : ∀ cod, ValidArrow dom cod → Type) :
  (∀ f, f ≈[Arrows] id -> P dom f)
    → (∀ mid cod (x : arr_idx) (xs : list arr_idx)
         (f' : objs mid ~> objs cod)
         (g' : objs dom ~> objs mid)
         (Hf' : arrowsD mid cod [x] ≈ Some f')
         (Hg' : arrowsD dom mid xs  ≈ Some g')
         f g h,
              f ≈ mkArr [x] f' Hf'
           -> g ≈ mkArr xs g' Hg'
           -> h ≈ f ∘[Arrows] g
           -> P mid g
           -> P cod h)
    → ∀ cod (a : ValidArrow dom cod), P cod a.
Proof.
  intros.
  destruct a.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros.
    destruct (ValidArrow_nil (mkArr [] f' e) eq_refl).
    subst; simpl_eq.
    simpl in *; subst.
    apply X.
    assumption.
  destruct (ValidArrow_cons (mkArr (a :: f) f' e) a f eq_refl), s, s, p.
  unshelve refine
           (X0 x cod a f (getArrMorph x0) (getArrMorph x1) _ _
               x0 x1 _ (reflexivity _) (reflexivity _) _ _); auto.
  - rewrite <- e0.
    destruct x0.
    apply e2.
  - rewrite <- e1.
    destruct x1.
    apply e2.
  - simpl.
    clear X X0 IHf.
    replace (a :: f) with ([a] ++ f) in e by reflexivity.
    unfold arrowsD in e.
    destruct_arrows.
    destruct (arrowsD_compose Heqo), s, s, p, p.
    destruct (Eq_eq_dec x2 cod); subst; [|contradiction].
    rewrite <- e, e2; clear e e2 Heqo.
    rewrite <- e0 in e3; clear e0.

    destruct x0, x1; simpl in *.
    unfold arrowsD in *.
    do 2 destruct_arrows.
    rewrite <- e, <- e0; clear e e0.
    inversion e4; subst; clear e4.
    apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
    rewrite Heqo in e3.
    inversion e3; subst; clear e3.
    apply Eqdep_dec.inj_pair2_eq_dec in H0; [|apply Pos.eq_dec].
    subst.
    reflexivity.
  - destruct x1.
    simpl in e1; subst.
    eapply IHf; eauto.
Defined.
*)

(*
Program Definition arr_break {dom cod} (n : nat) `(f : ValidArrow dom cod) :
  ∃ mid (g : ValidArrow mid cod) (h : ValidArrow dom mid),
    f ≈ g ∘[Arrows] h.
Proof.
  generalize dependent cod.
  induction n; intros.
    exists cod, (@id Arrows _), f; cat.
  generalize dependent cod.
  induction f using @arr_rect.
    exists dom, (@id Arrows _), (@id Arrows _); cat.
  clear IHf1.
  destruct (IHn mid f2), s, s.
  exists x0, (f1 ∘[Arrows] x1), x2.
  rewrite <- comp_assoc.
  rewrite <- e.
  assumption.
Defined.
*)

(*
Lemma arr_break_size {dom cod n f} :
  (0 < arr_size f)%nat -> (0 < n)%nat ->
  match @arr_break dom cod n f with
  | (mid; (g; (h; H))) =>
    (arr_size h < arr_size f)%nat
  end.
Proof.
  intros.
  generalize dependent cod.
  induction f using @arr_rect; intros.
Abort.
*)

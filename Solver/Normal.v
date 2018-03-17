Set Warnings "-notation-overridden".

Require Export Category.Lib.TList.
Require Export Category.Lib.NETList.
Require Export Category.Solver.Reflect.
Require Export Category.Solver.NArrows.

Generalizable All Variables.

Section Normal.

Context `{Env}.

Ltac desh :=
  repeat (
    repeat lazymatch goal with
    | [ H : match Pos_to_fin ?n with _ => _ end = _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _ = _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end     |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _   |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _ _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end = _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _ = _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end     |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _   |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _ _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end = _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ = _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end     |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _   |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match ?b with _ => _ end = _ |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _ = _ |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end     |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _   |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _ _ |- _ ] => destruct b eqn:?
    end;
    try contradiction;
    try discriminate;
    let n := numgoals in guard n < 2;
    simpl_eq;
    try rewrite eq_dec_refl in *;
    try rewrite Fin_eq_dec_refl in *;
    try rewrite Pos_eq_dec_refl in *;
    try rewrite Eq_eq_dec_refl in *;
    repeat lazymatch goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; try clear H
    | [ H : (?X; _) = (?X; _) |- _ ] =>
      apply Eqdep_dec.inj_pair2_eq_dec in H;
             [|solve [ apply Fin_eq_dec
                     | apply Pos.eq_dec
                     | apply Nat.eq_dec
                     | apply Eq_eq_dec
                     | apply eq_dec ]]; subst
    | [ H : ∃ _, _ |- _ ] =>
      let x := fresh "x" in
      let e := fresh "e" in
      destruct H as [x e]
    | [ H : _ ∧ _ |- _ ] =>
      let x := fresh "x" in
      let e := fresh "e" in
      destruct H as [x e]
    end); auto; try solve cat.

Fixpoint unsarrows (fs : list positive) : STerm :=
  match fs with
  | List.nil => SIdent
  | List.cons f List.nil => SMorph f
  | List.cons f fs => SComp (SMorph f) (unsarrows fs)
  end.

Lemma sarrows_unsarrows (f : list positive) : sarrows (unsarrows f) = f.
Proof.
  induction f; simpl; auto; simpl.
  destruct f; auto; simpl in *.
  now rewrite IHf.
Qed.

Lemma unsarrows_app d c (t1 t2 : list positive) f :
  stermD_work d (unsarrows (t1 ++ t2)) = Some (c; f)
    -> ∃ m g h, f ≈ g ∘ h ∧ stermD_work m (unsarrows t1) = Some (c; g)
                          ∧ stermD_work d (unsarrows t2) = Some (m; h).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold stermD; induction t1; simpl; intros.
  - desh.
    eexists c, _, f.
    now split; cat; desh.
  - desh.
    destruct t1.
      simpl in H0.
      destruct t2.
        simpl in *.
        desh.
        exists (fst (nth tys t)).
        exists (helper (ith arrs t)).
        exists id.
        split; cat.
        now rewrite Fin_eq_dec_refl.
      simpl in *.
      desh.
      exists (fst (nth tys t)).
      exists (helper (ith arrs t)).
      exists h.
      split; cat.
      now rewrite Fin_eq_dec_refl.
    simpl in *; desh.
    specialize (IHt1 t2 _ _ _ Heqo).
    desh.
    exists x, (helper (ith arrs t) ∘ x0), x1.
    rewrite x3.
    rewrite Fin_eq_dec_refl.
    split.
      now rewrite x2; cat.
    rewrite e.
    split; auto.
Qed.

Theorem unsarrows_sarrows d c (t : STerm) f :
  stermD d c (unsarrows (sarrows t)) = Some f
    -> stermD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold stermD; induction t; simpl; intros.
  - now desh.
  - now desh; cat.
  - desh.
    pose proof (unsarrows_app _ _ _ _ _ Heqo); desh.
    specialize (IHt2 _ _ x1).
    rewrite e in IHt2; clear e.
    specialize (IHt1 _ _ x0).
    rewrite x3 in IHt1; clear x3.
    rewrite Eq_eq_dec_refl in IHt1.
    rewrite Eq_eq_dec_refl in IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    rewrite Heqo3.
    rewrite Fin_eq_dec_refl.
    now rewrite IHt1, IHt2, <- x2.
Qed.

Lemma unsarrows_app_r d m c (t1 t2 : list positive) g h :
     stermD_work m (unsarrows t1) = Some (c; g)
  -> stermD_work d (unsarrows t2) = Some (m; h)
  -> ∃ f, f ≈ g ∘ h ∧
          stermD_work d (unsarrows (t1 ++ t2)) = Some (c; f).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold stermD; induction t1; simpl; intros.
  - desh.
    eexists h.
    now split; cat.
  - desh.
    destruct t1; simpl in *.
      destruct t2; simpl in *.
        desh.
        exists (helper (ith arrs t)).
        now split; cat.
      desh.
      exists (helper (ith arrs t) ∘ h).
      split; cat.
      rewrite H1.
      now rewrite Fin_eq_dec_refl.
    desh.
    specialize (IHt1 t2 _ _ _ _ eq_refl H1).
    desh.
    exists (helper (ith arrs t) ∘ x).
    split.
      now rewrite x0; cat.
    rewrite e0.
    now rewrite Fin_eq_dec_refl.
Qed.

Theorem unsarrows_sarrows_r d c (t : STerm) f :
  stermD d c t = Some f
    -> stermD d c (unsarrows (sarrows t)) ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold stermD; induction t; simpl; intros.
  - now desh.
  - now desh; cat.
  - desh.
    specialize (IHt2 _ _ h0).
    rewrite Heqo0 in IHt2; clear Heqo0.
    specialize (IHt1 _ _ h1).
    rewrite Heqo1 in IHt1; clear Heqo1.
    rewrite Eq_eq_dec_refl in IHt1.
    rewrite Eq_eq_dec_refl in IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    pose proof (unsarrows_app_r _ _ _ _ _ _ _ Heqo2 Heqo0); desh.
    rewrite e0.
    rewrite Fin_eq_dec_refl.
    now rewrite x1, IHt1, IHt2.
Qed.

Import VectorNotations.
Import EqNotations.

Fixpoint sarrowsD_work dom (fs : list positive) :
  option (∃ cod, objs[@dom] ~> objs [@cod]) :=
  match fs with
  | List.nil => Some (dom; @id _ (objs[@dom]))
  | (a :: fs)%list =>
    match Pos_to_fin a with
    | Some f =>
      match fs with
      | List.nil =>
        match Eq_eq_dec (fst (tys[@f])) dom with
        | left H =>
          Some (snd (tys[@f]);
                  rew [fun x => objs[@x] ~> _] H in helper (ith arrs f))
        | _ => None
        end
      | _ =>
        match sarrowsD_work dom fs with
        | Some (mid; g) =>
          match Eq_eq_dec mid (fst (tys[@f])) with
          | Specif.left H =>
            Some (snd (tys[@f]);
                  helper (ith arrs f)
                    ∘ rew [fun y => _ ~> objs[@y]] H in g)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Definition sarrowsD dom cod (fs : list positive) :
  option (objs[@dom] ~> objs[@cod]) :=
  match sarrowsD_work dom fs with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod =>
      Some (rew [fun y => _ ~> objs[@y]] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Lemma stermD_unsarrows_Comp f1 f2 {dom cod} :
  sarrowsD dom cod (sarrows (SComp f1 f2))
    ≈ sarrowsD dom cod (sarrows f1 ++ sarrows f1).
Proof.
  unfold sarrowsD; simpl.
Abort.

Lemma sarrowsD_sarrows f {dom cod} f' :
  sarrowsD dom cod (sarrows f) = Some f' ->
  sarrowsD dom cod (sarrows f) ≈ stermD dom cod f.
Proof.
  unfold sarrowsD, stermD; induction f; intros; simpl.
  - destruct (Fin_eq_dec dom cod); cat.
  - destruct (Pos_to_fin a); cat.
    destruct (Fin_eq_dec _ _); cat.
    destruct (Fin_eq_dec _ _); cat.
  - simpl in H0.
    rewrite H0.
    destruct (sarrowsD_work dom (sarrows f1 ++ sarrows f2)) eqn:?;
      [|discriminate].
    destruct s.
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
Abort.

Import VectorNotations.

Fixpoint sexprAD (e : SExpr) : Type :=
  match e with
  | STop    => True
  | SBottom => False
  | SEquiv x y f g =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some d, Some c =>
      match stermD d c (unsarrows (sarrows f)),
            stermD d c (unsarrows (sarrows g)) with
      | Some f, Some g => f ≈ g
      | _, _ => False
      end
    | _, _ => False
    end
  | SAnd p q  => sexprAD p ∧ sexprAD q
  | SOr p q   => sexprAD p + sexprAD q
  | SImpl p q => sexprAD p -> sexprAD q
  end.

Theorem sarrowsD_work_compose {xs ys dom cod f} :
  sarrowsD_work dom (xs ++ ys) = Some (cod; f) ->
  ∃ mid g h, f ≈ g ∘ h ∧
    sarrowsD_work mid xs = Some (cod; g) ∧
    sarrowsD_work dom ys = Some (mid; h).
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction xs; simpl; intros.
    exists cod, (@id cat _), f.
    split; cat.
Abort.

Lemma stermD_unsarrows_sarrows f {dom cod} f' :
  sarrowsD dom cod (sarrows f) ≈ Some f' ↔
  stermD dom cod f ≈ Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold sarrowsD, stermD; induction f; split; simpl; intros.
  - destruct (Fin_eq_dec _ _); [|contradiction].
    subst; simpl_eq; cat.
  - destruct (Fin_eq_dec _ _); [|contradiction].
    subst; simpl_eq; cat.
  - destruct (Pos_to_fin a); [|contradiction].
    destruct (Fin_eq_dec _ _); [|contradiction].
    destruct (Fin_eq_dec _ _); [|contradiction].
    subst; simpl_eq; cat.
  - destruct (Pos_to_fin a); [|contradiction].
    destruct (Fin_eq_dec _ _); [|contradiction].
    destruct (Fin_eq_dec _ _); [|contradiction].
    subst; simpl_eq; cat.
  - destruct (sarrowsD_work _ _) eqn:?; [|contradiction].
    destruct s.
    destruct (Fin_eq_dec _ _); [|contradiction].
    subst; simpl_eq.
    (* apply sarrowsD_work_compose in Heqo. *)
    (* repeat desh. *)
Abort.
(*
    destruct e, p.
    specialize (IHf2 _ _ x1).
    specialize (IHf1 _ _ x0).
    rewrite e1 in IHf2.
    rewrite e0 in IHf1.
    rewrite Eq_eq_dec_refl in IHf1.
    rewrite Eq_eq_dec_refl in IHf2.
    destruct IHf1 as [IHf1 _].
    destruct IHf2 as [IHf2 _].
    specialize (IHf1 (reflexivity _)).
    specialize (IHf2 (reflexivity _)).
    destruct (stermD_work dom f2) eqn:?; [|contradiction].
    destruct s.
    desh.
    destruct (stermD_work x f1) eqn:?; [|contradiction].
    destruct s.
    desh.
    rewrite !Fin_eq_dec_refl.
    red in IHf1.
    red in IHf2.
    rewrite IHf1, IHf2.
    rewrite <- X, e.
    reflexivity.
Abort.
(*
    destruct (stermD_work dom (unsarrows (sarrows f2))) eqn:?.
      destruct s.
      specialize (IHf2 _ _ h).
      unfold stermD in IHf2 at 1.
      rewrite Heqo in IHf2.
      rewrite Eq_eq_dec_refl in IHf2.
      specialize (IHf2 eq_refl).
      simpl sarrows.
      destruct (stermD_work x (unsarrows (sarrows f1))) eqn:?.
        destruct s.
        specialize (IHf1 _ _ h0).
        unfold stermD in IHf1 at 1.
        rewrite Heqo0 in IHf1.
        rewrite Eq_eq_dec_refl in IHf1.
        specialize (IHf1 eq_refl).
        unfold stermD in H0.
        simpl in H0.
        destruct s.
        destruct (Fin_eq_dec _ _); [|discriminate].
        subst.
        inv H0.
        admit.
      unfold stermD in H0.
      simpl in H0.
      rewrite Heqo in H0.
      rewrite Heqo0 in H0.
      discriminate.
    unfold stermD in H0.
    simpl in H0.
    rewrite Heqo in H0.
    discriminate.
Abort.
*)

Lemma stermD_unsarrows_sarrows_r f {dom cod} f' :
  stermD dom cod f = Some f' ->
  stermD dom cod (unsarrows (sarrows f)) ≈ Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; intros.
  - now simpl; rewrite H0.
  - unfold stermD in *; simpl in *.
    destruct (Pos_to_fin a); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst; simpl_eq; cat.
    now inv H0.
  - destruct (stermD_work dom f2) eqn:?.
      destruct s.
      specialize (IHf2 _ _ h).
      unfold stermD in IHf2 at 1.
      rewrite Heqo in IHf2.
      rewrite Eq_eq_dec_refl in IHf2.
      specialize (IHf2 eq_refl).
      simpl sarrows.
      destruct (stermD_work x f1) eqn:?.
        destruct s.
        specialize (IHf1 _ _ h0).
        unfold stermD in IHf1 at 1.
        rewrite Heqo0 in IHf1.
        rewrite Eq_eq_dec_refl in IHf1.
        specialize (IHf1 eq_refl).
        unfold stermD in H0.
        simpl in H0.
        rewrite Heqo in H0.
        rewrite Heqo0 in H0.
        destruct (Fin_eq_dec _ _); [|discriminate].
        subst.
        inv H0.
        admit.
      unfold stermD in H0.
      simpl in H0.
      rewrite Heqo in H0.
      rewrite Heqo0 in H0.
      discriminate.
    unfold stermD in H0.
    simpl in H0.
    rewrite Heqo in H0.
    discriminate.
Abort.
*)

Lemma sarrows_sterm e {dom cod} (f : objs[@dom] ~> objs[@cod]) :
  sarrowsD dom cod e = Some f
    -> stermD dom cod (unsarrows e) = Some f.
Proof.
Abort.

Theorem sexprAD_sound (e : SExpr) : sexprAD e ↔ sexprD e.
Proof.
  induction e; split; simpl in *; intuition.
  - destruct (Pos_to_fin _); [|contradiction].
    destruct (Pos_to_fin _); [|contradiction].
    desh.
    apply unsarrows_sarrows in Heqo.
    apply unsarrows_sarrows in Heqo0.
    simpl in *; desh.
    now rewrite Heqo, Heqo0, <- X.
  - desh.
    apply unsarrows_sarrows_r in Heqo1.
    apply unsarrows_sarrows_r in Heqo2.
    simpl in *; desh.
    now rewrite Heqo1, Heqo2, X.
Qed.

End Normal.

Require Export Category.Solver.Reify.

Ltac normalize := reify_terms_and_then
  ltac:(fun env g =>
          change (@sexprD env g);
          apply sexprAD_sound;
          vm_compute).

Example sample_2 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ id ∘ id ∘ id ∘ h ≈ i ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  repeat match goal with | [ H : _ ≈ _ |- _ ] => revert H end.
  (* Set Ltac Profiling. *)
(*
  reify_and_change.
  clear.
  apply sexprAD_sound.
*)
  Time normalize.
  (* Show Ltac Profile. *)
  intros; cat.
Qed.

Print Assumptions sample_2.

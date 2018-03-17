Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Solver.Arrows.
Require Export Category.Solver.Denote.

Generalizable All Variables.

Section Reflect.

Context `{Env}.

Import VectorNotations.
Import EqNotations.

Fixpoint Term_strip {dom cod} (e : Term tys dom cod) : STerm positive :=
  match e with
  | Ident => SIdent
  | Morph f => SMorph (Fin_to_pos f)
  | Comp f g => SComp (Term_strip f) (Term_strip g)
  end.

Fixpoint STerm_embed_work dom (e : STerm positive) :
  option (∃ cod, Term tys dom cod) :=
  match e with
  | SIdent => Some (dom; Ident)
  | SMorph a =>
    match Pos_to_fin a with
    | Some f =>
      match Eq_eq_dec (fst (tys[@f])) dom with
      | left H =>
        Some (snd (tys[@f]); rew [fun x => Term _ x _] H in Morph f)
      | _ => None
      end
    | _ => None
    end
  | SComp f g =>
    match STerm_embed_work dom g with
    | Some (mid; g) =>
      match STerm_embed_work mid f with
      | Some (y; f) => Some (y; Comp f g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition STerm_embed dom cod (e : STerm positive) :
  option (Term tys dom cod) :=
  match STerm_embed_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => Term tys _ y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Corollary Fin_to_pos_succ {n} {f : Fin.t n} :
  Fin_to_pos (Fin.FS f) = Pos.succ (Fin_to_pos f).
Proof. reflexivity. Qed.

Lemma Pos_to_fin_succ {p n} :
  Pos_to_fin (Pos.succ p) = option_map (@Fin.FS n) (Pos_to_fin p).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; simpl; intros; auto.
  unfold Pos_to_fin in *.
  rewrite !Pos.peano_rect_succ.
  destruct n; auto.
Qed.

Lemma Fin_to_pos_spec {p n} {f : Fin.t n} :
  Pos_to_fin p = Some f -> Fin_to_pos f = p.
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; simpl; intros; auto.
    destruct f.
      reflexivity.
    now inv H0.
  destruct f;
  unfold Pos_to_fin in *;
  rewrite Pos.peano_rect_succ in H0;
  (destruct (Pos.peano_rect _ _ _ _) eqn:?; [|discriminate]);
  specialize (IHp _ _ Heqy); clear Heqy;
  inv H0.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Nat.eq_dec].
  subst.
  apply Fin_to_pos_succ.
Qed.

Lemma Pos_to_fin_spec {n} {f : Fin.t n} :
  Pos_to_fin (Fin_to_pos f) = Some f.
Proof.
  induction f; simpl; intros; auto.
  rewrite Pos_to_fin_succ.
  now rewrite IHf.
Qed.

Lemma Fin_to_pos_inj {n} (x y : Fin.t n) :
  Fin_to_pos x = Fin_to_pos y -> x = y.
Proof.
  destruct n.
    inversion x.
  generalize dependent y.
  induction x; intros;
  dependent elimination y; simpl in *; intros; auto.
  - destruct (Fin_to_pos y); inv H0.
  - destruct (Fin_to_pos x); inv H0.
  - f_equal.
    apply Pos.succ_inj in H0.
    apply IHx; auto.
Qed.

Lemma STerm_embed_strip {dom cod} (t : Term tys dom cod) :
  STerm_embed dom cod (Term_strip t) = Some t.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold STerm_embed; induction t; simpl; intros.
  - rewrite Fin_eq_dec_refl.
    reflexivity.
  - rewrite Pos_to_fin_spec.
    rewrite !Fin_eq_dec_refl.
    reflexivity.
  - destruct (STerm_embed_work dom (Term_strip t2)); [|discriminate].
    destruct s.
    destruct (STerm_embed_work mid (Term_strip t1)) eqn:?; [|discriminate].
    destruct s.
    destruct (Eq_eq_dec _ _); [|discriminate].
    destruct (Eq_eq_dec _ _); [|discriminate].
    subst.
    inv IHt1.
    inv IHt2.
    rewrite Heqo.
    rewrite !Fin_eq_dec_refl.
    reflexivity.
Qed.

(** Induction over an STerm within the right environment provides a great deal
    more information. Most importantly, there is a corresponding well-typed
    Term. *)

(* Lemma stermD_ind : *)
(*   ∀ (P : ∀ (dom cod : positive) (s : STerm positive), Type), *)
(*       (∀ dom, P dom dom SIdent) *)
(*     → (∀ dom cod (f : positive), P dom cod (SMorph f)) *)
(*     → (∀ dom cod mid (f : STerm positive), P mid cod f *)
(*          → ∀ g : STerm positive, P dom mid g → P dom cod (SComp f g)) *)
(*     → ∀ dom cod (s : STerm positive), P dom cod s. *)
(* Proof. *)

Lemma Term_strip_embed dom cod (e : STerm positive) t :
  STerm_embed dom cod e = Some t -> Term_strip t = e.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold STerm_embed; induction e; simpl; intros.
  - destruct (Fin_eq_dec _ _); [|discriminate].
    now inv H0.
  - destruct (Pos_to_fin _) eqn:?; [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    simpl.
    f_equal.
    now apply Fin_to_pos_spec in Heqo.
  - destruct (STerm_embed_work dom e2) eqn:?; [|discriminate].
    destruct s.
    destruct (STerm_embed_work x e1) eqn:?; [|discriminate].
    destruct s.
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    specialize (IHe2 dom x t0).
    specialize (IHe1 x cod t1).
    rewrite Heqo in IHe2.
    rewrite Heqo0 in IHe1.
    rewrite Eq_eq_dec_refl in IHe1.
    rewrite Eq_eq_dec_refl in IHe2.
    specialize (IHe2 eq_refl).
    specialize (IHe1 eq_refl).
    simpl.
    now f_equal.
Qed.

(** This is the key connecting theorem between the richly-typed and
    weakly-typed term languages. It says that if we have a weakly-typed term
    that denotes within the environment, then there exists an embedded of that
    term into the richly-typed domain, meaning that _for this term_, all of
    our proofs concerning richly-typed terms also hold. *)
Lemma stermD_embeds e {dom cod} (f : objs[@dom] ~> objs[@cod]) :
  stermD dom cod e = Some f
    -> ∃ t, STerm_embed dom cod e = Some t ∧ termD t = f.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold stermD, STerm_embed; induction e; simpl; intros.
  - destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    exists Ident.
    cat.
  - destruct (Pos_to_fin _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    exists (Morph t).
    cat.
  - destruct (stermD_work dom e2) eqn:?; [|discriminate].
    destruct s.
    destruct (stermD_work x e1) eqn:?; [|discriminate].
    destruct s.
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    specialize (IHe1 x cod h0).
    specialize (IHe2 dom x h).
    rewrite Heqo in IHe2.
    rewrite Heqo0 in IHe1.
    rewrite Eq_eq_dec_refl in IHe1.
    rewrite Eq_eq_dec_refl in IHe2.
    simpl_eq.
    destruct (IHe1 eq_refl), p; clear IHe1.
    destruct (IHe2 eq_refl), p; clear IHe2.
    subst.
    destruct (STerm_embed_work dom e2) eqn:?; [|discriminate].
    destruct s.
    destruct (STerm_embed_work x e1) eqn:?; [|discriminate].
    destruct s.
    destruct (Eq_eq_dec _ _); [|discriminate].
    destruct (Eq_eq_dec _ _); [|discriminate].
    subst.
    inv e.
    inv e3.
    rewrite Heqo2.
    rewrite Fin_eq_dec_refl.
    exists (Comp x0 x1).
    cat.
Qed.

Fixpoint indices `(t : Arrows tys d c) : list (arr_idx num_arrs) :=
  match t with
  | tnil => List.nil
  | existT2 _ _ f _ _ ::: fs => f :: indices fs
  end.

Theorem indices_impl {d c} (x y : Arrows tys d c) :
  indices x = indices y -> x = y.
Proof.
  induction x; dependent elimination y;
  simpl; auto; intros.
  - destruct y0.
    inv H0.
  - destruct b.
    inv H0.
  - destruct b, y0.
    inv H0.
    f_equal; auto.
    f_equal; auto.
    apply eq_proofs_unicity.
Qed.

Theorem indices_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  indices (t1 +++ t2) = (indices t1 ++ indices t2)%list.
Proof.
  induction t1; simpl in *; cat.
  destruct b; subst.
  destruct t2; simpl; cat.
    now rewrite List.app_nil_r.
  f_equal.
  apply IHt1.
Qed.

Fixpoint term_indices `(t : Term tys d c) : list (arr_idx num_arrs) :=
  match t with
  | Ident => []
  | Morph a => [a]
  | Comp f g => term_indices f ++ term_indices g
  end.

Fixpoint sarrows {a} (t : STerm a) : list a :=
  match t with
  | SIdent    => List.nil
  | SMorph a  => [a]
  | SComp f g => sarrows f ++ sarrows g
  end.

Lemma arrows_and_indices f dom cod (t : Term tys dom cod) :
  STerm_embed dom cod f = Some t
    -> sarrows f = List.map Fin_to_pos (term_indices t).
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold STerm_embed, sarrows in *; induction f; simpl in *; auto.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b; [|discriminate]; cat
           end; subst.
    inv H0.
    reflexivity.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b eqn:?; [|discriminate]; cat
           end; subst.
    inv H0.
    inv Heqo.
    apply Fin_to_pos_spec in Heqo0; subst.
    reflexivity.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b eqn:?; [|discriminate]; cat
           end; subst.
    inv H0.
    inv Heqo.
    inv Heqo1.
    subst; simpl.
    specialize (IHf2 _ _ e1).
    specialize (IHf1 _ _ e2).
    rewrite Heqo0 in IHf2.
    rewrite H1 in IHf1.
    rewrite Fin_eq_dec_refl in *.
    simpl_eq.
    specialize (IHf2 eq_refl).
    specialize (IHf1 eq_refl).
    rewrite List.map_app.
    now rewrite IHf1, IHf2.
Qed.

Theorem term_indices_consistent {d c} (x : Arrows tys d c) :
  term_indices (unarrows x) = indices x.
Proof.
  induction x; simpl; auto.
  destruct b; subst; simpl_eq; simpl.
  now rewrite IHx.
Qed.

Theorem term_indices_unarrows {d c} (x : Term tys d c) :
  term_indices (unarrows (arrows x)) = term_indices x.
Proof.
  induction x; simpl; auto.
  rewrite <- IHx1, <- IHx2; clear IHx1 IHx2.
  rewrite !term_indices_consistent.
  now rewrite indices_app.
Qed.

Theorem term_indices_equiv {d c} (x y : Term tys d c) :
  term_indices x = term_indices y -> termD x ≈ termD y.
Proof.
  intros.
  rewrite <- term_indices_unarrows in H0.
  symmetry in H0.
  rewrite <- term_indices_unarrows in H0.
  rewrite !term_indices_consistent in H0.
  rewrite <- unarrows_arrows.
  symmetry.
  rewrite <- unarrows_arrows.
  apply indices_impl in H0.
  now rewrite H0.
Qed.

End Reflect.

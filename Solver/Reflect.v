Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Tactics.
Require Import Category.Solver.Env.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Arrows.

Generalizable All Variables.

Section Reflect.

Context `{Env}.

Import VectorNotations.
Import EqNotations.

Fixpoint Term_strip {dom cod} (e : Term tys dom cod) : STerm :=
  match e with
  | Ident => SIdent
  | Morph f => SMorph (Fin_to_pos f)
  | Comp f g => SComp (Term_strip f) (Term_strip g)
  end.

Lemma Term_strip_rel {dom cod} s (t : Term tys dom cod) :
  Term_strip t = s
    ↔ TermRel tys s t.
Proof.
  split; intros.
  - subst.
    induction t; constructor; intuition.
  - induction X; simpl; auto.
    now rewrite IHX1, IHX2.
Qed.

Fixpoint STerm_embed_work dom (e : STerm) : option (∃ cod, Term tys dom cod) :=
  match e with
  | SIdent => Some (dom; Ident)
  | SMorph a =>
    match Pos_to_fin a with
    | Some f =>
      match eq_dec (fst (tys[@f])) dom with
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

Definition STerm_embed dom cod (e : STerm) : option (Term tys dom cod) :=
  match STerm_embed_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
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
  Pos_to_fin p = Some f → Fin_to_pos f = p.
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
  Fin_to_pos x = Fin_to_pos y → x = y.
Proof.
  destruct n.
    inversion x.
  generalize dependent y.
  induction x; intros;
  dependent elimination y; simpl in *; intros; auto.
  - destruct (Fin_to_pos t0); inv H0.
  - destruct (Fin_to_pos x); inv H0.
  - f_equal.
    apply Pos.succ_inj in H0.
    apply IHx; auto.
Qed.

Lemma STerm_embed_rel {dom cod} (e : STerm) f :
  STerm_embed dom cod e = Some f
    ↔ TermRel tys e f.
Proof.
  unfold STerm_embed.
  split; intros.
  - generalize dependent cod.
    generalize dependent dom.
    induction e; simpl; intros.
    + destruct (eq_dec dom cod); subst; inv H0.
      constructor.
    + destruct (Pos_to_fin a) eqn:Heqe; inv H0.
      destruct (eq_dec _ dom); inv H2.
      destruct (eq_dec _ cod); inv H1.
      simpl.
      apply Fin_to_pos_spec in Heqe.
      rewrite <- Heqe.
      constructor.
    + destruct (STerm_embed_work dom e2) eqn:Heqe1; inv H0.
      destruct s.
      destruct (STerm_embed_work x e1) eqn:Heqe2; inv H2.
      destruct s.
      destruct (eq_dec x0 cod); inv H1.
      constructor.
      * apply IHe1.
        rewrite Heqe2, EqDec.peq_dec_refl.
        reflexivity.
      * apply IHe2.
        rewrite Heqe1, EqDec.peq_dec_refl.
        reflexivity.
  - induction X; simpl.
    + rewrite EqDec.peq_dec_refl.
      reflexivity.
    + rewrite Pos_to_fin_spec, !EqDec.peq_dec_refl.
      reflexivity.
    + destruct (STerm_embed_work dom sg) eqn:Heqg; inv IHX2.
      destruct s.
      destruct (eq_dec x mid); inv H1; subst.
      destruct (STerm_embed_work mid sf) eqn:Heqf; inv IHX1.
      destruct s.
      destruct (eq_dec x cod); inv H1; subst.
      reflexivity.
Qed.

Corollary STerm_embed_strip {dom cod} (t : Term tys dom cod) :
  STerm_embed dom cod (Term_strip t) = Some t.
Proof.
  apply STerm_embed_rel.
  now apply Term_strip_rel.
Qed.

Corollary Term_strip_embed dom cod (e : STerm) t :
  STerm_embed dom cod e = Some t → Term_strip t = e.
Proof.
  intros.
  apply Term_strip_rel.
  now apply STerm_embed_rel.
Qed.

Lemma stermD_rel {dom cod} (e : STerm) t :
  TermRel tys e t
    → ∃ f, stermD dom cod e = Some f ∧ f = termD t.
Proof.
  unfold stermD.
  intros.
  induction X; simpl.
  - rewrite EqDec.peq_dec_refl.
    simpl.
    now eexists.
  - rewrite Pos_to_fin_spec, !EqDec.peq_dec_refl.
    now eexists.
  - destruct IHX1, IHX2.
    destruct (stermD_work dom sg) eqn:Heqg; inv p0; inv H0.
    destruct s.
    destruct (eq_dec x0 mid); inv H2; subst.
    destruct (stermD_work mid sf) eqn:Heqf; inv p; inv H0.
    destruct s.
    destruct (eq_dec x cod); inv H3; subst.
    now eexists.
Qed.

(** This is the key connecting theorem between the richly-typed and
    weakly-typed term languages. It says that if we have a weakly-typed term
    that denotes within the environment, then there exists an embedded of that
    term into the richly-typed domain, meaning that _for this term_, all of
    our proofs concerning richly-typed terms also hold. *)

Lemma STerm_denotes e {dom cod} t :
  STerm_embed dom cod e = Some t
    → ∃ f, stermD dom cod e = Some f ∧ f = termD t.
Proof.
  intros.
  apply STerm_embed_rel in H0.
  now apply stermD_rel in H0.
Qed.

Lemma stermD_embeds e {dom cod} (f : objs[@dom] ~> objs[@cod]) :
  stermD dom cod e = Some f
    → ∃ t, STerm_embed dom cod e = Some t ∧ termD t = f.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold stermD, STerm_embed; induction e; simpl; intros; desh.
  - specialize (IHe1 _ _ h1).
    specialize (IHe2 _ _ h0).
    rewrite Heqo0 in IHe2.
    rewrite Heqo1 in IHe1.
    rewrite EqDec.peq_dec_refl in IHe1.
    rewrite EqDec.peq_dec_refl in IHe2.
    specialize (IHe1 eq_refl).
    specialize (IHe2 eq_refl).
    desh.
    eexists.
    rewrite Heqo2.
    now rewrite EqDec.peq_dec_refl.
Qed.

Import ListNotations.

Fixpoint term_indices `(t : Term tys d c) : list (arr_idx num_arrs) :=
  match t with
  | Ident => []
  | Morph a => [a]
  | Comp f g => term_indices f ++ term_indices g
  end.

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
  term_indices x = term_indices y → termD x ≈ termD y.
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

Fixpoint sindices (t : STerm) : list positive :=
  match t with
  | SIdent    => List.nil
  | SMorph a  => [a]
  | SComp f g => sindices f ++ sindices g
  end.

Lemma arrows_and_indices f dom cod (t : Term tys dom cod) :
  TermRel tys f t
    → sindices f = List.map Fin_to_pos (term_indices t).
Proof.
  intros.
  apply Term_strip_rel in X; subst.
  induction t; simpl; auto.
  now rewrite IHt1, IHt2, List.map_app.
Qed.

End Reflect.

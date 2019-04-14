Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
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

Fixpoint STerm_embed_work dom (e : STerm) : option (∃ cod, Term tys dom cod) :=
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

Definition STerm_embed dom cod (e : STerm) : option (Term tys dom cod) :=
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
  - destruct (Fin_to_pos t0); inv H0.
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
  - now desh.
  - now rewrite Pos_to_fin_spec; desh.
  - now desh; rewrite Heqo0; desh.
Qed.

Lemma Term_strip_embed dom cod (e : STerm) t :
  STerm_embed dom cod e = Some t -> Term_strip t = e.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold STerm_embed; induction e; simpl; intros; desh.
  - simpl; f_equal.
    now apply Fin_to_pos_spec in Heqo0.
  - specialize (IHe2 _ _ t1).
    specialize (IHe1 _ _ t2).
    rewrite Heqo0 in IHe2.
    rewrite Heqo1 in IHe1.
    rewrite Eq_eq_dec_refl in IHe1.
    rewrite Eq_eq_dec_refl in IHe2.
    specialize (IHe2 eq_refl).
    specialize (IHe1 eq_refl).
    now simpl; f_equal.
Qed.

(** This is the key connecting theorem between the richly-typed and
    weakly-typed term languages. It says that if we have a weakly-typed term
    that denotes within the environment, then there exists an embedded of that
    term into the richly-typed domain, meaning that _for this term_, all of
    our proofs concerning richly-typed terms also hold. *)

Lemma STerm_denotes e {dom cod} t :
  STerm_embed dom cod e = Some t
    -> ∃ f, stermD dom cod e = Some f ∧ termD t = f.
Proof.
  intros.
  apply Term_strip_embed in H0; subst.
  generalize dependent cod.
  generalize dependent dom.
  unfold stermD; induction t; simpl; intros; desh.
  - rewrite Pos_to_fin_spec; desh.
  - exists (termD t1 ∘ termD t2).
    now rewrite Heqo0, Fin_eq_dec_refl; cat.
Qed.

Lemma stermD_embeds e {dom cod} (f : objs[@dom] ~> objs[@cod]) :
  stermD dom cod e = Some f
    -> ∃ t, STerm_embed dom cod e = Some t ∧ termD t = f.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold stermD, STerm_embed; induction e; simpl; intros; desh.
  - specialize (IHe1 _ _ h1).
    specialize (IHe2 _ _ h0).
    rewrite Heqo0 in IHe2.
    rewrite Heqo1 in IHe1.
    rewrite Eq_eq_dec_refl in IHe1.
    rewrite Eq_eq_dec_refl in IHe2.
    specialize (IHe1 eq_refl).
    specialize (IHe2 eq_refl).
    desh.
    eexists.
    rewrite Heqo2.
    now rewrite Fin_eq_dec_refl.
Qed.

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

Fixpoint sarrows (t : STerm) : list positive :=
  match t with
  | SIdent    => List.nil
  | SMorph a  => [a]
  | SComp f g => sarrows f ++ sarrows g
  end.

Lemma arrows_and_indices f dom cod (t : Term tys dom cod) :
  STerm_embed dom cod f = Some t
    -> sarrows f = List.map Fin_to_pos (term_indices t).
Proof.
  intros.
  apply Term_strip_embed in H0; subst.
  induction t; simpl; auto.
  now rewrite IHt1, IHt2, List.map_app.
Qed.

End Reflect.

Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Tactics.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.

Generalizable All Variables.

Section Normal.

Context `{Env}.

Import ListNotations.

Fixpoint sindices (t : STerm) : list positive :=
  match t with
  | SIdent    => []
  | SMorph a  => [a]
  | SComp f g => sindices f ++ sindices g
  end.

Corollary sindices_ident :
  sindices SIdent = [].
Proof. reflexivity. Qed.

Corollary sindices_comp (t1 t2 : STerm) :
  sindices (SComp t1 t2) = sindices t1 ++ sindices t2.
Proof. reflexivity. Qed.

Corollary sindices_id_left (t : STerm) :
  sindices (SComp SIdent t) = sindices t.
Proof. reflexivity. Qed.

Lemma sindices_id_right (t : STerm) :
  sindices (SComp t SIdent) = sindices t.
Proof.
  rewrite sindices_comp, sindices_ident.
  apply app_nil_r.
Qed.

Lemma sindices_comp_assoc (t1 t2 t3 : STerm) :
  sindices (SComp (SComp t1 t2) t3) = sindices (SComp t1 (SComp t2 t3)).
Proof.
  rewrite !sindices_comp.
  now rewrite app_assoc.
Qed.

Fixpoint unsindices (fs : list positive) : STerm :=
  match fs with
  | List.nil => SIdent
  | List.cons f List.nil => SMorph f
  | List.cons f fs => SComp (SMorph f) (unsindices fs)
  end.

Lemma sindices_unsindices (f : list positive) : sindices (unsindices f) = f.
Proof.
  induction f; simpl; auto; simpl.
  destruct f; auto; simpl in *.
  now rewrite IHf.
Qed.

Lemma unsindices_app d c (t1 t2 : list positive) f :
  stermD_work d (unsindices (t1 ++ t2)) = Some (c; f)
    → ∃ m g h, f ≈ g ∘ h ∧ stermD_work m (unsindices t1) = Some (c; g)
                          ∧ stermD_work d (unsindices t2) = Some (m; h).
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
        exists (fst (Vector.nth tys t)).
        exists (helper (ith arrs t)).
        exists id.
        split; cat.
        now rewrite EqDec.peq_dec_refl.
      simpl in *.
      desh.
      exists (fst (Vector.nth tys t)).
      exists (helper (ith arrs t)).
      exists h.
      split; cat.
      now rewrite EqDec.peq_dec_refl.
    simpl in *; desh.
    specialize (IHt1 t2 _ _ _ Heqo).
    desh.
    exists x, (helper (ith arrs t) ∘ x0), x1.
    rewrite x3.
    rewrite EqDec.peq_dec_refl.
    split.
      now rewrite x2; cat.
    rewrite e.
    split; auto.
Qed.

Theorem unsindices_sindices d c (t : STerm) f :
  stermD d c (unsindices (sindices t)) = Some f
    → stermD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold stermD; induction t; simpl; intros.
  - now desh.
  - now desh; cat.
  - desh.
    pose proof (unsindices_app _ _ _ _ _ Heqo); desh.
    specialize (IHt2 _ _ x1).
    rewrite e in IHt2; clear e.
    specialize (IHt1 _ _ x0).
    rewrite x3 in IHt1; clear x3.
    rewrite EqDec.peq_dec_refl in IHt1.
    rewrite EqDec.peq_dec_refl in IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    rewrite Heqo3.
    rewrite EqDec.peq_dec_refl.
    now rewrite IHt1, IHt2, <- x2.
Qed.

Lemma unsindices_app_r d m c (t1 t2 : list positive) g h :
     stermD_work m (unsindices t1) = Some (c; g)
  → stermD_work d (unsindices t2) = Some (m; h)
  → ∃ f, f ≈ g ∘ h ∧
          stermD_work d (unsindices (t1 ++ t2)) = Some (c; f).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold stermD; induction t1; simpl; intros.
  - desh.
  - desh.
    destruct t1; simpl in *.
      destruct t2; simpl in *.
        desh.
      desh.
      exists (helper (ith arrs t) ∘ h).
      split; cat.
      rewrite H1.
      now rewrite EqDec.peq_dec_refl.
    desh.
    specialize (IHt1 t2 _ _ _ _ eq_refl H1).
    desh.
    exists (helper (ith arrs t) ∘ x).
    split.
      now rewrite x0; cat.
    rewrite e0.
    now rewrite EqDec.peq_dec_refl.
Qed.

Theorem unsindices_sindices_r d c (t : STerm) f :
  stermD d c t = Some f
    → stermD d c (unsindices (sindices t)) ≈ Some f.
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
    rewrite EqDec.peq_dec_refl in IHt1.
    rewrite EqDec.peq_dec_refl in IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    pose proof (unsindices_app_r _ _ _ _ _ _ _ Heqo2 Heqo0); desh.
    rewrite e0.
    rewrite EqDec.peq_dec_refl.
    now rewrite x1, IHt1, IHt2.
Qed.

(* Normalization step: Associate composition to the right *)

Fixpoint norm_assoc_aux t1 t2 : STerm :=
  match t1 with
  | SComp t t' => norm_assoc_aux t (norm_assoc_aux t' t2)
  | _ => SComp t1 t2
  end.

Theorem norm_assoc_aux_sound (t1 t2 : STerm) :
  sindices (norm_assoc_aux t1 t2) = sindices (SComp t1 t2).
Proof.
  generalize dependent t2.
  induction t1; intros;
  simpl norm_assoc_aux;
  try reflexivity.
  rewrite IHt1_1.
  rewrite !sindices_comp.
  rewrite IHt1_2.
  rewrite sindices_comp.
  now rewrite app_assoc.
Qed.

Fixpoint norm_assoc t : STerm :=
  match t with
  | SComp t1 t2 => norm_assoc_aux t1 (norm_assoc t2)
  | _ => t
  end.

Theorem norm_assoc_sound (t : STerm) :
  sindices (norm_assoc t) = sindices t.
Proof.
  induction t; intros; try reflexivity.
  simpl.
  rewrite norm_assoc_aux_sound.
  rewrite sindices_comp.
  now rewrite IHt2.
Qed.

(* Normalization step: Remove composed identities *)

Fixpoint norm_id t : STerm :=
  match t with
  | SComp f g =>
      match norm_id f, norm_id g with
      | SIdent, SIdent => SIdent
      | SIdent, g' => g'
      | f', SIdent => f'
      | f', g' => SComp f' g'
      end
  | _ => t
  end.

Theorem norm_id_sound (t : STerm) :
  sindices (norm_id t) = sindices t.
Proof.
  induction t; simpl; intros;
    try reflexivity.
  rewrite <- IHt1, <- IHt2.
  destruct (norm_id t1), (norm_id t2); auto.
  simpl sindices.
  now rewrite app_nil_r.
Qed.

Fixpoint norm_aux t1 t2 : STerm :=
  match t1 with
  | SIdent => t2
  | SMorph x => SComp (SMorph x) t2
  | SComp t t' => norm_aux t (norm_aux t' t2)
  end.

Definition norm t := norm_id (norm_assoc t).

Example norm_1 :
  norm (SComp
          (SComp
             (SComp
                (SComp
                   (SComp SIdent (SMorph 1%positive))
                   (SComp (SMorph 2%positive) SIdent))
                SIdent)
             (SMorph 3%positive))
          (SComp
             SIdent
             SIdent))
    = SComp (SMorph 1) (SComp (SMorph 2) (SMorph 3)).
Proof. reflexivity. Qed.

Theorem norm_sound (t : STerm) :
  sindices (norm t) = sindices t.
Proof.
  unfold norm.
  rewrite norm_id_sound.
  rewrite norm_assoc_sound.
  reflexivity.
Qed.

Theorem norm_impl (t1 t2 : STerm) :
  norm t1 = norm t2 →
  sindices t1 = sindices t2.
Proof.
  intros.
  rewrite <- (norm_sound t1).
  rewrite <- (norm_sound t2).
  rewrite H0.
  reflexivity.
Qed.

Fixpoint sexprAD (e : SExpr) : Type :=
  match e with
  | STop    => True
  | SBottom => False
  | SEquiv x y f g =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some d, Some c =>
      match stermD d c (unsindices (sindices (norm f))),
            stermD d c (unsindices (sindices (norm g))) with
      | Some f, Some g => f ≈ g
      | _, _ => False
      end
    | _, _ => False
    end
  | SAnd p q  => sexprAD p ∧ sexprAD q
  | SOr p q   => sexprAD p + sexprAD q
  | SImpl p q => sexprAD p → sexprAD q
  end.

Theorem sexprAD_sound (e : SExpr) : sexprAD e ↔ sexprD e.
Proof.
  induction e; split; simpl in *; intuition.
  - destruct (Pos_to_fin _); [|contradiction].
    destruct (Pos_to_fin _); [|contradiction].
    desh.
    rewrite norm_sound in Heqo.
    rewrite norm_sound in Heqo0.
    apply unsindices_sindices in Heqo.
    apply unsindices_sindices in Heqo0.
    simpl in *; desh.
    now rewrite Heqo, Heqo0, <- X.
  - desh.
    rewrite !norm_sound.
    apply unsindices_sindices_r in Heqo1.
    apply unsindices_sindices_r in Heqo2.
    simpl in *; desh.
    now rewrite Heqo1, Heqo2, X.
Qed.

End Normal.

(* * This is a much easier theorem to apply, so it speeds things up a lot! *)
Corollary sexprAD_sound' (env : Env) (e : SExpr) : sexprAD e → sexprD e.
Proof. apply sexprAD_sound. Qed.

Ltac normalize := reify_terms_and_then
  ltac:(fun env g =>
          change (@sexprD env g);
          simple apply sexprAD_sound';
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
  normalize.
  (* Show Ltac Profile. *)
  intros; cat.
Qed.

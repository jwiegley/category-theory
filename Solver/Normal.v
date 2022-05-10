Set Warnings "-notation-overridden".


Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Tactics.
Require Import Category.Solver.Env.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reflect.

Generalizable All Variables.

Section Normal.

Context `{Env}.

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
  - desh.
    destruct t1; simpl in *.
      destruct t2; simpl in *.
        desh.
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

Require Import Category.Solver.Reify.

(* * This is a much easier theorem to apply, so it speeds things up a lot! *)
Theorem sexprAD_sound' (env : Env) (e : SExpr) : sexprAD e -> sexprD e.
Proof.
  apply sexprAD_sound.
Qed.

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

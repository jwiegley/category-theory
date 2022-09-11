Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.

Section Normal.

Context `{Env}.

Import ListNotations.

Inductive Arrow : Set :=
  | Arr : positive → Arrow
  | Fork : list Arrow → list Arrow → Arrow
  | Exl : Arrow
  | Exr : Arrow.

Section Arrow_rect.

Inductive ForallT {A} (P : A → Type) : list A → Type :=
    ForallT_nil : ForallT []
  | ForallT_cons (x : A) (l : list A) :
    P x → ForallT l → ForallT (x :: l).

Fixpoint ForallT_toList {A} (P : Type) (l : list A)
  (x : ForallT (λ _, P) l) :  list P :=
  match x with
  | ForallT_nil _ => []
  | ForallT_cons _ x l p r => p :: ForallT_toList P l r
  end.

Variable P : Arrow → Type.

Variable Parr  : ∀ p : positive, P (Arr p).
Variable Pfork : ∀ f g : list Arrow,
  ForallT P f → ForallT P g → P (Fork f g).
Variable Pexl  : P Exl.
Variable Pexr  : P Exr.

Fixpoint Arrow_rect' `(a : Arrow) : P a.
Proof using P Parr Pexl Pexr Pfork.
 induction a.
  - now apply Parr.
  - apply Pfork.
    + induction l.
      * constructor.
      * constructor.
        ** now apply Arrow_rect'.
        ** exact IHl.
    + induction l0.
      * constructor.
      * constructor.
        ** now apply Arrow_rect'.
        ** exact IHl0.
  - now apply Pexl.
  - now apply Pexr.
Qed.

End Arrow_rect.

Fixpoint sindices (t : STerm) : list Arrow :=
  match t with
  | SIdent    => []
  | SMorph a  => [Arr a]
  | SComp f g => sindices f ++ sindices g
  | SFork f g => [Fork (sindices f) (sindices g)]
  | SExl      => [Exl]
  | SExr      => [Exr]
  end.

Definition compose_terms : list STerm → STerm :=
  let fix go xs :=
    match xs with
    | [] => SIdent
    | [x] => x
    | x :: xs => SComp x (go xs)
    end
  in go.

Definition unarrow : Arrow → STerm :=
  Arrow_rect'
    (λ _, STerm)
    (λ f', SMorph f')
    (λ f' g' Hf' Hg',
      SFork
        (compose_terms (ForallT_toList _ f' Hf'))
        (compose_terms (ForallT_toList _ g' Hg')))
    SExl
    SExr.

Definition unsindices (fs : list Arrow) : STerm :=
  compose_terms (map unarrow fs).

Ltac matches :=
  lazymatch goal with
  | [ H : context[match pos_obj ?f ?dom with _ => _ end] |- _ ] =>
    destruct (pos_obj f dom) as [[? ?]|] eqn:?
  | [ H : context[match @stermD_work ?h ?n ?s with _ => _ end] |- _ ] =>
    destruct (@stermD_work h n s) as [[? ?]|] eqn:?
  | [ H : context[match Classes.eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (Classes.eq_dec n m); subst
  end;
  try contradiction;
  try discriminate;
  let n := numgoals in guard n < 2.

Ltac desh :=
  repeat matches;
  simpl_eq;
  try rewrite EqDec.peq_dec_refl in *;
  repeat lazymatch goal with
  | [ H : Some _ = Some _ |- _ ] => inversion H; subst; try clear H
  | [ H : (?X; _) = (?X; _) |- _ ] =>
    apply Eqdep_dec.inj_pair2_eq_dec in H;
      [|now apply Classes.eq_dec]; subst
  | [ H : ∃ _, _ |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in destruct H as [x e]
  | [ H : _ ∧ _ |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in destruct H as [x e]
  end; auto; try solve [ cat ].

Lemma unsindices_app {d c} {t1 t2 : list Arrow} {f} :
  stermD_work d (unsindices (t1 ++ t2)) = Some (c; f)
    → ∃ m g h, f ≈ g ∘ h
        ∧ stermD_work m (unsindices t1) = Some (c; g)
        ∧ stermD_work d (unsindices t2) = Some (m; h).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold stermD; induction t1; simpl; intros.
  - eexists _, _, f.
    now split; cat.
  - destruct t1; simpl in *; desh.
    + destruct t2; simpl in *.
      * exists d, f, id.
        split; cat.
      * desh.
        exists _, h0, h.
        split; cat.
    + desh.
      specialize (IHt1 t2 _ _ _ Heqo); desh.
      exists _, (h0 ∘ x1), x2.
      split.
      * now rewrite x3; cat.
      * admit.
        (* rewrite Heqo0, e. *)
        (* split; auto. *)
Admitted.

Theorem unsindices_sindices {d c} {t : STerm} {f} :
  stermD d c (unsindices (sindices t)) = Some f
    → stermD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold stermD; induction t; simpl; intros; desh.
  - admit.
  - pose proof (unsindices_app Heqo); desh.
    specialize (IHt2 _ _ x1).
    rewrite e in IHt2; clear e.
    specialize (IHt1 _ _ x0).
    rewrite x3 in IHt1; clear x3.
    rewrite EqDec.peq_dec_refl in IHt1, IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    rewrite Heqo1, EqDec.peq_dec_refl.
    now rewrite IHt1, IHt2, <- x2.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma unsindices_app_r {d m c} {t1 t2 : list Arrow} {g h} :
     stermD_work m (unsindices t1) = Some (c; g)
  → stermD_work d (unsindices t2) = Some (m; h)
  → ∃ f, f ≈ g ∘ h ∧
          stermD_work d (unsindices (t1 ++ t2)) = Some (c; f).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold stermD; induction t1; simpl; intros; desh.
  destruct t1; simpl in *; desh.
  - destruct t2; simpl in *; desh.
    exists (g ∘ h).
    split; cat.
    admit.
    (* now rewrite H1, H0. *)
  - specialize (IHt1 t2 _ _ _ _ eq_refl H1); desh.
    exists (h1 ∘ x0).
    split.
    + now rewrite x1; cat.
    + now rewrite e0, Heqo0.
Qed.

Theorem unsindices_sindices_r {d c} {t : STerm} {f} :
  stermD d c t = Some f
    → stermD d c (unsindices (sindices t)) ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold stermD; induction t; simpl; intros; desh.
  specialize (IHt2 _ _ h).
  rewrite Heqo in IHt2; clear Heqo.
  specialize (IHt1 _ _ h0).
  rewrite Heqo0 in IHt1; clear Heqo0.
  rewrite EqDec.peq_dec_refl in IHt1, IHt2.
  specialize (IHt1 eq_refl).
  specialize (IHt2 eq_refl).
  simpl in *; desh.
  pose proof (unsindices_app_r Heqo0 Heqo); desh.
  rewrite e0, EqDec.peq_dec_refl.
  now rewrite x1, IHt1, IHt2.
Qed.

Fixpoint sexprAD (e : SExpr) : Type :=
  match e with
  | STop    => True
  | SBottom => False
  | SEquiv x y f g =>
    let d := Pos_to_fin num_objs x in
    let c := Pos_to_fin num_objs y in
    match stermD d c (unsindices (sindices f)),
          stermD d c (unsindices (sindices g)) with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | SAnd p q  => sexprAD p ∧ sexprAD q
  | SOr p q   => sexprAD p + sexprAD q
  | SImpl p q => sexprAD p → sexprAD q
  end.

Theorem sexprAD_sound (e : SExpr) : sexprAD e ↔ sexprD e.
Proof.
  induction e; split; simpl in *; intuition.
  - destruct (stermD _ _ _) eqn:?; [|tauto].
    destruct (stermD _ _ (_ (_ g))) eqn:?; [|tauto].
    apply unsindices_sindices in Heqo.
    apply unsindices_sindices in Heqo0.
    simpl in *.
    destruct (stermD _ _ f); [|tauto].
    destruct (stermD _ _ g); [|tauto].
    now rewrite Heqo, Heqo0, <- X.
  - desh.
    destruct (stermD _ _ f) eqn:?; [|tauto].
    destruct (stermD _ _ g) eqn:?; [|tauto].
    apply unsindices_sindices_r in Heqo.
    apply unsindices_sindices_r in Heqo0.
    simpl in *.
    destruct (stermD _ _ _) eqn:?; [|tauto].
    destruct (stermD _ _ (_ (_ g))) eqn:?; [|tauto].
    now rewrite Heqo, Heqo0, X.
Qed.

End Normal.

(* * This is a much easier theorem to apply, so it speeds things up a lot! *)
Corollary sexprAD_sound' (env : Env) (e : SExpr) : sexprAD e → sexprD e.
Proof. apply sexprAD_sound. Qed.

Ltac normalize :=
  reify_and_change;
  simple apply sexprAD_sound';
  vm_compute.

Example ex_normalize
  (C : Category) (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
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

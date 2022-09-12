Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.

Section Normal.

Context `{Arrows}.

Import ListNotations.

Set Transparent Obligations.

Inductive Morphism : Set :=
  | Identity
  | Morphisms (c : Composition)

with Composition : Set :=
  | Single   (f : Arrow)
  | Composed (f : Arrow) (fs : Composition)

with Arrow : Set :=
  | Arr     (n : nat)
  | ArrFork (f g : Morphism)
  | ArrExl
  | ArrExr.

Ltac breakit :=
  lazymatch goal with
  | [ H : Morphism |- _ ] => destruct H
  | [ H : Composition |- _ ] => destruct H
  | [ H : Arrow |- _ ] => destruct H
  end.

Ltac solveit :=
  solve [ intros; subst; breakit; intuition
        | split; intros; breakit; intuition; discriminate ].

Program Fixpoint morphism_eq_dec (f g : Morphism) : {f = g} + {f ≠ g} :=
  match f, g with
  | Identity, Identity => left eq_refl
  | Morphisms fs, Morphisms gs =>
    match composition_eq_dec fs gs with
    | left  _ => in_left
    | right _ => in_right
    end
  | _, _ => right _
  end

with composition_eq_dec (f g : Composition) : {f = g} + {f ≠ g} :=
  match f, g with
  | Single f, Single g =>
    match arrow_eq_dec f g with
    | left  _ => in_left
    | right _ => in_right
    end
  | Composed f fs, Composed g gs =>
    match arrow_eq_dec f g with
    | left  _ =>
      match composition_eq_dec fs gs with
      | left  _ => in_left
      | right _ => in_right
      end
    | right _ => in_right
    end
  | _, _ => in_right
  end

with arrow_eq_dec (f g : Arrow) : {f = g} + {f ≠ g} :=
  match f, g with
  | Arr f, Arr g =>
    match PeanoNat.Nat.eq_dec f g with
    | left  _ => in_left
    | right _ => in_right
    end
  | ArrFork f g, ArrFork h k =>
    match morphism_eq_dec f h with
    | left  _ =>
      match morphism_eq_dec g k with
      | left  _ => in_left
      | right _ => in_right
      end
    | right _ => in_right
    end
  | ArrExl, ArrExl => left eq_refl
  | ArrExr, ArrExr => left eq_refl
  | _, _ => in_right
  end.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

Fixpoint append (f g : Composition) : Composition :=
  match f, g with
  | Single f, gs      => Composed f gs
  | Composed f fs, gs => Composed f (append fs gs)
  end.

Definition combine (f g : Morphism) : Morphism :=
  match f, g with
  | Identity, g => g
  | f, Identity => f
  | Morphisms fs, Morphisms gs => Morphisms (append fs gs)
  end.

Fixpoint to_morphism (t : Term) : Morphism :=
  match t with
  | Ident    => Identity
  | Morph a  => Morphisms (Single (Arr a))
  | Comp f g => combine (to_morphism f) (to_morphism g)
  | Fork f g => Morphisms (Single (ArrFork (to_morphism f) (to_morphism g)))
  | Exl      => Morphisms (Single ArrExl)
  | Exr      => Morphisms (Single ArrExr)
  end.

Fixpoint to_morphism_f (k : Morphism → Morphism) (t : Term) : Morphism :=
  match t with
  | Ident    => k Identity
  | Morph a  => k (Morphisms (Single (Arr a)))
  | Comp f g => k (combine (to_morphism_f k f) (to_morphism_f k g))
  | Fork f g =>
    k (Morphisms (Single (ArrFork (to_morphism_f k f) (to_morphism_f k g))))
  | Exl      => k (Morphisms (Single ArrExl))
  | Exr      => k (Morphisms (Single ArrExr))
  end.

Fixpoint from_morphism (f : Morphism) : Term :=
  match f with
  | Identity => Ident
  | Morphisms fs => from_composition fs
  end

with from_composition (fs : Composition) : Term :=
  match fs with
  | Single f => from_arrow f
  | Composed f gs => Comp (from_arrow f) (from_composition gs)
  end

with from_arrow (a : Arrow) : Term :=
  match a with
  | Arr f => Morph f
  | ArrFork f g => Fork (from_morphism f) (from_morphism g)
  | ArrExl => Exl
  | ArrExr => Exr
  end.

Definition norm_cartesian (c : Morphism) : Morphism :=
  match c with
  | Morphisms (Composed ArrExl (Single (ArrFork f g))) => f
  | Morphisms (Composed ArrExl (Composed (ArrFork f g) h)) =>
      combine f (Morphisms h)

  | Morphisms (Composed ArrExr (Single (ArrFork f g))) => g
  | Morphisms (Composed ArrExr (Composed (ArrFork f g) h)) =>
      combine g (Morphisms h)

  | Morphisms
      (Single
         (ArrFork
            (Morphisms (Single ArrExl))
            (Morphisms (Single ArrExr)))) => Identity
  | Morphisms
      (Composed
         (ArrFork
            (Morphisms (Single ArrExl))
            (Morphisms (Single ArrExr))) h) => Morphisms h

  | f => f
  end.

(* id ∘ ((exl ∘ (id ∘ exl) △ exr) ∘ (1 ∘ 2 △ 3)) ≈ 1 ∘ 2 *)
Compute to_morphism_f norm_cartesian
  (Comp Ident
     (Comp (Comp Exl (Fork (Comp Ident Exl) Exr))
        (Fork (Comp (Morph 1) (Morph 2)) (Morph 3)))).

Ltac matches :=
  match goal with
  | [ H : context[match lookup_arr ?f ?dom with _ => _ end] |- _ ] =>
    destruct (lookup_arr f dom) as [[? ?]|] eqn:?
  | [ H : context[match @termD_work ?h ?n ?s with _ => _ end] |- _ ] =>
    destruct (@termD_work h n s) as [[? ?]|] eqn:?
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

Lemma from_morphism_app {d c} {t1 t2 : Morphism} {f} :
  termD_work d (from_morphism (combine t1 t2)) = Some (c; f)
    → ∃ m g h, f ≈ g ∘ h
        ∧ termD_work m (from_morphism t1) = Some (c; g)
        ∧ termD_work d (from_morphism t2) = Some (m; h).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold termD; destruct t1; simpl; intros.
  - eexists _, _, f.
    now split; cat.
  - generalize dependent c0.
    induction c; simpl; intros.
    + destruct t2; simpl in *.
      * exists d, f0, id.
        split; cat.
      * desh.
        exists _, h0, h.
        split; cat.
    + destruct t2; simpl in *; desh.
      * specialize (IHc _ _ eq_refl); desh.
        exists _, (h0 ∘ h), id.
        split; cat.
        now rewrite Heqo, Heqo0.
      * specialize (IHc _ _ eq_refl); desh.
        rewrite e.
        exists x0, (h0 ∘ x1), x2.
        rewrite x4, Heqo0.
        split; cat.
        rewrite x3; cat.
Qed.

Theorem from_morphism_to_morphism {d c} {t : Term} {f} :
  termD d c (from_morphism (to_morphism t)) = Some f
    → termD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold termD; induction t; simpl; intros; desh.
  - pose proof (from_morphism_app Heqo); desh.
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
  - specialize (IHt1 d x).
    rewrite Heqo, EqDec.peq_dec_refl in IHt1.
    specialize (IHt1 _ eq_refl).
    specialize (IHt2 d x0).
    rewrite Heqo0, EqDec.peq_dec_refl in IHt2.
    specialize (IHt2 _ eq_refl).
    simpl in *.
    desh.
    now rewrite IHt1, IHt2.
  - destruct d; [discriminate|]; desh.
  - destruct d; [discriminate|]; desh.
Qed.

Theorem from_morphism_to_morphism_f {d c} {t : Term} {f k} :
  k Identity = Identity →
  (∀ f, k (Morphisms (Single (Arr f))) = Morphisms (Single (Arr f))) →
  k (Morphisms (Single ArrExl)) = Morphisms (Single ArrExl) →
  k (Morphisms (Single ArrExr)) = Morphisms (Single ArrExr) →
  (∀ t1 t2, t1 = Morphisms (Single ArrExl) → t2 = Morphisms (Single ArrExr) → k (Morphisms (Single (ArrFork t1 t2))) = Identity) →
  (∀ t1 t2, t1 ≠ Morphisms (Single ArrExl) ∨ t2 ≠ Morphisms (Single ArrExr) → k (Morphisms (Single (ArrFork t1 t2))) = Morphisms (Single (ArrFork t1 t2))) →
  termD d c (from_morphism (to_morphism_f k t)) = Some f
    → termD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold termD; induction t; simpl; intros; desh.
  - rewrite H0 in Heqo; simpl in *; desh.
    now rewrite peq_dec_refl.
  - rewrite H1 in Heqo.
    simpl in Heqo.
    rewrite Heqo; desh.
  - admit.
  - destruct
      (to_morphism_f k t1) eqn:Ht1,
      (to_morphism_f k t2) eqn:Ht2;
    intuition.
    + rewrite H5 in Heqo.
      * simpl in Heqo.
        desh.
        admit.
      * left; intro; discriminate.
    + admit.
    + admit.
    + admit.
  - rewrite H2 in Heqo.
    simpl in Heqo.
    rewrite Heqo; desh.
  - rewrite H3 in Heqo.
    simpl in Heqo.
    rewrite Heqo; desh.
Admitted.

Lemma from_morphism_app_r {d m c} {t1 t2 : Morphism} {g h} :
    termD_work m (from_morphism t1) = Some (c; g)
  → termD_work d (from_morphism t2) = Some (m; h)
  → ∃ f, f ≈ g ∘ h ∧
          termD_work d (from_morphism (combine t1 t2)) = Some (c; f).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold termD; destruct t1; simpl; intros; desh.
  generalize dependent c0.
  induction c; simpl; intros; desh.
  - destruct t2; simpl in *; desh.
    exists (g ∘ h).
    split; cat.
    now rewrite H1, H0.
  - destruct t2; simpl in *; desh.
    + specialize (IHc _ _ eq_refl); desh.
      exists (h1 ∘ x0).
      split.
      * now rewrite x1; cat.
      * now rewrite e0, Heqo0.
    + specialize (IHc _ _ eq_refl); desh.
      exists (h1 ∘ x0).
      split.
      * now rewrite x1; cat.
      * now rewrite e0, Heqo0.
Qed.

Theorem from_morphism_to_morphism_r {d c} {t : Term} {f} :
  termD d c t = Some f
    → termD d c (from_morphism (to_morphism t)) ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold termD; induction t; simpl; intros; desh.
  - specialize (IHt2 _ _ h).
    rewrite Heqo in IHt2; clear Heqo.
    specialize (IHt1 _ _ h0).
    rewrite Heqo0 in IHt1; clear Heqo0.
    rewrite EqDec.peq_dec_refl in IHt1, IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    pose proof (from_morphism_app_r Heqo0 Heqo); desh.
    rewrite e0, EqDec.peq_dec_refl.
    now rewrite x1, IHt1, IHt2.
  - specialize (IHt1 d x).
    rewrite Heqo, EqDec.peq_dec_refl in IHt1.
    specialize (IHt1 _ eq_refl).
    specialize (IHt2 d x0).
    rewrite Heqo0, EqDec.peq_dec_refl in IHt2.
    specialize (IHt2 _ eq_refl).
    simpl in *.
    desh.
    now rewrite IHt1, IHt2.
  - destruct d; [discriminate|]; desh.
  - destruct d; [discriminate|]; desh.
Qed.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top    => True
  | Bottom => False
  | Equiv d c f g =>
    match termD d c (from_morphism (to_morphism f)),
          termD d c (from_morphism (to_morphism g)) with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | And p q  => exprAD p ∧ exprAD q
  | Or p q   => exprAD p + exprAD q
  | Impl p q => exprAD p → exprAD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e ↔ exprD e.
Proof.
  induction e; split; simpl in *; intuition.
  - destruct (termD _ _ _) eqn:?; [|tauto].
    destruct (termD _ _ (_ (_ g))) eqn:?; [|tauto].
    apply from_morphism_to_morphism in Heqo.
    apply from_morphism_to_morphism in Heqo0.
    simpl in *.
    destruct (termD _ _ f); [|tauto].
    destruct (termD _ _ g); [|tauto].
    now rewrite Heqo, Heqo0, <- X.
  - desh.
    destruct (termD _ _ f) eqn:?; [|tauto].
    destruct (termD _ _ g) eqn:?; [|tauto].
    apply from_morphism_to_morphism_r in Heqo.
    apply from_morphism_to_morphism_r in Heqo0.
    simpl in *.
    destruct (termD _ _ _) eqn:?; [|tauto].
    destruct (termD _ _ (_ (_ g))) eqn:?; [|tauto].
    now rewrite Heqo, Heqo0, X.
Qed.

End Normal.

(* * This is a much easier theorem to apply, so it speeds things up a lot! *)
Corollary exprAD_sound' (env : Arrows) (e : Expr) :
  exprAD e → exprD e.
Proof. apply exprAD_sound. Qed.

Ltac normalize :=
  reify_and_change;
  simple apply exprAD_sound';
  vm_compute.

Example ex_normalize
  (C : Category) `{@Cartesian C} (x y z w : C)
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

Example ex_normalize_cartesian
  (C : Category) `{@Cartesian C} (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
  g ∘ h ≈ i ->
  f ∘ (id ∘ exl ∘ (id ∘ g ∘ h) △ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  Fail reflexivity.
  normalize.
  Fail reflexivity.             (* would work with norm_cartesian *)
  cat.
Qed.

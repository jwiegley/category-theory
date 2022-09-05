Set Warnings "-notation-overridden".

Require Import
  Category.Instance.Lambda.Lib
  Category.Instance.Lambda.Ty
  Category.Instance.Lambda.Exp
  Category.Instance.Lambda.Ren
  Category.Instance.Lambda.Sem.

Require Import Category.Lib.
Require Import Category.Structure.BiCCC.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Lambda.

Context {A : Type}.
Context `{L : HostExprsSem A}.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

Lemma SemExp_identity {Γ τ} (se : SemEnv Γ) :
  SemExp (identity Γ τ) se = Datatypes.id.
Proof. now f_equal. Qed.

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

Lemma SemExp_composition `(E : SemEnv Γ)
      {τ τ' τ''} (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f g) E = Basics.compose (SemExp f E) (SemExp g E).
Proof.
  extensionality z.
  fold SemTy in z.
  unfold composition; simpl.
  now rewrite !SemExp_wk.
Qed.

Lemma SemExp_composition_identity_right `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_composition.
  reflexivity.
Qed.

Lemma SemExp_composition_identity_left `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (composition (identity Γ τ') f) E = SemExp f E.
Proof.
  rewrite SemExp_composition.
  reflexivity.
Qed.

Lemma SemExp_composition_assoc `(E : SemEnv Γ)
      {τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f (composition g h)) E =
  SemExp (composition (composition f g) h) E.
Proof.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

Program Definition Lambda Γ : Category := {|
  obj     := Ty;
  hom     := λ A B : Ty, Exp Γ (A ⟶ B);
  homset  := λ _ _, {| equiv := λ f g, SemExp f = SemExp g |};
  id      := @identity Γ;
  compose := @composition Γ
|}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation.
  extensionality se.
  rewrite !SemExp_composition.
  now rewrite H, H0.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  simp Keep; simpl.
  unfold wk.
  rewrite <- SemExp_RenSem.
  now rewrite RenSem_skip1.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  simp Keep; simpl.
  unfold wk.
  rewrite <- SemExp_RenSem.
  now rewrite RenSem_skip1.
Qed.
Next Obligation.
  extensionality se.
  pose proof (SemExp_composition_assoc se f g h).
  simpl in H.
  now apply H.
Qed.
Next Obligation.
  extensionality se.
  pose proof (SemExp_composition_assoc se f g h).
  symmetry in H.
  simpl in H.
  now apply H.
Qed.

#[export]
Program Instance Lambda_Terminal Γ : @Terminal (Lambda Γ) := {
  terminal_obj := TyUnit;
  one := λ _, LAM EUnit
}.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  now destruct (SemExp f se x0), (SemExp g se x0).
Qed.

#[export]
Program Instance Lambda_Cartesian Γ : @Cartesian (Lambda Γ) := {
  product_obj := TyPair;
  fork := λ _ _ _ f g,
    LAM (Pair (APP (wk f) (VAR ZV)) (APP (wk g) (VAR ZV)));
  exl  := λ _ _, LAM (Fst (VAR ZV));
  exr  := λ _ _, LAM (Snd (VAR ZV));
}.
Next Obligation.
  extensionality se.
  extensionality x2.
  fold SemTy in x2.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  rewrite !RenSem_skip1.
  simpl.
  now rewrite H, H0.
Qed.
Next Obligation.
  split; intros.
  - split.
    + extensionality se.
      extensionality x2.
      fold SemTy in x2.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      rewrite !RenSem_skip1.
      simpl.
      simp Keep; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      now rewrite !RenSem_skip1.
    + extensionality se.
      extensionality x2.
      fold SemTy in x2.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      rewrite !RenSem_skip1.
      simpl.
      simp Keep; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      now rewrite !RenSem_skip1.
  - destruct H.
    extensionality se.
    extensionality x2.
    fold SemTy in x2.
    unfold wk.
    rewrite <- !SemExp_RenSem.
    rewrite <- e, <- e0.
    simp Keep; simpl.
    unfold wk.
    rewrite <- !SemExp_RenSem.
    rewrite !RenSem_skip1; simpl.
    now destruct (SemExp h se x2).
Qed.

Definition curry {Γ a b c} (f : Exp Γ (a × b ⟶ c)) : Exp Γ (a ⟶ b ⟶ c) :=
  LAM (LAM (APP (wk (wk f)) (Pair (VAR (SV ZV)) (VAR ZV)))).

Definition uncurry {Γ a b c} (f : Exp Γ (a ⟶ b ⟶ c)) : Exp Γ (a × b ⟶ c) :=
  LAM (APP (APP (wk f) (Fst (VAR ZV))) (Snd (VAR ZV))).

#[export]
Program Instance Lambda_Closed Γ : @Closed (Lambda Γ) _ := {
  exponent_obj := TyArrow;
  exp_iso := λ _ _ _,
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
}.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  congruence.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  congruence.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  now repeat setoid_rewrite RenSem_skip1.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  repeat setoid_rewrite RenSem_skip1.
  now destruct x0.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
  unfold wk.
  simp RenVar.
  simpl.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  rewrite !RenSem_skip1.
  now setoid_rewrite RenSem_skip1.
Qed.

End Lambda.

Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sem.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Lambda.

Context {A : Type}.
Context `{L : HostExprsSem A}.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

#[export]
Program Instance TyArrow_Setoid {dom cod} : Setoid (SemTy (dom ⟶ cod)) := {
  equiv := λ f g, f ≈[Coq] g
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

#[export]
Program Instance Exp_Setoid {Γ dom cod} : Setoid (Exp Γ (dom ⟶ cod)) := {
  equiv := λ f g, ∀ E, SemExp f E ≈ SemExp g E
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

Lemma SemExp_identity {Γ τ} (E : SemEnv Γ) :
  SemExp (identity Γ τ) E ≈ id.
Proof. now f_equal. Qed.

Lemma SemExp_composition `(E : SemEnv Γ) {τ τ' τ''}
      (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f g) E ≈ SemExp f E ∘ SemExp g E.
Proof.
  intro.
  unfold composition; simpl.
  now rewrite !SemExp_wk.
Qed.

#[export]
Program Instance composition_respects {Γ τ τ' τ''} :
  Proper (equiv ==> equiv ==> equiv) (@composition Γ τ τ' τ'').
Next Obligation.
  unfold composition; simpl.
  rewrite !SemExp_wk.
  now rewrite H, H0.
Qed.

Lemma composition_identity_right {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition f (identity Γ τ) ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_identity_left {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition (identity Γ τ') f ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_assoc {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition f (composition g h) ≈
  composition (composition f g) h.
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

Lemma composition_assoc_sym {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition (composition f g) h ≈
  composition f (composition g h).
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

#[local] Obligation Tactic := intros.

Program Definition Lambda Γ : Category := {|
  obj     := Ty;
  hom     := λ A B : Ty, Exp Γ (A ⟶ B);
  homset  := @Exp_Setoid Γ;
  id      := @identity Γ;
  compose := @composition Γ;

  compose_respects := @composition_respects Γ;

  id_left := @composition_identity_left Γ;
  id_right := @composition_identity_left Γ;
  comp_assoc := @composition_assoc Γ;
  comp_assoc_sym := @composition_assoc_sym Γ;
|}.

#[export]
Program Instance Lambda_Terminal Γ : @Terminal (Lambda Γ) := {
  terminal_obj := TyUnit;
  one := λ _, LAM EUnit
}.
Next Obligation.
  repeat intro.
  now destruct (SemExp f E x0), (SemExp g E x0).
Qed.

#[export]
Program Instance Lambda_Cartesian Γ : @Cartesian (Lambda Γ) := {
  product_obj := TyPair;
  isCartesianProduct _ _ := {|
  fork := λ _ f g,
    LAM (Pair (APP (wk f) (VAR ZV)) (APP (wk g) (VAR ZV)));
  exl  := LAM (Fst (VAR ZV));
  exr  := LAM (Snd (VAR ZV)); |}
}.
Next Obligation.
  proper.
  rewrite !SemExp_wk.
  now rewrite X, X0.
Qed.
Next Obligation.
  split; repeat intro; simpl.
  - split; intros; rewrite !SemExp_wk.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
  - destruct X.
    rewrite !SemExp_wk.
    rewrite <- e, <- e0.
    simp Keep; simpl.
    rewrite !SemExp_wk.
    simp RenVar; simpl.
    apply surjective_pairing.
Qed.

Definition curry {Γ a b c} (f : Exp Γ (a × b ⟶ c)) : Exp Γ (a ⟶ b ⟶ c) :=
  LAM (LAM (APP (wk (wk f)) (Pair (VAR (SV ZV)) (VAR ZV)))).

Definition uncurry {Γ a b c} (f : Exp Γ (a ⟶ b ⟶ c)) : Exp Γ (a × b ⟶ c) :=
  LAM (APP (APP (wk f) (Fst (VAR ZV))) (Snd (VAR ZV))).

#[local] Obligation Tactic := program_simpl.

#[export]
Program Instance Lambda_Closed Γ : @Closed (Lambda Γ) _ := {
  exponent_obj := TyArrow;
  exp_iso := λ _ _ _,
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
}.
Next Obligation.
  proper.
  extensionality z.
  unfold wk at 1.
  unfold wk at 2.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  rewrite !SemExp_wk.
  eauto.
Qed.
Next Obligation.
  proper.
  rewrite !SemExp_wk; simpl.
  congruence.
Qed.
Next Obligation.
  extensionality z.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  rewrite SemExp_wk.
  now repeat setoid_rewrite RenSem_skip1; simpl.
Qed.
Next Obligation.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  repeat setoid_rewrite RenSem_skip1; simpl.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.
Next Obligation.
  simp RenVar; simpl.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.

End Lambda.

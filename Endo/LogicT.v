Require Export Iso.
Require Export Monad.

Inductive LogicT (M : Type -> Type) `{Monad M} (A : Type) :=
  LogicT_ : forall {R : Type}, ((A -> M R -> M R) -> M R -> M R) -> LogicT M A.

Inductive LogicT' (M : Type -> Type) `{Monad M} (A : Type) :=
  LogicT_' : forall {R : Type}, ((A -> R -> M R) -> R -> M R) -> LogicT' M A.

Definition fromLogicT (M : Type -> Type) `{Monad M} (A : Type)
  (l : LogicT M A) : LogicT' M A :=
  match l with
    LogicT_ _ await =>
      LogicT_' M A (fun yield =>
        await (compose (mu/M) ∘ (@fmap M _ _ _) ∘ yield) ∘ eta)
  end.

Definition toLogicT (M : Type -> Type) `{Monad M} (A : Type)
  (l : LogicT' M A) : LogicT M A :=
  match l with
    LogicT_' _ await =>
      LogicT_ M A (fun yield => mu ∘ fmap (await (fun x => yield x ∘ eta)))
  end.

Theorem mu_fmap_eta : forall (M : Type -> Type) `{Monad M} (A B : Type)
  (f : M A -> M B) (x : M A),
  mu ∘ fmap f = f ∘ mu -> mu ∘ fmap f ∘ fmap eta = f.
Proof.
  intros.
  rewrite comp_assoc.
  rewrite H0.
  rewrite <- comp_assoc.
  rewrite monad_law_2.
  rewrite comp_id_right.
  reflexivity.
Qed.

Theorem bind_fmap_eta : forall (M : Type -> Type) `{Monad M} (A B : Type)
  (f : M A -> M B) (x : M A),
  mu ∘ fmap f = f ∘ mu -> mu (fmap (fun y => f (eta y)) x) = f x.
Proof.
  intros.
  pose (mu_fmap_eta M A B f x).
  rewrite fun_composition in e.
  rewrite <- (uncompose mu).
  assert ((fun y : A => f ((eta/M) y)) = f ∘ (eta/M)).
    unfold compose. reflexivity. rewrite H1. clear H1.
  rewrite e. reflexivity.
  assumption.
  apply f. assumption.
Qed.

Global Instance LogicT_Restricted_Isomorphism
  (M : Type -> Type) `{Monad M} (A : Type)
  (J2 : forall A B (f : M A -> M B), mu ∘ fmap f = f ∘ mu)
  : LogicT' M A ≅ LogicT M A :=
{ to   := toLogicT M A
; from := fromLogicT M A
}.
Proof.
  intros.
  - ext_eq.
    unfold id.
    destruct x.
    unfold compose.
    simpl. f_equal.
    unfold flip, bind.
    ext_eq. ext_eq.
    unfold compose.
    rewrite <- app_fmap_compose_x.
    rewrite monad_law_3_x.
    f_equal.
    ext_eq. ext_eq.
    unfold compose.
    rewrite <- app_fmap_compose_x.
    rewrite monad_law_3_x.
    reflexivity.
  - ext_eq.
    unfold id.
    destruct x.
    unfold compose.
    simpl. f_equal.
    ext_eq. ext_eq.
    unfold compose.
    rewrite bind_fmap_eta.
    assert ((fun (x2 : A) (x3 : M R) =>
              (mu/M) ((fmap[M] (fun x4 : R => x x2 ((eta/M) x4))) x3)) = x).
      ext_eq. ext_eq.
      rewrite bind_fmap_eta.
      reflexivity.
    apply J2.
    rewrite H0. clear H0.
    reflexivity.
    apply J2.
Defined.

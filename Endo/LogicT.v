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

(* The condition J2 was given by Jones and Duponcheel as a condition in their
   treatment of "compatible" monads.  I'm not yet certain what part it plays
   here.
*)
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
    unfold id. destruct x.
    unfold compose. simpl.
    unfold compose at 5.
    f_equal. ext_eq.
    rewrite <- fun_composition.
    rewrite comp_assoc.
    rewrite J2.
    rewrite <- comp_assoc.
    rewrite monad_law_2.
    rewrite comp_id_right.
    f_equal. ext_eq.
    unfold compose at 1.
    rewrite <- fun_composition.
    rewrite comp_assoc.
    rewrite J2.
    rewrite <- comp_assoc.
    rewrite monad_law_2.
    reflexivity.
Defined.

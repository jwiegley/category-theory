Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Applicative.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Functor.Proofs.
Require Export Category.Theory.Coq.Applicative.

Generalizable All Variables.

Import ApplicativeNotations.

Corollary compose_ap  `{Applicative F} `{Applicative G} {x y} :
  ap[F ∘ G]%prg = (ap[F] ∘ fmap[F] (@ap G _ x y))%prg.
Proof. reflexivity. Qed.

Corollary ap_comp `{Applicative F} `{f : a → F (b → c)} {x} :
  (ap[F] ∘ f)%prg x = ap (f x).
Proof. reflexivity. Qed.

Corollary pure_comp `{Applicative F} `{f : a → b} {x} :
  (pure[F] ∘ f)%prg x = pure (f x).
Proof. reflexivity. Qed.

Definition EndoApplicative_Applicative
  `(H : EndoFunctor F)
  `(A : @Functor.Applicative.Applicative _ _ (FromAFunctor H)) :
  Applicative F := {|
  pure := λ _ x,
    @Pure.pure _ _ (FromAFunctor H) _ A _ x;
  ap   := λ _ _ f x,
    @Functor.Applicative.ap _ _ (FromAFunctor H) A _ _ (f, x)
|}.

Definition IsApplicative `(H : EndoFunctor F) `(Applicative F) : Type :=
  Functor.Applicative.Applicative (ToAFunctor H).

Theorem Identity_IsApplicative :
  IsApplicative Identity_IsFunctor Identity_Applicative.
Proof.
  construct.
  - apply Id_LaxMonoidalFunctor.
  - apply Coq_StrongFunctor.
Qed.

Theorem arrow_IsApplicative {x} :
  IsApplicative arrow_IsFunctor (arrow_Applicative x).
Proof.
  unfold arrow_Applicative, arrow.
  construct.
  - construct.
    + exact H.
    + construct; intuition eauto.
    + construct; intuition eauto; simpl.
      * extensionality z.
        now destruct (x1 z), u.
      * f_equal.
        now destruct a.
    + construct; intuition eauto; simpl.
      * extensionality z.
        now destruct (x1 z), u.
      * f_equal.
        now destruct b.
    + construct; intuition eauto; simpl.
      * extensionality w.
        now destruct (x1 w); simplify.
    + destruct x1; simpl.
      reflexivity.
    + destruct x1; simpl.
      reflexivity.
    + simplify; simpl.
      intuition eauto.
  - apply Coq_StrongFunctor.
Qed.

(* The composition of two applicatives is itself applicative. We establish
   this by appeal to the general proofs that:

   1. every Coq functor has strength;
   2. (also, but not needed: any two strong functors compose to a strong
      functor; if it is a Coq functor it is known to have strength); and
   3. any two lax monoidal functors compose to a lax monoidal functor. *)

Theorem Compose_IsApplicative
  `(HF : EndoFunctor F)
  `(AF : @Functor.Applicative.Applicative _ _ (FromAFunctor HF))
  `(HG : EndoFunctor G)
  `(AG : @Functor.Applicative.Applicative _ _ (FromAFunctor HG)) :
  IsApplicative (Compose_IsFunctor HF HG)
    (@Compose_Applicative
       F (EndoApplicative_Applicative HF AF)
       G (EndoApplicative_Applicative HG AG)).
Proof.
  construct.
  - apply (@Compose_LaxMonoidalFunctor _ _ _ _ _ _ _ _ AF AG).
  - apply Coq_StrongFunctor.
Qed.

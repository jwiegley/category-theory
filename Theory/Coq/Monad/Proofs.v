Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Applicative.
Require Import Category.Monad.Distributive.
Require Import Category.Monad.Compose.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Applicative.Proofs.
Require Export Category.Theory.Coq.Monad.

Generalizable All Variables.

Definition EndoMonad_Monad
  `(H : EndoFunctor F)
  `(A : @Functor.Applicative.Applicative _ _ (FromAFunctor H))
  `(M : @Theory.Monad.Monad _ (FromAFunctor H)) :
  Monad F := {|
  ret := @Pure.pure _ _ (FromAFunctor H) _ A;
  bind := λ x y m f,
    @Theory.Monad.join _ _ M y
      (@Theory.Functor.fmap _ _ (FromAFunctor H) x (F y) f m);
|}.

Definition IsMonad
  `(H : EndoFunctor F)
  `(A : @Functor.Applicative.Applicative _ _ (FromAFunctor H))
  `(Monad F) : Type :=
  Theory.Monad.Monad (ToAFunctor H).

Theorem Identity_IsMonad :
  IsMonad Identity_IsFunctor Identity_IsApplicative Identity_Monad.
Proof.
  construct; auto.
Qed.

Theorem arrow_IsMonad {x} :
  IsMonad arrow_IsFunctor arrow_IsApplicative (arrow_Monad x).
Proof.
  unfold arrow_Monad, arrow.
  construct; auto.
Qed.

Section Compose_Monad.

(* If we have a monad [M] composed with an applicative [N], and we know that
   they distribute as in [N (M (N a)) ~> M (N a)], then the composition is
   also a monad. *)

Context `(HF : EndoFunctor F).
Context `(AF : @Functor.Applicative.Applicative _ _ (FromAFunctor HF)).
Context `(MF : @Theory.Monad.Monad _ (FromAFunctor HF)).
Context `(HG : EndoFunctor G).
Context `(AG : @Functor.Applicative.Applicative _ _ (FromAFunctor HG)).

(* This is the essential condition, as explained by Mark P. Jones and Luc
   Duponcheel in their article "Composing monads", Research Report
   YALEU/DCS/RR-1004, December 1993. *)
Context `{D : @Monad_Distributive _ _ (FromAFunctor HF) _ (FromAFunctor HG) _ AG}.

Definition EndoMonad_Distributes : Monad_Distributes F G :=
  @Monad.Distributive.mprod _ _ (FromAFunctor HF) _ (FromAFunctor HG) _ AG _.

Theorem Compose_IsMonad :
  IsMonad
    (Compose_IsFunctor HF HG)
    (Compose_IsApplicative HF AF HG AG)
    (@Compose_Monad
       _ (EndoMonad_Monad HF AF MF)
       _ (EndoApplicative_Applicative HG AG)
       EndoMonad_Distributes).
Proof.
  exact (@Monad_Compose _ _ _ _ _ _ _ D).
Qed.

End Compose_Monad.

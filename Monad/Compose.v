Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Distributive.

Generalizable All Variables.

Section MonadCompose.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Strong LaxMonoidalFunctor N, and further given
   that M distributes over N according to Monad_Distributive, it can be shown
   that M ◯ N is always a Monad. *)

#[local] Obligation Tactic := idtac.

#[export] Program Instance Monad_Compose `{!Monad_Distributive M N} :
  @Monad _ (M ◯ N) := {
  ret  := fun _ => ret[M] ∘ pure[N];
  join := fun _ => join[M] ∘ fmap[M] mprod
}.
Next Obligation.
  simpl; intros.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  rewrite <- !comp_assoc.
  rewrite <- fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- comp_assoc with (f := join[M]).
  rewrite <- comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := fmap[M] mprod).
  rewrite <- join_fmap_fmap.
  rewrite comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite comp_assoc.
  rewrite <- mprod_fmap_join_fmap_mprod.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- join_fmap_ret.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite mprod_fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- mprod_pure.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret; cat.
Qed.
Next Obligation.
  simpl; intros.
  rewrite comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@mprod_fmap_fmap _ _ _ _ _ _ _ _ x).
  simpl in X.
  rewrite X.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

End MonadCompose.

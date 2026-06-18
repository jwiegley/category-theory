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

(** * The composite monad M ◯ N from a distributive law *)

(* nLab: https://ncatlab.org/nlab/show/distributive+law
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_law_between_monads

   Monads do not compose in general: there is no canonical monad structure on
   the composite endofunctor M ◯ N. A Beck distributive law — a natural
   transformation that swaps the two layers, here packaged as the operation
   mprod : N (M (N A)) ~> M (N A) from [Monad.Distributive] — is exactly the
   extra datum that makes the composite a monad, provided its four coherence
   laws (mprod_fmap_fmap, mprod_pure, mprod_fmap_pure, mprod_fmap_join_fmap_
   mprod) hold against the units and multiplications of both layers.

   Following the standard recipe, the composite M ◯ N is given the unit
   ret[M] ∘ pure[N] (η_M after η_N, the two units stacked) and the
   multiplication join[M] ∘ fmap[M] mprod : M (N (M (N A))) ~> M (N A): mprod
   swaps the inner N (M …) past M so the two N-layers and the two M-layers sit
   adjacent, then join[M] collapses the M-layers (the N-layers having already
   been merged inside mprod). The five [Monad] obligations below are the unit
   naturality, associativity, the two unit laws, and the multiplication
   naturality of M ◯ N; each is discharged using the corresponding M-law and
   one of the mprod coherence laws.

   This is the lax-monoidal-functor formulation of Mark P. Jones and Luc
   Duponcheel, "Composing monads", Research Report YALEU/DCS/RR-1004, Yale
   University, December 1993. There M is a full monad while N is required only
   to be a strong lax monoidal functor (it need not itself be a monad), and
   mprod plays the role of their distributivity operation prod. *)

Section MonadCompose.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

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

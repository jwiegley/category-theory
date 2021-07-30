Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Functor.Structure.Monoidal.Pure.
Require Export Category.Monad.Distributive.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonadComposition.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Strong LaxMonoidalFunctor N, and further given
   that M distributes over N according to Monad_Distributive, it can be shown
   that M ◯ N is always a Monad. *)

Local Obligation Tactic := idtac.

Global Program Instance Monad_Composition `{Monad_Distributive} :
  @Monad _ (M ◯ N) := {
  ret  := fun _ => ret[M] ∘ pure[N];
  join := fun _ => join[M] ∘ fmap[M] prod
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
  rewrite comp_assoc with (f := fmap[M] prod).
  rewrite <- join_fmap_fmap.
  rewrite comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite comp_assoc.
  rewrite <- prod_fmap_join_fmap_prod.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- join_fmap_ret.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite prod_fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- prod_pure.
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
  pose proof (@prod_fmap_fmap _ _ _ _ _ _ _ _ x).
  simpl in X.
  rewrite X.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

End MonadComposition.

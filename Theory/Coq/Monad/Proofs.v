Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Category.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* jww (2022-09-07): TODO
Class IsMonad_Distributes `{@IsMonad M MF MA MM MIF MIA} `{@IsApplicative N NF NA NIF}
  `{@Monad_Distributes M MF MA MM N NF NA} := {
  prod_fmap_fmap {A B : Coq} {f : A -> B} :
    prod M N B ∘ fmap[N] (fmap[M ∘ N] f) = fmap[M ∘ N] f ∘ prod M N A;
  prod_pure {A} :
    prod M N A ∘ pure[N] = id;
  prod_fmap_pure {A} :
    prod M N A ∘ fmap[N] (pure[M ∘ N]) = pure[M];
  prod_fmap_join_fmap_prod {A} :
    prod M N A ∘ fmap[N] (join[M] ∘ fmap[M] (prod M N A))
      = join[M] ∘ fmap[M] (prod M N A) ∘ prod M N (M (N A))
}.

#[export]
Program Instance Compose_MonadLaws `{IsMonad_Distributes M N} :
  IsMonad (M ∘ N).
Next Obligation.
  unfold fmap, Compose_Functor.
  unfold join, Compose_Monad.
  rewrite comp_assoc.
  rewrite <- comp_assoc with (f := join[M]).
  rewrite <- comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := fmap[M] (prod M N a)).
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat (rewrite comp_assoc).
  rewrite <- prod_fmap_join_fmap_prod.
  reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite <- join_fmap_pure.
  repeat (rewrite <- comp_assoc).
  repeat (rewrite fmap_comp).
  repeat f_equal.
  pose proof (@prod_fmap_pure M N _ _ _ _ _ a).
  simpl in H3.
  rewrite H3.
  reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite <- prod_pure.
  rewrite <- comp_id_left.
  rewrite <- (@join_pure M _ _ (N a)).
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  f_equal.
  rewrite comp_assoc.
  rewrite comp_assoc.
  f_equal.
  rewrite <- fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  intros.
  unfold comp at 2.
  rewrite comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite fmap_comp.
  pose proof (@prod_fmap_fmap M N _ _ _ _ _ a).
  simpl in H3.
  rewrite <- H3.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)

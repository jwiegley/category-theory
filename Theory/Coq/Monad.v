Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Coq.Category.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

(* This [Monad] class makes the somewhat controversial choice of choosing
   [join] as the fundamental defining operation of a monad, rather than
   [bind]. Other libraries have taken the opposite route. It is my feeling
   that since [bind] combines two operations (namely, [join] and [fmap]), it
   is not as fundamental and thus adds needless complexity to proof
   developments. *)

Class Monad (m : Coq → Coq) `{Applicative m} :=
  join : ∀ {a}, m (m a) ~> m a.

Definition bind `{Monad m} {X Y : Type} (f : (X -> m Y)) : m X -> m Y :=
  join ∘ fmap f.

Notation "'ret'" := pure (only parsing).

Notation "join[ M ]" := (@join M _ _) (at level 9) : morphism_scope.
Notation "join[ M N ]" := (@join (M ∘ N) _ _) (at level 9) : morphism_scope.

Notation "m >>= f" := (bind f m)
  (at level 42, right associativity) : morphism_scope.
Notation "a >> b" := (a >>= fun _ => b)%morphism
  (at level 81, right associativity) : morphism_scope.

Definition kleisli_compose `{Monad m} `(f : a -> m b) `(g : b -> m c) :
  a -> m c := fun x => (f x >>= g)%morphism.

Infix ">=>" := kleisli_compose
  (at level 42, right associativity) : morphism_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : morphism_scope.

Notation "f >=[ m ]=> g" := (@kleisli_compose _ m _ _ f _ g)
  (at level 42, right associativity) : morphism_scope.
Notation "f <=[ m ]=< g" := (@kleisli_compose _ m _ _ g _ f)
  (at level 42, right associativity) : morphism_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%morphism
  (at level 81, right associativity, only parsing) : morphism_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%morphism
  (at level 81, right associativity, only parsing) : morphism_scope.

Class IsMonad (m : Coq → Coq) `{@Monad m H A} `{@IsApplicative m H A IS} := {
  join_fmap_join {a} :
    join ∘ fmap (join[m] (a:=a)) = join ∘ join;
  join_fmap_pure {a} :
    join ∘ fmap (pure (a:=a)) = id;
  join_pure {a} :
    join ∘ pure = id[m a];
  join_fmap_fmap {a b} (f : a -> b) :
    join ∘ fmap (fmap f) = fmap f ∘ join
}.

Corollary join_fmap_join_x `{IsMonad m} {a x} :
  join (fmap (join (a:=a)) x) = join (join x).
Proof.
  replace (join[m] (join[m] x)) with ((join[m] ∘ join[m]) x).
    rewrite <- join_fmap_join.
    reflexivity.
  reflexivity.
Qed.

Corollary join_fmap_pure_x `{IsMonad m} {a x} :
  join (fmap (pure (a:=a)) x) = x.
Proof.
  replace x with (id x) at 2; auto.
  pose proof (@join_fmap_pure m _ _ _ _ _ _ a) as H3.
  eapply equal_f in H3; eauto.
Qed.

Corollary join_pure_x `{IsMonad m} {a} {x : m a} :
  join (pure x) = x.
Proof.
  intros.
  pose proof (@join_pure m _ _ _ _ _ _ a) as H3.
  eapply equal_f in H3; eauto.
Qed.

Corollary join_fmap_fmap_x `{IsMonad m} `{f : a -> b} {x} :
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  intros.
  replace (fmap[m] f (join[m] x)) with ((fmap[m] f ∘ join[m]) x).
    rewrite <- join_fmap_fmap.
    reflexivity.
  reflexivity.
Qed.

#[global]
Ltac monad_laws :=
  repeat (match goal with
    | [ |- context[join (fmap join _)] ] =>
      rewrite join_fmap_join_x || erew @join_fmap_join_x
    end; applicative_laws).

Class Monad_Distributes `{Monad M} `{Applicative N} :=
  prod : ∀ {x}, N (M (N x)) -> M (N x).

Arguments prod M {_ _ _} N {_ _ Monad_Distributes} x _.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having pure), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Class IsMonad_Distributes `{@IsMonad M MF MA MM MIF MIA} `{@IsApplicative N NF NA NIF}
  `{@Monad_Distributes M MF MA MM N NF NA} := {
  prod_fmap_fmap : forall A B (f : A -> B),
    prod M N B ∘ fmap[N] (fmap[M ∘ N] f) = fmap[M ∘ N] f ∘ prod M N A;
  prod_pure : forall A, prod M N A ∘ pure[N] = id;
  prod_fmap_pure : forall A, prod M N A ∘ fmap[N] (pure[M ∘ N]) = pure[M];
  prod_fmap_join_fmap_prod : forall A,
    prod M N A ∘ fmap[N] (join[M] ∘ fmap[M] (prod M N A))
      = join[M] ∘ fmap[M] (prod M N A) ∘ prod M N (M (N A))
}.

#[export]
Instance Compose_Monad `{Monad_Distributes M N} : Monad (M ∘ N) := {
  join := fun A => join[M] ∘ fmap[M] (prod M N A)
}.

(* #[local] Obligation Tactic := program_simpl; monad_laws; intuition eauto; cat. *)
#[local] Obligation Tactic := intros.

(*
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

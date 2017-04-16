(*
(*
Class Monad_Distributes `{M : Monad} `{N : Applicative} := {
  prod : forall A, N (M (N A)) -> M (N A)
}.

Arguments prod M {_} N {_ Monad_Distributes} A _.
*)

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having pure), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Class Monad_DistributesLaws `{Applicative (M ∘ N)} `{Monad_Distributes M N} :=
{
  m_monad_laws :> MonadLaws M;
  n_applicative_laws :> ApplicativeLaws N;

  prod_fmap_fmap : forall A B (f : A -> B),
    prod M N B ∘ fmap[N] (fmap[M ∘ N] f) ≈ fmap[M ∘ N] f ∘ prod M N A;
  prod_pure : forall A, prod M N A ∘ pure[N] ≈ @id (M (N A));
  prod_fmap_pure : forall A, prod M N A ∘ fmap[N] (pure[M ∘ N]) ≈ pure[M];
  prod_fmap_join_fmap_prod : forall A,
    prod M N A ∘ fmap[N] (join[M] ∘ fmap[M] (prod M N A))
      ≈ join[M] ∘ fmap[M] (prod M N A) ∘ prod M N (M (N A))
}.
*)

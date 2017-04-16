Require Import Category.Theory.Monad.

Generalizable All Variables.

(******************************************************************************)
(* Free monad transformer *)
(******************************************************************************)

Inductive FreeF (F : Type -> Type) (A B : Type) :=
  | PureF : A -> FreeF F A B
  | JoinF : F B -> FreeF F A B.

Inductive FreeT (F : Type -> Type) (M : Type -> Type) (A : Type) :=
  | mkFreeT : forall x, (x -> FreeT F M A) -> M (FreeF F A x) -> FreeT F M A.

Import MonadLaws.

Class MonadTransformerLaws `{MonadLaws M} `{FunctorLaws F} := {
  _ : Monad (FreeT F M);
  _ : MonadLaws (FreeT F M)
}.

(******************************************************************************)
(* Algebraic monad transformer *)
(******************************************************************************)

(* Q: Are they traversable? *)

Inductive Alg (c f g : Type -> Type) a :=
  | Const : c a -> Alg c f g a
  | Unit  : f a -> Alg c f g a
  | Prod  : f a * g a -> Alg c f g a
  | Sum   : f a + g a -> Alg c f g a.

(* Theorem: For all algebraic monads, we should be able to automatically
   derive prod from MonadCompose. *)

(* Program Instance Alg_Distributes (c t : Type -> Type) : *)
(*   Monad_Distributes Alg c t. *)

(* Program Instance Alg_DistributesLaws (c t : Type -> Type) : *)
(*   Monad_DistributesLaws Alg c t. *)

(******************************************************************************)
(* Monad transformer of a certain subclass of exponential monads *)
(******************************************************************************)

(* Q: Are they distributive? *)

(* M : Monad *)
(* C : Contravariant *)

(* M t = 1 *)
(* M t = t *)
(* M t = C t -> t *)
(* M t = A t * B t *)
(* M t = A t + t (??) *)

(* Theorem: Does M have a monad instance for any contravariant functor C? *)

(* For monads M and L: T M L t = M (L t) *)

(* M (r -> a) *)
(* r -> M a *)

(* c -> t            =>     c -> L t *)
(* (t -> c) -> t     =>     (L t -> c) -> L t *)

(******************************************************************************)
(* Monad transformers of monads from adjunctions *)
(******************************************************************************)

(* F ⊣ U *)

(* U ∘ F    T L = U ∘ L ∘ F *)

(* ULFULF = id *)
(* ULLF -> ULF : by join of L *)

(* MaybeT (State s) a =    StateT s Maybe a *)
(* s -> s * L t   ‌    =    s -> L (s * t) *)

(* Q : Is MaybeT (State s) a incorrect? *)

(* (ReaderT $ StateT $ ...) *)

(* T (t1 ∘ t2 ∘ t3 (l)) m *)

(* t1 ∘ t2 ∘ t3 ∘ tl (m ) *)
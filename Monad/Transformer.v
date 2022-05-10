Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Functor.Structure.Monoidal.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Transformer.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.
Context {T : (C ⟶ C) -> (C ⟶ C)}.
Context `{@Monad C (T M)}.

Class MonadTransformer := {
  lift {a} : M a ~> T M a;

  lift_return {a} : lift ∘ @ret C M _ a ≈ ret;
  lift_bind {a b} (f : a ~> M b) :
    lift ∘ join ∘ fmap f ≈ join ∘ fmap (lift ∘ f) ∘ lift
}.

End Transformer.

Arguments MonadTransformer {_ _ _} T {_}.

(******************************************************************************
 * Species 1: Identity transformations.
 ******************************************************************************)

Program Definition IdentityT {C : Category} (M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[M];
  fmap := fun _ _ => fmap[M]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition IdentityT_Monad {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @Monad C (@IdentityT C M) := {|
  ret  := fun _ => ret[M];
  join := fun _ => join[M]
|}.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.

#[global] Program Instance IdentityT_MonadTransformer {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @MonadTransformer C M _ (@IdentityT C) (IdentityT_Monad M) := {
  lift := fun _ => id
}.

(*
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
*)

(******************************************************************************
 * Species 2: Constant mapping transformations.
 ******************************************************************************)

Program Definition ConstT {C : Category} (K M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[K];
  fmap := fun _ _ => fmap[K]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition ConstT_Monad {C : Category} (K M : C ⟶ C) `{@Monad C K} :
  @Monad C (@ConstT C K M) := {|
  ret  := fun _ => ret[K];
  join := fun _ => join[K]
|}.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.

(* This is not a valid monad transformer, since there cannot be a morphism
   [M A ~> K A]. *)
Fail Definition ConstT_MonadTransformer {C : Category} (K M : C ⟶ C)
        `{@Monad C K} `{@Monad C M} :
  @MonadTransformer C M _ (@ConstT C K) (ConstT_Monad K M) := {|
  lift := fun _ => _
|}.

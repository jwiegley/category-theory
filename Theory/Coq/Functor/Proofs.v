Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Functor.

Generalizable All Variables.

Definition EndoFunctor := @AFunctor Coq Coq.

(** Every lawful endofunctor on Coq is trivially an instance of
    [Category.Theory.Coq.Functor.Functor]. *)
Program Definition EndoFunctor_Functor (F : Type → Type)
  `(H : EndoFunctor F) : Functor F := {|
  fmap := λ _ _ f, fmap[H] f;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Functor.

Definition IsFunctor `(Functor F) : Type := EndoFunctor F.

Import FunctorNotations.

(* We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide. *)
Program Definition Identity_IsFunctor : IsFunctor Identity_Functor :=
  ToAFunctor Id.

Program Definition arrow_IsFunctor {x} : IsFunctor (arrow_Functor x) := {|
  a_fmap := arrow_Functor x;
|}.
Next Obligation.
  proper.
  extensionality r.
  now rewrite H.
Qed.

(* If [F] and [G] are both functors in Coq, we know that the composition is
   also a valid functor, and so we can map [Compose_Functor] directly to this
   composition. *)
Definition Compose_IsFunctor `(HF : EndoFunctor F) `(HG : EndoFunctor G) :
  IsFunctor (@Compose_Functor _ HF _ HG) :=
  ToAFunctor (Compose (FromAFunctor HF) (FromAFunctor HG)).

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x → y) :
  fmap[F ∘ G]%prg f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.

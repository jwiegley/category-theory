Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Definition EndoFunctor := @AFunctor Coq Coq.

(** Every lawful endofunctor on Coq is trivially an instance of
    [Category.Theory.Coq.Functor.Functor]. *)
Program Definition EndoFunctor_Functor `(H : EndoFunctor F) :
  Coq.Functor.Functor F := {|
  Coq.Functor.fmap := λ _ _ f, fmap[H] f;
  Coq.Functor.fmap_const := λ _ _ x y, fmap[H] (const x) y;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Coq.Functor.Functor.

Definition IsFunctor `(Coq.Functor.Functor F) : Type := EndoFunctor F.

(* We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide. *)
Program Definition Identity_IsFunctor' : IsFunctor Identity_Functor :=
  ToAFunctor Id.

(* If [F] and [G] are both functors in Coq, we know that the composition is
   also a valid functor, and so we can map [Compose_Functor] directly to this
   composition. *)
Definition Compose_IsFunctor `{HF : EndoFunctor F} `{HG : EndoFunctor G} :
  IsFunctor (@Compose_Functor _ HF _ HG) :=
  ToAFunctor (Compose (FromAFunctor HF) (FromAFunctor HG)).

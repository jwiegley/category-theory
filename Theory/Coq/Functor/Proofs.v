Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Functor.

Generalizable All Variables.

(** Lawfulness of the Coq [Functor] instances, via categorical endofunctors *)

(* nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   The bare [Theory.Coq.Functor.Functor] class carries only [fmap], with no
   laws.  A Coq functor is lawful exactly when it satisfies the two functor
   laws: identity [fmap id ≈ id] and composition
   [fmap (g ∘ f) ≈ fmap g ∘ fmap f] (Wikipedia), equivalently when its object
   map and [fmap] form an endofunctor on the category [Coq] in the categorical
   sense, preserving identities [F id = id] and composition [F (g ∘ f) = F g ∘
   F f] (nLab).

   This file packages "lawful" as [EndoFunctor F := AFunctor Coq Coq F] and
   [IsFunctor], and exhibits witnesses that the identity, reader/arrow, and
   composite [Functor] instances are lawful, plus the [compose_fmap]
   characterisation of [fmap] for a composite.  The proofs that rely on
   [functional_extensionality_dep] (e.g. [arrow_IsFunctor]) inherit it from
   the applied/Coq layer; that axiom is expected here, not a regression. *)

Definition EndoFunctor := @AFunctor Coq Coq.

(* Every lawful endofunctor on Coq is trivially an instance of
   [Category.Theory.Coq.Functor.Functor]: forgetting the laws keeps [fmap]. *)
Definition EndoFunctor_Functor (F : Type → Type)
  `(H : EndoFunctor F) : Functor F := {|
  fmap := λ _ _ f, fmap[H] f;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Functor.

Definition IsFunctor `(Functor F) : Type := EndoFunctor F.

Import FunctorNotations.

(* We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide. *)
Definition Identity_IsFunctor : IsFunctor Identity_Functor :=
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

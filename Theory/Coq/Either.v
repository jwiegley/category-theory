Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.

Generalizable All Variables.

(** The Either/sum type [a + b] as bifunctor, and the error monad in [b] *)

(* nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Tagged_union

   FP reading.  [Either a b] (Haskell) / [sum a b], written [a + b] (Coq), is
   the canonical two-case tagged union: a value is either [Left x] carrying an
   [a] or [Right y] carrying a [b], with the tag recording which.  It is the
   standard way to return a result-or-error, [a] conventionally holding the
   error/exception and [b] the success value.  As a monad in its right argument
   (the exception/error monad), [Left] short-circuits and [Right] continues:
   [Left e >>= f = Left e] and [Right x >>= f = f x].

   Categorical reading.  [a + b] is the binary coproduct of [a] and [b], with
   [Left = inl : a → a + b] and [Right = inr : b → a + b] the coproduct
   injections.  Its universal property is the copairing: any [f : a → c] and
   [g : b → c] factor through a unique [[f, g] : a + b → c] (here [either])
   with [[f, g] ∘ inl = f] and [[f, g] ∘ inr = g].  The sum is a bifunctor
   [(+) : C × C → C]; fixing the left summand [E] gives the endofunctor
   [b ↦ E + b] (here [Either_Functor]), which carries the exception monad: the
   unit [η] is [Right] and the multiplication [μ : E + (E + b) → E + b] (here
   [Either_join]) collapses the two copies of [E].  [Maybe a = a + 1] is the
   special case [E = 1].

   Following the other [Theory/Coq] classes, the operations are recorded here
   without their laws; lawfulness is discharged per concrete use. *)

Notation Either := sum (only parsing).   (* [Either a b = a + b], the coproduct *)
Notation Left   := inl (only parsing).    (* [inl : a → a + b], left injection *)
Notation Right  := inr (only parsing).    (* [inr : b → a + b], right injection *)

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

(* The copairing [[f, g] : a + b → c] out of the coproduct: the unique map
   with [[f, g] ∘ inl = f] and [[f, g] ∘ inr = g] (the eliminator for sums). *)
Definition either `(f : a → c) `(g : b → c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

(* The bifunctor's action on the LEFT summand: [f + id : a + b → c + b],
   rewriting [Left l] to [Left (f l)] and leaving [Right] fixed.  Contrast
   [Either_map] below, which acts on the right summand. *)
Definition mapLeft `(f : a → c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

(* The functor [b ↦ E + b] (left summand [E] fixed): [fmap] maps over the
   [Right] value and propagates [Left e] unchanged. *)
Definition Either_map {E X Y} (f : X → Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

(* Applicative [ap]: a [Left] in either the function or the argument
   short-circuits to that [Left] (the function's [Left] taking priority). *)
Definition Either_ap {E X Y} (f : Either E (X → Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

(* The monad multiplication [μ : E + (E + b) → E + b], collapsing the two
   copies of the error summand [E] (an outer or inner [Left] both yield [Left]). *)
Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

(* Monadic [bind] of the exception monad: [Left e] short-circuits (ignoring [f]),
   [Right x'] continues with [f x']. *)
Definition Either_bind {E X Y} (x : Either E X) (f : X → Either E Y) :
  Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => f x'
  end.

(* The endofunctor [b ↦ E + b] on Coq types (left summand [E] fixed). *)
#[export]
Instance Either_Functor {E} : Functor (Either E) := {
  fmap := @Either_map E
}.

(* Applicative structure; [pure = Right] injects a success value. *)
#[export]
Instance Either_Applicative {E} : Applicative (Either E) := {
  pure := @Right E;
  ap := @Either_ap E;
}.

(* The exception monad in the right argument; the unit [η = ret] is [Right]. *)
#[export]
Instance Either_Monad {E} : Monad (Either E) := {
  ret := @Right E;
  bind := @Either_bind E;
}.

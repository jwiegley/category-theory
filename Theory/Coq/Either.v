Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.

Generalizable All Variables.

Notation Either := sum (only parsing).
Notation Left   := inl (only parsing).
Notation Right  := inr (only parsing).

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

Definition either `(f : a → c) `(g : b → c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition mapLeft `(f : a → c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

Definition Either_map {E X Y} (f : X → Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

Definition Either_ap {E X Y} (f : Either E (X → Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

Definition Either_bind {E X Y} (x : Either E X) (f : X → Either E Y) :
  Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => f x'
  end.

#[export]
Instance Either_Functor {E} : Functor (Either E) := {
  fmap := @Either_map E
}.

#[export]
Instance Either_Applicative {E} : Applicative (Either E) := {
  pure := @Right E;
  ap := @Either_ap E;
}.

#[export]
Instance Either_Monad {E} : Monad (Either E) := {
  bind := @Either_bind E
}.

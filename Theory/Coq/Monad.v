Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

Class Monad `{Applicative F} :=
  bind : ∀ {x y}, F x → (x → F y) → F y.

Arguments Monad F {_ _}.

Definition join `{Monad F} {x} (m : F (F x)) : F x := bind m id.

Definition kleisli_compose `{Monad m} `(f : a → m b) `(g : b → m c) :
  a → m c := λ x, bind (f x) g.

Module MonadNotations.

Include ApplicativeNotations.

Notation "'ret'" := pure (only parsing).

Notation "bind[ M ]" := (@bind M _ _ _ _ _) (at level 9).
Notation "bind[ M N ]" := (@bind (M ∘ N) _ _ _ _ _) (at level 9).

Notation "join[ M ]" := (@join M _ _ _ _) (at level 9).
Notation "join[ M N ]" := (@join (M ∘ N) _ _ _ _) (at level 9).

Notation "m >>= f" := (bind m f)
  (at level 42, right associativity).
Notation "m >>=[ M ] f" := (@bind M _ _ _ _ _ m f)
  (at level 42, right associativity, only parsing).
Notation "f =<< m" := (bind m f)
  (at level 42, right associativity).
Notation "f =<<[ M ] m" := (@bind M _ _ _ _ _ m f)
  (at level 42, right associativity, only parsing).
Notation "a >> b" := (a >>= λ _, b)
  (at level 81, right associativity).
Notation "b << a" := (a >>= λ _, b)
  (at level 81, right associativity).

Infix ">=>" := kleisli_compose
  (at level 42, right associativity).
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity).

Notation "f >=[ m ]=> g" := (@kleisli_compose _ m _ _ f _ g)
  (at level 42, right associativity).
Notation "f <=[ m ]=< g" := (@kleisli_compose _ m _ _ g _ f)
  (at level 42, right associativity).

Notation "x <- A ; B" := (A >>= (λ x, B))
  (at level 81, right associativity, only parsing).

Notation "A ;; B" := (A >>= (λ _, B))
  (at level 81, right associativity, only parsing).

End MonadNotations.

Class Monad_Distributes `{Monad M} `{Applicative N} :=
  prod : ∀ {x}, N (M (N x)) → M (N x).

Arguments prod M {_ _ _} N {_ _ Monad_Distributes x} _.

Import MonadNotations.

#[export]
Instance Compose_Monad `{Monad_Distributes M N} : Monad (M ∘ N) := {
  (* join := λ x, join[M] ∘ fmap[M] (prod M N x) *)
  bind := λ x y m f, m >>=[M] (prod M N ∘ fmap[N] f)
}.

Definition when `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if b then x else ret tt.

Definition unless `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if negb b then x else ret tt.

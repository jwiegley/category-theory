Require Import Category.Lib.
Require Export Category.Theory.Coq.Applicative.

Generalizable All Variables.

Class Monad@{d c} {F : Type@{d} → Type@{c}} `{Applicative F} :=
  bind : ∀ {x y : Type@{d}}, F x → (x → F y) → F y.

Arguments Monad F {_ _}.

Definition join `{Monad F} {x} (m : F (F x)) : F x := bind m id.

Definition kleisli_compose `{Monad m} `(f : a → m b) `(g : b → m c) :
  a → m c := λ x, bind (f x) g.

Definition when `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if b then x else pure tt.

Definition unless `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if negb b then x else pure tt.

Module MonadNotations.

Export ApplicativeNotations.

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

#[export]
Instance Identity_Monad : Monad id | 9 := {
  bind := λ _ _ m f, f m;
}.

#[export]
Instance arrow_Monad x : Monad (arrow x) := {
  bind := λ _ _ m f r, f (m r) r
}.

Class Monad_Distributes `{Monad M} `{Monad N} :=
  mprod : ∀ {x}, N (M (N x)) → M (N x).

Arguments Monad_Distributes M {_ _ _} N {_ _ _}.
Arguments mprod M {_ _ _} N {_ _ _ _ x} _.

Import MonadNotations.

#[export]
Instance Compose_Monad `{Monad_Distributes M N} : Monad (M ∘ N) := {
  (* join := λ x, join[M] ∘ fmap[M] (mprod M N x) *)
  bind := λ x y m f, m >>=[M] (mprod M N ∘ fmap[N] f)
}.

#[export]
Instance Yoneda_Monad `{Monad F} : Monad (Yoneda F) := {
  bind := λ _ _ m f, λ r k, join (m _ (λ h, f h _ k))
}.

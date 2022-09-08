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
  (at level 42, right associativity, format "m >>=[ M ] f").
Notation "a >> b" := (a >>= λ _, b)
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

Fixpoint mapM `{Applicative m} {A B : Type} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B : Type} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Applicative m} {A B : Type} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
  end.

Definition forM_ `{Applicative m} {A B : Type} (l : list A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A B : Type}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A B : Type}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM f s l.

Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

Definition concatMapM `{Applicative m} {A B : Type}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  fmap flatten (mapM f l).

Fixpoint replicateM_ `{Monad m} (n : nat) (x : m unit) : m unit :=
  match n with
  | O => pure tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM `{Monad m} {A : Type} (P : A -> A -> m bool)
  (z : A) (l : list A) : m (list A) :=
  match l with
  | nil => pure (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else pure (cons z (cons x xs))
  end.

Arguments insertM {m H _ _ A} P z l : simpl never.

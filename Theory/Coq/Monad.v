Require Import Category.Lib.
Require Export Category.Theory.Coq.Applicative.

Generalizable All Variables.

Class Monad@{d c} {F : Type@{d} → Type@{c}} := {
  ret : ∀ {x : Type@{d}}, x → F x;
  bind : ∀ {x y : Type@{d}}, F x → (x → F y) → F y;
}.

Arguments Monad : clear implicits.

Section Monad.

Universes d c.
Context {F : Type@{d} -> Type@{c}}.
Context `{Monad F}.

Definition join {x} (m : F (F x)) : F x := bind m id.

Definition kleisli_compose {x y z : Type@{d}} `(f : x → F y) `(g : y → F z) :
  x → F z := λ x, bind (f x) g.

Definition liftM {x y : Type@{d}} (f : x → y) : F x → F y :=
  λ x, bind x (λ x, ret (f x)).

Definition liftM2 {x y z : Type@{d}} (f : x → y → z) : F x → F y → F z :=
  Eval cbv beta iota zeta delta [ liftM ] in
    λ x y, bind x (λ x, liftM (f x) y).

Definition liftM3 {x y z w : Type@{d}} (f : x → y → z → w) :
  F x → F y → F z → F w :=
  Eval cbv beta iota zeta delta [ liftM2 ] in
    λ x y z, bind x (λ x, liftM2 (f x) y z).

Definition apM {x y : Type@{d}} (fM : F (x → y)) (aM : F x) : F y :=
  bind fM (λ f, liftM f aM).

Definition when (b : bool) (x : F unit) : F unit :=
  if b then x else ret tt.

Definition unless (b : bool) (x : F unit) : F unit :=
  if negb b then x else ret tt.

End Monad.

Module MonadNotations.

Export ApplicativeNotations.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Bind Scope monad_scope with Monad.

Notation "ret[ M ]" := (@ret M _ _) (at level 9) : monad_scope.
Notation "ret[ M N ]" := (@ret (M ∘ N) _ _) (at level 9) : monad_scope.

Notation "bind[ M ]" := (@bind M _ _ _) (at level 9) : monad_scope.
Notation "bind[ M N ]" := (@bind (M ∘ N) _ _ _) (at level 9) : monad_scope.

Notation "join[ M ]" := (@join M _ _ _ _) (at level 9) : monad_scope.
Notation "join[ M N ]" := (@join (M ∘ N) _ _) (at level 9) : monad_scope.

Notation "m >>= f" := (bind m f)
  (at level 42, right associativity) : monad_scope.
Notation "m >>=[ M ] f" := (@bind M _ _ _ m f)
  (at level 42, right associativity, only parsing) : monad_scope.
Notation "f =<< m" := (bind m f)
  (at level 42, right associativity) : monad_scope.
Notation "f =<<[ M ] m" := (@bind M _ _ _ m f)
  (at level 42, right associativity, only parsing) : monad_scope.
Notation "a >> b" := (a >>= λ _, b)%monad
  (at level 81, right associativity) : monad_scope.
Notation "b << a" := (a >>= λ _, b)%monad
  (at level 81, right associativity) : monad_scope.

Infix ">=>" := kleisli_compose
  (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ M ]=> g" := (@kleisli_compose M _ _ _ _ _ f _ g)
  (at level 42, right associativity) : monad_scope.
Notation "f <=[ M ]=< g" := (@kleisli_compose M _ _ _ _ _ g _ f)
  (at level 42, right associativity) : monad_scope.

Notation "x <- A ;; B" := (A >>= (λ x, B))%monad
  (at level 81, A at next level, right associativity) : monad_scope.

Notation "' pat <- A ;; B" := (A >>= (λ x, match x with pat => B end))%monad
  (at level 81, pat pattern, A at next level, right associativity) : monad_scope.

Notation "'let*' pat ':=' A 'in' B" := (@bind _ _ _ _ A (λ pat, B))
  (at level 81, pat as pattern, A at next level, right associativity) : monad_scope.

Notation "A ;; B" := (A >>= (λ _, B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

End MonadNotations.

#[export]
Instance Identity_Monad : Monad id | 9 := {
  ret := λ _ x, x;
  bind := λ _ _ m f, f m;
}.

#[export]
Instance arrow_Monad x : Monad (arrow x) := {
  ret := λ _ x _, x;
  bind := λ _ _ m f r, f (m r) r;
}.

Class Monad_Distributes (M N : Type → Type) :=
  mprod : ∀ {x}, N (M (N x)) → M (N x).

Arguments mprod M N {_ x} _.

Import MonadNotations.

Open Scope monad_scope.

#[export]
Instance Compose_Monad `{Monad M} `{Applicative N}
  `{@Monad_Distributes M N} : Monad (M ∘ N) := {
  ret := λ _ x, ret[M] (pure[N] x);
  bind := λ _ _ m f, m >>=[M] (mprod M N ∘ ap (pure f));
}.

#[export]
Instance Yoneda_Monad `{Monad F} : Monad (Yoneda F) := {
  ret := λ _ x, λ r k, ret (k x);
  bind := λ _ _ m f, λ r k, join (m _ (λ h, f h _ k));
}.

Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Monad F}.

#[export]  Instance Functor_Monad@{} : Functor F | 9 := {
  fmap := @liftM _ _
}.

#[export] Instance Applicative_Monad@{} : Applicative F | 9 := {
  pure := @ret _ _;
  ap := @apM _ _;
}.

End Instances.

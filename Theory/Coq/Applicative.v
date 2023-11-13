Require Import Category.Lib.
Require Export Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

Class Applicative@{d c} {F : Type@{d} → Type@{c}} := {
  pure {x : Type@{d}} : x → F x;
  ap {x y : Type @{d}} : F (x → y) → F x → F y;
}.

Arguments Applicative : clear implicits.

Definition liftA2 `{Applicative F} {x y z}
  (f : x → y → z) (a : F x) (b : F y) : F z :=
  ap (ap (pure f) a) b.

Class Alternative@{d c} {F : Type@{d} → Type@{c}} := {
  empty  {x : Type@{d}} : F x;
  choose {x : Type@{d}} : F x → F x → F x;
}.

Arguments Alternative : clear implicits.

Module ApplicativeNotations.

Export FunctorNotations.

Notation "pure[ M ]" := (@pure M _ _)
  (at level 0, format "pure[ M ]").
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _)
  (at level 0, format "pure[ M  N ]").

Notation "ap[ M ]" := (@ap M _ _ _)
  (at level 0, format "ap[ M ]").
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _)
  (at level 0, format "ap[ M  N ]").
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _)
  (at level 0, format "ap[ M  N  O ]").

Infix "<*>" := ap (at level 29, left associativity).
Infix "<*[ M ]>" := (@ap M _ _ _)
  (at level 29, left associativity, only parsing).

Notation "x <**> f" := (ap f x)
  (at level 29, left associativity, only parsing).
Notation "x <**[ M ]> f" := (@ap M _ _ _ f x)
  (at level 29, left associativity, only parsing).

Infix "*>" := (liftA2 (const id)) (at level 29, left associativity).
Infix "<*" := (liftA2 const) (at level 29, left associativity).

Notation "f <|> g" := (choose f g) (at level 29, left associativity).

End ApplicativeNotations.

Import ApplicativeNotations.

#[export]
Instance Identity_Applicative : Applicative id | 9 := {
  pure := λ _, id;
  ap := λ _ _ f x, f x;
}.

#[export]
Instance arrow_Applicative x : Applicative (arrow x) := {
  pure := λ _ x _, x;
  ap := λ _ _ f x r, f r (x r);
}.

#[export]
Instance Const_Applicative `{Monoid x} : Applicative (Const x) := {
  pure := λ _ _, mkConst mempty;
  ap := λ _ _ '(mkConst x) '(mkConst y), mkConst (x ⊗ y);
}.

#[export]
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ ap[F] (pure ap[G])
}.

(* jww (2022-09-07): This needs work *)
#[export]
Instance Compose_Alternative `{Alternative F} `{Alternative G} :
  Alternative (F ∘ G) := {
  empty  := λ x, @empty F _ (G x);
  choose := λ x, @choose F _ (G x);
}.

#[export]
Instance Yoneda_Applicative `{Applicative F} : Applicative (Yoneda F) := {
  pure := λ _ x, λ r k, pure (k x);
  ap := λ _ _ f x, λ r k, f _ (λ h, k ∘ h) <*> x _ id
}.

Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Applicative F}.

#[export]  Instance Functor_Applicative@{} : Functor F | 9 := {
  fmap := λ _ _ f x, ap (pure f) x
}.

End Instances.

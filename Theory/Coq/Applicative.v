Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.

Generalizable All Variables.

Class Applicative `{Functor F} := {
  pure {a} : a → F a;
  ap {a b} : F (a → b) → F a → F b;
}.

Arguments Applicative F {_}.

Definition liftA2 `{Applicative F} {a b c}
  (f : a → b → c) (x : F a) (y : F b) : F c :=
  ap (fmap f x) y.

Class Alternative `{Applicative F} := {
  empty  {x} : F x;
  choose {x} : F x → F x → F x;
  some   {x} : F x → list (F x);
  many   {x} : F x → list (F x);
}.

Arguments Alternative F {_ _}.

Module ApplicativeNotations.

Include FunctorNotations.

Notation "pure[ M ]" := (@pure M _ _)
  (at level 9, format "pure[ M ]").
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _)
  (at level 9, format "pure[ M  N ]").

Notation "ap[ M ]" := (@ap M _ _ _)
  (at level 9, format "ap[ M ]").
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _)
  (at level 9, format "ap[ M  N ]").
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _)
  (at level 9, format "ap[ M  N  O ]").

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
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ fmap ap
}.

Corollary compose_ap  `{Applicative F} `{Applicative G} {x y} :
  ap[F ∘ G] = ap[F] ∘ fmap[F] (@ap G _ _ x y).
Proof. reflexivity. Qed.

Corollary ap_comp `{Applicative F} `{f : a → F (b → c)} {x} :
  (ap[F] ∘ f) x = ap (f x).
Proof. reflexivity. Qed.

Corollary pure_comp `{Applicative F} `{f : a → b} {x} :
  (pure[F] ∘ f) x = pure (f x).
Proof. reflexivity. Qed.

(* jww (2022-09-07): This needs work *)
#[export]
Instance Compose_Alternative `{Alternative F} `{Alternative G} :
  Alternative (F ∘ G) := {
  empty  := λ x, @empty F _ _ _ (G x);
  choose := λ x, @choose F _ _ _ (G x);
  some   := λ x, @some F _ _ _ (G x);
  many   := λ x, @many F _ _ _ (G x);
}.

(*
Require Import Coq.Lists.List.

Import ListNotations.

#[export]
Program Instance list_Alternative : Alternative list := {
    empty := fun _ => [];
    choose := app;
    some := app;
    many := app;
}.
*)

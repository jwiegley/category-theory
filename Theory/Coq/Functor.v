Require Import Category.Lib.

Generalizable All Variables.

Class Functor@{d c} {F : Type@{d} → Type@{c}} := {
  fmap : ∀ {x y : Type@{d}}, (x → y) → F x → F y;
}.

Arguments Functor : clear implicits.

Coercion fmap : Functor >-> Funclass.

Class Contravariant@{d c} {F : Type@{d} → Type@{c}} :=
  contramap : ∀ {x y : Type@{d}}, (x → y) → F y → F x.

Arguments Contravariant : clear implicits.

Coercion contramap : Contravariant >-> Funclass.

Definition coerce `{Functor F} `{Contravariant F} {x y} : F x → F y :=
  fmap (False_rect _) ∘ contramap (False_rect _).

Module FunctorNotations.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing).
Infix "<$[ M ]>" := (@fmap M _ _ _)
  (at level 29, left associativity, only parsing).
Notation "x <$ m" := (fmap (const x) m)
  (at level 29, left associativity, only parsing).
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing).

Notation "fmap[ M ]" := (@fmap M _ _ _)
  (at level 9, format "fmap[ M ]").
Notation "fmap[ M N ]" := (@fmap (λ X, M (N X)) _ _ _)
  (at level 9, format "fmap[ M  N ]").
Notation "fmap[ M N O ]" := (@fmap (λ X, M (N (O X))) _ _ _)
  (at level 9, format "fmap[ M  N  O ]").

Infix ">$<" := contramap (at level 29, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 29, left associativity, only parsing).

Notation "contramap[ M ]" := (@contramap M _ _ _)
  (at level 9, format "contramap[ M ]").
Notation "contramap[ M N ]" := (@contramap (λ X, M (N X)) _ _ _)
  (at level 9, format "contramap[ M  N ]").
Notation "contramap[ M N O ]" := (@contramap (λ X, M (N (O X))) _ _ _)
  (at level 9, format "contramap[ M  N  O ]").

End FunctorNotations.

#[export]
Instance Identity_Functor : Functor id | 9 := {|
  fmap := λ _ _, id;
|}.

Inductive Const (c a : Type) := | mkConst : c → Const.

Arguments mkConst {c a} _.

#[export]
Instance Const_Functor {x : Type} : Functor (Const x) := {|
  fmap := λ _ _ _ '(mkConst x), mkConst x;
|}.

Import FunctorNotations.

(* Coq endofunctors always compose to form another endofunctor. *)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {|
  fmap := λ _ _, fmap[F] ∘ fmap[G];
|}.

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x → y) :
  fmap[F ∘ G] f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.

#[export]
Instance arrow_Functor x : Functor (arrow x) := {|
  fmap := λ _ _ f x r, f (x r);
|}.

Definition Yoneda@{d c u} (F : Type@{d} → Type@{c}) (x : Type@{u}) :=
  ∀ r : Type@{u}, (x → r) → F r.

#[export]
Instance Yoneda_Functor (F : Type → Type) : Functor (Yoneda F) := {
  fmap := λ _ _ g k _ h, k _ (h ∘ g)
}.

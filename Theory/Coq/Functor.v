Require Import Category.Lib.

Generalizable All Variables.

Class Functor (F : Type → Type) := {
  fmap : ∀ {x y}, (x → y) → F x → F y;
  (* This has the type of [fmap . const], but is made a member here to allow
     for more efficient implementations. *)
  fmap_const : ∀ {x y}, x → F y → F x;
}.

Coercion fmap : Functor >-> Funclass.

Module FunctorNotations.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing).
Infix "<$[ M ]>" := (@fmap M _ _ _)
  (at level 29, left associativity, only parsing).
Notation "x <$ m" := (fmap_const x m)
  (at level 29, left associativity, only parsing).
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing).

Notation "fmap[ M ]" := (@fmap M _ _ _)
  (at level 9, format "fmap[ M ]").
Notation "fmap[ M N ]" := (@fmap (λ X, M (N X)) _ _ _)
  (at level 9, format "fmap[ M  N ]").
Notation "fmap[ M N O ]" := (@fmap (λ X, M (N (O X))) _ _ _)
  (at level 9, format "fmap[ M  N  O ]").

End FunctorNotations.

#[export]
Instance Identity_Functor : Functor id | 9 := {|
  fmap := λ _ _, id;
  fmap_const := λ _ _, const;
|}.

Import FunctorNotations.

(* Coq endofunctors always compose to form another endofunctor. *)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {|
  fmap := λ _ _, fmap[F] ∘ fmap[G];
  fmap_const := λ _ _, fmap[F] ∘ fmap_const;
|}.

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x → y) :
  fmap[F ∘ G] f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.

#[export]
Instance prod_Functor {x} : Functor (prod x) := {|
  fmap := λ _ _ f '(x, y), (x, f y);
  fmap_const := λ _ _ y '(x, _), (x, y);
|}.

#[export]
Instance arrow_Functor {x} : Functor (arrow x) := {|
  fmap := λ _ _ f x r, f (x r);
  fmap_const := λ _ _ y _ _, y;
|}.

#[export]
Instance option_Functor : Functor option := {|
  fmap := λ _ _ f, option_map f;
  fmap_const := λ _ _ y m,
    match m with
    | Some _ => Some y
    | None   => None
    end;
|}.

Require Import Coq.Lists.List.

#[export]
Instance list_Functor : Functor list := {|
  fmap := λ _ _ f, List.map f;
  fmap_const := λ _ _ y, List.map (const y);
|}.

Require Import Category.Lib.
Require Export Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The Applicative type class (pure/ap), with its categorical reading *)

(* nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   FP reading.  An applicative functor (in the Haskell sense) is a type
   constructor [F : Type → Type] equipped with [pure : x → F x], injecting a
   plain value, and [ap : F (x → y) → F x → F y] (Haskell's [<*>]), applying a
   wrapped function to a wrapped argument.  It is lawful when it satisfies the
   four applicative laws:
     identity      [pure id <*> v ≈ v];
     composition   [pure (∘) <*> u <*> v <*> w ≈ u <*> (v <*> w)];
     homomorphism  [pure f <*> pure x ≈ pure (f x)];
     interchange   [u <*> pure y ≈ pure (λ g, g y) <*> u].
   Every applicative is a functor, with [fmap f x = pure f <*> x] (see
   [Functor_Applicative] below).

   Categorical reading.  This is exactly a lax monoidal endofunctor (with
   tensorial strength) on the category of Coq types, taken with its cartesian
   monoidal structure (product [×], unit [unit]).  The two structure morphisms
   of a lax monoidal functor [F] are the unit [η : 1 → F 1] and the laxator
   (a natural transformation) [μ : F x ⊗ F y → F (x ⊗ y)].  Here [η] is
   recovered from [pure] (as [pure tt]) and [μ] from [ap] (as
   [λ '(u, v), liftA2 pair u v]); conversely [pure x = fmap (const x) (η tt)]
   and [ap f x = fmap (λ '(g, a), g a) (μ (f, x))].  The four applicative laws
   above are precisely the lax-monoidal coherence axioms (associativity of [μ]
   and the two unit constraints involving [η]).

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Applicative] carries only [pure] and [ap], and lawfulness
   is an obligation discharged for each concrete instance. *)

Class Applicative@{d c} {F : Type@{d} → Type@{c}} := {
  pure {x : Type@{d}} : x → F x;                       (* unit: injects a value (lax-monoidal η) *)
  ap {x y : Type @{d}} : F (x → y) → F x → F y;         (* application derived from the laxator μ *)
}.

Arguments Applicative : clear implicits.

(* [liftA2] maps a binary function over two applicative arguments,
   [liftA2 f a b = pure f <*> a <*> b].  Categorically it is the curried form
   of the laxator [μ : F x ⊗ F y → F (x ⊗ y)] postcomposed with [fmap]: it is
   interdefinable with [ap], and [μ = liftA2 pair]. *)
Definition liftA2 `{Applicative F} {x y z}
  (f : x → y → z) (a : F x) (b : F y) : F z :=
  ap (ap (pure f) a) b.

(* nLab: https://ncatlab.org/nlab/show/distributive+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   The Alternative type class adds a monoid structure on each [F x] that is
   compatible with the applicative structure: [empty] is the neutral element
   and [choose] (Haskell's [<|>]) the binary operation.  As with the other
   classes here the monoid laws are NOT recorded as fields. *)
Class Alternative@{d c} {F : Type@{d} → Type@{c}} := {
  empty  {x : Type@{d}} : F x;                         (* neutral element of the [choose] monoid *)
  choose {x : Type@{d}} : F x → F x → F x;              (* binary [<|>] operation *)
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

(* The identity applicative [Id]: [pure = id] and [ap f x = f x].  As a lax
   monoidal functor it is the (strict) monoidal identity functor. *)
#[export]
Instance Identity_Applicative : Applicative id | 9 := {
  pure := λ _, id;
  ap := λ _ _ f x, f x;
}.

(* The reader / function applicative [λ a, x → a] (Haskell's [(->) x]):
   [pure] is the constant function and [ap] threads the shared environment
   [r] through both the function and the argument. *)
#[export]
Instance arrow_Applicative x : Applicative (arrow x) := {
  pure := λ _ x _, x;
  ap := λ _ _ f x r, f r (x r);
}.

(* The constant applicative [Const x] over a [Monoid x]: [pure] discards its
   value and returns [mempty]; [ap] combines the two accumulators with [⊗].
   This is the canonical example of a lax monoidal functor that is not a
   monad -- it is the lax monoidal functor [Types → Types] picking out the
   monoid [x], with [η = mempty] and [μ = (⊗)]. *)
#[export]
Instance Const_Applicative `{Monoid x} : Applicative (Const x) := {
  pure := λ _ _, mkConst mempty;
  ap := λ _ _ '(mkConst x) '(mkConst y), mkConst (x ⊗ y);
}.

(* Applicatives are closed under composition: [F ∘ G] is again applicative
   (unlike monads).  [pure] is [pure[F] ∘ pure[G]], and [ap] uses [F]'s [ap]
   twice, first lifting [G]'s [ap] under [F] (via [pure ap[G]]) and then
   applying it.  Categorically this is the composite of the two laxators. *)
#[export]
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ ap[F] (pure ap[G])
}.

(* This is the standard Haskell-style [Alternative (Compose f g)]: it lifts F's
   Alternative structure pointwise over G, and does NOT use G's Alternative
   structure at all -- there is no canonical way to combine an [F (G x)] and
   [F (G x)] using G's choose without committing to a specific shape. *)
#[export]
Instance Compose_Alternative `{Alternative F} `{Alternative G} :
  Alternative (F ∘ G) := {
  empty  := λ x, @empty F _ (G x);
  choose := λ x, @choose F _ (G x);
}.

(* The Yoneda / co-Yoneda encoding of an applicative [F] is again applicative:
   the continuation-passing presentation [Yoneda F x = ∀ r, (x → r) → F r]
   transports [pure] and [ap] through the natural isomorphism [Yoneda F ≅ F]. *)
#[export]
Instance Yoneda_Applicative `{Applicative F} : Applicative (Yoneda F) := {
  pure := λ _ x, λ r k, pure (k x);
  ap := λ _ _ f x, λ r k, f _ (λ h, k ∘ h) <*> x _ id
}.

(* Every applicative is a functor, recovering [fmap] from [pure] and [ap] by
   [fmap f x = pure f <*> x] (the standard [Applicative ⇒ Functor] derivation).
   Categorically: a lax monoidal functor is in particular a functor. *)
Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Applicative F}.

#[export]  Instance Functor_Applicative@{} : Functor F | 9 := {
  fmap := λ _ _ f x, ap (pure f) x
}.

End Instances.

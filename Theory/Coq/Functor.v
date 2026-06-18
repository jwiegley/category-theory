Require Import Category.Lib.

Generalizable All Variables.

(** The Functor type class (fmap), with its categorical reading *)

(* nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   FP reading.  A functor (in the Haskell sense) is a type constructor
   [F : Type → Type] equipped with [fmap : (x → y) → F x → F y], lifting a
   function on elements to a function on the wrapped type.  It is lawful when
   it satisfies the two functor laws: identity [fmap id ≈ id] and composition
   [fmap (g ∘ f) ≈ fmap g ∘ fmap f].

   Categorical reading.  This is exactly an endofunctor on the category of
   Coq types (the "category of types", Haskell's Hask).  The object map is
   the type constructor [F] itself, and the morphism (hom) map is [fmap],
   sending a morphism [f : x → y] to [fmap f : F x → F y].  The two functor
   laws are precisely preservation of identities [F id = id] and of
   composition [F (g ∘ f) = F g ∘ F f].

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Functor] carries only the [fmap] operation, and
   lawfulness is an obligation discharged for each concrete instance. *)

Class Functor@{d c} {F : Type@{d} → Type@{c}} := {
  fmap : ∀ {x y : Type@{d}}, (x → y) → F x → F y;  (* morphism map of the endofunctor F *)
}.

Arguments Functor : clear implicits.

(* The coercion lets a [Functor F] be applied directly, as in [Fobj f],
   reading off its action [fmap] on morphisms. *)
Coercion fmap : Functor >-> Funclass.

(* nLab: https://ncatlab.org/nlab/show/contravariant+functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance

   FP reading.  A contravariant functor equips [F : Type → Type] with
   [contramap : (x → y) → F y → F x], which reverses the direction of the
   mapped function.  The laws are again identity [contramap id ≈ id] and
   composition [contramap (g ∘ f) ≈ contramap f ∘ contramap g].

   Categorical reading.  This is an endofunctor [F : Types^op → Types],
   equivalently a functor out of the opposite category; [contramap f] is the
   image of [f] under that functor.  Presheaves are the paradigmatic
   example. *)
Class Contravariant@{d c} {F : Type@{d} → Type@{c}} :=
  contramap : ∀ {x y : Type@{d}}, (x → y) → F y → F x.  (* hom map reversing arrows *)

Arguments Contravariant : clear implicits.

Coercion contramap : Contravariant >-> Funclass.

(* If the same [F] is both covariant and contravariant, it must ignore its
   argument (it is a constant functor up to iso), so any [F x] can be moved to
   any [F y].  We route through [F False]: [contramap] with the unique map out
   of the initial type [False → x] sends [F x] to [F False], and [fmap] with
   [False → y] sends [F False] to [F y].  [False_rect : False → z] is the
   unique morphism from the initial object. *)
Definition coerce `{Functor F} `{Contravariant F} {x y} : F x → F y :=
  fmap (False_rect _) ∘ contramap (False_rect _).

(* Haskell-style infix notation for [fmap]/[contramap].  [<$>] is Haskell's
   infix [fmap]; [<$] replaces all contents with a constant; [fmap[M N]]
   selects [fmap] for the composite functor [λ X, M (N X)]. *)
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
  (at level 0, format "fmap[ M ]").
Notation "fmap[ M N ]" := (@fmap (λ X, M (N X)) _ _ _)
  (at level 0, format "fmap[ M  N ]").
Notation "fmap[ M N O ]" := (@fmap (λ X, M (N (O X))) _ _ _)
  (at level 0, format "fmap[ M  N  O ]").

Infix ">$<" := contramap (at level 29, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 29, left associativity, only parsing).

Notation "contramap[ M ]" := (@contramap M _ _ _)
  (at level 0, format "contramap[ M ]").
Notation "contramap[ M N ]" := (@contramap (λ X, M (N X)) _ _ _)
  (at level 0, format "contramap[ M  N ]").
Notation "contramap[ M N O ]" := (@contramap (λ X, M (N (O X))) _ _ _)
  (at level 0, format "contramap[ M  N  O ]").

End FunctorNotations.

(* The identity endofunctor [Id : Types → Types]; [fmap = id]. *)
#[export]
Instance Identity_Functor : Functor id | 9 := {
  fmap := λ _ _, id;
}.

(* The reader / function functor [λ a, x → a] (Haskell's [(->) x]).  Mapping
   post-composes, [fmap f g = f ∘ g]; this is the covariant hom functor
   [Hom(x, −)]. *)
#[export]
Instance arrow_Functor x : Functor (arrow x) := {
  fmap := λ _ _ f x r, f (x r);
}.

(* The constant functor [Const c], which sends every type to [c] and every
   morphism to the identity on [c]; [fmap] discards its function argument. *)
Inductive Const (c a : Type) := | mkConst : c → Const.

Arguments mkConst {c a} _.

#[export]
Instance Const_Functor {x : Type} : Functor (Const x) := {
  fmap := λ _ _ _ '(mkConst x), mkConst x;
}.

Import FunctorNotations.

(* Endofunctors are closed under composition: [G ∘ F] is again an endofunctor,
   with [fmap[G ∘ F] = fmap[G] ∘ fmap[F]].  (Here [F ∘ G] is function
   composition of the two type constructors.) *)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {
  fmap := λ _ _, fmap[F] ∘ fmap[G];
}.

(* nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   The (covariant, "co-Yoneda") presentation of [F] at [x]: the type of
   natural transformations [Hom(x, −) ⇒ F].  By the Yoneda lemma this type is
   naturally isomorphic to [F x], a continuation-passing encoding of [F]. *)
Definition Yoneda@{d c u} (F : Type@{d} → Type@{c}) (x : Type@{u}) :=
  ∀ r : Type@{u}, (x → r) → F r.

(* [Yoneda F] is itself a functor in [x], independently of whether [F] is one:
   [fmap g] precomposes the bundled continuation with [g]. *)
#[export]
Instance Yoneda_Functor (F : Type → Type) : Functor (Yoneda F) := {
  fmap := λ _ _ g k _ h, k _ (h ∘ g)
}.

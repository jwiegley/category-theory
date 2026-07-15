Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Kleisli.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(** * The co-Kleisli category of a comonad *)

(* nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   The co-Kleisli category C_W of a comonad (W, extract, duplicate) =
   (W, ε, δ) on C has the same objects as C, while a co-Kleisli morphism
   x ⇸ y is an ordinary C-morphism W x ~> y.  The identity on x is the
   counit extract (ε_x), and the co-Kleisli composite of f : W y ~> z after
   g : W x ~> y is

       f ∘_W g  ≈  f ∘ fmap[W] g ∘ duplicate    (f ∘ W g ∘ δ),

   which is exactly f composed onto the extension of g (f ∘ extend g).

   Since [Comonad C W] is by definition [@Monad (C^op) (W^op)], the
   co-Kleisli category is obtained here as the opposite of the Kleisli
   category of that opposite monad, rather than by re-proving the category
   laws:

       CoKleisli := (Kleisli (C^op) (W^op))^op

   Because duality is built into this library so that C^op^op = C holds by
   reflexivity, the covariant components of this construction are
   definitionally the expected ones: the hom-sets are literally
   W x ~{C}~> y ([cokleisli_hom], which holds by reflexivity), the identity
   is literally [extract] ([cokleisli_id]), and the categorical composite
   [cokleisli_compose f g] (f after g) is literally f ∘ extend g.  The
   fish operators name this the other way round: [f =>= g] runs the LEFT
   operand first (Monad/Kleisli.v convention), so [f =>= g ≈ g ∘ extend f]
   ([cokleisli_compose_extend]).  The category laws, inherited from
   Monad/Kleisli.v by duality and re-read covariantly, are the co-Kleisli
   triple laws [extract_extend], [extend_extract] and [extend_comp] of
   Comonad/Core.v; they appear below as [comonad_id_left],
   [comonad_id_right] and [comonad_comp_assoc]. *)

(* Context-dependent maps, dataflow, and linear logic

   nLab:  https://ncatlab.org/nlab/show/exponential+modality
   Paper: Uustalu, Vene, "The Essence of Dataflow Programming", APLAS
          2005, LNCS 3780, pp. 2-18
   Paper: Petricek, Orchard, Mycroft, "Coeffects: a calculus of
          context-dependent computation", ICFP 2014

   The co-Kleisli category is where the computational reading of a
   comonad becomes a category of programs.  A co-Kleisli morphism
   W x ~> y consumes not a bare x but an x in its W-context, and the
   composite of two such morphisms first promotes the earlier one to a
   context-preserving transformation ([extend]) so that the later one
   may read its result in context; arrows that observe their
   surroundings thereby compose as ordinary functions do.  The analogy
   with Kleisli categories runs in parallel throughout: as those model
   call-by-value languages, co-Kleisli categories model call-by-name,
   and for an idempotent comonad the construction collapses to the
   coreflective subcategory of the comonad's modal types.  Haskell's
   comonad package (Kmett) states the comonad laws in this vocabulary,
   with extract the identity of co-Kleisli composition, just as
   [comonad_id_left], [comonad_id_right] and [comonad_comp_assoc] do
   below.

   Dataflow programming supplies the motivating example.  Uustalu and
   Vene observed that both general and causal stream functions can be
   characterized as the co-Kleisli arrows of suitable stream comonads —
   causality meaning that the output at a given moment depends only on
   the input's past and present, which is to say on the input value in
   its history-context — and on that observation built a generic
   comonadic interpreter, recovering effects where needed through a
   distributive law of the comonad over a monad (APLAS 2005).  A
   co-Kleisli arrow of the stream comonad is a digital filter, and
   [extend] produces the filtered stream (Milewski, 2017).  The coeffect
   calculi of Petricek, Orchard and Mycroft (ICFP 2014) supply type
   systems for this class of programs; dataflow, implicit parameters,
   liveness and bounded usage are among their instances.

   Linear logic supplies the proof-theoretic example.  In models of
   linear logic the exponential modality ! is a comonad (Girard 1987,
   the comonadic reading developed by Seely 1989, de Paiva 1989, and
   Benton–Bierman–de Paiva–Hyland 1992): !A is A made freely duplicable
   and discardable.  When the linear category is closed symmetric
   monoidal, the co-Kleisli category of ! is cartesian closed — a
   categorical form of the translation of intuitionistic logic into
   linear logic (Seely) — and Benton (1995) showed that the !-comonad
   is induced by a monoidal adjunction between a cartesian monoidal and
   a symmetric monoidal category, the linear–non-linear adjunction.
   The category built below is the common shape behind both readings. *)

Section CoKleisli.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

Definition CoKleisli : Category := (@Kleisli (C^op) (W^op) H)^op.

(** The hom-sets of the co-Kleisli category are definitionally the
    covariant hom-sets [W x ~> y] of the base category. *)
Lemma cokleisli_hom (x y : C) : (x ~{CoKleisli}~> y) = (W x ~{C}~> y).
Proof. reflexivity. Qed.

(** The identity at x is the counit ε_x. *)
Lemma cokleisli_id {x : C} : @id CoKleisli x ≈ @extract C W H x.
Proof. reflexivity. Qed.

Definition cokleisli_compose `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  W a ~{C}~> c := @compose CoKleisli a b c f g.

(* Co-Kleisli composition operators, following the library's fish-operator
   convention (Monad/Kleisli.v [>=>]/[<=<]): in the right-pointing [=>=] the
   LEFT operand runs first, so [f =>= g] extends [f] and then applies [g]
   ([g ∘ extend f]).  Its transpose [f =<= g] runs the right operand first
   ([f ∘ extend g]) — the co-Kleisli dual of [<=<].  This matches the
   direction of [>=>] on the monad side rather than Haskell's Control.Comonad
   [=>=], whose right-pointing operator runs the right operand first. *)
Notation "f =>= g" :=
  (cokleisli_compose g f) (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g) (at level 40, left associativity) : morphism_scope.

(** Co-Kleisli composition agrees with the extension operator [extend] of
    Comonad/Core.v; by the built-in duality the agreement is definitional.
    [f] on the left runs first, so [f =>= g ≈ g ∘ extend f]. *)
Lemma cokleisli_compose_extend `(f : W a ~{C}~> b) `(g : W b ~{C}~> c) :
  f =>= g ≈ g ∘ extend f.
Proof. reflexivity. Qed.

Corollary cokleisli_compose_extend_flip
  `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  f =<= g ≈ f ∘ extend g.
Proof. reflexivity. Qed.

(* The comonad laws, re-expressed in terms of this category: dually to the
   monoid reading in Monad/Kleisli.v, they exhibit [extract] as the unit of
   co-Kleisli composition, with associativity mediated by [extend].  Each is
   the corresponding category law of [CoKleisli], read across the definitional
   agreements above. *)

Corollary comonad_id_left `(f : W x ~{C}~> y) : extract =>= f ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_id_right `(f : W x ~{C}~> y) : f =>= extract ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_comp_assoc `(f : W x ~{C}~> y) `(g : W y ~{C}~> z)
  `(h : W z ~{C}~> w) : f =>= (g =>= h) ≈ (f =>= g) =>= h.
Proof. exact (@comp_assoc_sym CoKleisli x y z w h g f). Qed.

End CoKleisli.

Notation "f =>= g" :=
  (cokleisli_compose g f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g)
  (at level 40, left associativity) : morphism_scope.

(* Explicit-endofunctor forms, the robust fallback when higher-order
   unification cannot infer [W] through the bare [=>=]/[=<=] holes
   (Monad/Kleisli.v exports the analogous [>=[ M ]=>]/[<=[ M ]=<]). *)
Notation "f =>[ W ]=> g" := (@cokleisli_compose _ W _ _ _ g _ f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<[ W ]=< g" := (@cokleisli_compose _ W _ _ _ f _ g)
  (at level 40, left associativity) : morphism_scope.

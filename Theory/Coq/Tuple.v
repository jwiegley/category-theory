Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The pair/tuple type [A * B], with its product (and writer-monad) reading *)

(* nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/writer+monad
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_product

   FP reading.  [Tuple] is just Coq's pair constructor [prod], i.e. the type
   [A * B].  Holding the first component fixed, [Tuple x = (x * −)] is a
   Functor whose [fmap] acts on the second component ([prod_map]); when the
   fixed component [x] carries a Monoid it becomes the writer monad, which
   threads (accumulates) a monoidal "log" alongside a value, with [ret]/[pure]
   seeding the empty log [mempty] and [bind]/[ap] combining logs with [⊗]
   (mappend).  [first]/[second] give the action of [prod] as a bifunctor on,
   respectively, the first and second components.

   Categorical reading.  [A * B] is the binary product of [A] and [B] in the
   category of Coq types: it comes with the two projections [fst : A * B → A]
   and [snd : A * B → B], and for any [f : Q → A], [g : Q → B] the pairing
   (tupling) map ⟨f, g⟩ = [λ q, (f q, g q)] is the unique mediating morphism
   with [fst ∘ ⟨f,g⟩ = f] and [snd ∘ ⟨f,g⟩ = g].  This is the Cartesian
   product of Set, here realized in Coq.  The associators below
   ([tuple_swap_*]) witness [A * (B * C) ≅ (A * B) * C]; [curry]/[uncurry]
   witness the product/exponential adjunction [(A * B) → C  ≅  A → (B → C)],
   the defining isomorphism of a closed structure.

   Equality on this data is plain Coq [=]: pairs are an inductive type with
   decidable structure, so no setoid [≈] is needed at this layer. *)

Notation Tuple := prod (only parsing).

(* The two halves of the product associator [A * (B * C) ≅ (A * B) * C];
   [tuple_swap_a_bc_to_ab_c] and [tuple_swap_ab_c_to_a_bc] are mutually
   inverse and witness that the product is associative up to isomorphism. *)
Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

(* Pairing maps building a 3-fold product from three components, associated to
   the left ([(A * B) * C]) and to the right ([A * (B * C)]) respectively. *)
Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

(* The bifunctorial action of [prod] on its first and second components:
   [first f] maps the left coordinate, [second f] the right one (Haskell's
   [first]/[second] from [Data.Bifunctor], here for the pair bifunctor). *)
Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

(* [curry]/[uncurry] are the two directions of the product/exponential
   adjunction iso [(a * b) → c  ≅  a → (b → c)], the universal property of the
   exponential object (currying). *)
Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

(* [prod_map] is [fmap] for the second-argument functor [(C * −)]: it maps the
   second component and leaves the first untouched (= [second]). *)
Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

(* [(x * −)] is a Functor (the endofunctor fixing the first component); its
   [fmap] maps the second component via [prod_map]. *)
#[export]
Instance Tuple_Functor x : Functor (Tuple x) := {
  fmap := λ _ _, prod_map   (* hom map: act on the second component only *)
}.

(* The writer monad as an Applicative, available when the fixed component [x]
   is a Monoid: [pure] seeds the empty log, [ap] runs both effects and joins
   their logs with [⊗] (mappend). *)
#[export]
Instance Tuple_Applicative x `{Monoid x} : Applicative (Tuple x) := {
  pure := λ _ y, (mempty, y);                         (* empty log [mempty], value [y] *)
  ap := λ _ _ '(xf, f) '(xx, x), (xf ⊗ xx, f x);      (* combine logs, apply function *)
}.

(* The writer monad: [ret] seeds the empty log; [bind] runs [f] on the held
   value and concatenates the incoming log [xm] with the produced log [xx].
   Lawful precisely because [x] is a Monoid (the monad laws follow from the
   monoid laws on [⊗]/[mempty]). *)
#[export]
Instance Tuple_Monad x `{Monoid x} : Monad (Tuple x) := {
  ret := λ _ y, (mempty, y);                                          (* unit: empty log [mempty] *)
  bind := λ _ _ '(xm, m) f, let '(xx, x) := f m in (xm ⊗ xx, x)       (* concatenate logs via [⊗] *)
}.

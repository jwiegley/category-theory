Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

Notation Tuple := prod (only parsing).

Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

#[export]
Instance Tuple_Functor x : Functor (Tuple x) := {
  fmap := λ _ _, prod_map
}.

#[export]
Instance Tuple_Applicative x `{Monoid x} : Applicative (Tuple x) := {
  pure := λ _ y, (mempty, y);
  ap := λ _ _ '(xf, f) '(xx, x), (xf ⊗ xx, f x);
}.

#[export]
Instance Tuple_Monad x `{Monoid x} : Monad (Tuple x) := {
  ret := λ _ y, (mempty, y);
  bind := λ _ _ '(xm, m) f, let '(xx, x) := f m in (xm ⊗ xx, x)
}.

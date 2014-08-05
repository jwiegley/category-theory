Require Import Functors.

Inductive Maybe (A : Type): Type :=
  | Nothing : Maybe A
  | Just : A -> Maybe A.

Definition Maybe_map {X Y} (f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
   | Nothing => Nothing Y
   | Just x' => Just Y (f x')
  end.

Hint Unfold Maybe_map.

Ltac simple_solver :=
  intros;
  try ext_eq;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      is_var X; destruct X; auto
    end);
  auto.

Program Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.
Obligation 1. simple_solver. Defined.
Obligation 2. simple_solver. Defined.

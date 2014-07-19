Require Export Monad.

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

Section Maybe.

  Variable A : Type.  (* The type which is mapped over. *)

  Inductive Maybe (A : Type): Type :=
    | Nothing : Maybe A
    | Just : A -> Maybe A.


  (** By registering our simple_solver as the obligation tactic, all our law
      obligations will be taken care of for us automatically by the Ltac
      scripts above. *)
  Obligation Tactic := simple_solver.


  Definition Maybe_map {X Y} (f : X -> Y) (x : Maybe X) : Maybe Y :=
    match x with
    | Nothing => Nothing Y
    | Just x' => Just Y (f x')
    end.
  Hint Unfold Maybe_map.

  Global Program Instance Maybe_Functor : Functor Maybe :=
  { fmap := @Maybe_map
  }.


  Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
    match f with
    | Nothing => Nothing Y
    | Just f' => match x with
      | Nothing => Nothing Y
      | Just x' => Just Y (f' x')
      end
    end.
  Hint Unfold Maybe_apply.

  Global Program Instance Maybe_Applicative : Applicative Maybe :=
  { is_functor := Maybe_Functor
  ; eta := Just
  ; apply := @Maybe_apply
  }.


  Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
    match x with
    | Nothing => Nothing X
    | Just Nothing => Nothing X
    | Just (Just x') => Just X x'
    end.
  Hint Unfold Maybe_join.

  Global Program Instance Maybe_Monad : Monad Maybe :=
  { is_applicative := Maybe_Applicative
  ; mu := @Maybe_join
  }.

End Maybe.
Require Export Either.

Inductive Source (M : Type -> Type) X : Type :=
  | ASource : (forall {R}, R -> (R -> X -> M R) -> M R) -> Source M X.

Definition source_map {M : Type -> Type} {X Y}
  (f : X -> Y) (x : Source M X) : Source M Y :=
  match x with
    | ASource await =>
        ASource M Y (fun R z yield => await R z (fun r y => yield r (f y)))
  end.

Global Instance Source_Functor (M : Type -> Type) (X : Type)
  : Functor (Source M) := {
  fmap := @source_map M
}.
Proof.
  intros. compute. destruct x. reflexivity.
  intros. compute. destruct x. reflexivity.
Defined.

(* Extraction Language Haskell. *)
(* Recursive Extraction Source. *)

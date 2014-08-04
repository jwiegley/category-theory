Inductive Maybe (X : Type) :=
  | Nothing : Maybe X
  | Just    : X -> Maybe X.

Definition Maybe_map {X Y} (f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
   | Nothing => Nothing Y
   | Just x' => Just Y (f x')
  end.

Definition Maybe_Functor : Functor Coq Coq Maybe.
  apply Build_Functor with (fmap := @Maybe_map).
  - (* fmap_respects *)
    intros. reduce. unfold Maybe_map. destruct x.
      reflexivity.
      reduce_hyp H. f_equal. apply H.
  - (* fun_identity *)
    intros. reduce. unfold Maybe_map. destruct x; reflexivity.
  - (* fun_composition *)
    intros. reduce. unfold Maybe_map. destruct x; reflexivity.
Defined.

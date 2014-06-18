Require Export Category.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
    | nil     => nil Y
    | cons h t => cons Y (f h) (map f t)
  end.

Global Instance List_Functor : Functor list := {
  fmap := @map
}.
Proof.
  (* functor_law_1 *)
  intros. induction x as [| x'].
    reflexivity.
    simpl. rewrite IHx. reflexivity.

  (* functor_law_2 *)
  intros. induction x as [| x'].
    reflexivity.
    unfold compose. unfold compose in IHx.
      simpl. rewrite IHx. reflexivity.
Defined.

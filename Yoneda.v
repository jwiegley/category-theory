Require Export Functor.

Inductive Yoneda (F : Type -> Type) X : Type :=
  | Embed : forall {Y}, F Y -> (Y -> X) -> Yoneda F X.

Definition lift_yoneda (F : Type -> Type) X (a : F X)
  : Yoneda F X := Embed F X a id.

Definition lower_yoneda (F : Type -> Type) (f_dict : Functor F)
  X (a : Yoneda F X) : F X :=
  match a with | Embed F x f => fmap f x end.

Theorem eq_remove_Embed : forall (F : Type -> Type) X Y (f : Y -> X) (n m : F Y),
    n = m -> Embed F X n f = Embed F X m f.
Proof.
  intros. inversion H. reflexivity.  Qed.

Definition yoneda_map {F : Type -> Type} {X Y}
  (f : X -> Y) (x : Yoneda F X) : Yoneda F Y :=
  match x with
    | Embed X y g => Embed F Y y (f ∘ g)
  end.

Global Instance Yoneda_Functor (F : Type -> Type) : Functor (Yoneda F) := {
  fmap := @yoneda_map F
}.
Proof.
  (* functor_law_1 *)
  intros. unfold yoneda_map. destruct x.
    rewrite comp_left_identity. reflexivity.

  (* functor_law_2 *)
  intros. compute. destruct x. reflexivity.  Qed.

Class Isomorphism X Y := {
  to : X -> Y; from : Y -> X;
  iso_to    : forall (x : X), from (to x) = x;
  iso_from  : forall (y : Y), to (from y) = y
}.

Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : type_scope.

Hypothesis yoneda_refl : forall (F : Type -> Type) (f_dict : Functor F)
  X Y (f : Y -> X) (x : F Y),
  Embed F X (fmap f x) id = Embed F X x f.

Global Instance Yoneda_Lemma (F : Type -> Type) (f_dict : Functor F) X
  : F X ≅ Yoneda F X := {
  to   := lift_yoneda F X;
  from := lower_yoneda F f_dict X
}.
Proof.
  - (* iso_to *)
    intros. compute. apply functor_law_1.

  - (* iso_from *)
    intros. unfold lower_yoneda. destruct y. unfold lift_yoneda.
      apply yoneda_refl.  Qed.

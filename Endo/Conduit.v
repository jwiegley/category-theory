Require Export Cont.
Require Export EitherT.
Require Export MCompose.

Inductive Source (M : Type -> Type) (R : Type) (A : Type) : Type :=
  Source_ : Cont (R -> EitherT R M R) A -> Source M R A.

Definition Source_map {M : Type -> Type} `{Functor M} {R X Y}
  (f : X -> Y) (x : Source M R X) : Source M R Y :=
  match x with
    Source_ k => Source_ M R Y (fmap f k)
  end.

Global Instance Source_Functor {M : Type -> Type} `{Functor M} {R}
  : Functor (Source M R) :=
{ fmap := @Source_map M _ R
}.
Proof.
  - (* fun_identity *) intros. ext_eq.
    unfold Source_map.
    destruct x.
    unfold id.
    f_equal. simpl.
    unfold Cont_map.
    destruct c.
    f_equal.
  - (* fun_composition *) intros. ext_eq.
    unfold Source_map.
    destruct x. simpl.
    unfold compose, Cont_map.
    f_equal.
    destruct c.
    f_equal.
Defined.

Definition Source_apply {M : Type -> Type} `{Applicative M}
  {R X Y} (f : Source M R (X -> Y)) (x : Source M R X) : Source M R Y :=
  match f with
    Source_ k => match x with
      Source_ j => Source_ M R Y (apply k j)
    end
  end.

Global Instance Source_Applicative {M : Type -> Type} `{Applicative M}
  {R} : Applicative (Source M R) :=
{ is_functor := Source_Functor
; eta := fun A x => Source_ M R A (eta x)
; apply := @Source_apply M _ R
}.
Proof.
  - (* app_identity *)
    intros. ext_eq.
    destruct x.
    unfold id, Source_apply.
    f_equal. simpl.
    apply (@app_identity_x _ Cont_Applicative).

  - (* app_composition *)
    intros.
    unfold Source_apply.
    destruct u. destruct v. destruct w.
    f_equal.
    apply app_composition.

  - (* app_homomorphism *)
    intros.
    unfold Source_apply.
    f_equal.

  - (* app_interchange *)
    intros.
    unfold Source_apply.
    destruct u.
    f_equal.
    apply app_interchange.

  - (* app_fmap_unit *)
    intros. ext_eq.
    unfold Source_apply.
    destruct x. simpl.
    f_equal.
    unfold Cont_map.
    destruct c.
    f_equal.
Defined.

Definition getSource {M : Type -> Type} {R X} (x : Source M R X)
  : Cont (R -> EitherT R M R) X :=
  match x with
    Source_ k => k
  end.

Definition Source_join {M : Type -> Type} `{Monad M}
  {R X} : Source M R (Source M R X) -> Source M R X :=
  Source_ M R X ∘ mu ∘ fmap getSource ∘ getSource.

Global Instance Source_Monad {M : Type -> Type} `{Monad M} {R}
  : Monad (Source M R) :=
{ is_applicative := Source_Applicative
; mu := fun _ => Source_join
}.
Proof.
  - (* monad_law_1 *)
    intros. ext_eq. simpl.
    unfold compose, Source_join.
    destruct x. simpl.
    unfold compose at 10.
    repeat f_equal.
    unfold compose at 4.
    unfold compose at 4.
    simpl.
    unfold getSource, compose.
    assert ((fun x : Source M R (Source M R X) =>
         match x with
         | Source_ k => k
         end) = getSource).
      reflexivity. rewrite H0. clear H0.
    assert ((fun x : Source M R X =>
         match x with
         | Source_ k => k
         end) = getSource).
      reflexivity. rewrite H0. clear H0.
    destruct c. simpl. f_equal.
    unfold compose, flip.
    ext_eq. f_equal.
    ext_eq.
    destruct x0. simpl. ext_eq. destruct c. simpl.
    assert ((fun x' : Source M R X => x x') = x).
      reflexivity. rewrite H0. clear H0.
    unfold compose, flip.
    admit.

  - (* monad_law_2 *)
    intros. ext_eq. simpl.
    unfold Source_join, Source_map, id, compose.
    destruct x.
    f_equal. simpl.
    pose proof (@fun_composition_x _ (@Cont_Functor (R -> EitherT R M R))).
    simpl in H0.
    rewrite H0.
    pose proof (@monad_law_2_x _ (@Cont_Monad (R -> EitherT R M R))).
    simpl in H1.
    unfold compose. simpl.
    apply H1.

  - (* monad_law_3 *)
    intros. ext_eq. simpl.
    unfold Source_join, id, compose.
    destruct x.
    f_equal. simpl.
    unfold compose.
    destruct c.
    f_equal.

  - (* monad_law_4 *)
    intros. ext_eq. simpl.
    unfold Source_join, Source_map, compose.
    destruct x.
    f_equal. simpl.
    destruct c. simpl.
    f_equal.
    unfold compose.
    ext_eq.
    f_equal. simpl.
    ext_eq.
    destruct x0.
    destruct c. simpl.
    reflexivity.
Abort.

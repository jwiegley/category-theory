Require Export Cont.
Require Export EitherT.
Require Export Trans.
Require Category.

(* A type-wrapper is not strictly necessary here, since the Functor,
   Applicative and Monad behaviors are all directly based on Cont.  In Haskell
   it is needed, so we match that behavior here, to prove that nothing is
   violated owing to the wrapping.
*)
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
  match x with Source_ k => k end.

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
    unfold Source_join, Source_map, id, compose.
    destruct x.
    destruct c. simpl.
    unfold compose, flip.
    repeat f_equal.
    ext_eq. f_equal.
    ext_eq. f_equal.
    destruct x0.
    destruct c.
    reflexivity.

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
Defined.

Definition source {M : Type -> Type} `{Monad M} {R A}
   (await : R -> (R -> A -> EitherT R M R) -> EitherT R M R)
  : Source M R A :=
  Source_ M R A (Cont_ (R -> EitherT R M R) A (flip await ∘ flip)).

Theorem join_inj : forall {M : Type -> Type} `{Monad M} {R A}
  {x y : EitherT R M (EitherT R M A)},
  mu x = mu y -> x = y.
Proof.
  intros. destruct x. destruct y.
  f_equal. inversion H. simpl in H0.

Theorem fmap_join_distr : forall {M : Type -> Type} `{Monad M} {A B C}
   (m : M A) (g : A -> M B) (f : B -> M C),
   fmap (mu ∘ fmap f ∘ g) m = fmap f (mu (fmap g m)).
Proof.
  intros. simpl.
  rewrite <- monad_law_4_x.
  rewrite fun_composition_x.
  rewrite <- fun_composition.
  unfold compose at 1.
  remember ((fmap[M] (fmap[M] f ∘ g)) m) as x.
Admitted.

Theorem source_distributes
  : forall {M : Type -> Type} `{Monad M} {R A}
    (m : EitherT R M A) (f : A -> EitherT R M A),
  source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
            m >>= yield r) >>=
    (fun x : A =>
       source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
                 f x >>= yield r)) =
  source (fun (r : R) (yield : R -> A -> EitherT R M R) =>
            m >>= f >>= yield r).
Proof.
  intros.
  unfold bind, flip.
  pose monad_law_4_x.
  simpl mu. simpl fmap.
  unfold source, flip, compose.
  unfold Source_join, compose. f_equal.
  simpl mu. simpl.
  f_equal. ext_eq. ext_eq.
  unfold compose, flip.
  f_equal. simpl.
  assert (EitherT_map
            (fun x1 : A => EitherT_join
               (EitherT_map (fun x2 : A => x x2 x0) (f x1))) m =
          EitherT_map
            (EitherT_join ∘ EitherT_map (fun x2 : A => x x2 x0) ∘ f) m).
    reflexivity. rewrite H0. clear H0.
  pose (@fmap_join_distr (EitherT R M) EitherT_Monad).
  simpl fmap in e0.
  simpl mu in e0.
  apply e0.
Qed.

Global Instance Source_MonadTrans {M : Type -> Type} `{Monad M} {R}
  : @MonadTrans (fun N => Source N R) M _ Source_Monad :=
{ lift := fun _ m => source (fun r yield => lift m >>= yield r)
}.
Proof.
  - (* trans_law_1 *) intros.
    unfold source. simpl eta.
    ext_eq. unfold compose at 1.
    f_equal. f_equal.
    unfold flip. unfold compose at 1.
    unfold bind.
    rewrite trans_law_1_x.
    pose proof app_fmap_compose_x.
    specialize (H0 (EitherT R M) is_applicative A (EitherT R M R)).
    simpl mu.
    simpl eta.
    simpl eta in H0.
    ext_eq. ext_eq.
    rewrite <- H0.
    pose proof monad_law_3_x.
    specialize (H1 (EitherT R M) EitherT_Monad R (x0 x x1)).
    simpl mu in H1.
    simpl eta in H1.
    assumption.

  - (* trans_law_2 *) intros.
    pose (@trans_law_2 (EitherT R) M _ _ _ A).
    unfold compose. rewrite e.
    rewrite source_distributes.
    reflexivity.
Defined.

Require Export Category.

(* Src is the category of simple-conduit Sources:

   Objects are sources
   Morphisms are the source homomorphisms (aka conduits)

   Identity is just simple identity
   Composition is just simple composition, since monadic folds
     are simply functions modulo type wrapping.

   Thus, the proof are extremely trivial and follow immediately from the
   definitions.

   Another way to say it is that since, by naturality, the image of a functor
   is always a sub-category in its codomain, and since Sources are functors,
   they must also then be categories.
*)
Global Instance Src {M : Type -> Type} `{Monad M} {R}
  : Category (sigT (Source M R))
             (fun dom ran => projT1 dom → projT1 ran) :=
{ id      := fun _ x => id x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun X Y f g => f ≈ g
}.
Proof.
  (* The proofs of all of these follow trivially from their definitions. *)
  - (* eqv_equivalence *)  crush.
  - (* compose_respects *) crush.
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)       crush.
Defined.

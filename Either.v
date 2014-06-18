Require Export Coq.Setoids.Setoid.
Require Export Coq.Logic.FunctionalExtensionality.

Require Export Functor.

Inductive Either (X : Type) (Y : Type): Type :=
  | Left : X -> Either X Y
  | Right : Y -> Either X Y.

Definition Either_map {E X Y} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
   | Left e => Left E Y e
   | Right x' => Right E Y (f x')
  end.

Definition Either_apply {E X Y} (f : Either E (X -> Y)) (x : Either E X)
: Either E Y :=
  match f with
   | Left e => Left E Y e
   | Right f' => match x with
       | Left e => Left E Y e
       | Right x' => Right E Y (f' x')
     end
  end.

Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
   | Left e => Left E X e
   | Right (Left e) => Left E X e
   | Right (Right x') => Right E X x'
  end.

Theorem Either_duplicated : forall {E X}
  (f : Either E X -> Either E (Either E X))
  (g : Either E X -> Either E (Either E X)) (z : f = g),
  (fun xv => match xv with
    | Left e => f (Left E X e)
    | Right x' => f (Right E X x')
    end) = g.
Proof.
  intros. ext_eq. destruct x; rewrite z; reflexivity.  Qed.

Global Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.
Proof.
  (* fun_identity *)
  intros. ext_eq. unfold Either_map. destruct x; reflexivity.
  (* fun_composition *)
  intros. ext_eq. compute. destruct x; reflexivity.
Defined.

Global Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; eta := Right E
; apply := @Either_apply E
}.
Proof.
  - (* app_identity *)
    intros. compute. destruct v. reflexivity. reflexivity.
  - (* app_composition *)
    intros. compute. destruct u. reflexivity.
      destruct v. reflexivity. destruct w. reflexivity. reflexivity.
  - (* app_homomorphism *)
    intros. compute. reflexivity.
  - (* app_interchange *)
    intros. compute. destruct u. reflexivity. reflexivity.
  - (* app_fmap_unit *)
    intros. unfold Either_apply. ext_eq.
    destruct x; unfold fmap; unfold Either_Functor; reflexivity.
Defined.

Global Instance Either_Monad {E} : Monad (Either E) :=
{ is_applicative := Either_Applicative
; mu := @Either_join E
}.
Proof.
  (* monad_law_1 *)
  intros. ext_eq. compute. destruct x. reflexivity.
    destruct e. reflexivity.
    destruct e. reflexivity.
    reflexivity.
  (* monad_law_2 *)
  intros. ext_eq. compute. destruct x; reflexivity.
  (* monad_law_2_x *)
  intros. compute. destruct x; reflexivity.
  (* monad_law_3 *)
  intros. ext_eq. compute. destruct x; reflexivity.
  (* monad_law_3_x *)
  intros. compute. destruct x; reflexivity.
  (* monad_law_4 *)
  intros. ext_eq. compute. reflexivity.
  (* monad_law_5 *)
  intros. ext_eq. compute. destruct x. reflexivity. destruct e; reflexivity.
Defined.

Inductive EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  | EitherT_ : M (Either X Y) -> EitherT X M Y.

Definition EitherT_map {E M} (m_dict : Monad M) {X Y}
  (f : X -> Y) (x : EitherT E M X) : EitherT E M Y :=
  match x with
   | EitherT_ m =>
      EitherT_ E M Y (fmap (@fmap (Either E) Either_Functor X Y f) m)
  end.

Definition EitherT_return {E M} (m_dict : Monad M) {X}
  (x : X) : EitherT E M X := EitherT_ E M X (eta (Right E X x)).

Definition EitherT_apply {E M} (m_dict : Monad M) {X Y}
  (f : EitherT E M (X -> Y)) (x : EitherT E M X) : EitherT E M Y :=
  match f with
   | EitherT_ mf => match x with
       | EitherT_ mx =>
          EitherT_ E M Y (mf >>= fun fv => match fv with
           | Left e => eta (Left E Y e)
           | Right f' => mx >>= fun xv => match xv with
              | Left e => eta (Left E Y e)
              | Right x' => eta (Right E Y (f' x'))
             end
           end)
     end
  end.

Definition EitherT_join {E M} (m_dict : Monad M) {X}
  (x : EitherT E M (EitherT E M X)) : EitherT E M X :=
  match x with
   | EitherT_ mx => EitherT_ E M X (mx >>= fun xv => match xv with
      | Left e => eta (Left E X e)
      | Right (EitherT_ mx') => mx'
     end)
  end.

Global Instance EitherT_Functor (E : Type) (M : Type -> Type)
  (m_dict : Monad M) : Functor (EitherT E M) :=
{ fmap := @EitherT_map E M m_dict
}.
Proof.
  (* fun_identity *)
  intros. ext_eq. unfold EitherT_map. destruct x.
    rewrite fun_identity.
    rewrite fun_identity. unfold id. reflexivity.
  (* fun_composition *)
  intros. ext_eq. unfold EitherT_map. destruct x.
    rewrite <- fun_composition.
    rewrite <- fun_composition.
    unfold compose. reflexivity.
Defined.

Global Instance EitherT_Applicative (E : Type) (M : Type -> Type)
  (m_dict : Monad M) : Applicative (EitherT E M) :=
{ is_functor := EitherT_Functor E M m_dict
; eta := @EitherT_return E M m_dict
; apply := @EitherT_apply E M m_dict
}.
Proof.
  Typeclasses Transparent Either_Functor.
  - (* app_identity *)
    intros.
    destruct v. unfold id. simpl. unfold bind.
    rewrite <- app_fmap_unit.
    rewrite app_homomorphism.
    rewrite <- app_fmap_unit.
    rewrite monad_law_3_x.
    f_equal.
    rewrite app_fmap_unit.
    pose proof (@Either_duplicated E X
      (@eta (Either E) is_applicative (Either E X))).
    rewrite H.
    (* How do I unfold a lambda over constructors? *)
    rewrite monad_law_2_x.
    reflexivity.
  - (* app_composition *)
    intros. admit.
  - (* app_homomorphism *)
    intros. admit.
  - (* app_interchange *)
    intros. admit.  Defined.

Global Instance EitherT_Monad {E M} (m_dict : Monad M) (X : Type)
: Monad (EitherT E M) :=
{ is_applicative := @EitherT_Applicative E M m_dict X
; mu := @EitherT_join E M m_dict
}.
Proof.
  (* monad_law_1 *)
  intros. admit.
  (* monad_law_2 *)
  intros. admit.
  (* monad_law_3 *)
  intros. admit.
  (* monad_law_4 *)
  intros. admit.
  (* monad_law_5 *)
  intros. admit.  Defined.

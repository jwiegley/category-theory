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

Global Instance Either_Functor {E} (X : Type) : Functor (Either E) :=
{ fmap := @Either_map E
}.
Proof.
  (* fun_identity *)
  intros. compute. destruct x. reflexivity. reflexivity.
  (* fun_composition *)
  intros. compute. destruct x. reflexivity.  reflexivity.  Defined.

Global Instance Either_Applicative {E} (X : Type)
: Applicative (Either E) :=
{ is_functor := @Either_Functor E X
; eta := Right E
; apply := @Either_apply E
}.
Proof.
  (* app_identity *)
  intros. compute. destruct v. reflexivity. reflexivity.
  (* app_composition *)
  intros. compute. destruct u. reflexivity.
    destruct v. reflexivity. destruct w. reflexivity. reflexivity.
  (* app_homomorphism *)
  intros. compute. reflexivity.
  (* app_interchange *)
  intros. compute. destruct u. reflexivity. reflexivity.  Defined.

Global Instance Either_Monad {E} (X : Type) : Monad (Either E) :=
{ is_applicative := Either_Applicative X
; mu := @Either_join E
}.
Proof.
  (* monad_law_1 *)
  intros. compute. destruct x. reflexivity.
    destruct e. reflexivity.
    destruct e. reflexivity.
    reflexivity.
  (* monad_law_2 *)
  intros. compute. destruct x. reflexivity. reflexivity.
  (* monad_law_3 *)
  intros. compute. destruct x. reflexivity. reflexivity.
  (* monad_law_4 *)
  intros. compute. reflexivity.
  (* monad_law_5 *)
  intros. compute. destruct x. reflexivity. destruct e.
    reflexivity. reflexivity.  Defined.

Inductive EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  | EitherT_ : M (Either X Y) -> EitherT X M Y.

Definition EitherT_map {E M} (m_dict : Monad M) {X Y}
  (f : X -> Y) (x : EitherT E M X) : EitherT E M Y :=
  match x with
   | EitherT_ m =>
      EitherT_ E M Y (fmap (@fmap (Either E) (Either_Functor E) X Y f) m)
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
  (m_dict : Monad M) (X : Type) : Functor (EitherT E M) :=
{ fmap := @EitherT_map E M m_dict
}.
Proof.
  Typeclasses Transparent Either_Functor.
  (* fun_identity *)
  intros. unfold EitherT_map. destruct x.
    
    (* pose proof (@monad_law_4 M m_dict X) as H. *)

  (* fun_composition *)
  intros. admit.  Defined.

Global Instance EitherT_Applicative `(MM : Monad M) {E M} (X : Type)
: Applicative (EitherT E M) :=
{ is_functor := @EitherT_Functor E M m_dict X
; eta := @EitherT_return E M m_dict  (* fun_identity *)
  intros. compute. destruct x. reflexivity. reflexivity.

; apply := @EitherT_apply E M m_dict
}.
Proof.
  (* app_identity *)
  intros. admit.
  (* app_composition *)
  intros. admit.
  (* app_homomorphism *)
  intros. admit.
  (* app_interchange *)
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

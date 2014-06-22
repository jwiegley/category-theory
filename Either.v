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
  - (* fun_identity *)
    intros. ext_eq. unfold Either_map. destruct x; reflexivity.
  - (* fun_composition *)
    intros. ext_eq. compute. destruct x; reflexivity.
Defined.

Global Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; eta := Right E
; apply := @Either_apply E
}.
Proof.
  - (* app_identity *)
    intros. ext_eq. compute. destruct x. reflexivity. reflexivity.
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
  - (* monad_law_1 *)
    intros. ext_eq. compute. destruct x. reflexivity.
    destruct e. reflexivity. destruct e. reflexivity. reflexivity.
  - (* monad_law_2 *)
    intros. ext_eq. compute. destruct x; reflexivity.
  - (* monad_law_3 *)
    intros. ext_eq. compute. destruct x; reflexivity.
  - (* monad_law_4 *)
    intros. ext_eq. compute. reflexivity.
  - (* monad_law_5 *)
    intros. ext_eq. compute. destruct x. reflexivity. destruct e; reflexivity.
Defined.

Inductive EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  | EitherT_ : M (Either X Y) -> EitherT X M Y.

Definition EitherT_map {E M} (m_dict : Functor M) {X Y}
  (f : X -> Y) (x : EitherT E M X) : EitherT E M Y :=
  match x with
   | EitherT_ m => EitherT_ E M Y (fmap (fmap f) m)
  end.

Global Instance EitherT_Functor (E : Type) (M : Type -> Type)
  (m_dict : Functor M) : Functor (EitherT E M) :=
{ fmap := @EitherT_map E M m_dict
}.
Proof.
  - (* fun_identity *)
    intros. ext_eq. unfold EitherT_map. destruct x.
    rewrite fun_identity.
    rewrite fun_identity. unfold id. reflexivity.

  - (* fun_composition *)
    intros. ext_eq. unfold EitherT_map. destruct x.
    rewrite <- fun_composition.
    rewrite <- fun_composition.
    unfold compose. reflexivity.
Defined.

Definition EitherT_return {E M} (m_dict : Applicative M) {X}
  (x : X) : EitherT E M X := EitherT_ E M X (eta (eta x)).

Definition EitherT_apply {E M} (m_dict : Applicative M) {X Y}
  (f : EitherT E M (X -> Y)) (x : EitherT E M X) : EitherT E M Y :=
  match f with
   | EitherT_ mf => match x with
       | EitherT_ mx => EitherT_ E M Y (apply (fmap apply mf) mx)
     end
  end.

Definition EitherT_join' {E M} `{Monad M} {X}
  (x : Either E (EitherT E M X)) : M (Either E X) :=
  match x with
  | Left e => eta (Left E X e)
  | Right (EitherT_ mx') => mx'
  end.

Definition EitherT_join {E M} `{m_dict : Monad M} {X}
  (x : EitherT E M (EitherT E M X)) : EitherT E M X :=
  match x with
   | EitherT_ mx =>
      EitherT_ E M X (mu (fmap (@EitherT_join' E M m_dict X) mx))
  end.

Global Instance EitherT_Applicative (E : Type) (M : Type -> Type)
  (m_dict : Applicative M) : Applicative (EitherT E M) :=
{ is_functor := EitherT_Functor E M (@is_functor M m_dict)
; eta := @EitherT_return E M m_dict
; apply := @EitherT_apply E M m_dict
}.
Proof.
  - (* app_identity *)
    intros. ext_eq. unfold EitherT_apply, EitherT_return.
    destruct x.
    rewrite_app_homomorphisms.
    rewrite fun_identity.
    rewrite fun_identity. reflexivity.

  - (* app_composition *)
    intros. unfold EitherT_apply, EitherT_return.
    destruct u. destruct v. destruct w. f_equal.
    admit.

  - (* app_homomorphism *)
    intros. unfold EitherT_apply, EitherT_return.
    rewrite_app_homomorphisms.
    rewrite_app_homomorphisms. reflexivity.

  - (* app_interchange *)
    intros. unfold EitherT_apply, EitherT_return.
    destruct u. f_equal.
    rewrite app_interchange.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x. reflexivity.

  - (* app_fmap_unit *)
    intros. unfold EitherT_apply, EitherT_return.
    rewrite_app_homomorphisms. reflexivity.
Defined.

Global Instance EitherT_Monad {E M} (m_dict : Monad M) (X : Type)
  : Monad (EitherT E M) :=
{ is_applicative := EitherT_Applicative E M (@is_applicative M m_dict)
; mu := @EitherT_join E M m_dict
}.
Proof.
  - (* monad_law_1 *)
    intros. ext_eq. unfold compose. simpl. f_equal.
    admit.

  - (* monad_law_2 *)
    intros. ext_eq. unfold compose. simpl.
    unfold EitherT_return.
    unfold EitherT_map. destruct x. simpl.
    unfold id. f_equal.
    admit.

  - (* monad_law_3 *)
    intros. ext_eq. unfold compose. simpl.
    rewrite_app_homomorphisms.
    rewrite monad_law_3_x. simpl. destruct x. reflexivity.

  - (* monad_law_4 *)
    intros. ext_eq. simpl.
    unfold EitherT_return. unfold compose. simpl. f_equal.
    rewrite <- monad_law_4_x. f_equal.

  - (* monad_law_5 *)
    intros. ext_eq. simpl.
    unfold EitherT_return. unfold compose.
    unfold EitherT_join. destruct x. simpl. f_equal.
    rewrite <- monad_law_5_x. f_equal.
    rewrite fun_composition_x.
    rewrite fun_composition_x. f_equal.
    unfold EitherT_map. simpl.
    admit.
Defined.

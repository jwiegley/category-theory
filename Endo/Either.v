Require Export Coq.Setoids.Setoid.

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

Global Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.
Proof.
  (* fun_identity *)    crush_ext.
  (* fun_composition *) crush_ext.
Defined.

Global Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; eta := Right E
; apply := @Either_apply E
}.
Proof.
  (* app_identity *)     crush_ext.
  (* app_composition *)  crush.
  (* app_homomorphism *) crush.
  (* app_interchange *)  crush.
  (* app_fmap_unit *)    crush.
Defined.

Global Instance Either_Monad {E} : Monad (Either E) :=
{ is_applicative := Either_Applicative
; mu := @Either_join E
}.
Proof.
  (* monad_law_1 *) crush_ext.
  (* monad_law_2 *) crush_ext.
  (* monad_law_3 *) crush_ext.
  (* monad_law_4 *) crush.
  (* monad_law_5 *) crush_ext.
Defined.

Inductive EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  | EitherT_ : M (Either X Y) -> EitherT X M Y.

Definition EitherT_shallow_map {E M} `{Functor M} {X Y}
  (f : M (Either E X) -> M (Either E Y)) (x : EitherT E M X) : EitherT E M Y :=
  match x with EitherT_ m => EitherT_ E M Y (f m) end.

Definition EitherT_map {E M} `{Functor M} {X Y}
  (f : X -> Y) (x : EitherT E M X) : EitherT E M Y :=
  match x with EitherT_ m => EitherT_ E M Y (fmap (fmap f) m) end.

(* Definition et_fun_composition {E M} (m_dict : Functor M) *)
(*   (X Y Z : Type) (f : Y -> Z) (g : X -> Y) : *)
(*   EitherT_map m_dict f ∘ EitherT_map m_dict g = EitherT_map m_dict (f ∘ g) := *)
(*   eq_ind_r *)
(*     (fun k => *)
(*       k _ = k _) eq_refl (f ∘ g). *)

Global Instance EitherT_Functor (E : Type) (M : Type -> Type)
  `{f_dict : Functor M} : Functor (EitherT E M) :=
{ fmap := @EitherT_map E M f_dict
}.
Proof.
  - (* fun_identity *)
    intros. ext_eq. unfold EitherT_map. destruct x.
    repeat (rewrite fun_identity). crush.

  - (* fun_composition *)
    intros. ext_eq. unfold EitherT_map. destruct x.
    repeat (rewrite <- fun_composition). crush.
Defined.

Definition EitherT_return {E M} `{Applicative M} {X}
  (x : X) : EitherT E M X := EitherT_ E M X (eta (eta x)).

Definition EitherT_apply {E M} `{Applicative M} {X Y}
  (f : EitherT E M (X -> Y)) (x : EitherT E M X) : EitherT E M Y :=
  match f with
    EitherT_ mf => match x with
      EitherT_ mx => EitherT_ E M Y (apply (fmap apply mf) mx)
    end
  end.

Definition EitherT_join' {E M} `{Applicative M} {X}
  (x : Either E (EitherT E M X)) : M (Either E X) :=
  match x with
  | Left e => eta (Left E X e)
  | Right (EitherT_ mx') => mx'
  end.

Definition EitherT_join {E M} `{m_dict : Monad M} {X}
  (x : EitherT E M (EitherT E M X)) : EitherT E M X :=
  EitherT_shallow_map (mu ∘ fmap EitherT_join') x.

Global Instance EitherT_Applicative (E : Type) (M : Type -> Type)
  `{app_dict : Applicative M} : Applicative (EitherT E M) :=
{ is_functor := EitherT_Functor E M
; eta := @EitherT_return E M app_dict
; apply := @EitherT_apply E M app_dict
}.
Proof.
  Typeclasses Transparent Compose_Applicative.

  - (* app_identity *)
    intros. ext_eq. unfold EitherT_apply, EitherT_return.
    destruct x. unfold id at 2. f_equal.
    apply (@app_identity_x (fun X => fobj (fobj X))
          (Compose_Applicative M (Either E))).

  - (* app_composition *)
    intros. unfold EitherT_apply, EitherT_return.
    destruct u. destruct v. destruct w. f_equal.
    apply (@app_composition (fun X => fobj (fobj X))
          (Compose_Applicative M (Either E))).

  - (* app_homomorphism *)
    intros. unfold EitherT_apply, EitherT_return. f_equal.
    apply (@app_homomorphism (fun X => fobj (fobj X))
          (Compose_Applicative M (Either E))).

  - (* app_interchange *)
    intros. unfold EitherT_apply, EitherT_return.
    destruct u. f_equal.
    apply (@app_interchange (fun X => fobj (fobj X))
          (Compose_Applicative M (Either E))).

  - (* app_fmap_unit *)
    intros. unfold EitherT_apply, EitherT_return.
    rewrite_app_homomorphisms. reflexivity.
Defined.

Global Instance EitherT_Monad {E M} (m_dict : Monad M) (X : Type)
  : Monad (EitherT E M) :=
{ is_applicative := EitherT_Applicative E M
; mu := @EitherT_join E M m_dict
}.
Proof.
  - (* monad_law_1 *)
    intros. ext_eq.
    unfold compose.
    unfold EitherT_join. f_equal.
    unfold compose. simpl.
    unfold EitherT_map. destruct x.
    unfold EitherT_shallow_map. f_equal.
    unfold EitherT_join'.
    admit.

  - (* monad_law_2 *)
    (* intros. ext_eq. unfold compose. simpl. *)
    (* unfold EitherT_join, EitherT_return. unfold id. *)
    (* unfold EitherT_map. destruct x. simpl. f_equal. *)
    (* unfold compose. *)
    (* assert ((fun x : X0 => EitherT_ E M X0 (eta (Right E X0 x))) = *)
    (*         (@eta (EitherT E M) _ _)). *)
    (*   reflexivity. rewrite H. clear H. *)
    (* rewrite fun_composition_x. *)
    (* assert (mu ((EitherT_join' ∘ Either_map eta) <$> m) = *)
    (*         (mu ∘ fmap (EitherT_join' ∘ Either_map eta)) m). *)
    (*   reflexivity. rewrite H. clear H. *)
    (* assert (fmap ((@EitherT_join' E M _ X) ∘ *)
    (*               (@Either_map E X (EitherT E M X)) (@eta (EitherT E M) _ X)) = *)
    (*         eta). *)
    (*   assert (fmap (EitherT_join' ∘ Either_map eta) = *)
    (*           ((compose mu) ∘ fmap ∘ (compose EitherT_join') ∘ Either_map) eta). *)
    (*   ext_eq. rewrite <- fun_composition. unfold compose. *)
    admit.

  - (* monad_law_3 *)
    intros. ext_eq. unfold EitherT_join, compose. simpl.
    rewrite_app_homomorphisms.
    rewrite monad_law_3_x. simpl. destruct x. reflexivity.

  - (* monad_law_4 *)
    intros. ext_eq. simpl.
    unfold EitherT_return. unfold compose.
    unfold EitherT_map. destruct x. simpl. f_equal.
    unfold compose.
    rewrite fun_composition_x.
    rewrite <- app_fmap_unit.
    rewrite <- monad_law_4_x. f_equal.
    rewrite app_fmap_unit.
    rewrite fun_composition_x. f_equal. ext_eq.
    unfold compose. unfold EitherT_join'. destruct x.
      simpl. unfold Either_map.
        rewrite <- app_fmap_unit.
        rewrite app_homomorphism. reflexivity.
      simpl. destruct e. reflexivity.
Defined.

Require Export Either.
Require Export MCompose.

Inductive EitherT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  EitherT_ : M (Either X Y) -> EitherT X M Y.

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
    intros.
    ext_eq.
    unfold EitherT_map.
    destruct x.
    repeat (rewrite fun_identity).
    unfold id.
    reflexivity.

  - (* fun_composition *)
    intros.
    ext_eq.
    unfold EitherT_map.
    destruct x.
    repeat (rewrite <- fun_composition).
    unfold compose.
    reflexivity.
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

Definition MEither_swap {E M} `{Monad M} `{Monad (Either E)} {X}

Definition EitherT_join {E M} `{Monad M} `{Monad (Either E)} {X}
  (x : EitherT E M (EitherT E M X)) : EitherT E M X :=
  compose_mu M (Either E) MEither_swap.

Global Instance EitherT_Applicative (E : Type) (M : Type -> Type)
  `{app_dict : Applicative M} : Applicative (EitherT E M) :=
{ is_functor := EitherT_Functor E M
; eta := @EitherT_return E M app_dict
; apply := @EitherT_apply E M app_dict
}.
Proof.
  - (* app_identity *) intros. ext_eq.
    unfold EitherT_apply, EitherT_return.
    destruct x.
    unfold id at 2.
    f_equal.
    apply (@app_identity_x (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_composition *) intros.
    unfold EitherT_apply, EitherT_return.
    destruct u. destruct v. destruct w. f_equal.
    apply (@app_composition (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_homomorphism *) intros.
    unfold EitherT_apply, EitherT_return. f_equal.
    apply (@app_homomorphism (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_interchange *) intros.
    unfold EitherT_apply, EitherT_return.
    destruct u. f_equal.
    apply (@app_interchange (fun X => fobj (fobj X))
          (Applicative_Compose M (Either E))).

  - (* app_fmap_unit *) intros.
    unfold EitherT_apply, EitherT_return.
    rewrite_app_homomorphisms.
    reflexivity.
Defined.

Global Instance EitherT_Monad {E M}
  `{Monad M} `{Monad (Either E)} {X}
  : Monad (EitherT E M) :=
{ is_applicative := EitherT_Applicative E M
; mu := EitherT_mu
}.
Proof.
  - (* monad_law_1 *)
    intros.
    apply (@monad_law_1 (fun X => M (Either E X))
          (Monad_Compose M (Either E) _ _ _ _ _)).
    admit.

  - (* monad_law_2 *) intros. ext_eq.
    unfold EitherT_join, compose. simpl.
    unfold EitherT_shallow_map.
    destruct x.
    unfold EitherT_map, id.
    simpl. f_equal.
    rewrite <- uncompose with (f := fmap[M] EitherT_join').
    rewrite <- uncompose with (f := mu).
    rewrite fun_composition.
    admit.

  - (* monad_law_3 *) intros. ext_eq.
    unfold EitherT_join, compose. simpl.
    rewrite_app_homomorphisms.
    rewrite monad_law_3_x.
    simpl. destruct x.
    reflexivity.

  - (* monad_law_4 *) intros. ext_eq. simpl.
    unfold EitherT_return.
    unfold compose.
    unfold EitherT_map.
    destruct x. simpl. f_equal.
    unfold compose.
    rewrite fun_composition_x.
    rewrite <- app_fmap_unit.
    rewrite <- monad_law_4_x.
    f_equal.
    rewrite app_fmap_unit.
    rewrite fun_composition_x.
    f_equal. ext_eq.
    unfold compose.
    unfold EitherT_join'.
    destruct x; simpl.
      unfold Either_map.
        rewrite <- app_fmap_unit.
        rewrite app_homomorphism.
        reflexivity.
      destruct e. reflexivity.
Defined.

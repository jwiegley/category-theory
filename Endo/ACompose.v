Require Export Applicative.
Require Export FCompose.

(* Composition of applicatives produces an applicative. *)

Definition compose_eta (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} {A} : A -> F (G A) :=
  (@eta F _ (G A)) ∘ (@eta G _ A).

Definition compose_apply (F : Type -> Type) (G : Type -> Type)
  `{Applicative F} `{Applicative G} {A B}
  : F (G (A -> B)) -> F (G A) -> F (G B) :=
  apply ∘ fmap (@apply G _ A B).

Global Instance Applicative_Compose
  (F : Type -> Type) (G : Type -> Type)
  `{f_dict : Applicative F} `{g_dict : Applicative G}
  : Applicative (fun X => F (G X))  :=
{ is_functor := Functor_Compose F G
; eta := fun _ => compose_eta F G
; apply := fun _ _ => compose_apply F G
}.
Proof.
  - (* app_identity *) intros.
    ext_eq.
    unfold compose_apply, compose_eta, compose.
    rewrite <- app_fmap_unit.
    rewrite app_homomorphism.
    rewrite app_identity.
    rewrite app_fmap_unit.
    rewrite fun_identity.
    reflexivity.

  - (* app_composition *) intros.
    (* apply <$> (apply <$> (apply <$> eta (eta compose) <*> u) <*> v) <*> w =
       apply <$> u <*> (apply <$> v <*> w) *)
    unfold compose_apply, compose_eta, compose.
    rewrite <- app_composition.
    f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    rewrite app_split.
    rewrite app_split.
    rewrite <- app_naturality.
    rewrite fun_composition_x.
    rewrite fun_composition_x.
    f_equal. ext_eq.
    destruct x.
    unfold compose at 3.
    unfold app_merge.
    rewrite uncurry_works.
    unfold compose at 1.
    unfold compose at 1.
    rewrite uncurry_works.
    ext_eq.
    rewrite <- app_fmap_unit.
    rewrite app_composition.
    unfold compose.
    reflexivity.

  - (* app_homomorphism *) intros.
    unfold compose_apply, compose_eta, compose.
    rewrite <- app_fmap_unit.
    repeat (rewrite app_homomorphism).
    reflexivity.

  - (* app_interchange *) intros.
    unfold compose_apply, compose_eta, compose.
    repeat (rewrite <- app_fmap_unit).
    rewrite app_interchange.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    unfold compose. f_equal. ext_eq.
    rewrite <- app_fmap_unit.
    rewrite app_interchange.
    reflexivity.

  - (* app_fmap_unit *) intros.
    unfold compose_apply, compose_eta, compose.
    rewrite_app_homomorphisms.
    reflexivity.
Defined.

Require Export Functor.

(* Composition of functors produces a functor. *)

Definition compose_fmap
  (F : Type -> Type) (G : Type -> Type)
  `{Functor F} `{Functor G} {A B} :=
  (@fmap F _ (G A) (G B)) ∘ (@fmap G _ A B).

Global Instance Functor_Compose
  (F : Type -> Type) (G : Type -> Type) `{Functor F} `{Functor G}
  : Functor (fun X => F (G X)) :=
{ fmap := fun _ _ => compose_fmap F G
}.
Proof.
  - (* fun_identity *)
    intros. ext_eq. unfold compose_fmap, compose.
    rewrite fun_identity.
    rewrite fun_identity. reflexivity.

  - (* fun_composition *)
    intros. ext_eq. unfold compose_fmap, compose.
    rewrite fun_composition_x.
    rewrite fun_composition. reflexivity.
Defined.

Theorem fmap_compose
  : forall (F : Type -> Type) (G : Type -> Type)
      `{f_dict : Functor F} `{g_dict : Functor G}
      `{fg : Functor (fun X => F (G X))}
      {X Y} (f : X -> Y),
  (@fmap F f_dict (G X) (G Y) (@fmap G g_dict X Y f)) =
  (@fmap (fun X => F (G X)) fg X Y f).
Proof.
  intros; simpl.
  unfold compose_fmap.
Admitted.

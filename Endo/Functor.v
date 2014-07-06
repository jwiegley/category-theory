Require Export Iso.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class Functor (F : Type -> Type) :=
{ fobj := F
; fmap : forall {X Y}, (X -> Y) -> F X -> F Y

; fun_identity : forall {X}, fmap (@id X) = id
; fun_composition : forall {X Y Z} (f : Y -> Z) (g : X -> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.
  Arguments fmap            [F] [Functor] [X] [Y] f g.
  Arguments fun_identity    [F] [Functor] [X].
  Arguments fun_composition [F] [Functor] [X] [Y] [Z] f g.

Hint Resolve fun_identity.
Hint Resolve fun_composition.

Notation "f <$> g" := (fmap f g) (at level 68, left associativity).

Notation "fmap[ M ]  f" := (@fmap M _ _ _ f) (at level 68).
Notation "fmap[ M N ]  f" := (@fmap (fun X => M (N X)) _ _ _ f) (at level 66).
Notation "fmap[ M N O ]  f" := (@fmap (fun X => M (N (O X))) _ _ _ f) (at level 64).

Theorem fun_identity_x
  : forall (F : Type -> Type) (app_dict : Functor F) {X} (x : F X),
  fmap id x = id x.
Proof.
  intros.
  rewrite fun_identity.
  reflexivity.
Qed.

Hint Resolve fun_identity_x.

Theorem fun_composition_x
  : forall (F : Type -> Type) (app_dict : Functor F)
      {X Y Z} (f : Y -> Z) (g : X -> Y) (x : F X),
  f <$> (g <$> x) = (f ∘ g) <$> x.
Proof.
  intros.
  rewrite <- fun_composition.
  reflexivity.
Qed.

Hint Resolve fun_composition_x.

(* Functions are trivial functors. *)

Global Instance Hom_Functor {A} : Functor (fun X => A -> X) :=
{ fmap := fun X Y f g => f ∘ g
}.
Proof.
  - (* fun_identity *)
    intros. ext_eq. rewrite comp_id_left; reflexivity.
  - (* fun_composition *)
    intros. ext_eq. compute. reflexivity.
Defined.

Theorem uncompose_fmap : forall {A B C} (x : A) (g : A -> B) (f : B -> C),
  fmap f g = f ∘ g.
Proof. reflexivity. Qed.

Global Instance Functor_Isomorphism
  {F : Type -> Type} `{Functor F} {A B} `(A ≅ B) : F A ≅ F B :=
{ to   := fmap to
; from := fmap from
}.
Proof.
  - rewrite fun_composition.
    rewrite iso_to.
    apply fun_identity.
  - rewrite fun_composition.
    rewrite iso_from.
    apply fun_identity.
Defined.

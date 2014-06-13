Definition id {X} (a : X) : X := a.

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 60, right associativity).

Theorem comp_left_identity : forall {X Y} (f : X -> Y), id ∘ f = f.
Proof. intros. reflexivity.  Qed.

Theorem comp_right_identity : forall {X Y} (f : X -> Y), f ∘ id = f.
Proof. intros. reflexivity.  Qed.

Class Functor (F : Type -> Type) := {
  fmap : forall {X Y}, (X -> Y) -> F X -> F Y;
  functor_law_1 : forall {X} (x : F X), fmap (@id X) x = @id (F X) x;
  functor_law_2 : forall {X Y Z} (x : F X) (f : Y -> Z) (g : X -> Y),
    (fmap f ∘ fmap g) x = fmap (f ∘ g) x
}.

Class Monad (M : Type -> Type) (f_dict : Functor M) := {
  eta : forall {X}, X -> M X;
  mu : forall {X}, M (M X) -> M X;

  monad_law_1 : forall {X} (x : M (M (M X))), (mu ∘ fmap mu) x = (mu ∘ mu) x;
  monad_law_2 : forall {X} (x : M X), (mu ∘ fmap eta) x = x;
  monad_law_3 : forall {X} (x : M X), (mu ∘ eta) x = x;
  monad_law_4 : forall {X Y} (x : X) (f : X -> Y), (eta ∘ f) x = (fmap f ∘ eta) x;
  monad_law_5 : forall {X Y} (x : M (M X)) (f : X -> Y),
    (mu ∘ fmap (fmap f)) x = (fmap f ∘ mu) x
}.

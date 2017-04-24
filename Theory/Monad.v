Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Monad.

Context `{C : Category}.
Context `{M : C ⟶ C}.

Reserved Notation "f <*> g" (at level 29, left associativity).

Class Monad := {
  ret {a} : a ~> M a;
  join {a} : M (M a) ~> M a;

  join_fmap_join {a} : join ∘ fmap (@join a) ≈ join ∘ join;
  join_fmap_pure {a} : join ∘ fmap (@ret a) ≈ id;
  join_pure      {a} : join ∘ ret ≈ @id _ (M a);
  join_fmap_fmap {a b} (f : a ~> b) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Notation "join[ M ]" := (@join _ _ _ _ _ M _) (at level 9, format "join[ M ]").

Section MonadLib.

Context `{C : Category}.
Context `{A : @Cartesian C}.
Context `{@Closed C A}.
Context `{M : C ⟶ C}.
Context `{@Monad C M}.

Program Definition bind {a b : C} (f : a ~> M b) : M a ~> M b :=
  join ∘ fmap[M] f.

End MonadLib.

Require Import Category.Instance.Coq.

Module CoqMonad.

Section CoqMonad.

Context `{m : Coq ⟶ Coq}.
Context `{M : @Monad Coq m}.

Definition pure {a} := @ret Coq m _ a.
Arguments pure {a} _ /.

Notation "()" := Datatypes.unit.

Delimit Scope monad_scope with monad.

Open Scope monad_scope.

Notation "x >>= f" :=
  (@bind Coq m _ _ _ f x) (at level 42, right associativity) : monad_scope.
Notation "x >> y" :=
  (x >>= fun _ => y)%monad (at level 81, right associativity) : monad_scope.

Definition bind {a b : Type} (x : m a) (f : a -> m b) := x >>= f.

Definition kleisli_compose `(f : a -> m b) `(g : b -> m c) :
  a -> m c := fun x => (f x >>= g)%category.

Infix ">=>" := kleisli_compose (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ f _ g) (at level 42, right associativity,
                                    format "f >=[ m ]=> g") : monad_scope.
Notation "f <=[ m ]=< g" :=
  (@kleisli_compose _ m _ _ g _ f) (at level 42, right associativity,
                                    format "f <=[ m ]=< g") : monad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Definition when `(b : bool) (x : m ()) : m () :=
  if b then x else pure tt.

Definition unless `(b : bool) (x : m ()) : m () :=
  if negb b then x else pure tt.

(*
Fixpoint mapM `{Applicative m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Applicative m} {A B} (f : A -> m B) (l : list A) : m () :=
  match l with
  | nil => pure tt
  | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
  end.

Definition forM_ `{Applicative m} {A B} (l : list A) (f : A -> m B) : m () :=
  mapM_ f l.
*)

Definition foldM {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM {A : Type} {B : Type}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM {A : Type} {B : Type}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM f s l.

Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

(*
Definition concatMapM `{Applicative m} {A B}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  fmap flatten (mapM f l).
*)

Fixpoint replicateM_ (n : nat) (x : m ()) : m () :=
  match n with
  | O => pure tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM {a} (P : a -> a -> m bool)
  (z : a) (l : list a) : m (list a) :=
  match l with
  | nil => pure (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else pure (cons z (cons x xs))
  end.
Arguments insertM {a} P z l : simpl never.

Corollary join_fmap_join_x : forall a (x : (m ○ m ○ m) a),
  join (fmap join x) = join (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_join0; reflexivity.
Qed.

Corollary join_fmap_pure_x : forall a x,
  join (fmap (pure (a:=a)) x) = x.
Proof.
  intros.
  replace x with (id x) at 2; auto.
  pose proof (@join_fmap_pure Coq m M a) as HA.
  rewrite <- HA; reflexivity.
Qed.

Corollary join_pure_x : forall a x,
  join (pure x) = @id _ (m a) x.
Proof.
  intros.
  pose proof (@join_pure Coq m M a) as HA.
  rewrite <- HA; reflexivity.
Qed.

Corollary join_fmap_fmap_x : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_fmap0; reflexivity.
Qed.

End CoqMonad.

End CoqMonad.

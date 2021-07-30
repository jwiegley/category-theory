Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Monad.
Require Export Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monad.

Context {m : Coq ⟶ Coq}.
Context {M : @Monad Coq m}.

Notation "()" := Datatypes.unit : category_scope.

Declare Scope monad_scope.
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
  if b then x else ret tt.

Definition unless `(b : bool) (x : m ()) : m () :=
  if negb b then x else ret tt.

(*
Fixpoint mapM {Applicative m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => ret nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM {Applicative m} {A B} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ {Applicative m} {A B} (f : A -> m B) (l : list A) : m () :=
  match l with
  | nil => ret tt
  | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
  end.

Definition forM_ {Applicative m} {A B} (l : list A) (f : A -> m B) : m () :=
  mapM_ f l.
*)

Definition foldM {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => ret z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM {A : Type} {B : Type}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => ret z
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
  | O => ret tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM {a} (P : a -> a -> m bool)
  (z : a) (l : list a) : m (list a) :=
  match l with
  | nil => ret (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else ret (cons z (cons x xs))
  end.
Arguments insertM {a} P z l : simpl never.

Corollary join_fmap_join_x : forall a (x : (m ◯ m ◯ m) a),
  join (fmap join x) = join (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_join; reflexivity.
Qed.

Corollary join_fmap_ret_x : forall a x,
  join (fmap (ret (x:=a)) x) = x.
Proof.
  intros.
  replace x with (id x) at 2; auto.
  pose proof (@join_fmap_ret Coq m M a) as HA.
  rewrites; reflexivity.
Qed.

Corollary join_ret_x : forall a x,
  join (ret x) = @id _ (m a) x.
Proof.
  intros.
  pose proof (@join_ret Coq m M a) as HA.
  rewrites; reflexivity.
Qed.

Corollary join_fmap_fmap_x : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_fmap; reflexivity.
Qed.

End Monad.

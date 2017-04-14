Require Import Lib.
Require Export Adjunction.
Require Export Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Monad.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.
Context `{F ⊣ U}.

Class Monad := {
  join {a} : U (F (U (F a))) ~> U (F a) := fmap counit;

  (* jww (2017-04-13): These laws should follow from the adjunction. *)
  join_fmap_join {a} : @join a ∘ fmap[U ○ F] join ≈ join ∘ join;
  join_fmap_pure {a} : @join a ∘ fmap[U ○ F] unit ≈ id;
  join_pure      {a} : @join a ∘ unit ≈ id;
  join_fmap_fmap {a b} (f : a ~> b) :
    join ∘ fmap[U ○ F] (fmap[U ○ F] f) ≈ fmap[U ○ F] f ∘ join
}.

End Monad.

Notation "join[ M  ]" := (@join _ _ _ _ _ M _) (at level 9).

Definition monad_functor `{C : Category} `{D : Category}
           `{F : D ⟶ C} `{U : C ⟶ D} `{J : F ⊣ U}
           `{M : @Monad _ _ F U J} : D ⟶ D := functor_comp U F.

Coercion monad_functor : Monad >-> Functor.

Section MonadLib.

Context `{C : Category}.
Context `{D : Category}.
Context `{A : @Cartesian D}.
Context `{@Closed D A}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.
Context `{J : F ⊣ U}.
Context `{M : @Monad _ _ F U J}.

Program Definition bind {a b : D} (f : a ~> M b) : M a ~> M b :=
  join ∘ fmap[M] f.

End MonadLib.

Require Import Coq.

Module CoqMonad.

Context `{F : Coq ⟶ Coq}.
Context `{U : Coq ⟶ Coq}.
Context `{J : F ⊣ U}.

Definition Monad : Type := @Monad Coq Coq F U J.

Definition pure {a} := @unit _ _ _ _ _ a.

Notation "()" := Datatypes.unit.

Delimit Scope monad_scope with monad.

Open Scope monad_scope.

Notation "m >>= f" :=
  (@bind Coq Coq _ _ _ _ _ _ f m) (at level 42, right associativity)
    : monad_scope.
Notation "a >> b" :=
  (a >>= fun _ => b)%monad (at level 81, right associativity)
    : monad_scope.

Definition bind `{m : Monad} {a b : Type} (x : m a) (f : a -> m b) :=
  x >>= f.

Definition kleisli_compose `{m : Monad} `(f : a -> m b) `(g : b -> m c) :
  a -> m c := fun x => (f x >>= g)%category.

Infix ">=>" := kleisli_compose (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ f _ g) (at level 42, right associativity) : monad_scope.
Notation "f <=[ m ]=< g" :=
  (@kleisli_compose _ m _ _ g _ f) (at level 42, right associativity) : monad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Definition when `{m : Monad} `(b : bool) (x : m ()) : m () :=
  if b then x else pure tt.

Definition unless `{m : Monad} `(b : bool) (x : m ()) : m () :=
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

Definition foldM `{m : Monad} {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{m : Monad} {A : Type} {B : Type}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{m : Monad} {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{m : Monad} {A : Type} {B : Type}
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

Fixpoint replicateM_ `{m : Monad} (n : nat) (x : m ()) : m () :=
  match n with
  | O => pure tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM `{m : Monad} {a} (P : a -> a -> m bool)
  (z : a) (l : list a) : m (list a) :=
  match l with
  | nil => pure (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$[U ○ F]> insertM P z xs
    else pure (cons z (cons x xs))
  end.
Arguments insertM {m a} P z l : simpl never.

(*
Class Monad_Distributes `{M : Monad} `{N : Applicative} := {
  prod : forall A, N (M (N A)) -> M (N A)
}.

Arguments prod M {_} N {_ Monad_Distributes} A _.
*)

Corollary join_fmap_join_x `{m : Monad} : forall a (x : (m ○ m ○ m) a),
  join[m] (fmap[m] join[m] x) = join[m] (join[m] x).
Proof.
  intros.
  pose proof (@join_fmap_join _ _ _ _ J m a).
  simpl in H.
  apply equal_f with (x0:=x) in H.
  unfold join.
  simpl in *.
  rewrite <- H.
  reflexivity.
Qed.

(*
Corollary join_fmap_pure_x `{m : Monad} : forall a x,
  join (fmap (pure (a:=a)) x) ≈ x.
Proof.
  intros.
  replace x with (id x) at 2; auto.
  rewrite <- join_fmap_pure.
  reflexivity.
Qed.

Corollary join_pure_x `{m : Monad} : forall a x,
  join (pure x) ≈ @id (m a) x.
Proof.
  intros.
  rewrite <- join_pure.
  reflexivity.
Qed.

Corollary join_fmap_fmap_x `{m : Monad} : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) ≈ fmap f (join x).
Proof.
  intros.
  replace (fmap[m] f (join[m] x)) with ((fmap[m] f ∘ join[m]) x).
    rewrite <- join_fmap_fmap.
    reflexivity.
  reflexivity.
Qed.
*)

(*
(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having pure), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Class Monad_DistributesLaws `{Applicative (M ∘ N)} `{Monad_Distributes M N} :=
{
  m_monad_laws :> MonadLaws M;
  n_applicative_laws :> ApplicativeLaws N;

  prod_fmap_fmap : forall A B (f : A -> B),
    prod M N B ∘ fmap[N] (fmap[M ∘ N] f) ≈ fmap[M ∘ N] f ∘ prod M N A;
  prod_pure : forall A, prod M N A ∘ pure[N] ≈ @id (M (N A));
  prod_fmap_pure : forall A, prod M N A ∘ fmap[N] (pure[M ∘ N]) ≈ pure[M];
  prod_fmap_join_fmap_prod : forall A,
    prod M N A ∘ fmap[N] (join[M] ∘ fmap[M] (prod M N A))
      ≈ join[M] ∘ fmap[M] (prod M N A) ∘ prod M N (M (N A))
}.
*)

End CoqMonad.
